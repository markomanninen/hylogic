"Arguments: premises and a conclusion.

  (require hylogic.argument [defargument])
  (defargument modus-ponens
    :premises [(→ P Q) P]
    :conclusion Q
    :meanings {P \"Today is Tuesday\" Q \"John will go to work\"})
  (print modus-ponens)
  (. modus-ponens valid)    ; => True

A propositional argument is checked with a truth table, which also finds a
counterexample when it is invalid. An argument with quantifiers or
predicates is checked with the resolution prover, using the search settings
the TPTP benchmarks measured best, and a countermodel is looked for when no
proof is found. Either way `used` names the premises a valid argument needs."

(import time
        hylogic.formulas [formula pretty operator-of args-of QUANTIFIERS]
        hylogic.terms [compound?]
        hylogic.truth [counterexample propositions]
        hylogic.sat [counterexample :as sat-counterexample]
        hylogic.resolution [prove clausify]
        hylogic.models [countermodel]
        hylogic.finite [find-finite-model distinct-constants])

;; the search settings benchmarks/tptp measured best: a main search, then
;; unordered superposition, which proves what the ordering prunes away
(setv SEARCH {"superposition" 1 "ordered" 1 "index" 1 "definitional" 8
              "age_ratio" 10 "goal_bias" 6})

(defn _mentions-equality [x]
  (cond
    (isinstance x tuple) (or (and x (= (get x 0) "=")) (any (gfor y x (_mentions-equality y))))
    True False))

(defn _finite-model-text [found]
  "A model from hylogic.finite as text: its size, function values and true facts."
  (setv [n facts] found lines [f"{n} elements"])
  (for [f (sorted facts :key str)]
    (.append lines (if (= (get f 0) "$fn")
                       (+ "  " (get f 1) "(" (.join ", " (map str (cut f 2 -1))) ") = " (str (get f -1)))
                       (if (isinstance f tuple)
                           (+ "  " (get f 0) "(" (.join ", " (map str (cut f 1 None))) ")")
                           (+ "  " (str f))))))
  (.join "\n" lines))

;; Up to this many propositions an argument is checked with a truth table,
;; which finds the first counterexample in table order. Beyond it the SAT
;; solver is used: benchmarks/methods.hy shows a truth table taking about
;; 0.15 s at 10 propositions and over 3 s at 14, and DPLL a few milliseconds.
(setv TRUTH-TABLE-LIMIT 10)

(defn propositional? [f]
  (setv op (operator-of f))
  (cond
    (in op QUANTIFIERS) False
    op (all (gfor a (args-of f) (propositional? a)))
    True (not (compound? f))))

(defclass Argument []
  (defn __init__ [self premises conclusion [meanings None] [limit 5000] [timeout 5]]
    (setv self.premises (lfor p premises (formula p))
          self.conclusion (formula conclusion)
          self.meanings (dfor [k v] (.items (or meanings {})) (str k) v)
          self.limit limit
          self.timeout timeout
          self._checked False))

  (defn check [self]
    "Decide validity once. Sets valid (True, False or None if undecided) and method."
    (when self._checked (return self))
    (setv self._checked True
          self.counterexample None
          self.used None
          self.proof None)
    (setv self.countermodel None)
    (cond
      (not (all (gfor f [#* self.premises self.conclusion] (propositional? f))))
        (do
          (setv equality (_mentions-equality #(#* self.premises self.conclusion))
                result (prove self.conclusion self.premises :limit self.limit
                              :timeout (* 0.6 self.timeout) #** SEARCH))
          (when (and (not result.proved) (!= result.status "saturated"))
            (setv second (prove self.conclusion self.premises :limit self.limit
                                :timeout (* 0.4 self.timeout) #** (| SEARCH {"ordered" 0})))
            (when second.proved (setv result second)))
          (setv self.method "resolution"
                self.proof (.proof result))
          (if result.proved
              (setv self.valid True
                    self.used (lfor i (.premises-used result) (+ i 1)))
              ;; a small world where the premises hold and the conclusion fails
              (do
                (setv self.countermodel (countermodel self.premises self.conclusion))
                (when (not self.countermodel)
                  (setv clauses (lfor f [#* self.premises #("not" self.conclusion)]  c (clausify f 8) c)
                        found (find-finite-model clauses :max-size 6
                                                 :fixed-constants (distinct-constants clauses)
                                                 :deadline (+ (time.monotonic) self.timeout)))
                  (when (isinstance found tuple)
                    (setv self.countermodel (_finite-model-text found))))
                (cond
                  self.countermodel (setv self.valid False self.method "countermodel")
                  ;; superposition may be incomplete, so its saturation proves nothing
                  (and (= result.status "saturated") (not equality)) (setv self.valid False)
                  True (setv self.valid None)))))
      True
        (do
          (setv small (<= (len (propositions #("and" #* self.premises self.conclusion))) TRUTH-TABLE-LIMIT)
                refute (if small counterexample sat-counterexample)
                self.method (if small "truth table" "SAT")
                self.counterexample (refute self.premises self.conclusion)
                self.valid (is self.counterexample None))
          ;; the premises needed: drop each one that the argument stays valid without
          (when self.valid
            (setv keep (list (range (len self.premises))))
            (for [i (list keep)]
              (setv trial (lfor k keep :if (!= k i) k))
              (when (is (refute (lfor k trial (get self.premises k)) self.conclusion) None)
                (setv keep trial)))
            (setv self.used (lfor k keep (+ k 1))))))
    self)

  (defn __getattr__ [self name]
    (when (in name #{"valid" "method" "counterexample" "countermodel" "proof" "used"})
      (.check self)
      (return (getattr self name)))
    (raise (AttributeError name)))

  (defn __str__ [self]
    (setv lines (lfor p self.premises (+ "  " (pretty p)))
          width (max (gfor l [#* lines (pretty self.conclusion)] (len l))))
    (.append lines (+ "  " (* "─" width)))
    (.append lines (+ "∴ " (pretty self.conclusion)))
    (when self.meanings
      (.append lines "")
      (for [[k v] (.items self.meanings)]
        (.append lines f"  {k}: {v}")))
    (.join "\n" lines))

  (defn explain [self]
    "The argument, its verdict and the reason."
    (.check self)
    (setv verdict (cond
                    self.valid "valid"
                    (is self.valid None) "undecided within the search limit"
                    True "invalid"))
    (setv lines [(str self) "" f"{(.capitalize verdict)}, by {self.method}."])
    (when self.counterexample
      (.append lines (+ "Counterexample: "
                        (.join ", " (gfor [k v] (.items self.counterexample)
                                          (+ k " = " (if v "⊤" "⊥")))))))
    (when self.countermodel
      (.append lines "A world where the premises are true and the conclusion is false:")
      (.append lines (str self.countermodel)))
    (.join "\n" lines)))

(defmacro defargument [name #* body]
  "Define an Argument from unquoted formulas: :premises [...] :conclusion f [:meanings {...}]."
  (setv opts (dict (zip (gfor k (cut body 0 None 2) k.name) (cut body 1 None 2))))
  (for [k opts]
    (when (not-in k #{"premises" "conclusion" "meanings"})
      (raise (SyntaxError f"defargument: unknown option :{k}"))))
  (setv meanings (.get opts "meanings"))
  (setv meanings
    (if meanings
        (hy.models.Dict (lfor [i x] (enumerate meanings) (if (% i 2) x (hy.models.String (str x)))))
        None))
  `(do
     (import hylogic.argument [Argument :as _Argument])
     (setv ~name (_Argument (quote ~(.get opts "premises" (hy.models.List)))
                            (quote ~(get opts "conclusion"))
                            :meanings ~meanings))))
