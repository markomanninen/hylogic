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
predicates is checked with the resolution prover."

(import hylogic.formulas [formula pretty operator-of args-of QUANTIFIERS]
        hylogic.terms [compound?]
        hylogic.truth [counterexample propositions]
        hylogic.sat [counterexample :as sat-counterexample]
        hylogic.resolution [prove]
        hylogic.models [countermodel])

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
  (defn __init__ [self premises conclusion [meanings None] [limit 5000]]
    (setv self.premises (lfor p premises (formula p))
          self.conclusion (formula conclusion)
          self.meanings (dfor [k v] (.items (or meanings {})) (str k) v)
          self.limit limit
          self._checked False))

  (defn check [self]
    "Decide validity once. Sets valid (True, False or None if undecided) and method."
    (when self._checked (return self))
    (setv self._checked True
          self.counterexample None
          self.proof None)
    (setv self.countermodel None)
    (cond
      (not (all (gfor f [#* self.premises self.conclusion] (propositional? f))))
        (do
          (setv result (prove self.conclusion self.premises :limit self.limit)
                self.method "resolution"
                self.proof (.proof result))
          (if result.proved
              (setv self.valid True)
              ;; a small world where the premises hold and the conclusion fails
              (do
                (setv self.countermodel (countermodel self.premises self.conclusion))
                (cond
                  self.countermodel (setv self.valid False self.method "countermodel")
                  (= result.status "saturated") (setv self.valid False)
                  True (setv self.valid None)))))
      (<= (len (propositions #("and" #* self.premises self.conclusion))) TRUTH-TABLE-LIMIT)
        (setv self.method "truth table"
              self.counterexample (counterexample self.premises self.conclusion)
              self.valid (is self.counterexample None))
      True
        (setv self.method "SAT"
              self.counterexample (sat-counterexample self.premises self.conclusion)
              self.valid (is self.counterexample None)))
    self)

  (defn __getattr__ [self name]
    (when (in name #{"valid" "method" "counterexample" "countermodel" "proof"})
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
