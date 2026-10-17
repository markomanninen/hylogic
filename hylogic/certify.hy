"Lean checks HyLogic's own proofs, one inference at a time.

hylogic.lean exports a problem to Lean as a statement. This module exports a
proof: every clause HyLogic derives becomes a small Lean theorem saying that
its premises imply it, and Lean has to prove each one. A proof is then trusted
because Lean checked every step, not because HyLogic says so.

A clause is the universal closure of the disjunction of its literals, over an
arbitrary nonempty type «$U». The symbols of the proof are implicit section
variables, so each step holds for every interpretation of them:

  theorem «$s10» («$h1» : ∀ «?X» «?T» : «$U», «inertia» «?X» («sk61» «?X» «?T») «?T» ∨ ¬«organization» «?X» «?T»)
      («$h2» : «organization» «sk80» «sk87») :
      «inertia» «sk80» («sk61» «sk80» «sk87») «sk87» := by
    have «$i1» := «$h1» «sk80» «sk87»
    grind

Lean's automation alone is weak at choosing instances of universally
quantified premises, so HyLogic replays each inference to find the
substitution it used (the unifier of a resolution or superposition, the
matches of the rewrite rules and unit clauses a simplification used) and
writes out those instances. What is left for grind is ground reasoning:
propositional logic and equality, which it decides. A variable that an
inference drops is instantiated with an arbitrary element of the domain.

  (certify result)   ; {\"verified\" True \"steps\" [...] ...}, Lean run on the proof

The last theorem, «$refutation», chains the steps: from the input clauses it
derives False by applying the step theorems. Lean checking it means the input
clauses are contradictory.

What is certified: every inference from the input clauses to the empty
clause. What is not: the clausal form itself (parsing, clausification and
Skolemization). The input clauses are taken as given, since a clause with a
Skolem function does not follow from its formula; it is only satisfiable
when the formula is. TPTP's distinct objects are input clauses too.

Grounding (hylogic.grounding) may split a clause A ∨ B whose parts share the
variables I into A ∨ s(I) and ¬s(I) ∨ B, with s a new predicate. Such an
instance does not follow from the clause alone, only together with the
definition s(I) ↔ ∀ y, B, which the step then takes as a premise. The
refutation takes the definitions as hypotheses as well, and «$closed»
discharges them by instantiating each s with its definition, so the input
clauses alone are shown contradictory."

(import os
        re
        subprocess
        tempfile
        time
        pathlib [Path]
        hylogic.lean [_name DOMAIN]
        hylogic.terms [variable? compound? show variables-of]
        hylogic.unify [unify substitute match-term instantiate]
        hylogic.superposition :as sp)

(setv WITNESS "?$w"            ; an arbitrary element, for variables an inference drops
      TACTIC "grind"
      ;; rules whose clause holds without premises; the others without premises are inputs
      VALID-RULES #{"equality lemma" "equality axiom"})

(defn _negative? [l] (and (compound? l) (= (get l 0) "not")))
(defn _atom [l] (if (_negative? l) (get l 1) l))
(defn _vars [lits] (sorted (sfor l lits v (variables-of l) v)))

;; Symbols

(defn _symbols-of [lits out]
  "Add the symbols of literals to out, a set of #(role name arity)."
  (defn term [t]
    (cond
      (variable? t) None
      (compound? t) (do (.add out #("fun" (get t 0) (- (len t) 1)))
                        (for [a (cut t 1 None)] (term a)))
      True (.add out #("const" t 0))))
  (for [l lits  :setv a (_atom l)]
    (cond
      (in a #{"true" "false"}) None
      (not (compound? a)) (.add out #("prop" a 0))
      (= (len a) 1) (.add out #("prop" (get a 0) 0))
      (and (= (get a 0) "=") (= (len a) 3)) (do (term (get a 1)) (term (get a 2)))
      True (do (.add out #("pred" (get a 0) (- (len a) 1)))
               (for [t (cut a 1 None)] (term t)))))
  out)

(defn _symbol-names [keys]
  "Lean names for symbols. A name used in two roles or arities gets them appended."
  (setv uses {})
  (for [k keys] (.setdefault uses (get k 1) []) (.append (get uses (get k 1)) k))
  (dfor k keys
        k (if (= (len (get uses (get k 1))) 1)
              (_name (get k 1))
              (_name (+ (str (get k 1)) "/" (get k 0) (str (get k 2)))))))

(defn _type-of [key]
  (setv [role _ n] key
        result (if (in role #{"prop" "pred"}) "Prop" DOMAIN))
  (.join " → " [#* (* [DOMAIN] n) result]))

;; Printing clauses as Lean propositions

(defclass Printer []
  "Clauses and terms as Lean text, with the proof's symbol names."
  (defn __init__ [self names [expand None]]
    (setv self.names names self.expand (or expand {})))

  (defn term [self t]
    (cond
      (variable? t) (_name t)
      (compound? t) (+ "(" (get self.names #("fun" (get t 0) (- (len t) 1))) " "
                       (.join " " (gfor a (cut t 1 None) (.term self a))) ")")
      True (get self.names #("const" t 0))))

  (defn atom [self a]
    (cond
      ;; a split predicate replaced by its definition, applied to the arguments
      (and (compound? a) (in (get a 0) self.expand))
        (if (> (len a) 1)
            (+ "((" (.lambda self (get a 0)) ") " (.join " " (gfor t (cut a 1 None) (.term self t))) ")")
            (+ "(" (.lambda self (get a 0)) ")"))
      (= a "true") "True"
      (= a "false") "False"
      (not (compound? a)) (get self.names #("prop" a 0))
      (= (len a) 1) (get self.names #("prop" (get a 0) 0))
      (and (= (get a 0) "=") (= (len a) 3)) (+ "(" (.term self (get a 1)) " = " (.term self (get a 2)) ")")
      True (+ "(" (get self.names #("pred" (get a 0) (- (len a) 1))) " "
              (.join " " (gfor t (cut a 1 None) (.term self t))) ")")))

  (defn literal [self l]
    (if (_negative? l) (+ "¬" (.atom self (get l 1))) (.atom self l)))

  (defn body [self lits]
    (if lits (.join " ∨ " (sorted (gfor l lits (.literal self l)))) "False"))

  (defn forall [self vs body]
    (if vs (+ "∀ " (.join " " (map _name vs)) " : " DOMAIN ", " body) body))

  (defn closure [self lits]
    "The universal closure of a clause."
    (.forall self (_vars lits) (.body self lits)))

  (defn lambda [self name]
    "A split predicate's definition as a Lean function of its shared variables."
    (setv [shared part] (get self.expand name)
          inner (.forall self (lfor v (_vars part) :if (not-in v shared) v) (.body self part)))
    (if shared (+ "fun " (.join " " (map _name shared)) " => " inner) inner))

  (defn definition [self name shared part]
    "The definition of a split predicate: s(I) ↔ ∀ y, B, y the other variables of B."
    (setv atom (if shared #(name #* shared) #(name))
          inner (lfor v (_vars part) :if (not-in v shared) v))
    (.forall self shared (+ (.atom self atom) " ↔ (" (.forall self inner (.body self part)) ")"))))

;; Replaying an inference to find the instances it used

(defn _rename [lits tag]
  "The literals with their variables renamed apart: #(literals mapping)."
  (setv mapping (dfor v (_vars lits) v (+ "?$" tag "_" (cut v 1 None))))
  #((frozenset (gfor l lits (instantiate l mapping))) mapping))

(defn _resolutions [a b]
  (for [x a  y b]
    (when (!= (_negative? x) (_negative? y))
      (setv s (unify (_atom x) (_atom y)))
      (when (is-not s None)
        (yield #((| (- a #{x}) (- b #{y})) s))))))

(defn _factors [a]
  (setv lits (sorted a :key show))
  (for [i (range (len lits))  j (range (+ i 1) (len lits))]
    (setv x (get lits i) y (get lits j))
    (when (= (_negative? x) (_negative? y))
      (setv s (unify (_atom x) (_atom y)))
      (when (is-not s None) (yield #(a s))))))

(defn _equality-resolutions [a]
  (for [l a]
    (when (and (_negative? l) (sp.equation? (_atom l)))
      (setv s (unify (get (_atom l) 1) (get (_atom l) 2)))
      (when (is-not s None) (yield #((- a #{l}) s))))))

(defn _equality-factors [a]
  (setv eqs (lfor l a :if (and (not (_negative? l)) (sp.equation? l)) l))
  (for [x eqs  y eqs  :if (is-not x y)
        [s t] [#((get x 1) (get x 2)) #((get x 2) (get x 1))]
        [s2 t2] [#((get y 1) (get y 2)) #((get y 2) (get y 1))]]
    (setv sub (unify s s2))
    (when (is-not sub None)
      (yield #((| (- a #{x}) #{#("not" #("=" t t2))}) sub)))))

(defn _superpositions [a b]
  "Superposition from the positive equations of a into b, ordering aside."
  (for [eq a  :if (and (not (_negative? eq)) (sp.equation? eq))
        [l r] [#((get eq 1) (get eq 2)) #((get eq 2) (get eq 1))]  :if (not (variable? l))
        lit b  [path u] (list (sp.atom-positions (_atom lit)))]
    (setv s (unify l u))
    (when (is-not s None)
      (setv new (sp.with-sign lit (sp.replace-at (_atom lit) path r)))
      (yield #((| (- a #{eq}) (- b #{lit}) #{new}) s)))))

(defn _candidates [rule parents]
  "#(literals substitution) for each way the rule derives a clause from the renamed
  parents; the literals are before the substitution is applied."
  (setv n (len parents))
  (cond
    (and (= rule "resolve") (= n 2)) (_resolutions #* parents)
    (and (= rule "factor") (= n 1)) (_factors #* parents)
    (and (= rule "equality resolution") (= n 1)) (_equality-resolutions #* parents)
    (and (= rule "equality factoring") (= n 1)) (_equality-factors #* parents)
    (and (= rule "superposition") (= n 2)) (_superpositions #* parents)
    ;; a rewritten clause: itself, before the rewriting below
    (and (in rule #{"simplification" "demodulation" "instance" "simplified"}) (>= n 1))
      [#((get parents 0) {})]
    True []))

(defn _rewrite [t rules found [budget 50]]
  "t rewritten innermost first, as hylogic.superposition does, recording each
  rule's premise and match in found. #(term steps)."
  (setv used 0)
  (when (compound? t)
    (setv args [])
    (for [a (cut t 1 None)]
      (setv [a2 n] (_rewrite a rules found (- budget used)))
      (+= used n)
      (.append args a2))
    (setv t #((get t 0) #* args)))
  (when (or (variable? t) (>= used budget)) (return #(t used)))
  (for [[l r k] rules]
    (setv m (match-term l t))
    (when (is-not m None)
      (.append found #(k m))
      (setv [t2 n] (_rewrite (instantiate r m) rules found (- budget used 1)))
      (return #(t2 (+ used 1 n)))))
  #(t used))

(defn _simplify [lits rules units found]
  "The clause as the prover simplifies it: without s ≠ s, rewritten with the
  rules, and without the literals a unit clause contradicts."
  (setv lits (sp.drop-false-equations lits) out [])
  (for [l lits  :setv a (_atom l)]
    (if (and (compound? a) (> (len a) 1))
        (setv a #((get a 0) #* (gfor x (cut a 1 None) (get (_rewrite x rules found) 0))))
        None)
    (setv l (if (_negative? l) #("not" a) a)
          hit (next (gfor [u k] units
                          :if (!= (_negative? u) (_negative? l))
                          :setv m (match-term (_atom u) a)
                          :if (is-not m None)
                          #(k m))
                    None))
    (if hit (.append found hit) (.append out l)))
  (sp.drop-false-equations (frozenset out)))

(defn _clause-match [c d [budget 20000]]
  "A substitution that maps every literal of c onto a literal of d, or None."
  (setv c (sorted c :key (fn [l] (len (str l)))) d (sorted d :key show) tries [budget])
  (defn go [i s]
    (when (= i (len c)) (return s))
    (for [m d]
      (-= (get tries 0) 1)
      (when (< (get tries 0) 0) (return None))
      (setv s2 (match-term (get c i) m s))
      (when (is-not s2 None)
        (setv r (go (+ i 1) s2))
        (when (is-not r None) (return r))))
    None)
  (go 0 {}))

(defn replay [clause premises]
  "The instances of the premises that clause follows from without further
  quantifier reasoning, as a list of #(premise-index substitution), the
  substitution mapping the premise's variables to terms over the clause's
  variables. None when no replay of the rule gives the clause."
  (setv rule (get (.split clause.rule "+") 0)
        n (len clause.parents)
        renamed (lfor [i p] (enumerate premises) (_rename p.literals (str i)))
        rules [] units [])
  ;; premises beyond the parents (and the given clause of a backward demodulation)
  ;; are the rewrite rules and units the simplification used
  (for [[k [lits _]] (enumerate renamed)]
    (when (or (>= k n) (and (= rule "demodulation") (= k 1)))
      (when (= (len lits) 1)
        (setv [l] lits)
        (.append units #(l k))
        (when (and (not (_negative? l)) (sp.equation? l))
          (for [[left right] (sp.rules-of l)] (.append rules #(left right k)))))))
  (for [[lits s] (_candidates rule (lfor [lits _] (cut renamed 0 n) lits))]
    (setv found []
          simplified (_simplify (frozenset (gfor l lits (substitute l s))) rules units found)
          theta (_clause-match simplified clause.literals))
    (when (is-not theta None)
      (defn final [t]
        "A term of the replay as a term over the clause's variables."
        (setv t (instantiate t theta))
        (instantiate t (dfor v (variables-of t) :if (in "$" v) v WITNESS)))
      (return
        (+ (lfor k (range n)
             :if (not (and (= rule "demodulation") (= k 1)))   ; the rule's premise: by its matches
             #(k (dfor [v x] (.items (get (get renamed k) 1)) v (final (substitute x s)))))
           (lfor [k m] found
             #(k (dfor [v x] (.items (get (get renamed k) 1)) v (final (instantiate x m)))))))))
  None)

;; The proof as Lean text

(defn proof-clauses [result]
  "The clauses of a proof, every clause after its premises, as in Result.proof."
  (setv order [] seen #{})
  (defn visit [c]
    (when (not-in (id c) seen)
      (.add seen (id c))
      (for [p [#* c.parents #* c.used]] (visit p))
      (.append order c)))
  (visit result.clause)
  order)

(defn _premises [c] [#* c.parents #* c.used])

(defn _split-definitions [clauses]
  "name -> #(shared part) for the split predicates the proof's instances mention,
  with those their definitions mention, from the records of hylogic.grounding."
  (setv out {})
  (for [c clauses  :setv known (getattr c "definitions" {})
        name (_definitions-needed c.literals known)]
    (setv (get out name) (get known name)))
  out)

(defn _definitions-needed [lits definitions]
  "The split predicates a clause mentions, and those their definitions mention, in order."
  (setv out [] todo (lfor l lits :setv a (_atom l) :if (compound? a) (get a 0)))
  (while todo
    (setv name (.pop todo))
    (when (and (in name definitions) (not-in name out))
      (.append out name)
      (for [l (get (get definitions name) 1)  :setv a (_atom l)  :if (compound? a)]
        (.append todo (get a 0)))))
  (sorted out))

(defn to-lean-proof [result [tactic TACTIC] [instances True]]
  "A proof as a Lean file: #(text steps), steps a list of dicts with the number,
  rule, theorem name and line span of each derived clause. Without instances,
  the replayed instances are left out and the tactic has to find them."
  (setv clauses (proof-clauses result)
        number (dfor [i c] (enumerate clauses) (id c) (+ i 1))
        definitions (_split-definitions clauses)
        keys (set))
  (for [c clauses] (_symbols-of c.literals keys))
  (for [[name [shared part]] (.items definitions)]
    (_symbols-of [#(name #* shared) #* part] keys))
  (setv names (_symbol-names keys) pr (Printer names)
        lines ["set_option maxRecDepth 100000"
               "set_option linter.unusedVariables false"
               "set_option linter.unusedSectionVars false"
               ""
               "section"
               (+ "variable {" DOMAIN " : Type} [Nonempty " DOMAIN "]")]
        steps [])
  (defn emit [#* texts]
    "Add text to the file, a line at a time, so that line numbers stay right."
    (for [t texts] (.extend lines (.split t "\n"))))
  (for [k (sorted keys :key str)]
    (emit (+ "variable {" (get names k) " : " (_type-of k) "}")))
  (defn define [name]
    (setv [shared part] (get definitions name))
    (.definition pr name shared part))
  (defn hyp [c] (+ "«$c" (str (get number (id c))) "»"))
  (for [c clauses  :if (or (_premises c) (in c.rule VALID-RULES))]
    (setv n (get number (id c))
          premises (_premises c)
          needed (if (.startswith c.rule "instance") (_definitions-needed c.literals definitions) [])
          start (+ (len lines) 1)
          head (+ "theorem «$s" (str n) "»")
          ground (all (gfor p premises (not (_vars p.literals))))
          replayed (if (or ground (not instances)) [] (replay c premises)))
    (emit "")
    (emit (+ "-- " (str n) ". " c.rule))
    (for [[i p] (enumerate premises)]
      (+= head (+ "\n    («$h" (str (+ i 1)) "» : " (.closure pr p.literals) ")")))
    (for [[i name] (enumerate needed)]
      (+= head (+ "\n    («$d" (str (+ i 1)) "» : " (define name) ")")))
    (emit (+ head " :\n    " (.closure pr c.literals) " := by"))
    (setv vs (_vars c.literals))
    (when vs (emit (+ "  intro " (.join " " (map _name vs)))))
    (setv haves (list (dict.fromkeys
                  (gfor [k s] (or replayed [])
                        :setv args (lfor v (_vars (. (get premises k) literals)) (.term pr (get s v)))
                        :if args
                        (+ "«$h" (str (+ k 1)) "» " (.join " " args)))))
          uses-witness (any (gfor h haves (in (_name WITNESS) h))))
    (when uses-witness
      (emit (+ "  have " (_name WITNESS) " : " DOMAIN " := Classical.ofNonempty")))
    (for [[i h] (enumerate haves)]
      (emit (+ "  have «$i" (str (+ i 1)) "» := " h)))
    (emit (+ "  " tactic))
    (.append steps {"number" n "rule" c.rule "theorem" (+ "$s" (str n))
                    "replayed" (or ground (and instances (is-not replayed None)))
                    "lines" #(start (len lines))}))
  ;; the refutation: the input clauses (and split definitions) give False
  (setv inputs (lfor c clauses :if (not (or (_premises c) (in c.rule VALID-RULES))) c)
        start (+ (len lines) 2)
        head "theorem «$refutation»")
  (for [c inputs] (+= head (+ "\n    (" (hyp c) " : " (.closure pr c.literals) ")")))
  (for [[i name] (enumerate (sorted definitions))]
    (+= head (+ "\n    («$d" name "» : " (define name) ")")))
  (emit "" (+ head " :\n    False := by"))
  (for [c clauses  :if (or (_premises c) (in c.rule VALID-RULES))]
    (setv needed (if (.startswith c.rule "instance") (_definitions-needed c.literals definitions) []))
    (emit (+ "  have " (hyp c) " : " (.closure pr c.literals) " := «$s" (str (get number (id c))) "»"
                      (.join "" (gfor p (_premises c) (+ " " (hyp p))))
                      (.join "" (gfor name needed (+ " «$d" name "»"))))))
  (emit (+ "  exact " (hyp result.clause)))
  (.append steps {"number" None "rule" "refutation" "theorem" "$refutation" "replayed" True
                  "lines" #(start (len lines))})
  (when definitions
    ;; the definitions hold when each split predicate is its definition
    (setv start (+ (len lines) 2) head "theorem «$closed»"
          expanding (Printer names definitions))
    (for [c inputs] (+= head (+ "\n    (" (hyp c) " : " (.closure pr c.literals) ")")))
    (emit "" (+ head " :\n    False :=")
                    (+ "  «$refutation»"
                       (.join "" (gfor name (sorted definitions)
                                       :setv shared (get (get definitions name) 0)
                                       (+ " (" (get names (if shared #("pred" name (len shared)) #("prop" name 0))) " := "
                                          (.lambda expanding name) ")")))
                       (.join "" (gfor c inputs (+ " " (hyp c))))
                       (.join "" (gfor name (sorted definitions)
                                       (if (get (get definitions name) 0)
                                           " (fun _ => Iff.rfl)"
                                           " Iff.rfl")))))
    (.append steps {"number" None "rule" "closed" "theorem" "$closed" "replayed" True
                    "lines" #(start (len lines))}))
  (emit "" "end" "")
  #((.join "\n" lines) steps))

;; Running Lean

;; such as Proof.lean:12:2: error: ... or, with a kind, error(lean.unknownIdentifier): ...
(setv _MESSAGE (re.compile r"^[^\n]*?\.lean:(\d+):\d+: (error|warning)(?:\([^)\n]*\))?: (.*?)(?=^[^\n]*?\.lean:\d+:\d+: |\Z)" (| re.M re.S)))

(defn run-lean [text [timeout 120]]
  "Lean's messages on a file: #(status messages), status ok, errors or timeout,
  messages a list of #(line kind text)."
  (with [d (tempfile.TemporaryDirectory)]
    (setv path (/ (Path d) "Proof.lean"))
    (.write-text path text)
    (try
      (setv out (subprocess.run [(os.environ.get "HYLOGIC_LEAN" "lean") (str path)] :capture-output True :text True :timeout timeout))
      (except [subprocess.TimeoutExpired] (return #("timeout" []))))
    (setv output (+ out.stdout out.stderr)
          messages (lfor m (.finditer _MESSAGE output)
                         #((int (.group m 1)) (.group m 2) (.strip (.group m 3)))))
    ;; an error the pattern did not read still counts, as an error on no line
    (when (and (!= out.returncode 0) (not (any (gfor m messages (= (get m 1) "error")))))
      (.append messages #(0 "error" (cut output 0 400))))
    #((if (and (= out.returncode 0) (not (any (gfor m messages (= (get m 1) "error"))))) "ok" "errors")
      messages)))

(defn certify [result [timeout 120] [tactic TACTIC] [instances True]]
  "Check a proof in Lean step by step. A dict: verified (Lean accepted every
  step and the refutation), status (ok, errors or timeout), steps (each with
  ok and Lean's first error), and seconds."
  (setv started (time.monotonic)
        [text steps] (to-lean-proof result tactic instances)
        [status messages] (run-lean text timeout))
  (for [s steps]
    (setv [a b] (get s "lines")
          problems (lfor [line kind msg] messages
                         :if (and (<= a line b) (or (= kind "error") (in "sorry" msg)))
                         msg))
    (setv (get s "ok") (not problems)
          (get s "error") (if problems (cut (get problems 0) 0 400) "")))
  (when (= status "timeout") (for [s steps] (setv (get s "ok") False (get s "error") "timeout")))
  ;; an error outside every step (such as in the declarations) fails them all
  (setv spans (lfor s steps (get s "lines"))
        stray (lfor [line kind msg] messages
                    :if (and (= kind "error") (not (any (gfor [a b] spans (<= a line b)))))
                    msg))
  (when stray (for [s steps] (setv (get s "ok") False (get s "error") (cut (get stray 0) 0 400))))
  {"verified" (and (= status "ok") (not stray) (all (gfor s steps (get s "ok"))))
   "status" status
   "steps" steps
   "text" text
   "seconds" (round (- (time.monotonic) started) 3)})
