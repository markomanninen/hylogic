"Deciding effectively propositional problems by grounding.

A problem is effectively propositional (EPR) when its clauses have constants
but no functions with arguments. Then the Herbrand universe, the terms the
clauses can talk about, is just the finite set of constants, and by Herbrand's
theorem the clauses are unsatisfiable exactly when the set of all their ground
instances is. That set is propositional, so the SAT solver decides it.

Equality needs its axioms as ground instances too: reflexivity, symmetry,
transitivity and congruence over the constants. With them, a satisfying
assignment describes a model where = is a congruence, which shows the problem
satisfiable, so EPR problems get an exact answer either way. This is the idea
behind instantiation-based provers such as iProver."

(import itertools [product count]
        time
        hylogic.terms [variable? compound? show variables-of]
        hylogic.unify [instantiate]
        hylogic.cdcl [cdcl :as dpll]
        hylogic.finite [split-clause])

(defn _atom [lit] (if (and (compound? lit) (= (get lit 0) "not")) (get lit 1) lit))

(defn _symbols [clauses]
  "Constants, predicates with arities, and whether any function has arguments."
  (setv constants #{} predicates {} functional False)
  (defn term [t]
    (nonlocal functional)
    (cond
      (variable? t) None
      (compound? t) (setv functional True)
      True (.add constants t)))
  (for [c clauses  l c]
    (setv a (_atom l))
    (when (compound? a)
      (setv (get predicates (get a 0)) (- (len a) 1))
      (for [t (cut a 1 None)] (term t))))
  #(constants predicates functional))

(defn _equality-axioms [constants predicates]
  (setv cs (sorted constants) out [])
  (for [a cs] (.append out [#("=" a a)]))
  (for [a cs b cs] (when (!= a b) (.append out [#("not" #("=" a b)) #("=" b a)])))
  (for [a cs b cs c cs]
    (when (and (!= a b) (!= b c))
      (.append out [#("not" #("=" a b)) #("not" #("=" b c)) #("=" a c)])))
  (for [[p n] (.items predicates)]
    (when (!= p "=")
      (for [i (range n)  args (product cs :repeat n)  b cs]
        (when (!= (get args i) b)
          (setv moved (+ (cut args 0 i) #(b) (cut args (+ i 1) None)))
          (.append out [#("not" #("=" (get args i) b)) #("not" #(p #* args)) #(p #* moved)])))))
  out)

(defn ground-clauses [clauses [max-clauses 50000] [deadline None] [origins None]]
  "All ground instances of EPR clauses (with equality axioms if = occurs),
  or None if the clauses are not EPR or the instances would be too many.
  With an origins list, it gets for every instance #(clause split?), the input
  clause it came from and whether it was split first, or None for an equality axiom."
  ;; split clauses whose variables fall into unconnected groups (see
  ;; hylogic.finite): n^a + n^b instances instead of n^(a+b). Symbols are
  ;; collected afterwards, so the new predicates get equality axioms too.
  (setv fresh (count 1)
        parts (lfor c clauses
                :setv split (split-clause (list c) fresh 1)
                part split
                #(part c (> (len split) 1)))
        [constants predicates functional] (_symbols (lfor [part _ _] parts part)))
  (when functional (return None))
  (when (not constants) (setv constants #{"c0"}))
  (setv cs (sorted constants) out [])
  (for [[c source split] parts]
    (setv vs (variables-of (tuple c)))
    (when (> (+ (len out) (** (len cs) (len vs))) max-clauses) (return None))
    (when (and deadline (> (time.monotonic) deadline)) (return None))
    (for [values (product cs :repeat (len vs))]
      (setv s (dict (zip vs values)))
      (.append out (lfor l c (instantiate l s)))
      (when (is-not origins None) (.append origins #(source split)))))
  (when (in "=" predicates)
    (setv eq (_equality-axioms constants predicates))
    (when (> (+ (len out) (len eq)) max-clauses) (return None))
    (+= out eq)
    (when (is-not origins None) (.extend origins (* [None] (len eq)))))
  out)

(defn _cnf [ground]
  "Ground clauses as DIMACS-style integer clauses, with the atom of each variable."
  (setv atoms {} names [None] cnf [])
  (for [c ground]
    (setv row [])
    (for [l c]
      (setv neg (and (compound? l) (= (get l 0) "not"))
            key (show (_atom l)))
      (when (not-in key atoms)
        (setv (get atoms key) (len names))
        (.append names (_atom l)))
      (.append row (if neg (- (get atoms key)) (get atoms key))))
    (.append cnf row))
  #(cnf names))

(defn epr-refutation [clauses [goal-clauses #()] [deadline None]]
  "A readable refutation of unsatisfiable EPR clauses, as a hylogic.resolution
  Result: the SAT solver's own resolution steps (see hylogic.cdcl.refutation),
  over the ground instances it used, each citing the clause it instantiates.
  None if the clauses are satisfiable or the deadline passes."
  (import hylogic.resolution [Clause Result]
          hylogic.cdcl [Solver refutation _Timeout])
  (setv origins [] ground (ground-clauses clauses :deadline deadline :origins origins))
  (when (is ground None) (return None))
  (setv [cnf names] (_cnf ground) solver (Solver cnf deadline))
  (when (is-not (try (.solve solver) (except [_Timeout] (return None))) None)
    (return None))
  (setv [steps root] (refutation solver) inputs {} made {})
  (defn literal [n] (if (< n 0) #("not" (get names (- n))) (get names n)))
  (defn node [k]
    (when (in k made) (return (get made k)))
    (setv [lits parents] (get steps k) atoms (lfor n lits (literal n)))
    (if (= (len parents) 1)
        (do
          (setv i (get parents 0) origin (get origins i))
          (setv c (if (is origin None)
                      (Clause atoms #() "equality axiom")
                      (do
                        (setv [source split] origin)
                        (when (not-in source inputs)
                          (setv (get inputs source)
                                (Clause source #() (if (in source goal-clauses) "negated goal" "axiom"))))
                        (Clause atoms #((get inputs source)) (if split "instance, split" "instance"))))))
        (setv c (Clause atoms #((node (get parents 0)) (node (get parents 1))) "resolve")))
    (setv (get made k) c)
    c)
  ;; deep proofs: build children before parents without recursion depth trouble
  (for [k (sorted steps)] (node k))
  (Result "proved" (node root) {"kept" 0 "generated" 0}))

(defn decide-epr [clauses [deadline None]]
  "proved (unsatisfiable), saturated (satisfiable), or None when grounding does not apply."
  (setv ground (ground-clauses clauses :deadline deadline))
  (when (is ground None) (return None))
  (setv model (dpll (get (_cnf ground) 0) :deadline deadline))
  (cond
    (= model "timeout") None
    (is model None) "proved"
    True "saturated"))
