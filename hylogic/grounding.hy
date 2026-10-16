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

(import itertools [product]
        time
        hylogic.terms [variable? compound? show variables-of]
        hylogic.unify [instantiate]
        hylogic.cdcl [cdcl :as dpll])

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

(defn ground-clauses [clauses [max-clauses 50000] [deadline None]]
  "All ground instances of EPR clauses (with equality axioms if = occurs),
  or None if the clauses are not EPR or the instances would be too many."
  (setv [constants predicates functional] (_symbols clauses))
  (when functional (return None))
  (when (not constants) (setv constants #{"c0"}))
  (setv cs (sorted constants) out [])
  (for [c clauses]
    (setv vs (variables-of (tuple c)))
    (when (> (+ (len out) (** (len cs) (len vs))) max-clauses) (return None))
    (when (and deadline (> (time.monotonic) deadline)) (return None))
    (for [values (product cs :repeat (len vs))]
      (setv s (dict (zip vs values)))
      (.append out (lfor l c (instantiate l s)))))
  (when (in "=" predicates)
    (setv eq (_equality-axioms constants predicates))
    (when (> (+ (len out) (len eq)) max-clauses) (return None))
    (+= out eq))
  out)

(defn decide-epr [clauses [deadline None]]
  "proved (unsatisfiable), saturated (satisfiable), or None when grounding does not apply."
  (setv ground (ground-clauses clauses :deadline deadline))
  (when (is ground None) (return None))
  (setv atoms {} cnf [])
  (for [c ground]
    (setv row [])
    (for [l c]
      (setv neg (and (compound? l) (= (get l 0) "not"))
            key (show (_atom l)))
      (when (not-in key atoms) (setv (get atoms key) (+ (len atoms) 1)))
      (.append row (if neg (- (get atoms key)) (get atoms key))))
    (.append cnf row))
  (setv model (dpll cnf :deadline deadline))
  (cond
    (= model "timeout") None
    (is model None) "proved"
    True "saturated"))
