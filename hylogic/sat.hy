"Satisfiability for propositional formulas, beyond what truth tables can reach.

A truth table has 2^n rows, so twenty propositions already mean a million.
A SAT solver does better in practice:

1. The Tseitin transformation gives every subformula a new variable and
   writes clauses that tie it to its parts. The result has as many clauses
   as the formula has connectives, where distributing or over and can grow
   exponentially, and it is satisfiable exactly when the formula is.
2. DPLL (Davis, Putnam, Logemann and Loveland, 1962) searches for an
   assignment. It sets every variable that a clause forces (unit
   propagation), and otherwise guesses a variable and backtracks on conflict.

Clauses use DIMACS conventions: variables are positive integers, and a
negative integer is a negated variable.

  (satisfiable '(∧ (∨ P Q) (¬ P)))     ; {\"P\" False \"Q\" True}
  (valid? '(→ (∧ P Q) P))              ; True"

(import hylogic.formulas [basic operator-of args-of QUANTIFIERS]
        hylogic.terms [compound? show])

(defclass CNF []
  "Clauses for a formula, and the variable number of each atom."
  (defn __init__ [self]
    (setv self.clauses []
          self.atoms {}
          self.count 0))
  (defn new-var [self]
    (+= self.count 1)
    self.count)
  (defn atom-var [self name]
    (when (not-in name self.atoms)
      (setv (get self.atoms name) (.new-var self)))
    (get self.atoms name))
  (defn add [self #* lits]
    (.append self.clauses (tuple lits))))

(defn _encode [f cnf]
  "The variable that stands for f, with clauses that define it."
  (setv op (operator-of f))
  (cond
    (in op QUANTIFIERS)
      (raise (ValueError "SAT works on propositional formulas; use prove for quantifiers"))
    (= f "true") (do (setv x (.new-var cnf)) (.add cnf x) x)
    (= f "false") (do (setv x (.new-var cnf)) (.add cnf (- x)) x)
    (is op None) (.atom-var cnf (show f))
    True
      (do
        (setv xs (lfor a (args-of f) (_encode a cnf))
              x (.new-var cnf))
        (cond
          (= op "not") (do (setv a (get xs 0))
                           (.add cnf (- x) (- a))
                           (.add cnf x a))
          (= op "and") (do (for [a xs] (.add cnf (- x) a))
                           (.add cnf x #* (gfor a xs (- a))))
          (= op "or") (do (for [a xs] (.add cnf x (- a)))
                          (.add cnf (- x) #* xs))
          (= op "=>") (do (setv [a b] xs)
                          (.add cnf (- x) (- a) b)
                          (.add cnf x a)
                          (.add cnf x (- b)))
          (= op "<=>") (do (setv [a b] xs)
                           (.add cnf (- x) (- a) b)
                           (.add cnf (- x) a (- b))
                           (.add cnf x a b)
                           (.add cnf x (- a) (- b))))
        x)))

(defn tseitin [form]
  "A CNF whose clauses are satisfiable exactly when the formula is."
  (setv cnf (CNF))
  (.add cnf (_encode (basic form) cnf))
  cnf)

(defn dpll [clauses]
  "A satisfying assignment {variable: bool} for the clauses, or None."
  (_dpll (lfor c clauses (tuple c)) {}))

(defn _value [lit assignment]
  (setv v (.get assignment (abs lit)))
  (if (is v None) None (= v (> lit 0))))

(defn _dpll [clauses assignment]
  (setv assignment (dict assignment))
  ;; unit propagation: a clause with one open literal and no true one forces it
  (setv changed True)
  (while changed
    (setv changed False)
    (for [c clauses]
      (setv open [] satisfied False)
      (for [lit c]
        (setv v (_value lit assignment))
        (cond
          (is v True) (do (setv satisfied True) (break))
          (is v None) (.append open lit)))
      (when satisfied (continue))
      (when (not open) (return None))           ; every literal false: conflict
      (when (= (len open) 1)
        (setv lit (get open 0)
              (get assignment (abs lit)) (> lit 0)
              changed True))))
  ;; choose the open variable that occurs in the most unsatisfied clauses
  (setv counts {})
  (for [c clauses]
    (when (not (any (gfor lit c (is (_value lit assignment) True))))
      (for [lit c]
        (when (is (_value lit assignment) None)
          (setv (get counts (abs lit)) (+ (.get counts (abs lit) 0) 1))))))
  (when (not counts) (return assignment))       ; every clause satisfied
  (setv var (max counts :key (fn [v] (get counts v))))
  (for [choice [True False]]
    (setv result (_dpll clauses (| assignment {var choice})))
    (when (is-not result None) (return result)))
  None)

(defn satisfiable [form]
  "An assignment of the formula's atoms that makes it true, or None if there is none."
  (setv cnf (tseitin form)
        model (dpll cnf.clauses))
  (when (is model None) (return None))
  (dfor [name var] (.items cnf.atoms) name (.get model var False)))

(defn valid? [form]
  "Is the formula true under every assignment?"
  (is (satisfiable #("not" (basic form))) None))

(defn counterexample [premises conclusion]
  "An assignment that makes the premises true and the conclusion false, or None."
  (satisfiable #("and" #* (gfor p premises (basic p)) #("not" (basic conclusion)))))

(defn to-dimacs [form]
  "The formula's Tseitin clauses in DIMACS format, for any SAT solver."
  (setv cnf (tseitin form)
        lines [f"p cnf {cnf.count} {(len cnf.clauses)}"])
  (for [[name var] (.items cnf.atoms)]
    (.insert lines (- (len lines) 1) f"c {var} {name}"))
  (for [c cnf.clauses]
    (.append lines (+ (.join " " (map str c)) " 0")))
  (.join "\n" lines))
