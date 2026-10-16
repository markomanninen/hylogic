(import random
        time
        pytest
        hylogic.formulas [formula pretty]
        hylogic.evaluate [evaluate]
        hylogic.truth [tautology? propositions]
        hylogic.sat [tseitin dpll satisfiable valid? counterexample to-dimacs]
        hylogic.export [to-smtlib to-tptp check-with-z3 signature]
        hylogic.problems [PROPOSITIONAL FIRST-ORDER HARD NON-THEOREMS])

(defn random-formula [rng depth]
  (if (or (= depth 0) (< (.random rng) 0.25))
      (.choice rng ["P" "Q" "R" "S"])
      (do
        (setv op (.choice rng ["¬" "∧" "∨" "→" "↔" "⊕" "↑" "↓" "≡"]))
        (if (= op "¬")
            #(op (random-formula rng (- depth 1)))
            #(op (random-formula rng (- depth 1)) (random-formula rng (- depth 1)))))))

;; SAT

(defn test-sat-agrees-with-truth-tables-on-random-formulas []
  (setv rng (random.Random 7))
  (for [_ (range 400)]
    (setv f (random-formula rng 5))
    (when (propositions f)
      (assert (= (valid? f) (tautology? f)) (pretty f))
      (setv model (satisfiable f))
      (when (is-not model None)
        ;; a model must really satisfy the formula
        (assert (evaluate f (| (dfor p (propositions f) p False) model)) (pretty f))))))

(defn test-sat-finds-counterexamples []
  (assert (is (counterexample ['(→ P Q) 'P] 'Q) None))
  (setv ce (counterexample ['(→ P Q) 'Q] 'P))
  (assert (= (get ce "P") False))
  (assert (= (get ce "Q") True)))

(defn pigeonhole [pigeons holes]
  "Every pigeon sits in some hole, and no two pigeons share a hole."
  (setv p (fn [i j] f"p{i}h{j}"))
  #("and"
    #* (gfor i (range pigeons) #("or" #* (gfor j (range holes) (p i j))))
    #* (gfor j (range holes) a (range pigeons) b (range (+ a 1) pigeons)
             #("not" #("and" (p a j) (p b j))))))

(defn test-sat-handles-more-variables-than-truth-tables []
  ;; 20 variables would mean a million truth-table rows
  (assert (is (satisfiable (pigeonhole 5 4)) None))      ; 5 pigeons do not fit in 4 holes
  (assert (is-not (satisfiable (pigeonhole 4 4)) None))
  ;; a chain of 40 equivalences
  (setv names (lfor i (range 40) f"x{i}")
        chain #("and" #* (gfor [a b] (zip names (cut names 1 None)) #("<=>" a b))))
  (assert (valid? #("=>" #("and" chain (get names 0)) (get names -1)))))

(defn test-tseitin-is-linear []
  (setv cnf (tseitin (pigeonhole 5 4)))
  (assert (< (len cnf.clauses) 500)))

(defn test-dimacs []
  (setv text (to-dimacs '(∨ P Q)))
  (assert (in "p cnf 3 4" text))
  (assert (in "c 1 P" text)))

;; SMT-LIB and TPTP

(defn test-signature []
  (setv sig (signature [(formula '(∀ [x] (→ (Man x) (Loves x (mother x))))) (formula '(∧ P (Man socrates)))]))
  (assert (= (get sig "predicates") {"Man" 1 "Loves" 2}))
  (assert (= (get sig "functions") {"mother" 1}))
  (assert (= (get sig "constants") #{"socrates"}))
  (assert (= (get sig "propositions") #{"P"})))

(defn test-smtlib-text []
  (setv text (to-smtlib ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)] '(Mortal socrates)))
  (assert (in "(declare-fun |Man| (U) Bool)" text))
  (assert (in "(declare-const |socrates| U)" text))
  (assert (in "(assert (forall ((|x| U)) (=> (|Man| |x|) (|Mortal| |x|))))" text))
  (assert (.endswith text "(check-sat)")))

(defn test-tptp-text []
  (setv text (to-tptp ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)] '(Mortal socrates)))
  (assert (in "fof(premise_1, axiom, (! [X_x] : (man(X_x) => mortal(X_x))))." text))
  (assert (in "fof(goal, conjecture, (mortal(socrates)))." text)))

(setv ALL [#* (lfor [n a g] [#* PROPOSITIONAL #* FIRST-ORDER #* HARD] #(n a g "valid"))
           #* (lfor [n a g] NON-THEOREMS #(n a g "invalid"))])

(defn [(pytest.mark.parametrize "name, axioms, goal, expected" ALL :ids (lfor p ALL (get p 0)))]
  test-z3-agrees-on-every-problem [name axioms goal expected]
  (pytest.importorskip "z3")
  (assert (= (check-with-z3 axioms goal) expected)))

;; Finite models

(import hylogic.models [find-model countermodel]
        hylogic.argument [Argument])

(defn test-countermodel-for-the-converse []
  (setv m (countermodel ['(∀ [x] (→ (Man x) (Mortal x))) '(Mortal fido)] '(Man fido)))
  (assert (is-not m None))
  (assert (= (len m.domain) 1))
  ;; the premises hold and the conclusion fails in the model it found
  (setv world (.as-model m))
  (assert (evaluate '(∀ [x] (→ (Man x) (Mortal x))) world m.domain))
  (assert (not (evaluate '(Man fido) world m.domain)))
  (assert (in "Domain: d1" (str m))))

(defn test-countermodels-for-the-non-theorems []
  (for [[name axioms goal] NON-THEOREMS]
    (assert (is-not (countermodel axioms goal) None) name)))

(defn test-no-countermodel-for-theorems []
  (for [[name axioms goal] (cut FIRST-ORDER 0 6)]
    (assert (is (countermodel axioms goal :max-size 3) None) name)))

(defn test-functions-get-tables []
  ;; everyone's mother loves them, but not everyone loves their mother
  (setv m (countermodel ['(∀ [x] (Loves (mother x) x))] '(∀ [x] (Loves x (mother x)))))
  (assert (is-not m None))
  (assert (in "mother" m.functions)))

(defn test-invalid-first-order-argument-gets-a-world []
  (setv a (Argument ['(∀ [x] (→ (Man x) (Mortal x))) '(Mortal fido)] '(Man fido)))
  (assert (is a.valid False))
  (assert (= a.method "countermodel"))
  (assert (in "A world where the premises are true" (.explain a))))

(defn test-large-propositional-argument-uses-sat []
  (setv names (lfor i (range 16) f"x{i}")
        a (Argument (lfor [p q] (zip names (cut names 1 None)) #("=>" p q)) #("=>" (get names 0) (get names -1))))
  (assert a.valid)
  (assert (= a.method "SAT")))

;; Finite models by flattening into SAT

(import hylogic.finite [find-finite-model flatten-clause distinct-constants]
        hylogic.resolution [clausify])

(defn clauses-of-all [fs] (lfor f fs c (clausify f) c))

(defn test-flattening []
  (setv flat (flatten-clause [#("p" #("f" "a"))]))
  ;; p(f(a)) becomes p(y1) with ¬$fn(a, y2) and ¬$fn(f, y2, y1)
  (assert (= (len flat) 3))
  (assert (any (gfor l flat (and (= (get l 0) "not") (= (get l 1 1) "f"))))))

(defn test-finite-model-for-a-function []
  ;; everyone's mother loves them, but not everyone loves their mother
  (setv found (find-finite-model (clauses-of-all ['(∀ [x] (Loves (mother x) x))
                                                  '(¬ (∀ [x] (Loves x (mother x))))])))
  (assert (isinstance found tuple)))

(defn test-no-finite-model-for-a-theorem []
  (assert (= (find-finite-model (clauses-of-all ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)
                                                 '(¬ (Mortal socrates))]) :max-size 3)
             "unsat")))

(defn test-distinct-constants []
  (assert (= (sorted (distinct-constants (clauses-of-all ['(¬ (= a b)) '(¬ (= b c)) '(¬ (= a c))])))
             ["a" "b" "c"])))

(defn test-equality-is-exported-as-equality []
  (setv smt (to-smtlib ['(= a b) '(P a)] '(P b)))
  (assert (in "(assert (= |a| |b|))" smt))
  (assert (not-in "declare-fun |=|" smt))
  (assert (in "(a = b)" (to-tptp ['(= a b)] '(P b)))))

(defn test-z3-checks-equality []
  (pytest.importorskip "z3")
  (assert (= (check-with-z3 ['(= a b) '(P a)] '(P b)) "valid"))
  (assert (= (check-with-z3 ['(P a)] '(P b)) "invalid")))

;; Ground problems with functions

(import hylogic.ground [decide-ground])

(defn closure [f]
  "Clauses saying f maps each of a, b to a or b."
  (lfor x ["a" "b"] (frozenset [#("=" #(f x) "a") #("=" #(f x) "b")])))

(defn test-ground-theorem-with-a-function []
  ;; f(a) = b, f(b) = a and a != b, so f(f(a)) = a
  (setv cl [#* (closure "f") (frozenset [#("=" #("f" "a") "b")]) (frozenset [#("=" #("f" "b") "a")])
            (frozenset [#("not" #("=" "a" "b"))]) (frozenset [#("not" #("=" #("f" #("f" "a")) "a"))])])
  (assert (= (decide-ground cl) "proved")))

(defn test-ground-non-theorem-has-a-model []
  ;; nothing forces f(a) = a
  (setv cl [#* (closure "f") (frozenset [#("not" #("=" "a" "b"))]) (frozenset [#("not" #("=" #("f" "a") "a"))])])
  (assert (= (decide-ground cl) "saturated")))

(defn test-ground-needs-ground-clauses []
  (assert (is (decide-ground [(frozenset [#("p" "?x")])]) None)))
