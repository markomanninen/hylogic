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

(defn test-ground-decision-never-claims-a-model-for-alg105 []
  ;; fixed constants once lacked "no other value", so a size-9 search could give a
  ;; constant two values and claim a model for this theorem (TPTP ALG105+1)
  (import os pathlib [Path] hylogic.tptp [read-problem])
  (setv root (os.environ.get "TPTP"))
  (when (or (not root) (not (.exists (/ (Path root) "Problems" "ALG" "ALG105+1.p"))))
    (pytest.skip "set TPTP to a TPTP library to run this test"))
  (setv p (read-problem (/ (Path root) "Problems" "ALG" "ALG105+1.p"))
        cl (lfor f [#* p.premises #("not" p.goal)] c (clausify f 8) c))
  (assert (!= (decide-ground cl :max-size 10) "saturated")))

(defn test-euf-congruence []
  ;; a = b gives f(a) = f(b) and then g(f(a)) = g(f(b)), with no domain bound
  (import hylogic.euf [decide-euf])
  (setv cl [(frozenset [#("=" "a" "b")])
            (frozenset [#("not" #("=" #("g" #("f" "a")) #("g" #("f" "b"))))])])
  (assert (= (decide-euf cl) "proved")))

(defn test-euf-non-theorem-and-predicates []
  (import hylogic.euf [decide-euf])
  ;; p(a), a = b, not p(b) is inconsistent; without a = b it has a model
  (setv base [(frozenset [#("p" "a")]) (frozenset [#("not" #("p" "b"))])])
  (assert (= (decide-euf [#* base (frozenset [#("=" "a" "b")])]) "proved"))
  (assert (= (decide-euf base) "saturated"))
  (assert (is (decide-euf [(frozenset [#("p" "?x")])]) None)))

(defn test-euf-distinct-objects []
  ;; TPTP distinct objects are different elements, so "x" = "y" is false
  (import hylogic.euf [decide-euf])
  (assert (= (decide-euf [(frozenset [#("=" "\"x\"" "\"y\"")])]) "proved"))
  (assert (= (decide-euf [(frozenset [#("=" "x" "y")])]) "saturated")))

(defn test-euf-agrees-with-the-bounded-ground-search []
  (import hylogic.euf [decide-euf])
  (setv rng (random.Random 5) agreed 0)
  (defn term [depth]
    (if (or (= depth 0) (< (.random rng) 0.4))
        (.choice rng ["a" "b" "c"])
        #("f" (term (- depth 1)))))
  (for [_ (range 60)]
    (setv cl (lfor _ (range (.randint rng 2 6))
               (frozenset (lfor _ (range (.randint rng 1 2))
                 :setv atom #("=" (term 2) (term 2))
                 (if (< (.random rng) 0.5) atom #("not" atom)))))
          exact (decide-euf cl) bounded (decide-ground cl))
    (when (is-not bounded None)
      (assert (= exact bounded))
      (+= agreed 1)))
  (assert (> agreed 30)))

(defn test-euf-proves-the-alg105-isomorphism []
  (import os pathlib [Path] hylogic.tptp [read-problem] hylogic.euf [decide-euf])
  (setv root (os.environ.get "TPTP"))
  (when (or (not root) (not (.exists (/ (Path root) "Problems" "ALG" "ALG105+1.p"))))
    (pytest.skip "set TPTP to a TPTP library to run this test"))
  (setv p (read-problem (/ (Path root) "Problems" "ALG" "ALG105+1.p"))
        cl (lfor f [#* p.premises #("not" p.goal)] c (clausify f 8) c))
  (assert (= (decide-euf cl) "proved")))

(defn test-split-clause-keeps-models-and-cuts-variables []
  (import itertools [count] hylogic.finite [split-clause] hylogic.terms [variables-of])
  ;; p(x,y) | q(y,z) | r(z,w) | s(w,v) shares one variable between neighbours
  (setv c [#("p" "?x" "?y") #("q" "?y" "?z") #("r" "?z" "?w") #("s" "?w" "?v")]
        parts (split-clause c (count 1)))
  (assert (> (len parts) 1))
  (assert (all (gfor p parts (< (len (variables-of (tuple p))) 5))))
  ;; a chain of 6 such clauses with a goal has the same answer either way
  (setv cl [(frozenset c) (frozenset [#("not" #("p" "?a" "?b"))]) (frozenset [#("not" #("q" "?a" "?b"))])
            (frozenset [#("not" #("r" "?a" "?b"))])])
  (assert (isinstance (find-finite-model cl :max-size 3) tuple))
  (assert (= (find-finite-model [#* cl (frozenset [#("not" #("s" "?a" "?b"))])] :max-size 3) "unsat")))

(defn test-skolem-terms-take-only-the-universals-they-need []
  (import hylogic.resolution [clausify] hylogic.terms [variables-of])
  ;; ∀x∀y (p(x) ∨ ∃z q(y, z)): the Skolem function depends on y alone
  (setv [c] (clausify #("forall" #("x" "y") #("or" #("p" "x") #("exists" #("z") #("q" "y" "z")))))
        q (next (gfor l c :if (= (get l 0) "q") l)))
  (assert (= (len (get q 2)) 2))
  ;; through an outer Skolem term: z = y = x keeps x
  (setv cl (clausify #("forall" #("x") #("exists" #("y") #("exists" #("z")
                        #("and" #("=" "y" "x") #("=" "z" "y")))))))
  (assert (all (gfor c cl l c (variables-of (tuple l))))))

(defn test-definitions-take-only-free-variables []
  (import hylogic.resolution [clausify])
  ;; a closed disjunct is named by a 0-ary atom; its own variable stays universal
  (setv inner #("forall" #("y") #("and" #("or" #("q" "y") #("r" "y")) #("or" #("s" "y") #("t" "y"))))
        cl (clausify #("or" inner #("and" "a" "b") #("and" "c" "d")) 2)
        defs (sfor c cl l c :setv a (if (= (get l 0) "not") (get l 1) l)
                   :if (and (isinstance a tuple) (.startswith (get a 0) "$def")) a))
  (assert defs)
  (assert (all (gfor a defs (= (len a) 1)))))

(defn test-epr-grounding-splits-unconnected-variables []
  ;; p(x) | q(y) | r(z) over 40 constants is 64000 instances, over the cap;
  ;; split into three one-variable parts it is 120 and decides at once
  (import hylogic.grounding [decide-epr])
  (setv facts (lfor i (range 40) (frozenset [#("s" f"c{i}")]))
        wide (frozenset [#("p" "?x") #("q" "?y") #("r" "?z")])
        refuted [(frozenset [#("not" #("p" "c5"))]) (frozenset [#("not" #("q" "c7"))])])
  (assert (= (decide-epr [#* facts wide #* refuted (frozenset [#("not" #("r" "c9"))])]) "proved"))
  (assert (= (decide-epr [#* facts wide #* refuted]) "saturated")))

(defn _check-ground-proof [clause]
  "Every resolve step is a resolvent of its parents on one complementary pair,
  and every instance cites a clause whose literals it instantiates."
  (import hylogic.unify [match-term])
  (setv seen #{} todo [clause] checked 0)
  (defn neg [l] (if (= (get l 0) "not") (get l 1) #("not" l)))
  (while todo
    (setv c (.pop todo))
    (when (in (id c) seen) (continue))
    (.add seen (id c))
    (.extend todo c.parents)
    (cond
      (= c.rule "resolve")
        (do
          (setv [a b] c.parents
                pairs (lfor l a.literals :if (in (neg l) b.literals) l))
          (assert (= (len pairs) 1))
          (setv [l] pairs)
          (assert (= c.literals (| (- a.literals #{l}) (- b.literals #{(neg l)}))))
          (+= checked 1))
      (.startswith c.rule "instance")
        (for [l c.literals :if (not (.startswith (str (get (if (= (get l 0) "not") (get l 1) l) 0)) "$split"))]
          (assert (any (gfor m (. (get c.parents 0) literals) (is-not (match-term m l) None)))))))
  checked)

(defn test-epr-proofs-replay-the-sat-solver-and-check []
  (import hylogic.grounding [epr-refutation])
  ;; every one of 40 constants has p or q, none has p, so some has q; but q(c7) is denied
  (setv facts (lfor i (range 40) (frozenset [#("s" f"c{i}")]))
        cl [#* facts (frozenset [#("p" "?x") #("q" "?x") #("not" #("s" "?x"))])
            (frozenset [#("not" #("p" "?y"))]) (frozenset [#("not" #("q" "c7"))])]
        r (epr-refutation cl))
  (assert r.proved)
  (assert (> (_check-ground-proof r.clause) 0))
  (assert (= (frozenset) r.clause.literals)))

(defn test-epr-proofs-on-random-problems-all-check []
  (import hylogic.grounding [decide-epr epr-refutation])
  (setv rng (random.Random 9) proved 0)
  (for [_ (range 120)]
    (setv cl (lfor _ (range (.randint rng 4 9))
               (frozenset (lfor _ (range (.randint rng 1 3))
                 :setv atom #((.choice rng ["p" "q" "r"]) (.choice rng ["a" "b" "?x" "?y"]))
                 (if (< (.random rng) 0.5) atom #("not" atom))))))
    (when (= (decide-epr cl) "proved")
      (setv r (epr-refutation cl))
      (assert r.proved)
      (_check-ground-proof r.clause)
      (+= proved 1)))
  (assert (> proved 10)))
