(import itertools [product]
        re
        pytest
        hylogic.terms [term show]
        hylogic.unify [unify substitute match-term]
        hylogic.rewrite [normalize]
        hylogic.resolution [clausify clause-text prove subsumes? connective? args]
        hylogic.problems [PROPOSITIONAL FIRST-ORDER HARD NON-THEOREMS PEANO DERIVATIVE])

;; Unification

(defn t [form] (term form))

(defn test-unify-binds-both-sides []
  (setv s (unify (t '(Knows john ?x)) (t '(Knows ?y (mother ?y)))))
  (assert (= (show (substitute (t '(Knows john ?x)) s)) "(Knows john (mother john))")))

(defn test-unify-fails-on-clash-and-occurs-check []
  (assert (is (unify (t '(f a)) (t '(f b))) None))
  (assert (is (unify (t '?x) (t '(f ?x))) None)))

(defn test-match-binds-pattern-side-only []
  (assert (= (match-term (t '(+ 0 ?y)) (t '(+ 0 (s 0)))) {"?y" #("s" 0)}))
  (assert (is (match-term (t '(f a)) (t '(f ?y))) None))
  ;; a repeated pattern variable must match equal terms
  (assert (is (match-term (t '(d ?x ?x)) (t '(d x y))) None)))

;; Rewriting

(defn test-peano-two-times-two-is-four []
  (setv [nf steps] (normalize '(* (s (s 0)) (s (s 0))) PEANO))
  (assert (= (show nf) "(s (s (s (s 0))))"))
  (assert (> (len steps) 5)))

(defn test-derivative-of-x-times-x []
  (setv [nf _] (normalize '(d x (* x x)) DERIVATIVE))
  (assert (= (show nf) "(+ x x)"))
  (setv [nf _] (normalize '(d x (+ (* 3 x) 5)) DERIVATIVE))
  (assert (= (show nf) "3")))

(defn test-looping-rules-are-reported []
  (require hylogic.rewrite [defrules])
  (defrules LOOP (f ?x) -> (f (f ?x)))
  (with [(pytest.raises RuntimeError)]
    (normalize '(f a) LOOP :limit 50)))

;; Clausal form

(defn test-skolem-function-depends-on-the-universal-in-scope []
  (setv [c] (clausify '(forall [x] (exists [y] (Loves x y)))))
  (setv [lit] c)
  (assert (= (get lit 0) "Loves"))
  (assert (= (get lit 2 1) (get lit 1)))   ; (Loves ?x7 (sk8 ?x7))
  (assert (.startswith (get lit 2 0) "sk")))

(defn test-socrates-clauses []
  ;; variables get fresh numbers, ?x1, ?x2, ...
  (assert (= (lfor c (clausify '(forall [x] (=> (Man x) (Mortal x)))) (re.sub r"\?x\d+" "?x" (clause-text c)))
             ["(Mortal ?x) | (not (Man ?x))"])))

;; Truth tables, an independent check of the propositional problems

(defn atoms [f [found None]]
  (when (is found None) (setv found #{}))
  (cond
    (connective? f) (for [a (args f)] (atoms a found))
    True (.add found f))
  found)

(defn truth [f env]
  (if (not (connective? f))
      (get env f)
      (do
        (setv op (get f 0) xs (lfor a (args f) (truth a env)))
        (cond
          (= op "not") (not (get xs 0))
          (= op "and") (all xs)
          (= op "or") (any xs)
          (= op "=>") (or (not (get xs 0)) (get xs 1))
          (= op "<=>") (= (get xs 0) (get xs 1))))))

(defn valid? [axioms goal]
  (setv fs (lfor a axioms (term a)) g (term goal)
        names (sorted (atoms #("and" #* fs g))))
  (all (gfor values (product [True False] :repeat (len names))
             :setv env (dict (zip names values))
             (or (not (all (gfor f fs (truth f env)))) (truth g env)))))

(defn ids [problems] (lfor p problems (get p 0)))

(defn [(pytest.mark.parametrize "name, axioms, goal" PROPOSITIONAL :ids (ids PROPOSITIONAL))]
  test-propositional-problems [name axioms goal]
  (assert (valid? axioms goal))
  (assert (. (prove goal axioms) proved)))

(defn [(pytest.mark.parametrize "name, axioms, goal" FIRST-ORDER :ids (ids FIRST-ORDER))]
  test-first-order-problems [name axioms goal]
  (setv result (prove goal axioms))
  (assert result.proved)
  (assert (in "□" (get (.proof result) -1))))

(defn [(pytest.mark.parametrize "name, axioms, goal" NON-THEOREMS :ids (ids NON-THEOREMS))]
  test-non-theorems-are-not-proved [name axioms goal]
  (assert (not (. (prove goal axioms :limit 500) proved))))

(defn test-a-proof-reads-from-axioms-to-the-empty-clause []
  (setv [_ axioms goal] (get FIRST-ORDER 0)
        lines (.proof (prove goal axioms)))
  (assert (in "axiom" (get lines 0)))
  (assert (in "□" (get lines -1)))
  (assert (any (gfor l lines (in "negated goal" l)))))

(defn [(pytest.mark.parametrize "name, axioms, goal" HARD :ids (ids HARD))]
  test-hard-problems-need-a-larger-search [name axioms goal]
  (assert (= (. (prove goal axioms :limit 2000) status) "gave-up"))
  (assert (. (prove goal axioms :limit 10000) proved)))

(defn test-matching-with-shared-variable-names-does-not-loop []
  ;; the rule's ?x and ?y meet a term that uses the same names swapped
  (import hylogic.superposition [demodulate orient])
  (setv rule (orient #("=" #("m" "?x" "?y") "?x")))
  (setv [out changed] (demodulate (frozenset [#("p" #("m" "?y" "?x"))]) [rule]))
  (assert changed)
  (assert (= out (frozenset [#("p" "?y")]))))

(defn test-ordered-resolution-stays-complete-on-swb020 []
  ;; selection once depended on variable names, so a clause could select different
  ;; literals as given clause and as partner, and this theorem saturated unproved
  (import os pathlib [Path] hylogic.tptp [read-problem])
  (setv root (os.environ.get "TPTP"))
  (when (or (not root) (not (.exists (/ (Path root) "Problems" "SWB" "SWB020+2.p"))))
    (pytest.skip "set TPTP to a TPTP library to run this test"))
  (setv p (read-problem (/ (Path root) "Problems" "SWB" "SWB020+2.p")))
  (for [opts [{"ordered" 1 "definitional" 8} {"age_ratio" 10 "superposition" 1 "ordered" 1 "index" 1 "definitional" 8}]]
    (assert (= (. (prove p.goal p.premises :limit 1000000 :timeout 60 #** opts) status) "proved") opts)))

(defn test-unit-deletion-cuts-literals-and-cites-the-unit []
  ;; ¬q(a) removes q(a) from p(x) | q(x) once processed; the proof names it
  (setv r (prove #("p" "a") [#("forall" #("x") #("or" #("p" "x") #("q" "x"))) #("not" #("q" "a"))]))
  (assert r.proved)
  (setv lines (.proof r))
  (assert (any (gfor l lines (in "unit deletion" l)))))

(defn test-a-new-rule-rewrites-the-processed-goal []
  ;; e = c arrives after the goal is processed; backward demodulation
  ;; turns f(e) ≠ f(c) into f(c) ≠ f(c), and the proof cites the rule
  (setv r (prove #("=" #("f" "e") #("f" "c"))
                 [#("forall" #("x" "y") #("=" #("g" #("g" "e")) "c"))
                  #("forall" #("x") #("=" #("g" "x") "x"))]
                 :superposition 1))
  (assert r.proved)
  (assert (any (gfor l (.proof r) (in "(= e c)" l)))))

(defn test-solve-keeps-its-time-limit []
  ;; grounding once checked the clock only between clauses, and clause splitting
  ;; was cubic on long clauses: ALG026+1 took 27 s with a 10 s limit
  (import os time pathlib [Path] hylogic.tptp [solve])
  (setv root (os.environ.get "TPTP"))
  (when (or (not root) (not (.exists (/ (Path root) "Problems" "ALG" "ALG026+1.p"))))
    (pytest.skip "set TPTP to a TPTP library to run this test"))
  (setv start (time.monotonic))
  (solve (str (/ (Path root) "Problems" "ALG" "ALG026+1.p")) :time-limit 4 :epr 1 :equality 2
         :definitional 8 :finder_first 30 :portfolio 80 :ordered 1 :index 1)
  (assert (< (- (time.monotonic) start) 5.5)))

(defn test-subsumption-of-long-similar-clauses-stays-fast []
  ;; 12 literals r(?xi, ?xi+1) against 14 ground r(ai, bj): matching each one
  ;; separately succeeds, chaining them fails, and the search used to try
  ;; exponentially many mappings (LCL657+1.020 ran 68 s with an 8 s limit)
  (import time)
  (setv c (frozenset (gfor i (range 12) #("r" f"?x{i}" f"?x{(+ i 1)}")))
        d (frozenset (gfor i (range 14) #("r" f"a{(% i 3)}" f"b{(% i 5)}")))
        start (time.monotonic))
  (assert (not (subsumes? c d)))
  (assert (< (- (time.monotonic) start) 1))
  ;; and real subsumption is still found
  (assert (subsumes? (frozenset [#("p" "?x") #("q" "?x")]) (frozenset [#("p" "a") #("q" "a") #("r" "b")]))))
