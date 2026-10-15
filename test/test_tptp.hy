(import os
        pytest
        hylogic.tptp [Parser tokens read-problem solve TPTPError])

(defn parse [text]
  (.logic (Parser (tokens text))))

(defn test-quantifiers-and-precedence []
  (assert (= (parse "! [X] : (p(X) => q(X))")
             #("forall" #("X") #("=>" #("p" "X") #("q" "X")))))
  (assert (= (parse "~ p & q | r") #("and" #("not" "p") "q")) "| after & needs parentheses in TPTP")
  (assert (= (parse "(~ p & q) | r") #("or" #("and" #("not" "p") "q") "r")))
  (assert (= (parse "? [X,Y] : f(X) = g(Y)") #("exists" #("X" "Y") #("=" #("f" "X") #("g" "Y"))))))

(defn test-all-binary-connectives []
  (assert (= (parse "p <=> q") #("<=>" "p" "q")))
  (assert (= (parse "p <= q") #("=>" "q" "p")))
  (assert (= (parse "p <~> q") #("not" #("<=>" "p" "q"))))
  (assert (= (parse "p ~| q") #("not" #("or" "p" "q"))))
  (assert (= (parse "p ~& q") #("not" #("and" "p" "q"))))
  (assert (= (parse "a != b") #("not" #("=" "a" "b"))))
  (assert (= (parse "$true & $false") #("and" "true" "false"))))

(defn test-names-that-look-like-connectives-are-renamed []
  (assert (= (parse "or(not, 'and')") #("or_" "not_" "and_")))
  (assert (= (parse "'two words'(c)") #("two words" "c"))))

(defn test-comments-are-skipped []
  (assert (= (parse "p % comment\n /* block\n comment */ & q") #("and" "p" "q"))))

(defn problem-tree [tmp-path]
  "A small TPTP root with an axiom file and a problem that includes part of it."
  (setv axioms (/ tmp-path "Axioms") problems (/ tmp-path "Problems" "TST"))
  (.mkdir axioms :parents True)
  (.mkdir problems :parents True)
  (.write-text (/ axioms "TST001+0.ax")
               "fof(man_mortal, axiom, ! [X] : (man(X) => mortal(X))).\nfof(unused, axiom, $false).\n")
  (.write-text (/ problems "TST001+1.p")
               (+ "% Status   : Theorem\n"
                  "include('Axioms/TST001+0.ax', [man_mortal]).\n"
                  "fof(socrates, axiom, man(socrates)).\n"
                  "fof(goal, conjecture, mortal(socrates)).\n"))
  (.write-text (/ problems "TST002+1.p")
               (+ "% Status   : CounterSatisfiable\n"
                  "fof(goal, conjecture, a = b).\n"))
  (.write-text (/ problems "TST003-1.p")
               (+ "cnf(c1, axiom, ~ p(X) | q(X)).\n"
                  "cnf(c2, axiom, p(a)).\n"
                  "cnf(c3, negated_conjecture, ~ q(a)).\n"))
  problems)

(defn test-include-with-selection [tmp-path]
  (setv problems (problem-tree tmp-path)
        p (read-problem (/ problems "TST001+1.p")))
  ;; only the selected axiom comes in, not $false
  (assert (= (len p.premises) 2))
  (assert (= p.conjecture #("mortal" "socrates")))
  (assert (= p.status "Theorem"))
  (setv [status result _] (solve (/ problems "TST001+1.p") :time-limit 5))
  (assert (= status "Theorem")))

(defn test-equality-countermodel-respects-identity [tmp-path]
  ;; a = b does not follow from nothing; with = as identity a two-element model shows it
  (setv problems (problem-tree tmp-path)
        [status _ _] (solve (/ problems "TST002+1.p") :time-limit 5))
  (assert (= status "CounterSatisfiable")))

(defn test-cnf-clauses-are-closed-and-refuted [tmp-path]
  (setv problems (problem-tree tmp-path)
        [status _ problem] (solve (/ problems "TST003-1.p") :time-limit 5))
  (assert (is problem.conjecture None))
  (assert (= status "Unsatisfiable")))

(defn test-unsupported-formula-kinds [tmp-path]
  (setv path (/ tmp-path "Problems" "TST" "TST004^1.p"))
  (.mkdir path.parent :parents True)
  (.write-text path "thf(a, axiom, p).\n")
  (with [(pytest.raises TPTPError :match "thf")]
    (read-problem path)))
