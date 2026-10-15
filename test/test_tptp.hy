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

(defn test-include-with-selection [tmp-path monkeypatch]
  ;; includes resolve against this temporary root, not a real library in TPTP
  (.delenv monkeypatch "TPTP" :raising False)
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

(defn test-equality-axioms-prove-a-substitution [tmp-path]
  ;; a = b and p(a) give p(b) only when = means equality
  (setv path (/ tmp-path "Problems" "TST" "TST005+1.p"))
  (.mkdir path.parent :parents True)
  (.write-text path "fof(e, axiom, a = b).\nfof(p, axiom, p(f(a))).\nfof(g, conjecture, p(f(b))).\n")
  (assert (= (get (solve path :time-limit 5) 0) "GaveUp"))
  (assert (= (get (solve path :time-limit 5 :equality 1) 0) "Theorem")))

(defn test-superposition-proves-the-substitution [tmp-path]
  (setv path (/ tmp-path "Problems" "TST" "TST005+1.p"))
  (.mkdir path.parent :parents True)
  (.write-text path "fof(e, axiom, a = b).\nfof(p, axiom, p(f(a))).\nfof(g, conjecture, p(f(b))).\n")
  (assert (= (get (solve path :time-limit 5 :equality 2) 0) "Theorem")))

(defn test-superposition-group-theory [tmp-path]
  ;; in a group where every element is its own inverse, multiplication commutes
  (setv path (/ tmp-path "Problems" "TST" "TST006+1.p"))
  (.mkdir path.parent :parents True)
  (.write-text path (+ "fof(assoc, axiom, ! [X,Y,Z] : m(m(X,Y),Z) = m(X,m(Y,Z))).\n"
                       "fof(left_id, axiom, ! [X] : m(e,X) = X).\n"
                       "fof(right_id, axiom, ! [X] : m(X,e) = X).\n"
                       "fof(self_inv, axiom, ! [X] : m(X,X) = e).\n"
                       "fof(goal, conjecture, ! [X,Y] : m(X,Y) = m(Y,X)).\n"))
  (assert (= (get (solve path :time-limit 20 :equality 2) 0) "Theorem")))

(defn test-epr-problems-are-decided-by-grounding [tmp-path]
  (setv d (/ tmp-path "Problems" "TST"))
  (.mkdir d :parents True)
  ;; a theorem: with a = b and p(a), p(b) holds
  (.write-text (/ d "TST007+1.p") "fof(e, axiom, a = b).\nfof(p, axiom, ! [X] : (q(X) => p(X))).\nfof(q, axiom, q(a)).\nfof(g, conjecture, p(b)).\n")
  ;; not a theorem: nothing says a and b are equal
  (.write-text (/ d "TST008+1.p") "fof(p, axiom, p(a)).\nfof(g, conjecture, p(b)).\n")
  (assert (= (get (solve (/ d "TST007+1.p") :time-limit 5 :epr 1) 0) "Theorem"))
  (assert (= (get (solve (/ d "TST008+1.p") :time-limit 5 :epr 1) 0) "CounterSatisfiable")))
