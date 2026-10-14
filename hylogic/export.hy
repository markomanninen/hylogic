"Export to the input languages of real solvers and provers.

SMT-LIB is the common language of SMT solvers such as Z3 and cvc5, and is
itself written in s-expressions. TPTP is the common language of first-order
provers such as Vampire and E. Both functions write the question \"do the
premises entail the goal?\" as premises plus the negated goal, so the answer
is unsat (SMT-LIB) or Theorem (TPTP) when the goal follows.

  (print (to-smtlib ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)] '(Mortal socrates)))

`check-with-z3` runs the SMT-LIB version in Z3, if the z3-solver package is
installed (pip install hylogic[z3])."

(import re
        hylogic.formulas [basic operator-of args-of QUANTIFIERS]
        hylogic.terms [compound?])

;; Signature: what each name is

(defn signature [formulas]
  "Propositions, predicates, functions and constants used in the formulas, with arities."
  (setv sig {"propositions" #{} "predicates" {} "functions" {} "constants" #{}})
  (defn term [t bound]
    (cond
      (compound? t) (do (setv (get (get sig "functions") (get t 0)) (- (len t) 1))
                        (for [a (cut t 1 None)] (term a bound)))
      (in t bound) None
      True (.add (get sig "constants") (str t))))
  (defn formula [f bound]
    (setv op (operator-of f))
    (cond
      (in op QUANTIFIERS) (formula (get f 2) (| bound (set (get f 1))))
      op (for [a (args-of f)] (formula a bound))
      (in f #{"true" "false"}) None
      (compound? f) (do (setv (get (get sig "predicates") (get f 0)) (- (len f) 1))
                        (for [a (cut f 1 None)] (term a bound)))
      True (.add (get sig "propositions") f)))
  (for [f formulas] (formula f #{}))
  sig)

;; SMT-LIB

(defn _smt-name [name] (+ "|" (.replace (str name) "|" "_") "|"))

(defn _smt-term [t bound]
  (if (compound? t)
      (+ "(" (_smt-name (get t 0)) " " (.join " " (gfor a (cut t 1 None) (_smt-term a bound))) ")")
      (_smt-name t)))

(setv _SMT-OPS {"not" "not" "and" "and" "or" "or" "=>" "=>" "<=>" "="})

(defn _smt [f bound]
  (setv op (operator-of f))
  (cond
    (in op QUANTIFIERS)
      (+ "(" op " (" (.join " " (gfor v (get f 1) f"({(_smt-name v)} U)")) ") "
         (_smt (get f 2) (| bound (set (get f 1)))) ")")
    op (do
         (setv xs (lfor a (args-of f) (_smt a bound)))
         (cond
           (and (= op "and") (not xs)) "true"
           (and (= op "or") (not xs)) "false"
           True (+ "(" (get _SMT-OPS op) " " (.join " " xs) ")")))
    (in f #{"true" "false"}) f
    (compound? f) (_smt-term f bound)
    True (_smt-name f)))

(defn to-smtlib [premises goal [check-sat True]]
  "An SMT-LIB 2 script asserting the premises and the negated goal."
  (setv fs [#* (gfor p premises (basic p)) #("not" (basic goal))]
        sig (signature fs)
        lines ["(set-logic ALL)" "(declare-sort U 0)"])
  (for [p (sorted (get sig "propositions"))]
    (.append lines f"(declare-const {(_smt-name p)} Bool)"))
  (for [c (sorted (get sig "constants"))]
    (.append lines f"(declare-const {(_smt-name c)} U)"))
  (for [[name n] (sorted (.items (get sig "functions")))]
    (setv domain (.join " " (* ["U"] n)))
    (.append lines f"(declare-fun {(_smt-name name)} ({domain}) U)"))
  (for [[name n] (sorted (.items (get sig "predicates")))]
    (setv domain (.join " " (* ["U"] n)))
    (.append lines f"(declare-fun {(_smt-name name)} ({domain}) Bool)"))
  (for [f fs]
    (.append lines f"(assert {(_smt f #{})})"))
  (when check-sat (.append lines "(check-sat)"))
  (.join "\n" lines))

(defn check-with-z3 [premises goal [timeout 10000]]
  "valid, invalid or unknown, decided by Z3. Needs the z3-solver package."
  (import z3)
  (setv solver (z3.Solver))
  (.set solver "timeout" timeout)
  (.from-string solver (to-smtlib premises goal :check-sat False))
  (setv result (.check solver))
  (cond
    (= result z3.unsat) "valid"
    (= result z3.sat) "invalid"
    True "unknown"))

;; TPTP

(defn _tptp-word [name]
  "A lowercase TPTP word for a predicate, function or constant name."
  (setv w (re.sub r"[^A-Za-z0-9_]" "_" (str name)))
  (setv w (+ (.lower (cut w 0 1)) (cut w 1 None)))
  (if (and w (.isalpha (get w 0))) w (+ "c_" w)))

(defn _tptp-var [name]
  (setv w (re.sub r"[^A-Za-z0-9_]" "_" (str name)))
  (+ "X_" w))

(defn _tptp-term [t bound]
  (cond
    (compound? t) (+ (_tptp-word (get t 0)) "(" (.join "," (gfor a (cut t 1 None) (_tptp-term a bound))) ")")
    (in t bound) (_tptp-var t)
    True (_tptp-word t)))

(setv _TPTP-OPS {"and" "&" "or" "|" "=>" "=>" "<=>" "<=>"})

(defn _tptp [f bound]
  (setv op (operator-of f))
  (cond
    (in op QUANTIFIERS)
      (+ (if (= op "forall") "! [" "? [") (.join "," (map _tptp-var (get f 1))) "] : "
         (_tptp (get f 2) (| bound (set (get f 1)))))
    (= op "not") (+ "~ " (_tptp (get f 1) bound))
    op (do
         (setv xs (lfor a (args-of f) (_tptp a bound)))
         (cond
           (not xs) (if (= op "and") "$true" "$false")
           (= (len xs) 1) (get xs 0)
           True (+ "(" (.join f" {(get _TPTP-OPS op)} " xs) ")")))
    (= f "true") "$true"
    (= f "false") "$false"
    (compound? f) (_tptp-term f bound)
    True (_tptp-word f)))

(defn to-tptp [premises goal]
  "A TPTP problem in first-order form (FOF) with the premises as axioms and the goal as conjecture."
  (setv lines (lfor [i p] (enumerate premises)
                    f"fof(premise_{(+ i 1)}, axiom, ({(_tptp (basic p) #{})}))."))
  (.append lines f"fof(goal, conjecture, ({(_tptp (basic goal) #{})})).")
  (.join "\n" lines))
