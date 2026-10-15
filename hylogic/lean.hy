"Exporting problems as Lean 4 theorems.

Lean checks proofs in a logic strong enough for all of mathematics. A
first-order problem becomes a theorem over an arbitrary nonempty type U:
predicates are functions into Prop, functions and constants are parameters,
and the premises are hypotheses:

  theorem socrates {U : Type} [Nonempty U]
      («Man» «Mortal» : U → Prop) («socrates» : U)
      (h1 : ∀ «x» : U, «Man» «x» → «Mortal» «x») (h2 : «Man» «socrates») :
      «Mortal» «socrates» := by grind

Every name is written in «guillemets», so TPTP names cannot clash with Lean
keywords. The proof is a tactic: sorry only checks that the statement is well
formed, and grind asks Lean's own automation to find the proof."

(import subprocess
        tempfile
        pathlib [Path]
        hylogic.formulas [basic operator-of args-of QUANTIFIERS]
        hylogic.export [signature]
        hylogic.terms [compound?])

(defn _name [n] (+ "«" (.replace (str n) "»" "_") "»"))

(defn _term [t]
  (if (compound? t)
      (+ "(" (_name (get t 0)) " " (.join " " (map _term (cut t 1 None))) ")")
      (_name t)))

(setv _BINARY {"and" "∧" "or" "∨" "=>" "→" "<=>" "↔"})

(defn _formula [f]
  (setv op (operator-of f))
  (cond
    (in op QUANTIFIERS)
      (+ "(" (if (= op "forall") "∀" "∃") " " (.join " " (map _name (get f 1))) " : U, " (_formula (get f 2)) ")")
    (= op "not") (+ "¬" (_formula (get f 1)))
    op (do
         (setv xs (lfor a (args-of f) (_formula a)))
         (cond
           (not xs) (if (= op "and") "True" "False")
           (= (len xs) 1) (get xs 0)
           True (+ "(" (.join f" {(get _BINARY op)} " xs) ")")))
    (= f "true") "True"
    (= f "false") "False"
    (and (compound? f) (= (get f 0) "=")) (+ "(" (_term (get f 1)) " = " (_term (get f 2)) ")")
    (compound? f) (_term f)
    True (_name f)))

(defn _arrow [n result] (.join " → " [#* (* ["U"] n) result]))

(defn to-lean [premises goal [name "problem"] [tactic "sorry"]]
  "A Lean 4 theorem saying that the premises entail the goal."
  (setv fs (lfor p premises (basic p))
        g (basic goal)
        sig (signature [#* fs g])
        params [])
  (for [p (sorted (get sig "propositions"))] (.append params f"({(_name p)} : Prop)"))
  (for [[p n] (sorted (.items (get sig "predicates")))]
    (when (!= p "=") (.append params (+ "(" (_name p) " : " (_arrow n "Prop") ")"))))
  (for [[f n] (sorted (.items (get sig "functions")))] (.append params (+ "(" (_name f) " : " (_arrow n "U") ")")))
  (for [c (sorted (get sig "constants"))] (.append params f"({(_name c)} : U)"))
  (for [[i f] (enumerate fs)] (.append params f"(h{(+ i 1)} : {(_formula f)})"))
  (+ "theorem " (_name name) " {U : Type} [Nonempty U]\n    "
     (.join "\n    " params)
     " :\n    " (_formula g) " := by\n  " tactic "\n"))

(defn check-lean [text [timeout 30]]
  "Run Lean on a file's text. #(ok message): ok when Lean accepts it without errors."
  (with [d (tempfile.TemporaryDirectory)]
    (setv path (/ (Path d) "Problem.lean"))
    (.write-text path text)
    (try
      (setv out (subprocess.run ["lean" (str path)] :capture-output True :text True :timeout timeout))
      (except [subprocess.TimeoutExpired] (return #(False "timeout"))))
    (setv message (+ out.stdout out.stderr))
    #((and (= out.returncode 0) (not-in "error" message)) message)))
