(import os
        pytest
        hylogic.external [read-tstp ExternalResult prover-path prove-external])

;; real outputs of Vampire 5.1.0 and E 3.2.5 for the Socrates problem
(setv VAMPIRE "% SZS status Theorem for s
% SZS output start Proof for s
fof(f1,axiom,(
  ! [X0] : (man(X0) => mortal(X0))),
  file('s.p','a1')).
fof(f2,axiom,(
  man(socrates)),
  file('s.p','a2')).
fof(f3,conjecture,(
  mortal(socrates)),
  file('s.p','g')).
fof(f4,negated_conjecture,(
  ~ mortal(socrates)),
  inference(negated_conjecture,[status(cth)],[f3])).
cnf(f10,plain,(
  ~man(socrates)),
  inference(resolution,[],[f4,f1])).
cnf(f11,plain,(
  $false),
  inference(resolution,[],[f10,f2])).
% SZS output end Proof for s
")

(setv E "# SZS status Theorem
# SZS output start CNFRefutation
fof(g, conjecture, mortal(socrates), file('s.p', g)).
fof(a1, axiom, ![X1]:((man(X1)=>mortal(X1))), file('s.p', a1)).
cnf(c_0_6, negated_conjecture, (~mortal(socrates)), inference(split_conjunct,[status(thm)],[g])).
cnf(c_0_9, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, a1])])]), ['proof']).
# SZS output end CNFRefutation
")

(defn test-vampire-proof-is-read []
  (setv steps (read-tstp VAMPIRE))
  (assert (= (len steps) 6))
  (assert (= (. (get steps 0) formula) #("forall" #("X0") #("=>" #("man" "X0") #("mortal" "X0")))))
  (assert (= (. (get steps -1) formula) "false"))
  (assert (= (. (get steps -1) parents) ["f10" "f2"]))
  (setv lines (.proof (ExternalResult "vampire" "Theorem" steps "")))
  (assert (in "resolution 5, 2" (get lines -1)))
  (assert (in "⊥" (get lines -1))))

(defn test-nested-e-inferences-are-unwrapped []
  (setv steps (read-tstp E))
  (assert (= (len steps) 4))
  (assert (= (. (get steps -1) rule) "cn ∘ rw ∘ spm"))
  (assert (= (. (get steps -1) parents) ["c_0_6" "a1"])))

(defn test-no-proof-section []
  (assert (= (read-tstp "% SZS status Timeout") [])))

(defn [(pytest.mark.parametrize "prover" ["vampire" "eprover"])] test-live-prover [prover]
  (when (is (prover-path prover) None) (pytest.skip f"{prover} is not installed"))
  (setv r (prove-external '(Mortal socrates) ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)] :prover prover))
  (assert r.proved)
  (assert (in "⊥" (get (.proof r) -1))))

(import shutil
        hylogic.lean [to-lean check-lean])

(defn test-lean-statement []
  (setv text (to-lean ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)] '(Mortal socrates) :name "s"))
  (assert (in "(«Man» : «$U» → Prop)" text))
  (assert (in "(«$h1» : (∀ «x» : «$U», ((«Man» «x») → («Mortal» «x»))))" text))
  (assert (.endswith text "sorry\n")))

(defn test-lean-checks-and-proves []
  (when (is (shutil.which "lean") None) (pytest.skip "lean is not installed"))
  (setv premises ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)])
  (assert (get (check-lean (to-lean premises '(Mortal socrates) :tactic "grind")) 0))
  ;; grind must not prove what does not follow
  (assert (not (get (check-lean (to-lean premises '(Man plato) :tactic "grind")) 0))))
