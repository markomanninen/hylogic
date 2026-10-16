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

;; Lean checks HyLogic's own proofs step by step (hylogic.certify)

(import hylogic.certify [certify to-lean-proof proof-clauses]
        hylogic.resolution [prove clausify]
        hylogic.grounding [epr-refutation]
        hylogic.euf [euf-refutation]
        hylogic.problems [FIRST-ORDER])

(defn _need-lean []
  (when (is (shutil.which "lean") None) (pytest.skip "lean is not installed")))

(defn _verified [result rules]
  "Certify a proof, check that Lean accepted every step, and that it had the rules."
  (setv c (certify result))
  (assert (get c "verified") (lfor s (get c "steps") :if (not (get s "ok")) s))
  (setv seen (sfor s (get c "steps") (get s "rule")))
  (for [r rules] (assert (any (gfor s seen (in r s))) #(r seen)))
  c)

(defn test-lean-proof-text []
  (setv [_ axioms goal] (get FIRST-ORDER 0)
        [text steps] (to-lean-proof (prove goal axioms)))
  (assert (in "theorem «$s" text))
  (assert (in "theorem «$refutation»" text))
  ;; the instance the resolution used is written out, not left to search
  (assert (in "have «$i1» := «$h1» «socrates»" text))
  (assert (= (. (get steps -1) ["rule"]) "refutation")))

(defn test-lean-checks-resolution-proofs []
  (_need-lean)
  (setv rules #{})
  (for [[name axioms goal] FIRST-ORDER]
    (setv r (prove goal axioms))
    (assert r.proved name)
    (.update rules (gfor s (get (_verified r []) "steps") (get s "rule"))))
  (assert (& rules #{"resolve" "resolve+unit deletion"})))

(defn test-lean-checks-superposition-and-demodulation []
  (_need-lean)
  (setv axioms ['(forall [x] (= (mult e x) x))
                '(forall [x] (= (mult (inv x) x) e))
                '(forall [x y z] (= (mult (mult x y) z) (mult x (mult y z))))]
        r (prove '(= (mult (inv a) (mult a b)) b) axioms :superposition 1))
  (_verified r ["superposition+demod" "demodulation"])
  None)

(defn test-lean-checks-epr-proof-with-split []
  (_need-lean)
  (setv clauses (lfor f ['(forall [x y] (or (P x) (Q y))) '(not (P a)) '(not (Q b))]
                      c (clausify f) c)
        c (_verified (epr-refutation clauses) ["instance, split" "resolve"]))
  ;; the split predicate is discharged by its definition
  (assert (in "theorem «$closed»" (get c "text"))))

(defn test-lean-checks-euf-proof []
  (_need-lean)
  (setv clauses [(frozenset [#("=" "a" "b")])
                 (frozenset [#("=" #("f" #("f" "a")) "c")])
                 (frozenset [#("not" #("=" #("f" #("f" "b")) "c"))])])
  (_verified (euf-refutation clauses) ["equality lemma" "resolve"])
  None)

(defn test-lean-rejects-a-corrupted-step []
  (_need-lean)
  (setv [_ axioms goal] (get FIRST-ORDER 1)
        r (prove goal axioms)
        clauses (proof-clauses r)
        step (next (gfor c clauses :if (and c.parents c.literals) c))
        number (+ (.index clauses step) 1))
  ;; one derived clause made into something its premises do not imply
  (setv step.literals (frozenset (gfor l step.literals (if (and (isinstance l tuple) (= (get l 0) "not"))
                                                           (get l 1)
                                                           #("not" l)))))
  (setv c (certify r)
        bad (lfor s (get c "steps") :if (not (get s "ok")) (get s "number")))
  (assert (not (get c "verified")))
  ;; Lean reports that step first; a later step may fail too, when it no
  ;; longer follows from the corrupted clause
  (assert (= (get bad 0) number)))
