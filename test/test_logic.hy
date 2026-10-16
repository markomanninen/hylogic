(import itertools [product]
        random
        pytest
        hylogic.connectives :as c
        hylogic.formulas [formula pretty basic]
        hylogic.evaluate [evaluate]
        hylogic.truth [truth-table tautology? satisfiable? contradiction? equivalent?
                       entails? counterexample propositions assignments connective-tables]
        hylogic.resolution [prove]
        hylogic.argument [Argument]
        hylogic [is-tautology entails :as py-entails])
(require hylogic.argument [defargument]
         hylogic.quantifiers [∀ ∃ forall exists])

;; Connectives

(setv TRUTH [True False])

(defn test-binary-connectives-match-their-definitions []
  (for [p TRUTH q TRUTH]
    (assert (= (c.∧ p q) (and p q)))
    (assert (= (c.∨ p q) (or p q)))
    (assert (= (c.↑ p q) (not (and p q))))
    (assert (= (c.↓ p q) (not (or p q))))
    (assert (= (c.⊕ p q) (!= p q)))
    (assert (= (c.≡ p q) (= p q) (c.↔ p q)))
    (assert (= (c.≢ p q) (!= p q)))
    (assert (= (c.→ p q) (or (not p) q)))
    (assert (= (c.← p q) (or p (not q))))
    (assert (= (c.↛ p q) (and p (not q))))
    (assert (= (c.↚ p q) (and (not p) q))))
  (assert (= (c.¬ True) False)))

(defn test-variadic-connectives []
  (assert (c.⊕ True True True))          ; odd number of trues
  (assert (not (c.⊕ True True)))
  (assert (c.≡ False False False))       ; all equal
  (assert (not (c.≡ True True False)))
  (assert (= (len c.CONNECTIVES) 13)))

;; Formulas

(defn test-symbols-and-ascii-names-give-the-same-formula []
  (assert (= (formula '(∀ [x] (→ (Man x) (Mortal x))))
             (formula '(forall [x] (=> (Man x) (Mortal x))))))
  (assert (= (formula '(¬ (∧ P ⊤))) #("not" #("and" "P" "true")))))

(defn test-pretty-prints-logical-notation []
  (assert (= (pretty '(=> (and P (=> P Q)) Q)) "(P ∧ (P → Q)) → Q"))
  (assert (= (pretty '(forall [x] (=> (Man x) (Mortal x)))) "∀x ((Man x) → (Mortal x))")))

(setv EXTENDED ['(xor P Q R) '(nand P Q) '(nor P Q R) '(eqv P Q R) '(neqv P Q)
                '(<= P Q) '(nimp P Q) '(cnimp P Q) '(⊕ P) '(and) '(or)])

(defn [(pytest.mark.parametrize "f" EXTENDED :ids (lfor f EXTENDED (pretty f)))]
  test-desugared-formulas-have-the-same-truth-values [f]
  (setv names (or (propositions f) ["P"]))
  (for [env (assignments names)]
    (assert (= (evaluate f env) (evaluate (basic f) env)))))

;; Evaluation

(defn test-evaluate-propositions []
  (assert (evaluate '(→ P Q) {"P" False "Q" False}))
  (assert (not (evaluate '(∧ P (¬ P)) {"P" True})))
  (with [(pytest.raises KeyError)]
    (evaluate '(∧ P Q) {"P" True})))

(defn test-evaluate-in-a-finite-model []
  (setv model {"Man" #{"socrates" "plato"}
               "Mortal" #{"socrates" "plato" "fido"}
               "Loves" #{#("plato" "socrates")}
               "teacher" (fn [x] (if (= x "plato") "socrates" x))}
        domain ["socrates" "plato" "fido"])
  (assert (evaluate '(∀ [x] (→ (Man x) (Mortal x))) model domain))
  (assert (not (evaluate '(∀ [x] (→ (Mortal x) (Man x))) model domain)))
  (assert (evaluate '(∃ [x y] (Loves x y)) model domain))
  (assert (evaluate '(Loves plato (teacher plato)) model domain))
  (with [(pytest.raises ValueError)]
    (evaluate '(∀ [x] (Man x)) model)))

;; Truth tables

(defn test-truth-table-text []
  (setv text (str (truth-table '(→ (∧ P (→ P Q)) Q))))
  (assert (in "P │ Q │ (P ∧ (P → Q)) → Q" text))
  (assert (= (.count text "⊥") 4))          ; P and Q columns only; the formula is always ⊤
  (assert (= (len (.splitlines text)) 6)))

(defn test-truth-table-html []
  (assert (.startswith (._repr_html_ (truth-table '(∨ P Q))) "<table>")))

(defn test-tautology-satisfiable-contradiction []
  (assert (tautology? '(∨ P (¬ P))))
  (assert (not (tautology? '(→ P Q))))
  (assert (satisfiable? '(→ P Q)))
  (assert (contradiction? '(∧ P (¬ P))))
  (assert (is-tautology '(=> (=> (=> p q) p) p))))

(defn test-equivalence-and-entailment []
  (assert (equivalent? '(→ P Q) '(∨ (¬ P) Q)))
  (assert (equivalent? '(¬ (∧ P Q)) '(∨ (¬ P) (¬ Q))))   ; De Morgan
  (assert (entails? ['(→ P Q) 'P] 'Q))
  (assert (py-entails ['(→ P Q) '(¬ Q)] '(¬ P)))
  (assert (= (counterexample ['(→ P Q) 'Q] 'P) {"P" False "Q" True})))

(defn test-predicates-are-not-propositional []
  (with [(pytest.raises ValueError)]
    (truth-table '(∀ [x] (P x)))))

(defn test-connective-tables-list-all-thirteen []
  (setv text (connective-tables))
  (for [conn c.CONNECTIVES] (assert (in conn.name text))))

;; Two methods must agree: truth tables and resolution

(defn random-formula [rng depth]
  (if (or (= depth 0) (< (.random rng) 0.25))
      (.choice rng ["P" "Q" "R"])
      (do
        (setv op (.choice rng ["¬" "∧" "∨" "→" "↔" "⊕" "↑" "↓" "←" "↛"]))
        (if (= op "¬")
            #(op (random-formula rng (- depth 1)))
            #(op (random-formula rng (- depth 1)) (random-formula rng (- depth 1)))))))

(defn test-prover-agrees-with-truth-tables-on-random-formulas []
  (setv rng (random.Random 2026) checked 0 theorems 0)
  (for [_ (range 300)]
    (setv f (random-formula rng 4))
    (when (propositions f)
      (setv expected (tautology? f)
            result (prove f :limit 3000))
      (assert (!= result.status "gave-up") (pretty f))
      (assert (= result.proved expected) (pretty f))
      (+= checked 1)
      (when expected (+= theorems 1))))
  (assert (> checked 250))
  (assert (> theorems 10)))

(defn test-prover-reads-symbols []
  (assert (. (prove '(∃ [x] (→ (Drinks x) (∀ [y] (Drinks y))))) proved))
  (assert (. (prove '(≡ (⊕ P Q) (⊕ Q P))) proved))
  (assert (. (prove 'Q ['⊥]) proved))                 ; anything follows from ⊥
  (assert (not (. (prove 'Q ['⊤]) proved))))

;; Arguments

(defargument modus-ponens
  :premises [(→ P Q) P]
  :conclusion Q
  :meanings {P "Today is Tuesday" Q "John will go to work"})

(defargument affirming-the-consequent
  :premises [(→ P Q) Q]
  :conclusion P)

(defn test-valid-propositional-argument []
  (assert modus-ponens.valid)
  (assert (= modus-ponens.method "truth table"))
  (setv text (str modus-ponens))
  (assert (in "∴ Q" text))
  (assert (in "P: Today is Tuesday" text)))

(defn test-invalid-argument-has-a-counterexample []
  (assert (is affirming-the-consequent.valid False))
  (assert (= affirming-the-consequent.counterexample {"P" False "Q" True}))
  (assert (in "Counterexample: P = ⊥, Q = ⊤" (.explain affirming-the-consequent))))

(defn test-first-order-arguments-use-the-prover []
  (setv socrates (Argument ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)] '(Mortal socrates)))
  (assert socrates.valid)
  (assert (= socrates.method "resolution"))
  (assert (in "□" (get socrates.proof -1)))
  (setv converse (Argument ['(∀ [x] (→ (Man x) (Mortal x))) '(Mortal fido)] '(Man fido)))
  (assert (is converse.valid False)))

(defn test-defargument-rejects-unknown-options []
  (with [(pytest.raises Exception)]
    (hy.eval '(defargument bad :premises [P] :conclusion P :because x)
             :module (__import__ "hylogic.argument" :fromlist ["x"]))))

;; Quantifiers over Python data

(defn test-quantifier-macros []
  (assert (∀ [x (range 1 10)] (> x 0)))
  (assert (∃ [x (range 10)] (< x 1)))
  (assert (not (∃ [x (range 1 10)] (< x 1))))
  (assert (∀ [x [1 2] y [-1 -2]] (!= (+ x y) 5)))
  (assert (forall [x []] False))           ; vacuously true
  (assert (not (exists [x []] True))))


(defn test-quoted-forms-inside-tuples-are-converted []
  ;; a tuple built in code can hold quoted Hy forms
  (assert (= (formula #("not" '(∧ P Q))) #("not" #("and" "P" "Q")))))
