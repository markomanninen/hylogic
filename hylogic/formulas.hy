"Formulas as data.

Formulas are written as quoted Hy code, with logical symbols or ASCII names:

  '(∀ [x] (→ (Man x) (Mortal x)))
  '(forall [x] (=> (Man x) (Mortal x)))

`formula` turns either into the same plain data, with every operator in its
ASCII form: not and or => <=> xor nand nor eqv neqv <= nimp cnimp forall
exists, and the constants ⊤ and ⊥ as true and false.

`desugar` rewrites the extended connectives with the five basic ones
(not and or => <=>), which is what the prover works with."

(import hylogic.terms [term compound?])

(setv OPERATORS {
  "¬" "not"     "not" "not"
  "∧" "and"     "and" "and"     "&" "and"
  "∨" "or"      "or" "or"       "|" "or"
  "→" "=>"      "=>" "=>"       "->" "=>"     "implies" "=>"
  "↔" "<=>"     "<=>" "<=>"     "<->" "<=>"   "iff" "<=>"
  "⊕" "xor"     "↮" "xor"       "xor" "xor"
  "↑" "nand"    "nand" "nand"
  "↓" "nor"     "nor" "nor"
  "≡" "eqv"     "eqv" "eqv"
  "≢" "neqv"    "neqv" "neqv"
  "←" "<="      "<=" "<="
  "↛" "nimp"    "nimp" "nimp"
  "↚" "cnimp"   "cnimp" "cnimp"
  "∀" "forall"  "forall" "forall"
  "∃" "exists"  "exists" "exists"})

(setv CONSTANTS {"⊤" "true" "⊥" "false" "true" "true" "false" "false"
                 "True" "true" "False" "false"})

(setv QUANTIFIERS #{"forall" "exists"})
(setv CONNECTIVE-NAMES (- (set (.values OPERATORS)) QUANTIFIERS))

(defn operator-of [f]
  "The canonical operator of a formula, or None for an atom."
  (when (and (compound? f) f (isinstance (get f 0) str))
    (.get OPERATORS (get f 0))))

(defn _normalize [f]
  (setv op (operator-of f))
  (cond
    (in op QUANTIFIERS)
      (do
        (when (or (!= (len f) 3) (not (compound? (get f 1))))
          (raise (ValueError f"a quantifier needs a variable list and a body: {f}")))
        #(op (get f 1) (_normalize (get f 2))))
    op #(op #* (gfor a (cut f 1 None) (_normalize a)))
    (isinstance f bool) (if f "true" "false")
    (and (isinstance f str) (in f CONSTANTS)) (get CONSTANTS f)
    True f))

(defn formula [form]
  "A quoted Hy form (or a term) as a formula with canonical operator names."
  (_normalize (term form)))

(defn atom? [f]
  (is (operator-of f) None))

(defn args-of [f] (cut f 1 None))

(defn _fold [op xs]
  (setv result (get xs 0))
  (for [x (cut xs 1 None)]
    (setv result #(op result x)))
  result)

(defn desugar [f]
  "Rewrite xor, nand, nor, eqv, neqv, <=, nimp and cnimp with not, and, or, => and <=>."
  (setv op (operator-of f))
  (when (is op None) (return f))
  (when (in op QUANTIFIERS)
    (return #(op (get f 1) (desugar (get f 2)))))
  (setv xs (lfor a (args-of f) (desugar a)))
  (cond
    (= op "xor") (cond
                   (not xs) "false"
                   (= (len xs) 1) (get xs 0)
                   True (_fold "xor-2" xs))
    (= op "nand") #("not" #("and" #* xs))
    (= op "nor") #("not" #("or" #* xs))
    (= op "eqv") (if (< (len xs) 2)
                     "true"
                     #("and" #* (gfor [a b] (zip xs (cut xs 1 None)) #("<=>" a b))))
    (= op "neqv") #("not" (desugar #("eqv" #* xs)))
    (= op "<=") #("=>" (get xs 1) (get xs 0))
    (= op "nimp") #("and" (get xs 0) #("not" (get xs 1)))
    (= op "cnimp") #("and" #("not" (get xs 0)) (get xs 1))
    (and (in op #{"and" "or"}) (not xs)) (if (= op "and") "true" "false")
    True #(op #* xs)))

(defn _xor-2 [f]
  "Replace the binary xor-2 nodes left by desugar."
  (cond
    (not (compound? f)) f
    (= (get f 0) "xor-2") #("not" #("<=>" (_xor-2 (get f 1)) (_xor-2 (get f 2))))
    (in (get f 0) QUANTIFIERS) #((get f 0) (get f 1) (_xor-2 (get f 2)))
    (in (get f 0) CONNECTIVE-NAMES) #((get f 0) #* (gfor a (args-of f) (_xor-2 a)))
    True f))

(defn basic [form]
  "A formula with only not, and, or, =>, <=>, forall and exists."
  (_xor-2 (desugar (formula form))))

(setv SYMBOLS {"not" "¬" "and" "∧" "or" "∨" "=>" "→" "<=>" "↔" "xor" "⊕" "nand" "↑"
               "nor" "↓" "eqv" "≡" "neqv" "≢" "<=" "←" "nimp" "↛" "cnimp" "↚"
               "forall" "∀" "exists" "∃" "true" "⊤" "false" "⊥"})

(defn pretty [form]
  "A formula in the usual logical notation: (P ∧ Q) → R, ∀x (Man x → Mortal x)."
  (_pretty (formula form) True))

(defn _pretty [f top]
  (import hylogic.terms [show])
  (setv op (operator-of f))
  (cond
    (is op None) (if (in f #{"true" "false"}) (get SYMBOLS f) (show f))
    (= op "not") (+ "¬" (_pretty (get f 1) False))
    (in op QUANTIFIERS)
      (+ (get SYMBOLS op) (.join " " (get f 1)) " " (_pretty (get f 2) False))
    True
      (do
        (setv inner (.join f" {(get SYMBOLS op)} " (gfor a (args-of f) (_pretty a False))))
        (if top inner (+ "(" inner ")")))))
