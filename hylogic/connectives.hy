"Truth functions for the logical connectives.

Each connective is a function on truth values, available by name and by its
logical symbol:

  (import hylogic.connectives [∧ ∨ ¬ →])
  (→ (∧ True False) True)   ; => True

The variadic ones (∧ ∨ ↑ ↓ ⊕ ≡ ≢) take any number of arguments. The others
take exactly as many as their usual definition: ¬ one, the implications and
↔ two."

(import collections [namedtuple])

(defn negation [p] (not p))
(defn conjunction [#* ps] (all ps))
(defn disjunction [#* ps] (any ps))
(defn nand [#* ps] (not (all ps)))
(defn nor [#* ps] (not (any ps)))

(defn exclusive-or [#* ps]
  "True when an odd number of arguments is true (parity)."
  (= (% (sum (gfor p ps (bool p))) 2) 1))

(defn equivalence [#* ps]
  "True when all arguments have the same truth value."
  (<= (len (sfor p ps (bool p))) 1))

(defn nonequivalence [#* ps] (not (equivalence #* ps)))
(defn biconditional [p q] (= (bool p) (bool q)))
(defn implication [p q] (or (not p) (bool q)))
(defn converse-implication [p q] (or (bool p) (not q)))
(defn nonimplication [p q] (and (bool p) (not q)))
(defn converse-nonimplication [p q] (and (not p) (bool q)))

(setv ¬ negation
      ∧ conjunction
      ∨ disjunction
      ↑ nand
      ↓ nor
      ⊕ exclusive-or
      ↮ exclusive-or
      ≡ equivalence
      ≢ nonequivalence
      ↔ biconditional
      → implication
      ← converse-implication
      ↛ nonimplication
      ↚ converse-nonimplication)

(setv Connective (namedtuple "Connective" ["symbol" "operator" "name" "function" "arity"]))

;; symbol, operator name in formulas, English name, truth function, arity
;; (None for any number of arguments)
(setv CONNECTIVES [
  (Connective "¬" "not" "Negation" negation 1)
  (Connective "∧" "and" "Conjunction" conjunction None)
  (Connective "∨" "or" "Disjunction" disjunction None)
  (Connective "↑" "nand" "Nonconjunction (NAND)" nand None)
  (Connective "↓" "nor" "Nondisjunction (NOR)" nor None)
  (Connective "⊕" "xor" "Exclusive or" exclusive-or None)
  (Connective "≡" "eqv" "Equivalence (all equal)" equivalence None)
  (Connective "≢" "neqv" "Nonequivalence" nonequivalence None)
  (Connective "↔" "<=>" "Biconditional" biconditional 2)
  (Connective "→" "=>" "Material implication" implication 2)
  (Connective "←" "<=" "Converse implication" converse-implication 2)
  (Connective "↛" "nimp" "Material nonimplication" nonimplication 2)
  (Connective "↚" "cnimp" "Converse nonimplication" converse-nonimplication 2)])

(setv BY-OPERATOR (dfor c CONNECTIVES c.operator c))
