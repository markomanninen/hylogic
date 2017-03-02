#!/usr/bin/python3
(require [hylogic.hyffix.macros [*]])
(import (hylogic.hyffix.macros (*)))

; define connective functions and math aliases (op-symbol)
; plus set them to operators global list
(defmacro defconnective [op-name op-symbol params &rest body]
  `(do 
    (defoperator ~op-name ~params ~@body)
    (setv ~op-symbol ~op-name)
    #>~op-symbol))

; define math operands
; so that in addition to 1 and True also symbol ⊤ can be used
(setv ⊤ 1)
(setv ⊥ 0)

; define true comparison function
; note that textual version of "1", "True" or "⊤" are not supported 
; so they will be regarded as False
(defn true? [value] 
  (or (= value 1) (= value True)))

; same as nor at the moment... not? is a reserved word
(defconnective nope? ¬ [&rest truth-list] 
  (not (any truth-list)))

; and operation : zero or more arguments, zero will return false, 
; otherwise all items needs to be true
(defconnective and? ∧ [&rest truth-list]
  (all (map true? truth-list)))

; negation of and
(defconnective nand? ↑ [&rest truth-list]
  (not (apply and? truth-list)))

; or operation : zero or more arguments, zero will return false, 
; otherwise at least one of the values needs to be true
(defconnective or? ∨ [&rest truth-list]
  (any (map true? truth-list)))

; negation of or
(defconnective nor? ↓ [&rest truth-list]
  (not (apply or? truth-list)))

; xor operation (parity check) : zero or more arguments, zero will return false, 
; otherwise odd number of true's is true
(defconnective xor? ⊕ [&rest truth-list]
  (setv boolean False)
  (for [truth-value truth-list]
    (if (true? truth-value)
      (setv boolean (not boolean))))
  boolean)

;synonym for xor
(setv ↮ xor?)
#>↮

; negation of xor
(defconnective xnor? ↔ [&rest truth-list]
  (not (apply xor? truth-list)))

; equivalence
; https://en.wikipedia.org/wiki/Logical_equivalence
; with two values same as xnor but with more values
; result differs: [1 1 1] = True = [0 0 0]
; TODO; should be recursive: [1 1 1] -> [[1 1] 1]
(defconnective eqv? ≡ [&rest truth-list]
  (setv boolean (if (pos? (len truth-list)) True False))
  (for [truth-value truth-list]
    (if (not? truth-value (first truth-list))
      (do (setv boolean False) (break))))
  boolean)

; unquivalence
(defconnective neqv? ≢ [&rest truth-list]
  (not (apply eqv? truth-list)))

; Four implications macro
; Behaviour:
; (1 op 0 op 0) -> (op 1 0 0 ) -> (op (op 1 0) 0)
; Truth tables:
; (for [y (range 2)]
;   (print "(→ y) =>" (x y)))
; (for [y (range 2)]
;   (for [z (range 2)]
;     (print (% "(op %s" y) (% "%s) =>" z) (x y z))))
; Also note that for all implications [(op 1) (op 0)] = [True, False]
(defmacro defimplication [op-name op-symbol func]
  `(defconnective ~op-name ~op-symbol [&rest truth-list]
  (do 
    ; passed arguments is a tuple 
    ; so it needs to be cast to list for pop
    (setv args (list truth-list))
    (if (= (len args) 1) (true? (first args))
      ; else
      (do
        ; default return value is False
        (setv result False)
        ; take the first element of list and remove it
        (setv prev (first args))
        (.remove args prev)
        ; loop over all args
        (while
          (pos? (len args))
          (do
            ; there are at least two items on a list at the moment
            ; so we can get the next and remove it too
            (setv next (first args))
            (.remove args next)
            ; recurisvely get the result. previous could be a list as
            ; well as next could be a list, thus prev needs to be evaluated
            ; at least once more.
            (setv result ~func)
            ;(print 'prev prev 'next next 'result result)
            ; and set result for the previous one
            (setv prev result)))
        ; return resulting boolean value
        result)))))

; Converse implication (P ∨ ¬Q)
; https://en.wikipedia.org/wiki/Converse_implication
(defimplication cimp? ← (any [(← prev) (not (← next))]))

; Material nonimplication (P ∧ ¬Q)
; https://en.wikipedia.org/wiki/Material_nonimplication
(defimplication mnimp? ↛ (all [(↛ prev) (not (↛ next))]))

; Converse nonimplication (¬P ∨ Q)
; https://en.wikipedia.org/wiki/Converse_nonimplication
(defimplication cnimp? ↚ (any [(not (↚ prev)) (↚ next)]))

; Material implication (¬P ∧ Q)
; https://en.wikipedia.org/wiki/Material_conditional
(defimplication mimp? → (all [(not (→ prev)) (→ next)]))
