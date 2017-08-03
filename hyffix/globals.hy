#!/usr/bin/python3
(eval-and-compile 
  ; without eval setv doesn't work as a global variable for macros
  (setv operators []
        operators-precedence []
        operands {}))

; add support list for custom operators. note that
; native operands like + - * / = or any usual one
; doesn't need to be added to the operators list
; for singular usage: #>operator
; for multiple: #>[operator1 operator 2 ...]
(defsharp > [items] 
  (do
    ; transforming singular value to a list for the next for loop
    (if-not (coll? items) (setv items [items]))
    (for [item items]
      ; discard duplicates
      (if-not (in item operators)
        (.append operators item)))))

; set the order of precedence for operators
; for singular usage: #<operator
; for multiple: #<[operator1 operator 2 ...]
; note that calling this macro will empty the previous list of precedence!
(defsharp < [items]
  (do
    ; (setv operators-precedence []) is not working here
    ; for some macro evaluation - complilation order reason
    ; so emptying the current operators-precedence list more verbose way
    (if (pos? (len operators-precedence))
      (while (pos? (len operators-precedence))
        (.pop operators-precedence)))
    ; transforming singular value to a list for the next for loop
    (if-not (coll? items) (setv items [items]))
    (for [item items]
      ; discard duplicates
      (if-not (in item operators-precedence)
        (.append operators-precedence item)))))
