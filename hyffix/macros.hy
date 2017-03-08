#!/usr/bin/python3
; require > and < reader macros
(require [hyffix.globals [< >]])
; import operator list. this makes globals.hy executed first
; so that operators variable is found in the current scope
; setting variable in the same file by setv or eval-and-compile 
; didn't work. this will also import operators-precedence list
(import (hyffix.globals (operands operators operators-precedence)))

; print multiple statements on new lines
(defmacro println [&rest args]
  `(do
    (setv args (list ~args))
    (for [line args]
      (print line))))

; define operator function and set it to operators global list
(defmacro defoperator [op-name params &rest body]
  `(do 
    (defn ~op-name ~params ~@body)
    #>~op-name))

; for example: (defoperand x 1 y 2 z 3)
(defmacro defoperand [&rest args]
  ; cast tuple to list to make removal of list items work
  (setv args (list args))
  ; only even number of arguments are accepted
  (if (even? (len args))
      (do
        (setv rtrn (second args))
        (while (pos? (len args))
             (do
               ; update dictionary key with a value
               (assoc operands (first args) (second args))
               ; remove first two arguments (key-value pair)
               (.remove args (get args 0))
               (.remove args (get args 0))))
        rtrn)
      (raise (Exception "defoperand needs an even number of arguments"))))

; function to change precedence order of the operations.
; argument list will be passed to the #< readermacro which 
; will reset arguments to a new operators-precedence list
; example: (defprecedence * / + -)
; or straight to the reader macro way: #<[* / + -]
;
; note that calling this macro will empty the previous list of precedence!
; to keep the previous set one should use precedence+
;
; call (defprecedence) to empty the list to the default state
; in that case left-wise order of precedence is used when evaluating
; the list of propositional logic or other symbols
(defmacro defprecedence [&rest args] `#<~args)

; append to operators-precedence list rather than resetting totally new list
(defmacro defprecedence+ [&rest args] 
  `(doto operators-precedence (.extend ~args)) None)

; macro that takes mixed prefix and infix notation clauses
; for evaluating their value. this is same as calling
; $ reader macro directly but might be more convenient way
; inside lips code to use than reader macro syntax
; there is no need to use parentheses with this macro
(defmacro deffix [&rest items] `#$~items)

; pass multiple (n) evaluation clauses. each of the must be
; wrapped by () parentheses
(defmacro deffix-n [&rest items]
  (list-comp `#$~item [item items]))

; for hy.HyExpression
(import hy)

; helper functions for #$ reader macro
(eval-and-compile
  ; this takes a list of items at least 3
  ; index must be bigger than 1 and smaller than the length of the list
  ; left and right side of the index will be picked to a new list where
  ; centermost item is moved to left and left to center
  ; [1 a 2 b 3 c 4] idx=3 -> [1 a [b 2 3] c 4]
  (defn list-nest [lst idx]
    (setv tmp
      (doto 
        (list (take 1 (drop idx lst))) 
        (.append (get lst (dec idx))) 
        (.append (get lst (inc idx)))))
    (doto 
      (list (take (dec idx) lst))
      (.append tmp)
      (.extend (list (drop (+ 2 idx) lst)))))

  (setv func-type (type (fn [])))

  ; https://docs.python.org/2/library/functions.html
  ; https://docs.python.org/3.5/library/functions.html
  ; most suitable from these are: abs (cmp) divmod max min pow
  (setv built-in-func-type (type pow))

  ; support: list tuple range
  (setv type-type (type range))
  
  (defn func? [code] 
    (and (symbol? code)
         (do
           (setv eval-type (type (eval code)))
           ; + - / * = !=
           (or (= eval-type func-type)
               ; TODO: these might need some additional check which is good to pass and which is not
               ; (if (in code ['abs 'cmp 'divmod 'max 'min 'pow 'range])) ...
               ; abs (cmp) divmod max min pow and all other built in function, 
               ; that might or might not be suitable for unary / binary / multiary operation
               (= eval-type built-in-func-type)
               ; list tuple range
               (= eval-type type-type)))))

  (defn operator? [code]
    (and ; should not be a collection
         (not (coll? code))
         ; should not be one of the custom operands
         ; without this check unnamed variable error occurs
         (not (in code operands))
         (or ; could be a custom operator added with #>
             (in code operators)
             ; or one of the native math operators: + - * / = !=
             ; or built in function and methods, where the most suitable are:
             ; abs (cmp) divmod max min pow
             ; or just a range, list or tuple
             (func? code))))

  (defn one? [code] (= (len code) 1))

  (defn not-expression? [code] (not (isinstance code hy.HyExpression)))

  (defn one-operand? [code]
    (and (one? code)
         (not (coll? (first code))) 
         (in (first code) operands)))

  (defn one-not-operator? [code]
    (and (one? code)
         (not (operator? (first code)))))

  ; infix
  (defn second-operator? [code]
    (and (pos? (len code)) 
         (operator? (second code))
         (not (operator? (first code)))
         (not (operator? (last code)))))

  ; postfix
  (defn last-operator? [code]
    (and (> (len code) 1) 
         (operator? (last code))))
  
  ; prefix
  (defn first-operator? [code]
    (and (> (len code) 1) 
         (operator? (first code))))
  
  (defn third [lst] (get lst 2)))

; main parser loop for infix prefix and postfix clauses
(defreader $ [code]
  (if
    ; scalar or some other value
    (not (coll? code))
      ; if code is one of the custom variables, return the value of it
      (if (in code operands)
          (get operands code)
          ; else return just the value
          code)
    ; list with lenght of 1 and the single item is the operand
    (one-operand? code) (get operands (first code))
    ; list with lenght of 1 and the single item not being the operator
    (one-not-operator? code) `#$~@code
    ; two or more items, last item is an operator: postfix
    (last-operator? code) `#$(~(last code) ~@(take (dec (len code)) code))
    ; list with three or more items, second is the operator: prefix
    (second-operator? code)
      (do
        ; the second operator on the list is the default index
        (setv idx 1)
        ; loop over all operators
        (for [op operators-precedence]
          ; set new index if operator is found from the code and break in that case
          (if (in op code) (do (setv idx (.index code op)) (break))))
        ; make list nested based on the found index and evaluate again
        `#$~(list-nest code idx))
    ; list with more than 1 items and the first item is the operator: prefix
    (first-operator? code)
      ; take the first item i.e. operator and use
      ; rest of the items as arguments once evaluated by #$
      `(~(first code) ~@(list-comp `#$~part [part (drop 1 code)]))
    ; list or tuple should be accepted also
    (not-expression? code) code
    ; possibly syntax error on clause
    ; might be caused by arbitrary usage of operators and operands
    ; something like: (1 1 + 0 -)
    `(raise (Exception "Expression error. Formula is not recognized as a well-formed expression!"))))
