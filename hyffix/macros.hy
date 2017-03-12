#!/usr/bin/python3
; require > and < reader macros
(require [hyffix.globals [< >]])
; import operator list. this makes globals.hy executed first
; so that operators variable is found in the current scope
; setting variable in the same file by setv or eval-and-compile 
; didn't work. this will also import operators-precedence list
(import (hyffix.globals (operands operators operators-precedence)))

; print multiple statements on new lines
; TODO other place more suitable? helpers.hy
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
; TODO: how necessary this is if setv works?
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
(defmacro deffix [&rest items] `(first #$~items))

; pass multiple (n) evaluation clauses. each of the must be
; wrapped by () parentheses
(defmacro deffix-n [&rest items]
  (list-comp `(deffix ~item) [item items]))

; for hy.HyExpression
(import hy)

; helper functions for #$ reader macro
(eval-and-compile
  ; this takes a list of items at least 3
  ; index must be bigger than 1 and smaller than the length of the list
  ; left and right side of the index will be picked to a new list where
  ; centermost item is moved to left and left to center
  ; [1 a 2 b 3 c 4] idx=3 -> [1 a [b 2 3] c 4]
  (defn list-nest [code indx]
    (setv tmp
      (doto 
        (list (take 1 (drop indx code))) 
        (.append (get code (dec indx))) 
        (.append (get code (inc indx)))))
    (setv fin
      (doto
        (list (take (dec indx) code))
        (.append (hy.HyExpression tmp))
        (.extend (list (drop (+ 2 indx) code)))))
    (if (isinstance code hy.HyExpression)
        (hy.HyExpression fin)
        fin))

  (setv func-type (type (fn [])))

  ; https://docs.python.org/2/library/functions.html
  ; https://docs.python.org/3.5/library/functions.html
  ; most suitable from these are: abs (cmp) divmod max min pow
  (setv built-in-func-type (type pow))

  ; support: list tuple range
  (setv type-type (type range))
  (setv list-type (type '[]))
  (defn list-type? [code] (and (= list-type (type code)) (not-expression? code)))

  ; is function
  ; TODO: could perhaps be smarter...
  (defn func? [code] 
    (and (symbol? code)
         (do 
           (try
             ; catch "name is not defined" errors
             (setv eval-type (type (eval code)))
             (except (e Exception) 
               (setv eval-type None)))
           ; + - / * = != < > <= >=
           (or (= eval-type func-type)
               ; TODO: these might need some additional check which is good to pass and which is not
               ; (if (in code ['abs 'cmp 'divmod 'max 'min 'pow 'range])) ...
               ; abs (cmp) divmod max min pow and all other built in function, 
               ; that might or might not be suitable for unary / binary / multiary operation
               (= eval-type built-in-func-type)
               ; list tuple range
               (= eval-type type-type)))))

  ; is operator
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

  (defn not-expression? [code]
    (not (isinstance code hy.HyExpression)))

  ; collection length one
  (defn one? [code] (and (= (len code) 1)))

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
         (operator? (first code)))))

; main macro parser loop for infix, prefix, and postfix clauses
(defreader $ [code]
  (if
    ;;; 1
    ; not collection / expression -> scalar or some other value
    (not (coll? code))
      ; if code is one of the custom variables, return the value of it
      (if (in code operands) (get operands code)
          ; else return the code as a value
          code)
    ;;; 2
    ; collection with lenght of 1
    ; this must be checked before last and first checks
    ; because they could also match. second operator of course couldnt
    (one? code)
        ; wrap list by a list, but evaluate content
        (if (list-type? code) [`#$~@code]
            ; else just evaluate content
            `#$~@code)
    ;;; 3
    ; two or more items, last item is an operator: postfix
    (last-operator? code) `#$(~(last code) ~@(take (dec (len code)) code))
    ;;; 4
    ; list with three or more items, second is the operator: infix
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
    ;;; 5
    ; list with more than 1 items and the first item is the operator: prefix
    (first-operator? code)
      ; take the first item i.e. operator and use
      ; rest of the items as arguments once evaluated by #$
      `(~(first code) ~@(list-comp `#$~part [part (drop 1 code)]))
    ; try just plain code
    ; this makes possible to evaluate all the other types of expressions
    ; that doesn't match previous 5 cases. that makes it almost anything
    code))
