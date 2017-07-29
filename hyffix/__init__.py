#!/usr/bin/python3
# -*- coding: utf-8 -*-
#
# Copyright (c) 2013 Paul Tagliamonte <paultag@debian.org>
# Copyright (c) 2013 Gergely Nagy <algernon@madhouse-project.org>
# Copyright (c) 2013 James King <james@agentultra.com>
# Copyright (c) 2013 Julien Danjou <julien@danjou.info>
# Copyright (c) 2013 Konrad Hinsen <konrad.hinsen@fastmail.net>
# Copyright (c) 2013 Thom Neale <twneale@gmail.com>
# Copyright (c) 2013 Will Kahn-Greene <willg@bluesock.org>
# Copyright (c) 2013 Bob Tolbert <bob@tolbert.org>
#
# Permission is hereby granted, free of charge, to any person obtaining a
# copy of this software and associated documentation files (the "Software"),
# to deal in the Software without restriction, including without limitation
# the rights to use, copy, modify, merge, publish, distribute, sublicense,
# and/or sell copies of the Software, and to permit persons to whom the
# Software is furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
# THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
# DEALINGS IN THE SOFTWARE.
#
# hymagic is an adaptation of the HyRepl to allow ipython iteration
# hymagic author - Todd Iverson
# Available as github.com/yardsale8/hymagic
#
# Credits for the starting point of the magic:
# https://github.com/yardsale8/hymagic/blob/master/hymagic/__init__.py
#
# and special mentions to:
# Ryan (https://github.com/kirbyfan64) and 
# Tuukka (https://github.com/tuturto) in the hylang discuss forum: 
# https://groups.google.com/forum/#!forum/hylang-discuss
# who made it possible for me to resolve all essential obstacles
# when struggling with macros

from IPython.core.magic import Magics, magics_class, line_cell_magic
import ast

try:
    from hy.lex import LexException, PrematureEndOfInput, tokenize
    from hy.compiler import hy_compile, HyTypeError
    from hy.importer import ast_compile
except ImportError as e:
    print("To use this magic extension, please install Hy (https://github.com/hylang/hy) with: pip install git+https://github.com/hylang/hy.git")
    from sys import exit
    exit(e)

#print("Use for example: %hylang (+ 1 1)")
#print("Or: %deffix (1 + (+ 1 (1 +))")

from IPython.display import HTML
from remarkuple import helper as h, table

hy_program = """

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
(defreader > [items] 
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
(defreader < [items]
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

; add input here
%s

"""

def get_tokens(source, filename):
    try:
        return tokenize(source)
    except PrematureEndOfInput as e:
        print(e)
    except LexException as e:
        if e.source is None:
            e.source = source
            e.filename = filename
        print(e)

def parse(tokens, source, filename, shell, interactive):
    try:
        _ast = hy_compile(tokens, "__console__", root = interactive)
        shell.run_ast_nodes(_ast.body, filename, compiler = ast_compile)
    except HyTypeError as e:
        if e.source is None:
            e.source = source
            e.filename = filename
        print(e)
    except Exception:
        shell.showtraceback()

tests_run = {}

@magics_class
class HyMagics(Magics):
    """ 
    Jupyter Notebook Magics (%plc and %%plc) for Propositional Logic Clauses (PLC) 
    written in Hy language (Lispy Python).
    """
    def __init__(self, shell):
        super(HyMagics, self).__init__(shell)
    
    @line_cell_magic
    def hylang(self, line = None, cell = None, filename = '<input>'):
        # both line %hylang and cell %%hylang magics are prepared here.
        source = line if line else cell
        # get input tokens for compile
        tokens = get_tokens(source, filename)
        if tokens:
            return parse(tokens, source, filename, self.shell, ast.Interactive)

    @line_cell_magic
    def deffix(self, line = None, cell = None, filename = '<input>'):
        # both line %plc and cell %%plc magics are prepared here.
        # if line magic is used then we prepend code #$ reader macro
        # to enable prefix hy code evaluation
        source = hy_program % ("(deffix %s)" % line if line else cell)
        # get input tokens for compile
        tokens = get_tokens(source, filename)
        if tokens:
            return parse(tokens, source, filename, self.shell, ast.Interactive)

    @line_cell_magic
    def runtests(self, line = None, cell = None, filename = '<input>'):
        """
        The %runtests magic searches your IPython namespace for functions
        with names that begin with 'test_'. It will attempt to run these
        functions (calling them with no arguments), and report whether they
        pass, fail (raise an AssertionError), or error (raise any other
        kind of error).

        For tests that fail or error %runtests will show the exception raised
        but not the traceback, so write informative messages!
        """

        import collections
        import time

        ip = get_ipython()

        tests = {}

        # collect tests, only find functions that start with 'test'
        for k, v in ip.user_ns.items():
            if k.startswith('test') and isinstance(v, collections.Callable) and ((not line) or (k not in tests_run)):
                tests[k] = v
                tests_run[k] = True

        # initialize table object
        tbl = table(CLASS='data')
        tbl.addColGroup(h.col(), h.col())
        tbl.addCaption('Collected {} tests.\n'.format(len(tests)))
        tbl.addHeadRow(h.tr(h.th('Test function name'), h.th('Status')))

        # run tests
        ok = 0
        fail = {}
        error = {}

        t1 = time.time()

        for name, func in tests.items():
            try:
                func()
            except AssertionError as e:
                msg = 'failed'
                fail[name] = e
            except Exception as e:
                msg = 'error'
                error[name] = e
            else:
                msg = 'successful'
                ok += 1
            tbl.addBodyRow(h.tr(h.td(name), h.td(msg), Class=msg))

        t2 = time.time()

        # collect info on any failures
        if fail:
            tbl.addBodyRows(h.tr(h.th("Failed", span=2)))
            trs = []
            for name, e in fail.items():
                trs.append(h.tr(h.td(name), h.td(repr(e))))
            tbl.addBodyRows(*trs, CLASS='failures')

        # collect info on any errors
        if error:
            tbl.addBodyRows(h.tr(h.th("Errors", span=2)))
            trs = []
            for name, e in error.items():
                trs.append(h.tr(h.td(name), h.td(repr(e))))
            tbl.addBodyRows(*trs, CLASS='errors')

        # summary and timer of the tests
        tbl.addFootRow(h.tr(h.td('Successful', Class="right"), h.td('{}'.format(ok))))
        tbl.addFootRow(h.tr(h.td('Failed',     Class="right"), h.td('{}'.format(len(fail)))))
        tbl.addFootRow(h.tr(h.td('Errors',     Class="right"), h.td('{}'.format(len(error)))))
        tbl.addFootRow(h.tr(h.td("Execution",  Class="right"), h.td('{:.4g} seconds'.format(t2 - t1))))

        # return html table string
        return HTML(str(tbl))

def load_ipython_extension(ip):
    """ Load the extension in Jupyter. """
    ip.register_magics(HyMagics)
