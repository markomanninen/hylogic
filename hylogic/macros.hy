#!/usr/bin/python3
(require [hylogic.connectives [*]])
(import (hylogic.connectives (*)))

; define proposition class
(defclass Proposition [object]
  ; init object
  ; at least symbol needs to be given
  ; but truth-value is optional. it could be Null just to maintain
  ; proposition on a theorem state. also sentence, that is a human
  ; readable natural language statement phrase, is optional
  ; sentence is usually a statement that claims that something
  ; is either true or false
  (defn --init-- [self symbol &optional truth-value sentence]
    (setv self.symbol symbol)
    (setv self.truth-value truth-value)
    (setv self.sentence sentence))
  ; string representation, for print and str calls
  ; combines symbol<sentence>=truth-value
  (defn --str-- [self]
    (str (% "%s%s%s"
       (, self.symbol
          (if-not (empty? self.sentence) (% "<%s>" self.sentence) "")
          (if-not (null? self.truth-value) (% "=%s" (str (= 1 self.truth-value))))))))
  ; __repr__ and __bool__ are needed for all, any, and, or, not and similar
  ; boolean type functions checks
  (defn --repr-- [self]
    (str (self.__bool__)))
  (defn --bool-- [self]
    (= True self.truth-value)))

(defclass Premise [object]
  (defn --init-- [self rule]
    (setv self.rule rule)))

(defclass Conclusion [object]
  (defn --init-- [self rule]
    (setv self.rule rule)))

(defclass Argument [object]
  (defn --init-- [self &rest premises]
    (setv self.premises premises)
    (setv self.valid Null))
  (defn --str-- [self]
    (str (self.premises)))
  (defn valid [self]
    self.valid))

; define proposition macro. init proposition and set variable as a local instance
(defmacro defproposition [symbol &optional truth-value sentence]
  `(setv ~symbol (Proposition ~(str symbol) ~truth-value ~sentence)))

; define premise macro
(defmacro defpremise [&rest rules]
  `(Premise ~rules))

; define conclusion macro
(defmacro defconclusion [&rest rules]
  `(Conclusion ~rules))

; define argument macro
(defmacro defargument [&rest premises-and-conclusion]
  `(Argument ~@premises-and-conclusion))
