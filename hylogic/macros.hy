#!/usr/bin/python3
(require [hylogic.connectives [*]])
(import (hylogic.connectives (*)))

; define axiom class
(defclass Axiom [object]
  ; iit object
  (defn --init-- [self symbol value &optional sentence]
    (setv self.symbol symbol)
    (setv self.value value)
    (setv self.sentence sentence))
  ; string representation, for print and str calls
  ; combines symbol<sentence>=truth-value
  (defn --str-- [self]
    (str (% "%s%s=%s"  
       (, self.symbol
          (if-not (empty? self.sentence) (% "<%s>" self.sentence) "")
          (str (= 1 self.value))))))
  ; __repr__ and __bool__ are needed for all, any, and, or, not and similar
  ; boolean type functions checks
  (defn --repr-- [self]
    (str (self.__bool__)))
  (defn --bool-- [self]
    (= True self.value)))

; define axiom macro. init axiom and set variable as a local instance
(defmacro defaxiom [symbol truth-value &optional sentence]
  `(setv ~symbol (Axiom ~(str symbol) ~truth-value ~sentence)))

; define proposition macro
(defmacro defproposition [&rest axioms])

; define argument macro
(defmacro defargument [&rest propositions])
