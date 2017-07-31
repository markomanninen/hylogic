#!/usr/bin/python3
(require [hylogic.connectives [*]])
(import (hylogic.connectives (*)))
; for negation symbol creation
(import hy)

; define proposition class
(defclass Proposition [object]
  ; init object
  ; at least symbol needs to be given
  ; but truth-value is optional. it could be Null just to maintain
  ; proposition on a theorem state. also sentence, that is a human
  ; readable natural language statement phrase, is optional
  ; sentence is usually a statement that claims that something
  ; is either true or false
  (defn --init-- [self symbol &optional [truth-value True] [sentence ""]]
    (setv self.symbol symbol)
    (setv self.truth-value truth-value)
    (setv self.sentence sentence))
  ; string representation, for print and str calls
  ; combines symbol<sentence>=truth-value
  (defn --str-- [self]
    (str (% "%s%s%s"
       (, self.symbol
          (if-not (empty? self.sentence) (% "<%s>" self.sentence) "")
          (if-not (none? self.truth-value) (% "=%s" (str (= 1 self.truth-value))))))))
  ; __repr__ and __bool__ are needed for all, any, and, or, not and similar
  ; boolean type functions checks
  (defn --repr-- [self]
    (str (self.__bool__)))
  ; map, = checks
  (defn --eq-- [self x]
    (= x self.truth-value))
  ; != checks
  (defn --ne-- [self x]
    (!= x self.truth-value))
  ; all, any, not checks
  (defn --bool-- [self]
    (= True self.truth-value)))

(defclass Premise [object]
  (defn --init-- [self rules truth-value]
    (setv self.rules rules)
    (setv self.truth-value truth-value))
  (defn --str-- [self]
     (+ "\r\n  " (.replace (.join " " (map str self.rules)) "'" ""))))

(defclass Conclusion [Premise]
  (defn --init-- [self proposition]
    (setv self.proposition proposition)
    (setv self.truth-value proposition.truth-value))
  (defn --str-- [self] 
     (+ "\r\n--------------\r\n∴ " self.proposition.symbol "\r\n")))

(defclass Argument [object]
  (defn --init-- [self &rest premises]
    (setv self.premises premises)
    (setv self.valid None))
  (defn --str-- [self]
    (str (.join "" (map str self.premises))))
  (defn valid [self]
    self.valid))

(defn create-symbol [&rest args]
  (hy.HySymbol (.join "" (map str args))))

; define proposition macro. init proposition and set variable as a local instance
(defmacro defproposition [symbol &optional [truth-value True] [sentence ""]]
  `(setv ~symbol (defoperand ~symbol (Proposition ~(str symbol) ~truth-value ~sentence))))

; define multiple simple propositions macro
(defmacro defpropositions+ [name &rest args]
  (if (len args)
      `(do
         (~name ~(get args 0))
         (defpropositions+ ~name ~@(cut args 1)))))

; define multiple simple propositions macro
(defmacro defpropositions [&rest args]
  `(defpropositions+ defproposition ~@args))

; slightly different proposition macro definer that creates also negation variable
(defmacro defproposition* [symbol &optional [truth-value True] [sentence ""]]
  `(do
    (defproposition ~symbol ~truth-value ~sentence)
    (defproposition ~(create-symbol '¬ symbol) (not ~truth-value) ~sentence)))

; define multiple simple propositions with negatives macro
(defmacro defpropositions* [&rest args]
  `(defpropositions+ defproposition* ~@args))

; define premise macro
(defmacro defpremise [&rest rules]
  `(Premise '~rules (deffix ~@rules)))

; define conclusion macro
(defmacro defconclusion [rule]
  `(Conclusion ~rule))

; define argument macro
(defmacro defargument [&rest premises-and-conclusion]
  `(Argument ~@premises-and-conclusion))

; quantifier y factor
(defmacro quantifier-y [quantifier variables func &rest domains]
  `(~quantifier (map
      ; map anonymous function for the domain set
      ; vars is for example (x) or (x y) ...
      (fn ~variables
        (do
          ; init variable(s) for possible deffix routines
          (defoperand ~@(flatten (zip variables variables)))
          ; if multiple domain sets are provided, then values are
          ; passed to the anonymous functions in tuples taking one item from each
          ; domain to match each argument on anonymous function
          ; (, (, 1 2 3) (, 1 2 3 4)) for example sends arguments in groups of:
          ; (, 1 1) (, 2 2) (, 3 3) and leaves the last iteration because there is no
          ; pair for y: (, undefined 4)
          ~func)) ~@domains)))

; quantifier x factor
(defmacro quantifier-x [quantifier variables func &rest domains]
  ; if there are quantifiers on the function ...
  (if (or (= (first func) '∀) (= (first func) '∃))
    ; recursive calls for nested quantifiers
    `(quantifier-y ~quantifier ~variables (~(first func) ~@(drop 1 func)) ~@domains)
    ; lowest level function needs to be passed to deffix resolver
    `(quantifier-y ~quantifier ~variables (deffix ~func) ~@domains)))

; universal quantifier, forall
(defmacro ∀ [variables func &rest domains] 
  `(quantifier-x all ~variables ~func ~@domains))

; existential quantifier, some
(defmacro ∃ [variables func &rest domains]
  `(quantifier-x any ~variables ~func ~@domains))
