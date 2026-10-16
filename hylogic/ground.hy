"Ground problems with functions and equality, decided with SAT.

Some problems have no variables at all, only constants and functions, like the
finite algebra problems in TPTP: their operations are tabulated on named
elements, and the question is about those tables. Resolution is a poor fit,
and grounding over the constants does not apply, because there are functions.

The encoding here gives every ground term a value in a domain {1..n}:

  val(t, e)    term t has value e; every term has exactly one value
  F(ē, v)      function f maps the elements ē to v; one table per function,
               shared by all its terms, so equal arguments give equal values
  t = s        an auxiliary variable, true exactly when t and s have the same value

and hands the clauses to the SAT solver. A satisfying assignment is a model.

When is \"no model\" a proof? Ground clauses only talk about the terms that
occur in them. If every compound term t among them is said to equal a constant
(a clause t = c1 | ... | t = ck), then in any model every such term has a
constant's value, so the elements that matter are the constants' values, and
a model with at most as many elements as there are constants exists whenever
any model does. Finding none up to that size proves the clauses unsatisfiable.
Constants that unit clauses c != d keep apart are fixed to their own elements,
which removes symmetric models."

(import itertools [product]
        time
        hylogic.terms [variable? compound? variables-of]
        hylogic.cdcl [cdcl :as dpll]
        hylogic.finite [distinct-constants])

(defn _negative? [l] (and (compound? l) (= (get l 0) "not")))
(defn _atom [l] (if (_negative? l) (get l 1) l))

(defn ground? [clauses]
  (not (any (gfor c clauses (variables-of (tuple c))))))

(defn _terms [clauses]
  "Every ground term in the clauses' atoms, subterms first."
  (setv found [] seen #{})
  (defn walk [t]
    (when (compound? t) (for [a (cut t 1 None)] (walk a)))
    (when (not-in t seen) (.add seen t) (.append found t)))
  (for [c clauses  l c]
    (setv a (_atom l))
    (when (compound? a) (for [x (cut a 1 None)] (walk x))))
  found)

(defn closure-bound [clauses terms]
  "An upper bound on the size of a smallest model: the number of constants, plus
  one for every term whose value is not forced to be a constant.

  A clause t = c1 | ... | t = ck says t takes one of those constants as its value.
  For a term f(t1, ..., tn) without such a clause, every combination of its
  arguments' possible values must be covered for f, and its possible values are
  then the union of those. This follows the problem's own structure, so in a
  problem about two algebras each operation only needs to be covered on its own
  algebra's elements."
  (setv constants (lfor t terms :if (not (compound? t)) t)
        covered {})
  (for [c clauses]
    (setv lefts #{} values #{})
    (for [l c]
      (if (and (not (_negative? l)) (compound? l) (= (get l 0) "=") (= (len l) 3))
          (setv [_ s t] l)
          (do (setv lefts None) (break)))
      (cond
        (and (compound? s) (not (compound? t))) (do (.add lefts s) (.add values t))
        (and (compound? t) (not (compound? s))) (do (.add lefts t) (.add values s))
        True (do (setv lefts None) (break))))
    (when (and lefts (= (len lefts) 1))
      (setv term (next (iter lefts))
            (get covered term) (& (.get covered term values) values))))
  (setv memo {})
  (defn possible [t]
    "The constants t can equal, or None if it is not bounded."
    (when (in t memo) (return (get memo t)))
    (setv result
      (cond
        (not (compound? t)) #{t}
        (in t covered) (get covered t)
        True
          (do
            (setv arg-values (lfor a (cut t 1 None) (possible a)))
            (if (in None arg-values)
                None
                (do
                  (setv out #{})
                  (for [combo (product #* (gfor v arg-values (sorted v)))]
                    (setv key #((get t 0) #* combo))
                    (if (in key covered)
                        (|= out (get covered key))
                        (return None)))
                  out)))))
    (setv (get memo t) result)
    result)
  ;; every term with no forced constant value may be a new element of its own
  (+ (len constants) (sum (gfor t terms (is (possible t) None)))))

(defclass _Encoder []
  (defn __init__ [self n] (setv self.n n self.vars {} self.cnf []))
  (defn var [self key]
    (when (not-in key self.vars) (setv (get self.vars key) (+ (len self.vars) 1)))
    (get self.vars key))
  (defn add [self clause] (.append self.cnf clause))
  (defn exactly-one [self keys]
    (setv vs (lfor k keys (.var self k)))
    (.add self vs)
    (for [i (range (len vs)) j (range (+ i 1) (len vs))]
      (.add self [(- (get vs i)) (- (get vs j))]))))

(defn _encode [clauses terms n fixed]
  (setv enc (_Encoder n) dom (list (range 1 (+ n 1))) funs {} preds {})
  (for [t terms]
    ;; every term has exactly one value; a fixed constant also has its own one
    (.exactly-one enc (lfor e dom #("val" t e)))
    (when (in t fixed)
      (.add enc [(.var enc #("val" t (get fixed t)))]))
    (when (compound? t)
      (setv f (get t 0) args (cut t 1 None) (get funs f) (len args))
      (for [es (product dom :repeat (len args))  v dom]
        (.add enc [#* (gfor [a e] (zip args es) (- (.var enc #("val" a e))))
                   (- (.var enc #("fn" f es v))) (.var enc #("val" t v))]))))
  (for [[f k] (.items funs)  es (product dom :repeat k)]
    (.exactly-one enc (lfor v dom #("fn" f es v))))
  (defn literal [l]
    (setv a (_atom l) neg (_negative? l))
    (setv v
      (cond
        (and (compound? a) (= (get a 0) "="))
          (do
            (setv [_ s t] a q (.var enc #("eq" s t)))
            (for [e dom]
              (.add enc [(- (.var enc #("val" s e))) (- (.var enc #("val" t e))) q])
              (.add enc [(- q) (- (.var enc #("val" s e))) (.var enc #("val" t e))]))
            q)
        (compound? a)
          (do
            (setv p (get a 0) args (cut a 1 None) r (.var enc #("atom" a)))
            (for [es (product dom :repeat (len args))]
              (setv guard (lfor [x e] (zip args es) (- (.var enc #("val" x e))))
                    table (.var enc #("pred" p es)))
              (.add enc [#* guard (- table) r])
              (.add enc [#* guard table (- r)]))
            r)
        (= a "true") None
        (= a "false") None
        True (.var enc #("prop" a))))
    (cond
      (= a "true") (if neg "false" "true")
      (= a "false") (if neg "true" "false")
      True (if neg (- v) v)))
  (for [c clauses]
    (setv row [] satisfied False)
    (for [l c]
      (setv x (literal l))
      (cond (= x "true") (do (setv satisfied True) (break))
            (= x "false") None
            True (.append row x)))
    (when (not satisfied) (.add enc row)))
  enc)

(defn _model-holds? [clauses enc model]
  "Do the original clauses hold in the model the SAT solver found? A last check
  that a model is real before it is reported."
  (setv names (dfor [key v] (.items enc.vars) v key)
        value {} props #{} preds #{})
  (for [[v on] (.items model)]
    (when on
      (setv key (.get names v))
      (cond
        (is key None) None
        (= (get key 0) "val") (setv (get value (get key 1)) (get key 2))
        (= (get key 0) "prop") (.add props (get key 1))
        (= (get key 0) "pred") (.add preds #((get key 1) (get key 2))))))
  (defn holds [l]
    (setv neg (_negative? l) a (_atom l))
    (setv r (cond
              (and (compound? a) (= (get a 0) "=")) (= (get value (get a 1)) (get value (get a 2)))
              (= a "true") True
              (= a "false") False
              (compound? a) (in #((get a 0) (tuple (gfor x (cut a 1 None) (get value x)))) preds)
              True (in a props)))
    (!= r neg))
  (all (gfor c clauses (any (gfor l c (holds l))))))

(defn decide-ground [clauses [deadline None] [max-size 14]]
  "proved, saturated (a model exists) or None, for ground clauses with functions."
  (when (not (ground? clauses)) (return None))
  (setv terms (_terms clauses)
        bound (closure-bound clauses terms)
        clique (distinct-constants clauses)
        fixed (dfor [i c] (enumerate clique) c (+ i 1))
        top (min bound max-size))
  (for [n (range (max 1 (len clique)) (+ top 1))]
    (when (and deadline (> (time.monotonic) deadline)) (return None))
    (setv enc (_encode clauses terms n fixed)
          model (dpll enc.cnf :deadline deadline))
    (cond
      (= model "timeout") (return None)
      (is-not model None)
        (if (_model-holds? clauses enc model)
            (return "saturated")
            (raise (RuntimeError "ground encoding produced a model that violates the clauses")))))
  ;; no model up to the bound proves unsatisfiability; a bound beyond max-size proves nothing
  (if (<= bound max-size) "proved" None))
