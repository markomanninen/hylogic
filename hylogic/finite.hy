"Finite models by flattening and SAT, in the style of Paradox.

The model finder in hylogic.models enumerates function tables one by one,
which is hopeless for a binary function over five elements (5^25 tables).
Paradox (Claessen and Sörensson, 2003) lets the SAT solver choose the tables:

1. Flatten every clause, so that functions occur only in literals that say
   what they are equal to: p(f(x)) becomes  ¬F(x, y) ∨ p(y),  where F(x, y)
   means f(x) = y. Constants are functions without arguments.
2. For a domain {1..n}, make a SAT variable for every predicate fact and every
   function value F(ā, e), add for every function and argument tuple that it
   has at most one value (functionality) and at least one (totality), and
   ground the flattened clauses over the domain. Equality between elements is
   decided on the spot: an element equals only itself.
3. Try n = 1, 2, ... A satisfying assignment is a model of that size.

When the axioms bound the domain, for instance with a clause
x = e1 ∨ ... ∨ x = ek, every model has at most k elements, so finding no
model up to k proves the clauses unsatisfiable: a theorem."

(import itertools [product count]
        time
        hylogic.terms [variable? compound? variables-of]
        hylogic.sat [dpll])

(defn _negative? [l] (and (compound? l) (= (get l 0) "not")))
(defn _atom [l] (if (_negative? l) (get l 1) l))

(defn flatten-clause [clause [fixed None]]
  "The clause with every function application replaced by a variable, plus the
  literals ¬($fn f args... y) that define those variables. Constants in fixed
  (constant -> element) are replaced by their element instead."
  (setv fresh (count 1) extra [] seen {} fixed (or fixed {}))
  (defn flat [t]
    "A variable standing for term t, adding its defining literal once."
    (cond
      (variable? t) t
      (in t fixed) (get fixed t)
      (in t seen) (get seen t)
      True
        (do
          (setv args (if (compound? t) (lfor a (cut t 1 None) (flat a)) [])
                name (if (compound? t) (get t 0) t)
                y f"?_f{(next fresh)}")
          (setv (get seen t) y)
          (.append extra #("not" #("$fn" name #* args y)))
          y)))
  (setv out [])
  (for [l clause]
    (setv a (_atom l))
    (setv flat-atom (if (compound? a) #((get a 0) #* (gfor x (cut a 1 None) (flat x))) a))
    (.append out (if (_negative? l) #("not" flat-atom) flat-atom)))
  [#* out #* extra])

(defn _signature [flat-clauses]
  "Predicates and functions (with constants as 0-ary functions) with arities."
  (setv preds {} funs {})
  (for [c flat-clauses  l c]
    (setv a (_atom l))
    (cond
      (and (compound? a) (= (get a 0) "$fn")) (setv (get funs (get a 1)) (- (len a) 3))
      (and (compound? a) (!= (get a 0) "=")) (setv (get preds (get a 0)) (- (len a) 1))
      (and (not (compound? a)) (not-in a #{"true" "false"})) (setv (get preds a) 0)))
  #(preds funs))

(defn _constant? [t] (and (isinstance t str) (not (variable? t))))

(defn distinct-constants [clauses]
  "A largest set of constants that unit clauses c != d say are pairwise distinct.
  They can be fixed to the elements 1..k in any model (symmetry breaking)."
  (setv unequal #{})
  (for [c clauses]
    (when (= (len c) 1)
      (setv [l] c)
      (when (and (_negative? l) (compound? (get l 1)) (= (get (get l 1) 0) "=")
                 (_constant? (get (get l 1) 1)) (_constant? (get (get l 1) 2)))
        (.add unequal (frozenset [(get (get l 1) 1) (get (get l 1) 2)])))))
  ;; greedy clique, starting from the constant with most inequalities
  (setv degree {})
  (for [pair unequal  c pair] (setv (get degree c) (+ (.get degree c 0) 1)))
  (setv clique [])
  (for [c (sorted degree :key (fn [c] #((- (get degree c)) c)))]
    (when (all (gfor d clique (in (frozenset [c d]) unequal)))
      (.append clique c)))
  clique)

(defn closure-bound [clauses]
  "The number of constants if every function applied to constants is said to equal
  one of them (clauses f(c...) = d1 | ... | f(c...) = dk), else None. Then every
  ground term equals a constant, so term-generated models are no larger."
  (setv constants #{} functions {} covered #{})
  (defn walk [t]
    (cond
      (variable? t) None
      (compound? t) (do (setv (get functions (get t 0)) (- (len t) 1)) (for [a (cut t 1 None)] (walk a)))
      True (.add constants t)))
  (for [c clauses  l c]
    (setv a (_atom l))
    (when (compound? a) (for [x (cut a 1 None)] (walk x))))
  (for [c clauses]
    (setv lefts (sfor l c (if (and (not (_negative? l)) (compound? l) (= (get l 0) "=")
                                   (compound? (get l 1)) (_constant? (get l 2))
                                   (all (gfor x (cut (get l 1) 1 None) (_constant? x))))
                              (get l 1) None)))
    (when (and (= (len lefts) 1) (is-not (next (iter lefts)) None))
      (.add covered (next (iter lefts)))))
  (for [[f k] (.items functions)  args (product (sorted constants) :repeat k)]
    (when (not-in #(f #* args) covered) (return None)))
  (len constants))

(defn domain-bound [clauses]
  "k if some clause says every element equals one of k constants, else None."
  (setv best None)
  (for [c clauses]
    (setv vs (variables-of (tuple c)) constants #{})
    (when (and (= (len vs) 1) c
               (all (gfor l c (and (not (_negative? l)) (compound? l) (= (get l 0) "=")
                                   (= (len l) 3)
                                   (or (and (= (get l 1) (get vs 0)) (not (compound? (get l 2)))
                                            (not (variable? (get l 2))))
                                       (and (= (get l 2) (get vs 0)) (not (compound? (get l 1)))
                                            (not (variable? (get l 1)))))))))
      (for [l c] (.add constants (if (= (get l 1) (get vs 0)) (get l 2) (get l 1))))
      (when (or (is best None) (< (len constants) best)) (setv best (len constants)))))
  best)

(defclass _TooBig [Exception])

(defn _encode [flat-clauses n preds funs [max-clauses 400000]]
  "SAT clauses for a model of size n, with the variable numbering."
  (setv domain (list (range 1 (+ n 1))) vars {} cnf [])
  (defn var [key]
    (when (not-in key vars) (setv (get vars key) (+ (len vars) 1)))
    (get vars key))
  (for [[f k] (.items funs)  args (product domain :repeat k)]
    (.append cnf (lfor e domain (var #("$fn" f #* args e))))
    (for [e1 domain e2 domain]
      (when (< e1 e2)
        (.append cnf [(- (var #("$fn" f #* args e1))) (- (var #("$fn" f #* args e2)))]))))
  (for [c flat-clauses]
    (setv vs (variables-of (tuple c)))
    (for [values (product domain :repeat (len vs))]
      (setv s (dict (zip vs values)) row [] satisfied False)
      (for [l c]
        (setv neg (_negative? l) a (_atom l))
        (setv a (if (compound? a) #((get a 0) #* (gfor x (cut a 1 None) (.get s x x))) a))
        (cond
          (= a "true") (if neg None (setv satisfied True))
          (= a "false") (if neg (setv satisfied True) None)
          (and (compound? a) (= (get a 0) "="))
            (when (!= (= (get a 1) (get a 2)) neg) (setv satisfied True))
          True (.append row (if neg (- (var a)) (var a))))
        (when satisfied (break)))
      (when (not satisfied)
        (.append cnf row)
        (when (> (len cnf) max-clauses) (raise (_TooBig))))))
  #(cnf vars))

(defn find-finite-model [clauses [max-size 6] [deadline None] [sizes None] [fixed-constants None]]
  "The smallest model of the clauses with at most max-size elements:
  #(n facts) where facts are the true predicate and function atoms; or the
  string unsat if there is none up to max-size, or None if the search could
  not finish (too large, or out of time)."
  (setv fixed-constants (or fixed-constants [])
        fixed (dfor [i c] (enumerate fixed-constants) c (+ i 1))
        flat (lfor c clauses (flatten-clause c fixed))
        [preds funs] (_signature flat))
  (for [n (or sizes (range (max 1 (len fixed-constants)) (+ max-size 1)))]
    (when (and deadline (> (time.monotonic) deadline)) (return None))
    (try
      (setv [cnf vars] (_encode flat n preds funs))
      (except [_TooBig] (return None)))
    (setv model (dpll cnf :deadline deadline))
    (cond
      (= model "timeout") (return None)
      (is-not model None)
        (return #(n (lfor [key v] (.items vars) :if (.get model v False) key)))))
  "unsat")

(defn decide-finite [clauses [deadline None] [max-size 4]]
  "proved, saturated (a model exists) or None, by finite model search.
  proved only when the clauses bound the domain and no model fits the bound."
  (setv bound (or (domain-bound clauses) (closure-bound clauses))
        limit (if bound (min bound 10) max-size)
        found (find-finite-model clauses :max-size limit :deadline deadline
                                 :fixed-constants (distinct-constants clauses)))
  (cond
    (is found None) None
    (= found "unsat") (if bound "proved" None)
    True "saturated"))
