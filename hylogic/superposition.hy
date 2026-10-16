"Equality built into the inference rules: superposition and demodulation.

Equality axioms let resolution reason about =, but they resolve with almost
everything. Superposition instead replaces equals by equals directly:

  superposition        from C ∨ l = r and D[u], where l and u unify with σ,
                       derive (C ∨ D[r])σ, replacing u by r
  equality resolution  from C ∨ s ≠ t, where s and t unify with σ, derive Cσ
  equality factoring   from C ∨ s = t ∨ s' = t', where s and s' unify with σ,
                       derive (C ∨ t ≠ t' ∨ s' = t')σ
  demodulation         rewrite a new clause with known unit equations l = r,
                       always from the larger side to the smaller

\"Larger\" is the Knuth-Bendix ordering (KBO): a term is larger when it has
more symbols, or as many and a larger head symbol, and it never has fewer
occurrences of any variable. Replacing only larger terms by smaller ones keeps
the search from rewriting back and forth. Superposition is the method E and
Vampire use; this is a small version of it without literal selection."

(import collections [Counter]
        hylogic.terms [variable? compound? size]
        hylogic.unify [unify substitute match-term rename instantiate])

;; The Knuth-Bendix ordering

(defn _head [t]
  (if (compound? t) #((- (len t) 1) (str (get t 0))) #(0 (str t))))

(defn _var-counts [t [c None]]
  (when (is c None) (setv c (Counter)))
  (cond
    (variable? t) (+= (get c t) 1)
    (compound? t) (for [a (cut t 1 None)] (_var-counts a c)))
  c)

(defn _occurs [v t]
  (cond (= v t) True
        (compound? t) (any (gfor a (cut t 1 None) (_occurs v a)))
        True False))

(defn kbo> [s t]
  "Is term s greater than term t in the Knuth-Bendix ordering?"
  (cond
    (= s t) False
    (variable? s) False
    (variable? t) (_occurs t s)
    True
      (do
        (setv vs (_var-counts s) vt (_var-counts t))
        (when (any (gfor [x n] (.items vt) (> n (get vs x)))) (return False))
        (setv ws (size s) wt (size t))
        (cond
          (> ws wt) True
          (< ws wt) False
          (> (_head s) (_head t)) True
          (< (_head s) (_head t)) False
          True (do
                 (for [[a b] (zip (cut s 1 None) (cut t 1 None))]
                   (when (!= a b) (return (kbo> a b))))
                 False)))))

;; Literals

(defn equation? [atom] (and (compound? atom) (= (get atom 0) "=") (= (len atom) 3)))
(defn negative? [lit] (and (compound? lit) (= (get lit 0) "not")))
(defn atom-of [lit] (if (negative? lit) (get lit 1) lit))
(defn with-sign [lit atom] (if (negative? lit) #("not" atom) atom))

(defn positions [t [path #()]]
  "Non-variable subterms of t with their paths."
  (when (variable? t) (return))
  (yield #(path t))
  (when (compound? t)
    (for [i (range 1 (len t))]
      (yield :from (positions (get t i) #(#* path i))))))

(defn atom-positions [atom]
  "Rewritable positions inside an atom: its arguments and their subterms."
  (when (compound? atom)
    (for [i (range 1 (len atom))]
      (yield :from (positions (get atom i) #(i))))))

(defn replace-at [t path new]
  (if (not path)
      new
      (do
        (setv i (get path 0))
        #(#* (cut t 0 i) (replace-at (get t i) (cut path 1 None) new) #* (cut t (+ i 1) None)))))

;; Inference rules, each yielding frozensets of literals

(defn superpositions [from-clause into-clause]
  "Superposition from the positive equations of from-clause into into-clause."
  ;; nothing to do without a positive equation; checked before the costly renaming
  (when (not (any (gfor l from-clause (and (not (negative? l)) (equation? l)))))
    (return))
  ;; rename apart with one mapping, so a variable stays the same across the clause
  (setv mapping {}
        into (frozenset (gfor l into-clause (rename l mapping))))
  (for [eq from-clause]
    (when (and (not (negative? eq)) (equation? eq))
      (for [[l r] [#((get eq 1) (get eq 2)) #((get eq 2) (get eq 1))]]
        (when (variable? l) (continue))
        (for [lit into  [path u] (list (atom-positions (atom-of lit)))]
          (setv s (unify l u))
          (when (is s None) (continue))
          (setv ls (substitute l s) rs (substitute r s))
          (when (or (= ls rs) (kbo> rs ls)) (continue))
          (setv new-lit (with-sign lit (replace-at (substitute (atom-of lit) s) path rs)))
          (yield (frozenset [#* (gfor x (- from-clause #{eq}) (substitute x s))
                             #* (gfor x (- into #{lit}) (substitute x s))
                             new-lit])))))))

(defn equality-resolvents [clause]
  (for [lit clause]
    (when (and (negative? lit) (equation? (atom-of lit)))
      (setv s (unify (get (atom-of lit) 1) (get (atom-of lit) 2)))
      (when (is-not s None)
        (yield (frozenset (gfor x (- clause #{lit}) (substitute x s))))))))

(defn equality-factors [clause]
  (setv eqs (lfor l clause :if (and (not (negative? l)) (equation? l)) l))
  (for [a eqs b eqs]
    (when (is-not a b)
      (for [[s t] [#((get a 1) (get a 2)) #((get a 2) (get a 1))]
            [s2 t2] [#((get b 1) (get b 2)) #((get b 2) (get b 1))]]
        (setv sub (unify s s2))
        (when (is-not sub None)
          (yield (frozenset (gfor x [#* (- clause #{a}) #("not" #("=" t t2))] (substitute x sub)))))))))

;; Simplification

(defn orient [unit]
  "A unit equation as a rewrite rule #(l r) with l > r, or None if it cannot be oriented."
  (setv [_ s t] unit)
  (cond (kbo> s t) #(s t) (kbo> t s) #(t s) True None))

(defn _rewrite-term [t rules budget]
  "t rewritten innermost first with the rules, at most budget steps; #(term steps-used)."
  (setv used 0)
  (when (compound? t)
    (setv args [])
    (for [a (cut t 1 None)]
      (setv [a2 n] (_rewrite-term a rules (- budget used)))
      (+= used n)
      (.append args a2))
    (setv t #((get t 0) #* args)))
  (when (or (variable? t) (>= used budget)) (return #(t used)))
  (for [[l r] rules]
    (setv m (match-term l t))
    (when (is-not m None)
      (setv [t2 n] (_rewrite-term (instantiate r m) rules (- budget used 1)))
      (return #(t2 (+ used 1 n)))))
  #(t used))

(defn demodulate [literals rules [budget 50]]
  "The literals with every argument rewritten by the rules; #(literals changed?)."
  (when (not rules) (return #(literals False)))
  (setv out [] changed False)
  (for [lit literals]
    (setv atom (atom-of lit))
    (if (compound? atom)
        (do
          (setv args [])
          (for [a (cut atom 1 None)]
            (setv [a2 n] (_rewrite-term a rules budget))
            (when n (setv changed True))
            (.append args a2))
          (.append out (with-sign lit #((get atom 0) #* args))))
        (.append out lit)))
  #((frozenset out) changed))

(defn trivial? [literals]
  "Does the clause contain s = s, which makes it true?"
  (any (gfor l literals (and (not (negative? l)) (equation? l) (= (get l 1) (get l 2))))))

(defn drop-false-equations [literals]
  "The clause without literals s ≠ s, which are false."
  (frozenset (gfor l literals :if (not (and (negative? l) (equation? (atom-of l))
                                            (= (get (atom-of l) 1) (get (atom-of l) 2))))
                   l)))
