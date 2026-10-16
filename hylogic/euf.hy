"Ground problems with equality and functions, decided exactly: SAT plus congruence closure.

The theory of equality with uninterpreted functions (EUF) is decidable for
ground formulas: no domain size or bound is needed. hylogic.ground searches
for finite models, which needs a bound on their size; this module needs none.
It is the lazy DPLL(T) scheme that SMT solvers such as Z3 are built on:

1. Every distinct equation s = t becomes a Boolean variable, and a predicate
   atom p(t...) becomes the equation p(t...) = ⊤, so one mechanism covers both.
2. The SAT solver proposes an assignment to these variables.
3. Congruence closure checks it: merge the terms of the true equations, and
   whenever two terms f(a...) and f(b...) have pairwise equal arguments, merge
   them too. If a false equation then has both sides in one class, the
   assignment is inconsistent.
4. The merge history (a proof forest) names the true equations e1..ek
   behind each violated one, and the clause ¬e1 ∨ ... ∨ ¬ek ∨ d (they imply the violated equation d) is learned.
   Back to 2.

If the SAT solver finds no assignment, the clauses are unsatisfiable. If an
assignment passes congruence closure, the equivalence classes form a model.
Each round learns a clause that rules out at least the current assignment,
and there are finitely many, so the loop ends."

(import time
        hylogic.terms [variable? compound? variables-of]
        hylogic.cdcl [Solver _Timeout])

(defn _negative? [l] (and (compound? l) (= (get l 0) "not")))
(defn _atom [l] (if (_negative? l) (get l 1) l))

(setv TRUE "$⊤"
      LEMMAS 256)  ; lemmas learned per round (measured on ALG: 256 beats 16, 64 and all)

(defn _equation [a]
  "An atom as a canonical equation #(s t), or None for a propositional atom."
  (cond
    (and (compound? a) (= (get a 0) "=") (= (len a) 3))
      (do (setv [_ s t] a) (if (<= (repr s) (repr t)) #(s t) #(t s)))
    (compound? a) #(#("$p" #* a) TRUE)
    True None))

(defclass _Closure []
  "Congruence closure that remembers why classes were merged (a proof forest),
  so a merge can be explained by the input equations behind it."
  (defn __init__ [self terms]
    (setv self.parent (dfor t terms t t)
          self.size (dfor t terms t 1)
          self.proof (dfor t terms t None)
          self.uses (dfor t terms t [])
          self.memo {}
          self.table {})
    (for [t terms :if (compound? t)]
      (for [a (cut t 1 None)] (.append (get self.uses a) t))
      (setv (get self.table (._signature self t)) t)))
  (defn _signature [self app]
    #((get app 0) (len app) #* (gfor a (cut app 1 None) (.find self a))))
  (defn find [self t]
    (while (!= (get self.parent t) t)
      (setv (get self.parent t) (get self.parent (get self.parent t))
            t (get self.parent t)))
    t)
  (defn close [self equations]
    "Merge the equations and everything congruence then forces."
    (setv pending (lfor e equations #((get e 0) (get e 1) e)))
    (while pending
      (setv [a b reason] (.pop pending)
            ra (.find self a) rb (.find self b))
      (when (= ra rb) (continue))
      (when (> (get self.size ra) (get self.size rb)) (setv [ra rb] [rb ra] [a b] [b a]))
      ;; the proof forest: a becomes the root of its (smaller) tree, then points to b
      (._reroot self a)
      (setv (get self.proof a) #(b reason))
      (setv (get self.parent ra) rb)
      (+= (get self.size rb) (get self.size ra))
      ;; applications over the smaller class get new signatures
      (for [app (get self.uses ra)]
        (setv sig (._signature self app) other (.get self.table sig))
        (if (is other None)
            (setv (get self.table sig) app)
            (when (!= (.find self other) (.find self app))
              (.append pending #(other app #("$cong" other app))))))
      (.extend (get self.uses rb) (get self.uses ra)))
    self)
  (defn _reroot [self a]
    "Reverse the proof edges from a to the root of its tree."
    (setv prev None x a)
    (while (is-not x None)
      (setv step (get self.proof x)
            (get self.proof x) prev)
      (when (is-not step None)
        (setv prev #(x (get step 1)) x (get step 0)))
      (when (is step None) (setv x None))))
  (defn _path [self a b]
    "The reasons on the proof forest path between a and b."
    (setv above {} x a)
    (while (is-not x None)
      (setv (get above x) True step (get self.proof x) x (if step (get step 0) None)))
    (setv reasons [] x b)
    (while (not-in x above)
      (setv [x reason] (get self.proof x))
      (.append reasons reason))
    (setv common x x a)
    (while (!= x common)
      (setv [x reason] (get self.proof x))
      (.append reasons reason))
    reasons)
  (defn explain [self a b]
    "The input equations that make a and b equal. Explanations are remembered,
    since the lemmas of one round share most of theirs."
    (when (= a b) (return (frozenset)))
    (setv key #(a b))
    (when (in key self.memo) (return (get self.memo key)))
    (setv out #{})
    (for [reason (._path self a b)]
      (if (= (get reason 0) "$cong")
          (for [[x y] (zip (cut (get reason 1) 1 None) (cut (get reason 2) 1 None))]
            (.update out (.explain self x y)))
          (.add out reason)))
    (setv out (frozenset out) (get self.memo key) out)
    out))

(defn _subterms [t out]
  (when (compound? t) (for [a (cut t 1 None)] (_subterms a out)))
  (.add out t))

(defn _decide [clauses deadline max-rounds]
  "#(verdict solver eq-of origins): the verdict of decide-euf, with what a proof needs."
  (when (any (gfor c clauses (variables-of (tuple c)))) (return #(None None None None)))
  (setv var-of {} eq-of {} cnf [] origins [] terms #{TRUE})
  (defn var [key]
    (when (not-in key var-of)
      (setv (get var-of key) (+ (len var-of) 1) (get eq-of (get var-of key)) key))
    (get var-of key))
  (for [c clauses]
    (setv row [] satisfied False)
    (for [l c]
      (setv a (_atom l) neg (_negative? l))
      (cond
        (= a "true") (if neg None (setv satisfied True))
        (= a "false") (if neg (setv satisfied True) None)
        True
          (do
            (setv e (_equation a))
            (if (is e None)
                (.append row (if neg (- (var #("prop" a))) (var #("prop" a))))
                (if (= (get e 0) (get e 1))
                    (if neg None (setv satisfied True))
                    (do
                      (_subterms (get e 0) terms) (_subterms (get e 1) terms)
                      (.append row (if neg (- (var e)) (var e)))))))))
    (when satisfied (continue))
    (.append cnf row)
    (.append origins c))
  ;; TPTP distinct objects such as "abc" denote pairwise different elements
  (setv objects (sorted (gfor t terms :if (and (isinstance t str) (.startswith t "\"")) t)))
  (for [[i s] (enumerate objects)  t (cut objects (+ i 1) None)]
    (.append cnf [(- (var (_equation #("=" s t))))])
    (.append origins None))
  (setv terms (list terms))
  (setv solver (Solver cnf deadline))
  (for [_ (range max-rounds)]
    (setv model (try (.solve solver) (except [_Timeout] (return #(None None None None)))))
    (when (is model None) (return #("proved" solver eq-of origins)))
    (setv trues [] falses [])
    (for [[v key] (.items eq-of)]
      (when (!= (get key 0) "prop")
        (.append (if (.get model v False) trues falses) key)))
    (setv cc (.close (_Closure terms) trues)
          violated (lfor d falses :if (= (.find cc (get d 0)) (.find cc (get d 1))) d))
    (when (not violated) (return #("saturated" None None None)))
    (when (and deadline (> (time.monotonic) deadline)) (return #(None None None None)))
    ;; every violated equation gives a lemma: its explanation implies it
    (for [d (cut violated 0 LEMMAS)]
      (.add solver [#* (gfor e (.explain cc #* d) (- (get var-of e))) (get var-of d)]
            #("lemma" None))))
  #(None None None None))

(defn decide-euf [clauses [deadline None] [max-rounds 100000]]
  "proved (unsatisfiable), saturated (a model exists) or None (not ground, or out of time)."
  (get (_decide clauses deadline max-rounds) 0))

(defn _literal [n eq-of]
  "SAT literal n as a formula literal: an equation, a predicate atom or a proposition."
  (setv key (get eq-of (abs n)))
  (setv atom (cond
               (= (get key 0) "prop") (get key 1)
               (= (get key 1) TRUE) (tuple (cut (get key 0) 1 None))
               True #("=" #* key)))
  (if (< n 0) #("not" atom) atom))

(defn decide-euf-with-proof [clauses [goal-clauses #()] [deadline None] [max-rounds 100000]]
  "#(verdict result): decide-euf's verdict, and for proved the refutation below."
  (setv decided (_decide clauses deadline max-rounds) verdict (get decided 0))
  #(verdict (when (= verdict "proved") (_proof decided goal-clauses))))

(defn euf-refutation [clauses [goal-clauses #()] [deadline None] [max-rounds 100000]]
  "A readable refutation of unsatisfiable ground clauses, as a hylogic.resolution
  Result: the SAT solver's resolution steps (see hylogic.cdcl.refutation) over
  the input clauses and the equality lemmas congruence closure supplied. A lemma
  ¬e1 ∨ ... ∨ ¬ek ∨ d says that the equations e1..ek imply d, which holds in
  every interpretation of = and the functions. None if not proved in time."
  (get (decide-euf-with-proof clauses goal-clauses deadline max-rounds) 1))

(defn _proof [decided goal-clauses]
  (import hylogic.resolution [Clause Result]
          hylogic.cdcl [refutation])
  (setv [verdict solver eq-of origins] decided
        [steps root] (refutation solver) made {})
  (defn node [k]
    (when (in k made) (return (get made k)))
    (setv [lits parents] (get steps k) atoms (lfor n lits (_literal n eq-of)))
    (if (= (len parents) 1)
        (do
          (setv origin (get parents 0))
          (setv c (cond
                    (= (get origin 0) "lemma") (Clause atoms #() "equality lemma")
                    (is (get origins (get origin 1)) None) (Clause atoms #() "distinct objects")
                    True (do
                           (setv source (get origins (get origin 1))
                                 rule (if (in source goal-clauses) "negated goal" "axiom"))
                           (if (= (frozenset atoms) (frozenset source))
                               (Clause source #() rule)
                               (Clause atoms #((Clause source #() rule)) "simplified"))))))
        (setv c (Clause atoms (tuple (gfor p parents (node p))) "resolve")))
    (setv (get made k) c)
    c)
  (for [k (sorted steps)] (node k))
  (Result "proved" (node root) {"kept" 0 "generated" 0}))
