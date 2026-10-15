"Resolution theorem proving for first-order logic.

Formulas are quoted Hy forms, with logical symbols (¬ ∧ ∨ → ↔ ∀ ∃ and the other
connectives) or their ASCII names:

  (Man socrates)                       an atom
  (not A)  (and A B ...)  (or A B ...)  (=> A B)  (<=> A B)
  (forall [x y] A)  (exists [x] A)     quantifiers; x is a bound variable

To prove a goal from axioms, the prover adds the goal's negation and looks for
a contradiction (refutation):

1. Each formula is turned into clauses, disjunctions of literals, by
   `clausify`: remove => and <=>, push negations inward, replace existential
   variables with Skolem functions, drop the universal quantifiers, and
   distribute or over and.
2. Resolution: from (A or C) and (not A' or D), where A and A' unify with
   substitution s, derive (C or D)s. Factoring merges two unifiable literals
   of one clause.
3. Deriving the empty clause, a disjunction of nothing, means the axioms and
   the negated goal contradict each other, so the goal follows.

The search is the given-clause loop that real provers use: pick the smallest
unprocessed clause, resolve it against everything processed so far, keep the
new clauses that are neither duplicates nor subsumed by older ones."

(import heapq
        time
        hylogic.superposition :as sp
        itertools [count]
        hylogic.formulas [basic]
        hylogic.terms [term compound? show size variables-of]
        hylogic.unify [unify substitute match-term rename FRESH])

(setv QUANTIFIERS #{"forall" "exists"}
      CONNECTIVES #{"not" "and" "or" "=>" "<=>"})

(defn connective? [f]
  (and (compound? f) (in (get f 0) (| QUANTIFIERS CONNECTIVES))))

(defn args [f] (cut f 1 None))

;; Clausal form, one step per function

(defn eliminate-implications [f]
  "Rewrite (=> A B) as (or (not A) B), and (<=> A B) as two implications."
  (when (not (connective? f)) (return f))
  (setv op (get f 0))
  (when (in op QUANTIFIERS)
    (return #(op (get f 1) (eliminate-implications (get f 2)))))
  (setv xs (lfor a (args f) (eliminate-implications a)))
  (cond
    (= op "=>") #("or" #("not" (get xs 0)) (get xs 1))
    (= op "<=>") (do
      (setv [a b] xs)
      #("and" #("or" #("not" a) b) #("or" #("not" b) a)))
    True #(op #* xs)))

(defn nnf [f]
  "Negation normal form: push every not down to an atom (De Morgan, quantifier duality)."
  (when (not (connective? f)) (return f))
  (setv op (get f 0))
  (cond
    (= op "not") (do
      (setv g (get f 1))
      (when (not (connective? g)) (return f))
      (setv gop (get g 0))
      (cond
        (= gop "not") (nnf (get g 1))
        (= gop "and") #("or" #* (gfor a (args g) (nnf #("not" a))))
        (= gop "or") #("and" #* (gfor a (args g) (nnf #("not" a))))
        (= gop "forall") #("exists" (get g 1) (nnf #("not" (get g 2))))
        (= gop "exists") #("forall" (get g 1) (nnf #("not" (get g 2))))
        True (raise (ValueError f"nnf: unexpected {(show g)}; eliminate implications first"))))
    (in op QUANTIFIERS) #(op (get f 1) (nnf (get f 2)))
    True #(op #* (gfor a (args f) (nnf a)))))

(defn _replace-bound [t env]
  "Replace bound variable names in a term by their clause variables or Skolem terms."
  (cond
    (compound? t) #((get t 0) #* (gfor x (args t) (_replace-bound x env)))
    (in t env) (get env t)
    True t))

(defn skolemize [f [env None] [universals #()]]
  "Give each universal variable a fresh clause variable (?x1, ...), replace each
  existential one by a Skolem term over the universals in scope, and drop the
  quantifiers. The formula must be in negation normal form."
  (when (is env None) (setv env {}))
  (setv op (if (connective? f) (get f 0) None))
  (cond
    (in op QUANTIFIERS) (do
      (setv env (dict env))
      (for [v (get f 1)]
        (setv n (next FRESH))
        (if (= op "forall")
            (setv (get env v) f"?{v}{n}"
                  universals #(#* universals (get env v)))
            (setv (get env v) (if universals #(f"sk{n}" #* universals) f"sk{n}"))))
      (skolemize (get f 2) env universals))
    (is op None) (if (compound? f) #((get f 0) #* (gfor x (args f) (_replace-bound x env))) f)
    True #(op #* (gfor a (args f) (skolemize a env universals)))))

(setv DEFINITIONS (count 1))

(defn cnf-clauses [f [definitions None] [max-product 8]]
  "Clauses (lists of literals) of a quantifier-free formula in negation normal form,
  by distributing or over and. This can grow exponentially.

  With a definitions list, a disjunction whose distribution would make more than
  max-product clauses gets its multi-clause parts named instead: a part C becomes a
  new atom d(x...) over C's variables, and the clauses (not d(x...)) | c for each
  clause c of C go to definitions. Since the formula is in negation normal form,
  d occurs only positively, so this one direction is enough (Plaisted and
  Greenbaum, 1986), and the clause set grows linearly."
  (setv op (if (connective? f) (get f 0) None))
  (cond
    (= op "and") (lfor a (args f) c (cnf-clauses a definitions max-product) c)
    (= op "or") (do
      (setv parts (lfor a (args f) (cnf-clauses a definitions max-product)))
      (when (is-not definitions None)
        (setv product 1)
        (for [p parts] (*= product (len p)))
        (when (> product max-product)
          (setv parts
            (lfor p parts
              (if (> (len p) 1)
                  (do
                    (setv atom #(f"$def{(next DEFINITIONS)}" #* (variables-of (tuple (gfor c p l c l)))))
                    (for [c p] (.append definitions [#("not" atom) #* c]))
                    [[atom]])
                  p)))))
      (setv result [[]])
      (for [p parts]
        (setv result (lfor c1 result c2 p (+ c1 c2))))
      result)
    True [[f]]))

(defn negative? [lit] (and (compound? lit) (= (get lit 0) "not")))
(defn atom-of [lit] (if (negative? lit) (get lit 1) lit))
(defn complement [lit] (if (negative? lit) (get lit 1) #("not" lit)))

(defn tautology? [lits]
  (any (gfor l lits (in (complement l) lits))))

(defn clausify [formula [definitional False]]
  "A formula (quoted Hy form or term) as a list of clauses, each a frozenset of literals.
  definitional names subformulas instead of distributing them (see cnf-clauses)."
  (clauses-of (skolemize (nnf (eliminate-implications (basic formula)))) definitional))

(defn clauses-of [f [definitional False]]
  "Clauses of a Skolemized formula, without tautologies and duplicates."
  (setv clauses []
        definitions (when definitional []))
  ;; definitional is off (False or 0), on (True: name above 8 clauses) or the threshold itself
  (setv max-product (if (and (isinstance definitional int) (> definitional 1)) definitional 8)
        clauses-f (cnf-clauses f definitions max-product))
  (for [c (+ clauses-f (or definitions []))]
    ;; ⊤ makes a clause always true; ⊥ adds nothing to it
    (when (any (gfor l c (in l #{"true" #("not" "false")}))) (continue))
    (setv c (frozenset (gfor l c :if (not-in l #{"false" #("not" "true")}) l)))
    (when (and (not (tautology? c)) (not-in c clauses))
      (.append clauses c)))
  clauses)

(defn clausify-steps [formula]
  "Each intermediate form of clausify, for study."
  (setv f (basic formula)
        a (eliminate-implications f)
        b (nnf a)
        c (skolemize b))
  [#("formula" (show f))
   #("without => and <=>" (show a))
   #("negation normal form" (show b))
   #("Skolemized, quantifiers dropped" (show c))
   #("clauses" (lfor cl (clauses-of c) (clause-text cl)))])

;; Clauses and the search

(defn clause-text [lits]
  (if lits (.join " | " (sorted (map show lits))) "□"))

(defclass Clause []
  (defn __init__ [self literals [parents #()] [rule "axiom"]]
    (setv self.literals (frozenset literals)
          self.parents parents
          self.rule rule
          self.id None))
  (defn __str__ [self] (clause-text self.literals)))

(defn weight [lits] (sum (gfor l lits (size l))))

(defn _mask [t]
  (cond (and (isinstance t str) (.startswith t "?")) "?"
        (compound? t) (tuple (map _mask t))
        True t))

(defn canonical [lits]
  "The clause with its variables renamed in a fixed order, to spot duplicates."
  (setv ordered (sorted lits :key (fn [l] #((show (_mask l)) (show l))))
        mapping {})
  (for [v (variables-of (tuple ordered))]
    (setv (get mapping v) f"?v{(len mapping)}"))
  (frozenset (gfor l lits (substitute l mapping))))

(defn subsumes? [c d]
  "Does clause c subsume d, that is, does some substitution map every literal of c into d?
  Then d says nothing that c does not, and d can be dropped."
  (and (<= (len c) (len d))
       (_subsumes (sorted c :key size :reverse True) d {})))

(defn _subsumes [lits d s]
  (when (not lits) (return True))
  (setv [head #* rest] lits)
  (for [l d]
    (setv s2 (match-term head l s))
    (when (and (is-not s2 None) (_subsumes rest d s2))
      (return True)))
  False)

(defn resolvents [c1 c2]
  "All binary resolvents of two clauses, c2 renamed apart first."
  (setv mapping {}
        l2 (frozenset (gfor l c2 (rename l mapping))))
  ;; sorted, so that every run takes the same path whatever the hash seed
  (for [a (sorted c1 :key show)  b (sorted l2 :key show)]
    (when (!= (negative? a) (negative? b))
      (setv s (unify (atom-of a) (atom-of b)))
      (when (is-not s None)
        (yield (frozenset (gfor l (| (- c1 #{a}) (- l2 #{b})) (substitute l s))))))))

(defn factors [c]
  "Clauses made by unifying two literals of the same sign in c."
  (setv lits (sorted c :key show))
  (for [i (range (len lits)) j (range (+ i 1) (len lits))]
    (setv a (get lits i) b (get lits j))
    (when (= (negative? a) (negative? b))
      (setv s (unify (atom-of a) (atom-of b)))
      (when (is-not s None)
        (yield (frozenset (gfor l lits (substitute l s))))))))

(defclass Result []
  "What a proof attempt found. status is proved, saturated (no contradiction exists,
  so the goal does not follow) or gave-up (the clause limit was reached)."
  (defn __init__ [self status clause stats]
    (setv self.status status self.clause clause self.stats stats))
  (defn [property] proved [self] (= self.status "proved"))
  (defn proof [self]
    "The proof as numbered lines, from input clauses to the empty clause."
    (when (not self.proved) (return []))
    (setv order [] seen #{})
    (defn visit [c]
      (when (not-in c.id seen)
        (.add seen c.id)
        (for [p c.parents] (visit p))
        (.append order c)))
    (visit self.clause)
    ;; a parent always has a smaller number than its child, so this order is valid
    (lfor c (sorted order :key (fn [c] c.id))
      (+ (.rjust (str c.id) 4) ". " (.ljust (str c) 44) " "
         (if c.parents
             (+ c.rule " " (.join ", " (gfor p c.parents (str p.id))))
             c.rule)))))

(defn saturate [clauses [limit 5000] [timeout None] [age-ratio 0] [superposition 0]]
  "The given-clause loop. clauses are Clause objects. Stops after timeout seconds if given.

  The next clause to process is the lightest one, except that with age-ratio n
  every (n+1)th pick is the oldest unprocessed clause instead. Picking only by
  weight can postpone a heavy clause forever; mixing in age makes the search
  fair, so every clause is eventually processed.

  With superposition, equality is built in: new clauses are rewritten with the
  unit equations processed so far, and superposition, equality resolution and
  equality factoring run alongside resolution (see hylogic.superposition)."
  (setv deadline (when timeout (+ (time.monotonic) timeout))
        ids (count 1)
        tie (count)
        processed []
        queue []
        by-age []
        picks 0
        seen #{}
        rules []
        stats {"kept" 0 "generated" 0})

  (defn pick []
    "The next unprocessed clause, by weight or, every (age-ratio + 1)th time, by age."
    (nonlocal picks)
    (+= picks 1)
    (setv heap (if (and age-ratio (= (% picks (+ age-ratio 1)) 0)) by-age queue))
    (for [h [heap queue by-age]]
      (while h
        (setv c (get (heapq.heappop h) 2))
        (when (not c.done)
          (setv c.done True)
          (return c))))
    None)

  (defn add [clause]
    "Keep a new clause unless it is a tautology, a duplicate or subsumed."
    (when superposition
      (setv [lits changed] (sp.demodulate (sp.drop-false-equations clause.literals) rules))
      (when (sp.trivial? lits) (return None))
      (when changed (setv clause.rule (+ clause.rule "+demod")))
      (setv clause.literals lits))
    (setv lits clause.literals)
    (when (tautology? lits) (return None))
    (setv key (canonical lits))
    (when (in key seen) (return None))
    (.add seen key)
    (when (any (gfor p processed (subsumes? p.literals lits))) (return None))
    (setv clause.id (next ids)
          clause.done False)
    (+= (get stats "kept") 1)
    (heapq.heappush queue #((weight lits) (next tie) clause))
    (when age-ratio (heapq.heappush by-age #(clause.id 0 clause)))
    clause)

  (defn inferences [given processed]
    "Every clause derived from the given clause and the processed ones."
    (for [lits (factors given.literals)]
      (yield #(lits #(given) "factor")))
    (for [other processed  lits (resolvents given.literals other.literals)]
      (yield #(lits #(given other) "resolve")))
    (when superposition
      (for [lits (sp.equality-resolvents given.literals)]
        (yield #(lits #(given) "equality resolution")))
      (for [lits (sp.equality-factors given.literals)]
        (yield #(lits #(given) "equality factoring")))
      (for [other processed]
        (for [lits (sp.superpositions given.literals other.literals)]
          (yield #(lits #(given other) "superposition")))
        (when (is-not other given)
          (for [lits (sp.superpositions other.literals given.literals)]
            (yield #(lits #(other given) "superposition")))))))

  (for [c clauses]
    (add c)
    (when (not c.literals) (return (Result "proved" c stats))))
  (while True
    (setv given (pick))
    (when (is given None) (break))
    (when (any (gfor p processed (subsumes? p.literals given.literals)))
      (continue))
    ;; drop processed clauses that the given clause makes redundant
    (setv processed (lfor p processed :if (not (subsumes? given.literals p.literals)) p))
    (.append processed given)
    ;; a processed unit equation that can be oriented becomes a rewrite rule
    (when (and superposition (= (len given.literals) 1))
      (setv [lit] given.literals)
      (when (and (sp.equation? lit) (not (sp.negative? lit)))
        (setv rule (sp.orient lit))
        (when rule (.append rules rule))))
    (for [[lits parents rule] (inferences given processed)]
      (+= (get stats "generated") 1)
      (when (and deadline (= (% (get stats "generated") 256) 0) (> (time.monotonic) deadline))
        (return (Result "timeout" None stats)))
      (setv new (add (Clause lits parents rule)))
      (when (and new (not new.literals))
        (return (Result "proved" new stats))))
    (when (> (get stats "kept") limit)
      (return (Result "gave-up" None stats)))
    (when (and deadline (> (time.monotonic) deadline))
      (return (Result "timeout" None stats))))
  (Result "saturated" None stats))

(defn prove [goal [axioms #()] [limit 5000] [timeout None] [definitional False] #** options]
  "Try to prove goal from axioms: refute the axioms together with the negated goal."
  (setv clauses [])
  (for [a axioms  lits (clausify a definitional)]
    (.append clauses (Clause lits)))
  (for [lits (clausify #("not" (basic goal)) definitional)]
    (.append clauses (Clause lits :rule "negated goal")))
  (saturate clauses limit timeout #** options))
