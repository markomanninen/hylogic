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
        hylogic.terms [term variable? compound? show size variables-of]
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

(defn _free-names [f [bound #()]]
  "The names occurring free in a formula: in its atoms, outside quantifiers binding them."
  (setv out #{})
  (defn walk [t bound]
    (cond
      (compound? t) (for [x (args t)] (walk x bound))
      (and (isinstance t str) (not-in t bound)) (.add out t)))
  (defn visit [g bound]
    (setv op (if (connective? g) (get g 0) None))
    (cond
      (in op QUANTIFIERS) (visit (get g 2) #(#* bound #* (get g 1)))
      (is op None) (walk g bound)
      True (for [a (args g)] (visit a bound))))
  (visit f bound)
  out)

(defn skolemize [f [env None] [universals #()] [keep-forall False]]
  "Give each universal variable a fresh clause variable (?x1, ...), replace each
  existential one by a Skolem term over the universals it depends on, and drop the
  quantifiers. The formula must be in negation normal form. keep-forall keeps
  the universal quantifiers, over the new names, to mark their scope."
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
            ;; a Skolem term needs only the universals free under its quantifier
            ;; (inner Skolemization): fewer arguments, smaller terms and models
            (setv used (_free-names f)
                  ;; through outer Skolem terms too: their universals count
                  reached (sfor [name t] (.items env) :if (in name used) u (variables-of t) u)
                  deps (tuple (gfor u universals :if (in u reached) u))
                  (get env v) (if deps #(f"sk{n}" #* deps) f"sk{n}"))))
      (setv body (skolemize (get f 2) env universals keep-forall))
      (if (and keep-forall (= op "forall"))
          #("forall" (tuple (gfor v (get f 1) (get env v))) body)
          body))
    (is op None) (if (compound? f) #((get f 0) #* (gfor x (args f) (_replace-bound x env))) f)
    True #(op #* (gfor a (args f) (skolemize a env universals keep-forall)))))

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
    (= op "forall") (cnf-clauses (get f 2) definitions max-product)
    (= op "and") (lfor a (args f) c (cnf-clauses a definitions max-product) c)
    (= op "or") (do
      (setv parts (lfor a (args f) (cnf-clauses a definitions max-product)))
      (when (is-not definitions None)
        (setv product 1)
        (for [p parts] (*= product (len p)))
        (when (> product max-product)
          (setv parts
            (lfor [a p] (zip (args f) parts)
              (if (> (len p) 1)
                  (do
                    ;; the name takes the part's free variables: those bound inside it
                    ;; (marked by kept universal quantifiers) stay universal in its clauses
                    (setv inside (_bound-inside a)
                          atom #(f"$def{(next DEFINITIONS)}"
                                 #* (gfor v (variables-of (tuple (gfor c p l c l))) :if (not-in v inside) v)))
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

(defn _bound-inside [f]
  "The variables bound by universal quantifiers kept inside f."
  (setv out #{})
  (defn visit [g]
    (when (connective? g)
      (when (= (get g 0) "forall") (.update out (get g 1)))
      (for [a (if (in (get g 0) QUANTIFIERS) [(get g 2)] (args g))] (visit a))))
  (visit f)
  out)

(defn clausify [formula [definitional False]]
  "A formula (quoted Hy form or term) as a list of clauses, each a frozenset of literals.
  definitional names subformulas instead of distributing them (see cnf-clauses)."
  (clauses-of (skolemize (nnf (eliminate-implications (basic formula))) :keep-forall True)
              definitional))

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
  (defn __init__ [self literals [parents #()] [rule "axiom"] [source None]]
    (setv self.literals (frozenset literals)
          self.source source
          self.parents parents
          self.rule rule
          self.rules-seen 0
          self.units-seen 0
          self.used []
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

(defn subsumes? [c d [budget 2000]]
  "Does clause c subsume d, that is, does some substitution map every literal of c into d?
  Then d says nothing that c does not, and d can be dropped.

  Finding the substitution can take exponentially many tries on long clauses
  of similar literals, so each literal first gets the literals of d it matches
  on its own, the most constrained go first, and after budget tries the answer
  is no: keeping a clause that could have been dropped is always safe."
  (when (> (len c) (len d)) (return False))
  (setv options [])
  (for [l c]
    (setv fits (lfor m d :if (is-not (match-term l m) None) m))
    (when (not fits) (return False))
    (.append options #(l fits)))
  (.sort options :key (fn [o] (len (get o 1))))
  (setv tries [budget])
  (_subsumes options {} tries))

(defn _subsumes [options s tries]
  (when (not options) (return True))
  (setv [[head fits] #* rest] options)
  (for [m fits]
    (-= (get tries 0) 1)
    (when (< (get tries 0) 0) (return False))
    (setv s2 (match-term head m s))
    (when (and (is-not s2 None) (_subsumes rest s2 tries))
      (return True)))
  False)

(defn features [lits]
  "The sign and predicate of each literal: a clause can subsume another only if its
  features are a subset of the other's, and resolve with it only if they share a
  predicate with opposite signs. Checking this first skips most futile work."
  (frozenset (gfor l lits #((negative? l) (_predicate (atom-of l))))))

(defn symbols [lits]
  "The constants and function symbols of a clause. Matching only instantiates
  variables, so a clause can subsume another only if its symbols occur there too."
  (setv found #{})
  (defn walk [t]
    (cond
      (variable? t) None
      (compound? t) (do (.add found #((get t 0) (- (len t) 1))) (for [a (cut t 1 None)] (walk a)))
      True (.add found #(t 0))))
  (for [l lits  :setv a (atom-of l)]
    (when (compound? a) (for [x (cut a 1 None)] (walk x))))
  (frozenset found))

(defn _predicate [atom] (if (compound? atom) (get atom 0) atom))

(defn _unit-key [sign atom [pattern False]]
  "Where unit deletion files a unit atom, or looks for units matching an atom:
  sign, predicate and the head of the first argument. A unit whose first
  argument is a variable can match anything, so it is filed under *."
  (setv first (when (and (compound? atom) (> (len atom) 1)) (get atom 1)))
  #(sign (_predicate atom)
    (cond (is first None) "-"
          (and pattern (variable? first)) "*"
          (variable? first) "?"
          (compound? first) #((get first 0) (len first))
          True first)))

(defn eligible [lits]
  "The literals of a clause that ordered resolution may resolve on.
  If the clause has negative literals, only the heaviest of them is selected;
  otherwise its maximal literals in the Knuth-Bendix ordering of their atoms.
  Resolving only on these literals keeps resolution complete while cutting most
  inferences (Bachmair and Ganzinger, 1994)."
  (setv negs (lfor l lits :if (negative? l) l))
  (if negs
      #{(max negs :key (fn [l] #((size l) (show (_mask l)) (show l))))}
      (set (gfor l lits :if (not (any (gfor m lits (sp.kbo> (atom-of m) (atom-of l))))) l))))

(defn resolvents [c1 c2 [ordered False]]
  "All binary resolvents of two clauses, c2 renamed apart first.
  With ordered, only eligible literals are resolved on."
  ;; eligibility is decided before renaming: selection must not depend on
  ;; variable names, or the same clause could select different literals
  ;; at different times, and ordered resolution would lose completeness
  (setv mapping {}
        e1 (if ordered (eligible c1) c1)
        e2 (frozenset (gfor l (if ordered (eligible c2) c2) (rename l mapping)))
        l2 (frozenset (gfor l c2 (rename l mapping))))
  ;; sorted, so that every run takes the same path whatever the hash seed
  (for [a (sorted e1 :key show)  b (sorted e2 :key show)]
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
  (defn premises-used [self]
    "The positions of the axioms the proof starts from, in order: what the
    conclusion depends on. Empty when the negated goal alone is contradictory."
    (when (or (not self.proved) (is self.clause None)) (return []))
    (setv seen #{} found #{} todo [self.clause])
    (while todo
      (setv c (.pop todo))
      (when (in (id c) seen) (continue))
      (.add seen (id c))
      (when (is-not (getattr c "source" None) None) (.add found c.source))
      (.extend todo [#* c.parents #* (getattr c "used" [])]))
    (sorted found))
  (defn proof [self]
    "The proof as numbered lines, from input clauses to the empty clause."
    (when (or (not self.proved) (is self.clause None)) (return []))
    ;; numbered in the order a depth-first walk finishes the clauses, so every
    ;; clause comes after the ones it was derived from
    (setv order [] number {})
    (defn visit [c]
      (when (not-in (id c) number)
        (setv (get number (id c)) None)
        (for [p [#* c.parents #* c.used]] (visit p))
        (.append order c)
        (setv (get number (id c)) (len order))))
    (visit self.clause)
    (lfor c order
      (+ (.rjust (str (get number (id c))) 4) ". " (.ljust (str c) 44) " "
         (if (or c.parents c.used)
             (+ c.rule " " (.join ", " (gfor p [#* c.parents #* c.used] (str (get number (id p))))))
             c.rule)))))

(defn saturate [clauses [limit 5000] [timeout None] [age-ratio 0] [superposition 0]
                [ordered 0] [index 0] [goal-bias 0]]
  "The given-clause loop. clauses are Clause objects. Stops after timeout seconds if given.

  The next clause to process is the lightest one, except that with age-ratio n
  every (n+1)th pick is the oldest unprocessed clause instead. Picking only by
  weight can postpone a heavy clause forever; mixing in age makes the search
  fair, so every clause is eventually processed.

  With superposition, equality is built in: new clauses are rewritten with the
  unit equations processed so far, and superposition, equality resolution and
  equality factoring run alongside resolution (see hylogic.superposition).

  ordered restricts resolution to eligible literals (see eligible), and index
  filters subsumption checks and resolution partners by features first.

  With goal-bias b, a clause that does not descend from the negated goal weighs
  b/2 times its size when picking by weight (b = 2: no bias; b = 3: 1.5 times),
  so the search stays near the goal, as in the set-of-support strategy."
  (setv deadline (when timeout (+ (time.monotonic) timeout))
        ids (count 1)
        tie (count)
        processed []
        queue []
        by-age []
        picks 0
        seen #{}
        rules (sp.RuleIndex)
        rule-source {}
        units {}
        unit-count 0
        stats {"kept" 0 "generated" 0})

  (defn cut-units [lits]
    "The literals without those a processed unit clause refutes (unit deletion):
    a unit ¬A removes every literal that is an instance of A, and a unit A every
    instance of ¬A. #(literals changed?)."
    (when (not units) (return #(lits False [])))
    (setv out [] used [])
    (for [l lits]
      (setv a (atom-of l) sign (not (negative? l))
            hit (next (gfor key [(_unit-key sign a) #(sign (_predicate a) "*")]
                            [u source] (.get units key [])
                            :if (is-not (match-term u a) None) source)
                      None))
      (if (is hit None) (.append out l) (.append used hit)))
    #((frozenset out) (bool used) used))

  (defn rewrite [lits]
    "The literals rewritten with the rules: #(literals changed? clauses used)."
    (setv fired [] [lits changed] (sp.demodulate lits rules :fired fired))
    #(lits changed (lfor r (dict.fromkeys fired) (get rule-source r))))

  (defn pick []
    "The next unprocessed clause, by weight or, every (age-ratio + 1)th time, by age.
    With superposition it is first rewritten with the rules found since it was kept."
    (nonlocal picks)
    (+= picks 1)
    (setv heap (if (and age-ratio (= (% picks (+ age-ratio 1)) 0)) by-age queue))
    (for [h [heap queue by-age]]
      (while h
        (setv c (get (heapq.heappop h) 2))
        (when (not c.done)
          (setv c.done True)
          (when (or (and superposition (< c.rules-seen (len rules))) (< c.units-seen unit-count))
            (setv [lits changed used] (if superposition (rewrite c.literals) #(c.literals False []))
                  [lits cut used2] (cut-units lits)
                  changed (or changed cut))
            (when changed
              (setv lits (sp.drop-false-equations lits))
              (when (sp.trivial? lits) (continue))
              (setv c (Clause lits #(c) "simplification")
                    c.used [#* used #* used2]
                    c.id (next ids) c.done True
                    c.goal (getattr (get c.parents 0) "goal" False)
                    c.features (features lits) c.symbols (symbols lits))))
          (return c))))
    None)

  (defn add [clause]
    "Keep a new clause unless it is a tautology, a duplicate or subsumed."
    (when superposition
      (setv [lits changed used] (rewrite (sp.drop-false-equations clause.literals)))
      (when (sp.trivial? lits) (return None))
      (when changed (setv clause.rule (+ clause.rule "+demod") clause.used [#* clause.used #* used]))
      (setv clause.literals lits
            clause.rules-seen (len rules)))
    (setv [lits cut used] (cut-units clause.literals)
          clause.units-seen unit-count)
    (when cut (setv clause.literals lits clause.rule (+ clause.rule "+unit deletion")
                    clause.used [#* clause.used #* used]))
    (when (tautology? lits) (return None))
    (setv key (canonical lits))
    (when (in key seen) (return None))
    (.add seen key)
    (setv clause.features (features lits)
          clause.symbols (symbols lits))
    (when (any (gfor p processed (and (or (not index) (and (<= p.features clause.features)
                                                           (<= p.symbols clause.symbols)))
                                      (subsumes? p.literals lits))))
      (return None))
    (setv clause.id (next ids)
          clause.done False
          clause.goal (or (= clause.rule "negated goal") (any (gfor p clause.parents (getattr p "goal" False)))))
    (+= (get stats "kept") 1)
    (heapq.heappush queue #((if (and goal-bias (not clause.goal)) (* (weight lits) (/ goal-bias 2)) (weight lits))
                            (next tie) clause))
    (when age-ratio (heapq.heappush by-age #(clause.id 0 clause)))
    clause)

  (defn inferences [given processed]
    "Every clause derived from the given clause and the processed ones."
    (for [lits (factors given.literals)]
      (yield #(lits #(given) "factor")))
    (setv partners (frozenset (gfor [neg pred] given.features #((not neg) pred))))
    (for [other processed]
      (when (or (not index) (& partners other.features))
        (for [lits (resolvents given.literals other.literals ordered)]
          (yield #(lits #(given other) "resolve")))))
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
    (when (not given.literals) (return (Result "proved" given stats)))
    (when (any (gfor p processed (and (or (not index) (and (<= p.features given.features)
                                                           (<= p.symbols given.symbols)))
                                      (subsumes? p.literals given.literals))))
      (continue))
    ;; drop processed clauses that the given clause makes redundant
    (setv processed (lfor p processed
                          :if (not (and (or (not index) (and (<= given.features p.features)
                                                             (<= given.symbols p.symbols)))
                                        (subsumes? given.literals p.literals)))
                          p))
    (.append processed given)
    (when (= (len given.literals) 1)
      (setv [lit] given.literals)
      (.append (.setdefault units (_unit-key (negative? lit) (atom-of lit) True) [])
               #((atom-of lit) given))
      (+= unit-count 1))
    ;; a processed unit equation becomes rewrite rules, which also rewrite the
    ;; processed clauses (backward demodulation): a rewritten one is taken out
    ;; and comes back as a new clause
    (when (and superposition (= (len given.literals) 1))
      (setv [lit] given.literals)
      (when (and (sp.equation? lit) (not (sp.negative? lit)))
        (setv new-rules (sp.rules-of lit))
        (.extend rules new-rules)
        (for [r new-rules] (.setdefault rule-source r given))
        (when new-rules
          (setv kept [] rewritten [])
          (for [p processed]
            (setv [lits changed] (if (is p given) #(None False) (sp.demodulate p.literals new-rules)))
            (if changed (.append rewritten #(p lits)) (.append kept p)))
          (setv processed kept)
          (for [[p lits] rewritten]
            (setv new (add (Clause lits #(p given) "demodulation")))
            (when (and new (not new.literals))
              (return (Result "proved" new stats)))))))
    (for [[lits parents rule] (inferences given processed)]
      (+= (get stats "generated") 1)
      (when (and deadline (> (time.monotonic) deadline))
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
  ;; every input clause remembers which axiom it came from (see premises-used)
  (for [[i a] (enumerate axioms)  lits (clausify a definitional)]
    (.append clauses (Clause lits :source i)))
  (for [lits (clausify #("not" (basic goal)) definitional)]
    (.append clauses (Clause lits :rule "negated goal")))
  (saturate clauses limit timeout #** options))
