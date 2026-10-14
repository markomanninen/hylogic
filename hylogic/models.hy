"Finding finite models, and countermodels for invalid arguments.

Resolution can show that a goal follows, but when it does not, the search
may end without a contradiction or run out of time, and either way it does
not say why. A countermodel says why: a small world where every premise is
true and the goal is false.

`find-model` looks for one by grounding. For a domain of n elements it fixes
what each constant and function means, replaces ∀ with a conjunction and ∃
with a disjunction over the elements, and hands the resulting propositional
formula to the SAT solver, whose answer says which predicate facts hold.
This is the idea behind model finders such as MACE and Paradox, here only
for small domains.

  (countermodel ['(∀ [x] (→ (Man x) (Mortal x))) '(Mortal fido)] '(Man fido))"

(import itertools [product]
        hylogic.formulas [basic operator-of args-of QUANTIFIERS]
        hylogic.export [signature]
        hylogic.sat [satisfiable]
        hylogic.terms [compound?])

(defn _element [i] f"d{(+ i 1)}")

(defclass Model []
  "A finite interpretation: domain, constants, functions and the predicate facts that hold."
  (defn __init__ [self domain constants functions facts propositions]
    (setv self.domain domain
          self.constants constants
          self.functions functions
          self.facts facts
          self.propositions propositions))
  (defn __str__ [self]
    (setv lines [(+ "Domain: " (.join ", " self.domain))])
    (for [[c d] (sorted (.items self.constants))]
      (.append lines f"  {c} = {d}"))
    (for [[name table] (sorted (.items self.functions))  [args value] (sorted (.items table))]
      (setv shown-args (.join ", " args))
      (.append lines f"  {name}({shown-args}) = {value}"))
    (for [[p v] (sorted (.items self.propositions))]
      (setv truth (if v "true" "false"))
      (.append lines f"  {p} is {truth}"))
    (for [[name tuples] (sorted (.items self.facts))]
      (setv shown (or (.join ", " (gfor t (sorted tuples) (+ "(" (.join " " t) ")"))) "nothing"))
      (.append lines f"  {name} holds for: {shown}"))
    (.join "\n" lines))
  (defn as-model [self]
    "The model in the form evaluate takes, with constants mapped to elements."
    (| (dict self.constants)
       (dict self.propositions)
       (dfor [name tuples] (.items self.facts) name (set tuples))
       (dfor [name table] (.items self.functions) name (_lookup table)))))

(defn _lookup [table]
  (fn [#* args] (get table args)))

(defn _term [t bound constants functions]
  (cond
    (compound? t) (get (get functions (get t 0))
                       (tuple (gfor a (cut t 1 None) (_term a bound constants functions))))
    (in t bound) (get bound t)
    True (get constants t)))

(defn _ground [f domain bound constants functions]
  (setv op (operator-of f))
  (cond
    (in op QUANTIFIERS)
      (do
        (setv names (get f 1)
              parts (lfor values (product domain :repeat (len names))
                          (_ground (get f 2) domain (| bound (dict (zip names values))) constants functions)))
        #((if (= op "forall") "and" "or") #* parts))
    op #(op #* (gfor a (args-of f) (_ground a domain bound constants functions)))
    (compound? f)
      (+ (get f 0) "(" (.join "," (gfor a (cut f 1 None) (_term a bound constants functions))) ")")
    True f))

(defn _tables [functions domain]
  "Every way to interpret the functions over the domain."
  (setv names (sorted functions)
        options [])
  (for [name names]
    (setv inputs (list (product domain :repeat (get functions name))))
    (.append options (lfor outputs (product domain :repeat (len inputs))
                           (dict (zip inputs outputs)))))
  (gfor choice (product #* options) (dict (zip names choice))))

(defn find-model [formulas [max-size 4] [max-tries 20000]]
  "A smallest finite model of the formulas, or None if none has at most max-size elements."
  (setv fs (lfor f formulas (basic f))
        sig (signature fs)
        constants (sorted (get sig "constants"))
        tries 0)
  (for [n (range 1 (+ max-size 1))]
    (setv domain (lfor i (range n) (_element i)))
    (for [consts (product domain :repeat (len constants))
          functions (_tables (get sig "functions") domain)]
      (+= tries 1)
      (when (> tries max-tries) (return None))
      (setv constant-map (dict (zip constants consts))
            grounded #("and" #* (gfor f fs (_ground f domain {} constant-map functions)))
            assignment (satisfiable grounded))
      (when (is-not assignment None)
        (return (_model domain constant-map functions assignment sig)))))
  None)

(defn _model [domain constants functions assignment sig]
  (setv facts (dfor name (get sig "predicates") name #{})
        propositions {})
  (for [[atom value] (.items assignment)]
    (if (in "(" atom)
        (when value
          (setv [name rest] (.split atom "(" 1))
          (.add (get facts name) (tuple (.split (cut rest 0 -1) ","))))
        (setv (get propositions atom) value)))
  (for [p (get sig "propositions")]
    (when (not-in p propositions) (setv (get propositions p) False)))
  (Model domain constants functions facts propositions))

(defn countermodel [premises goal [max-size 4]]
  "A finite world where the premises are true and the goal is false, or None."
  (find-model [#* premises #("not" (basic goal))] :max-size max-size))
