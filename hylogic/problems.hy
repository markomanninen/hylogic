"Problems for the prover.

Most are from Pelletier's \"Seventy-five problems for testing automatic theorem
provers\" (Journal of Automated Reasoning, 1986), the standard first set for a
new prover. All of them are theorems. The non-theorems at the end must not be
proved."

(import hylogic.rewrite [make-rule])
(require hylogic.rewrite [defrules])

;; name, axioms, goal

(setv PROPOSITIONAL [
  #("P1" [] '(<=> (=> p q) (=> (not q) (not p))))
  #("P2" [] '(<=> (not (not p)) p))
  #("P3" [] '(=> (not (=> p q)) (=> q p)))
  #("P4" [] '(<=> (=> (not p) q) (=> (not q) p)))
  #("P5" [] '(=> (=> (or p q) (or p r)) (or p (=> q r))))
  #("P6" [] '(or p (not p)))
  #("P7" [] '(or p (not (not (not p)))))
  #("P8 (Peirce's law)" [] '(=> (=> (=> p q) p) p))
  #("P9" [] '(=> (and (or p q) (or (not p) q) (or p (not q))) (not (or (not p) (not q)))))
  #("P10" ['(=> q r) '(=> r (and p q)) '(=> p (or q r))] '(<=> p q))
  #("P11" [] '(<=> p p))
  #("P12" [] '(<=> (<=> (<=> p q) r) (<=> p (<=> q r))))
  #("P13" [] '(<=> (or p (and q r)) (and (or p q) (or p r))))
  #("P14" [] '(<=> (<=> p q) (and (or q (not p)) (or (not q) p))))
  #("P15" [] '(<=> (=> p q) (or (not p) q)))
  #("P16" [] '(or (=> p q) (=> q p)))
  #("P17" [] '(<=> (=> (and p (=> q r)) s) (and (or (not p) q s) (or (not p) (not r) s))))])

(setv FIRST-ORDER [
  #("Socrates"
    ['(forall [x] (=> (Man x) (Mortal x))) '(Man socrates)]
    '(Mortal socrates))
  #("Curiosity killed the cat"
    ['(exists [x] (and (Dog x) (Owns jack x)))
     '(forall [x] (=> (exists [y] (and (Dog y) (Owns x y))) (AnimalLover x)))
     '(forall [x] (=> (AnimalLover x) (forall [y] (=> (Animal y) (not (Kills x y))))))
     '(or (Kills jack tuna) (Kills curiosity tuna))
     '(Cat tuna)
     '(forall [x] (=> (Cat x) (Animal x)))]
    '(Kills curiosity tuna))
  #("P18" [] '(exists [y] (forall [x] (=> (F y) (F x)))))
  #("P19" [] '(exists [x] (forall [y z] (=> (=> (P y) (Q z)) (=> (P x) (Q x))))))
  #("P20" []
    '(=> (forall [x y] (exists [z] (forall [w] (=> (and (P x) (Q y)) (and (R z) (S w))))))
         (=> (exists [x y] (and (P x) (Q y))) (exists [z] (R z)))))
  #("P21" ['(exists [x] (=> p (F x))) '(exists [x] (=> (F x) p))]
    '(exists [x] (<=> p (F x))))
  #("P22" [] '(=> (forall [x] (<=> p (F x))) (<=> p (forall [x] (F x)))))
  #("P23" [] '(<=> (forall [x] (or p (F x))) (or p (forall [x] (F x)))))
  #("P24"
    ['(not (exists [x] (and (S x) (Q x))))
     '(forall [x] (=> (P x) (or (Q x) (R x))))
     '(=> (not (exists [x] (P x))) (exists [y] (Q y)))
     '(forall [x] (=> (or (Q x) (R x)) (S x)))]
    '(exists [x] (and (P x) (R x))))
  #("Drinker paradox" [] '(exists [x] (=> (Drinks x) (forall [y] (Drinks y)))))])

(setv HARD [
  ;; Andrews' challenge: easy for people, but clausal form blows up to over a thousand clauses
  #("P34 (Andrews' challenge)" []
    '(<=> (<=> (exists [x] (forall [y] (<=> (P x) (P y))))
               (<=> (exists [x] (Q x)) (forall [y] (Q y))))
          (<=> (exists [x] (forall [y] (<=> (Q x) (Q y))))
               (<=> (exists [x] (P x)) (forall [y] (P y))))))])

(setv NON-THEOREMS [
  #("p implies q" [] '(=> p q))
  #("some to all" [] '(=> (exists [x] (P x)) (forall [x] (P x))))
  #("swapped quantifiers" [] '(=> (forall [x] (exists [y] (L x y))) (exists [y] (forall [x] (L x y)))))])

;; Rewriting

(defrules PEANO
  (+ 0 ?y)      -> ?y
  (+ (s ?x) ?y) -> (s (+ ?x ?y))
  (* 0 ?y)      -> 0
  (* (s ?x) ?y) -> (+ ?y (* ?x ?y)))

(defn free-of? [t x]
  "Is t free of the symbol x?"
  (if (isinstance t tuple)
      (all (gfor a t (free-of? a x)))
      (!= t x)))

(defrules DERIVATIVE
  (d ?x ?x)        -> 1
  (d ?x ?c)        -> 0                                   :if (free-of? ?c ?x)
  (d ?x (+ ?u ?v)) -> (+ (d ?x ?u) (d ?x ?v))
  (d ?x (* ?u ?v)) -> (+ (* (d ?x ?u) ?v) (* ?u (d ?x ?v)))
  (+ 0 ?u)         -> ?u
  (+ ?u 0)         -> ?u
  (* 0 ?u)         -> 0
  (* ?u 0)         -> 0
  (* 1 ?u)         -> ?u
  (* ?u 1)         -> ?u)
