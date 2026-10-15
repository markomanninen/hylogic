"Unification and matching.

A substitution is a dict from variables to terms. Bindings may point to
other bound variables, so a term is looked up with `walk` until it reaches
something unbound, and `substitute` applies the whole substitution.

`unify` makes two terms equal by binding variables on both sides.
`match-term` binds variables on one side only, the pattern. Rewriting
uses matching: a rule's left side is a pattern, and the term being
rewritten must not change."

(import itertools [count]
        hylogic.terms [variable? compound?])

(defn walk [t s]
  "Follow variable bindings until an unbound variable or a non-variable."
  (while (and (variable? t) (in t s))
    (setv t (get s t)))
  t)

(defn occurs? [v t s]
  "Does variable v occur in t? Binding v to such a t would make an infinite term."
  (setv t (walk t s))
  (cond
    (= v t) True
    (compound? t) (any (gfor x t (occurs? v x s)))
    True False))

(defn unify [a b [s None]]
  "The most general substitution that makes a and b equal, extending s, or None."
  (when (is s None) (setv s {}))
  (setv a (walk a s)
        b (walk b s))
  (cond
    (= a b) s
    (variable? a) (if (occurs? a b s) None (| s {a b}))
    (variable? b) (if (occurs? b a s) None (| s {b a}))
    (and (compound? a) (compound? b) (= (len a) (len b)))
      (do
        (for [[x y] (zip a b)]
          (setv s (unify x y s))
          (when (is s None) (return None)))
        s)
    True None))

(defn substitute [t s]
  "Apply substitution s to term t."
  (setv t (walk t s))
  (if (compound? t)
      (tuple (gfor x t (substitute x s)))
      t))

(defn instantiate [t s]
  "Replace the variables of t by their values in s, once, without following chains.
  This is how a match applies: the matched term's variables may share names with
  the pattern's, and following chains could then loop (?x -> ?y -> ?x)."
  (cond
    (variable? t) (.get s t t)
    (compound? t) (tuple (gfor x t (instantiate x s)))
    True t))

(defn match-term [pattern t [s None]]
  "A substitution for the variables of pattern that turns it into t, or None.
  Variables in t are treated like constants."
  (when (is s None) (setv s {}))
  (cond
    (variable? pattern)
      (cond
        (not-in pattern s) (| s {pattern t})
        (= (get s pattern) t) s
        True None)
    (and (compound? pattern) (compound? t) (= (len pattern) (len t)))
      (do
        (for [[p x] (zip pattern t)]
          (setv s (match-term p x s))
          (when (is s None) (return None)))
        s)
    (= pattern t) s
    True None))

(setv FRESH (count 1))

(defn rename [t [mapping None]]
  "t with every variable replaced by a fresh one: ?x7 becomes ?x12, and so on."
  (when (is mapping None) (setv mapping {}))
  (cond
    (variable? t)
      (do
        (when (not-in t mapping)
          (setv (get mapping t) (+ (.rstrip t "0123456789") (str (next FRESH)))))
        (get mapping t))
    (compound? t) (tuple (gfor x t (rename x mapping)))
    True t))
