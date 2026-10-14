# How the prover works

The prover in hylogic is built from unification, term rewriting and
resolution, the core of classical automated theorem proving, in about 400
lines of Hy. It is meant to be read and changed, not to compete with real
provers.

```bash
hy examples/tour.hy                  # a guided tour with output
pytest                               # the tests
```

| File | What it contains |
|---|---|
| `hylogic/terms.hy` | Terms as data, and how quoted Hy forms become terms |
| `hylogic/unify.hy` | Unification, one-way matching, renaming variables |
| `hylogic/rewrite.hy` | Rewrite rules, the `defrules` macro, normalization |
| `hylogic/resolution.hy` | Clausal form, resolution, factoring, subsumption, the search loop, proofs |
| `hylogic/problems.hy` | Pelletier's problems, textbook examples, non-theorems, two rule sets |
| `examples/tour.hy` | The tour |
| `test/test_prover.hy` | Tests, including a truth-table check of every propositional problem |

## 1. Terms

Formulas can use logical symbols or ASCII names: `(∀ [x] (→ (Man x) (Mortal x)))`
is the same formula as `(forall [x] (=> (Man x) (Mortal x)))`. `hylogic.formulas`
turns the symbols into the ASCII names, and rewrites the extended connectives
(⊕ ↑ ↓ ≡ ≢ ← ↛ ↚) with the basic five before the prover sees them.

Logic needs terms like `(Loves ?x (mother-of ?x))`: constants (`socrates`),
variables (`?x`), and function or predicate applications. In Hy you can write
them directly as quoted code, `'(Loves ?x (mother-of ?x))`. This is the Lisp
idea of code as data, and it is the most natural thing Hy brings here.

`term` turns the quoted form into plain tuples and strings, because Hy's own
models compare by type (a `Symbol` is not equal to the same `str`), which
makes them awkward as dictionary keys and set members.

## 2. Unification

Unification asks whether two terms can be made equal by choosing values for
their variables, and finds the most general such choice:

```
unify (Knows john ?x) and (Knows ?y (mother ?y))
  substitution: ?y = john, ?x = (mother ?y)
  both become:  (Knows john (mother john))
```

The substitution is kept in triangular form (`?x` points to a term that
still contains `?y`), and `walk` follows the chain. The occurs check refuses
`?x = (f ?x)`, which would need an infinite term. Without it the prover
would be unsound.

Matching is one-sided unification: only the pattern's variables are bound.
Rewriting uses matching, resolution uses unification.

## 3. Rewriting

A rewrite rule `lhs -> rhs` replaces any instance of the left side with the
same instance of the right side. Applying rules until none applies gives the
term's normal form. Two times two in Peano arithmetic, where `(s n)` means
n + 1:

```hy
(defrules PEANO
  (+ 0 ?y)      -> ?y
  (+ (s ?x) ?y) -> (s (+ ?x ?y))
  (* 0 ?y)      -> 0
  (* (s ?x) ?y) -> (+ ?y (* ?x ?y)))
```

```
   (* (s (s 0)) (s (s 0)))
=> (+ (s (s 0)) (* (s 0) (s (s 0))))          by (* (s ?x) ?y) -> (+ ?y (* ?x ?y))
   ...
=> (s (s (s (s 0))))                          by (+ 0 ?y) -> ?y
```

The strategy is innermost first: arguments are normalized before the term
around them. A rule can have a condition. Symbolic differentiation needs one,
because the derivative of a constant is zero only if the term is free of the
variable:

```hy
(d ?x ?c) -> 0  :if (free-of? ?c ?x)
```

`defrules` is a macro, and it has to be one. Its arguments are rule text,
which must not be evaluated, and each condition has to become a function of
the rule's bindings, so `?c` inside `(free-of? ?c ?x)` is rewritten to a
lookup. A function cannot see its arguments before they are evaluated. This
is one of the few places where a macro does something Python cannot.

Rewriting can loop (`(f ?x) -> (f (f ?x))`), so `normalize` has a step limit.
Whether a rule set always terminates, and whether its normal forms are
unique, are the central questions of rewriting theory.

## 4. Resolution

Resolution proves a goal by refutation. Add the negation of the goal to the
axioms, and derive a contradiction.

### Clausal form

Resolution works on clauses, disjunctions of literals such as
`(Mortal ?x) | (not (Man ?x))`. Every formula is turned into clauses in four
steps, shown here for Pelletier's problem 20:

1. **Remove `=>` and `<=>`.** `(=> A B)` becomes `(or (not A) B)`.
2. **Negation normal form.** Push every `not` down to an atom, using De
   Morgan's laws and `(not (forall [x] A))` = `(exists [x] (not A))`.
3. **Skolemize.** Each universal variable becomes a clause variable such as
   `?x5`. Each existential variable becomes a new function of the universal
   variables in scope: in `(forall [x] (exists [y] (Loves x y)))`, the `y`
   depends on `x`, so it becomes `(sk8 ?x7)`. The result is not equivalent,
   but it is satisfiable exactly when the original is, which is all a
   refutation needs.
4. **Distribute `or` over `and`** and read off the clauses.

```
Skolemized, quantifiers dropped:
    (or (and (and (P sk1) (Q sk2)) (or (not (R ?z3)) (not (S (sk4 ?z3))))) (or (or (not (P ?x5)) (not (Q ?y6))) (R sk7)))
clauses:
    (P sk1) | (R sk7) | (not (P ?x5)) | (not (Q ?y6))
    (Q sk2) | (R sk7) | (not (P ?x5)) | (not (Q ?y6))
    (R sk7) | (not (P ?x5)) | (not (Q ?y6)) | (not (R ?z3)) | (not (S (sk4 ?z3)))
```

### Inference

- **Resolution.** From `A | C` and `(not A') | D`, where `A` and `A'` unify
  with substitution s, derive `(C | D)s`. The second clause's variables are
  renamed first, because variables in different clauses are unrelated.
- **Factoring.** Merge two literals of the same sign in one clause that unify.
  Binary resolution needs it to be complete.
- **The empty clause `□`**, a disjunction of nothing, is false. Deriving it
  proves the goal.

Robinson showed in 1965 that this is refutation complete. If the clauses are
contradictory, the empty clause can be derived. If they are not, the search
may run forever, since first-order logic is only semi-decidable.

### Search

`saturate` is the given-clause loop that real provers use. It takes the
lightest unprocessed clause (fewest symbols), resolves it against every
processed clause, and keeps a new clause only if it is not a tautology, not a
duplicate up to renaming, and not subsumed by a processed clause. A clause C
subsumes D if some substitution maps all of C into D. D then says nothing C
does not.

The prover prints the proof with every step's parents:

```
   1. (Dog sk15)                                   axiom
   2. (Owns jack sk15)                             axiom
   3. (AnimalLover ?x16) | (not (Dog ?y17)) | (not (Owns ?x16 ?y17)) axiom
   4. (not (Animal ?y19)) | (not (AnimalLover ?x18)) | (not (Kills ?x18 ?y19)) axiom
   5. (Kills curiosity tuna) | (Kills jack tuna)   axiom
   6. (Cat tuna)                                   axiom
   7. (Animal ?x20) | (not (Cat ?x20))             axiom
   8. (not (Kills curiosity tuna))                 negated goal
   9. (Animal tuna)                                resolve 7, 6
  10. (Kills jack tuna)                            resolve 5, 8
  12. (AnimalLover jack) | (not (Dog sk15))        resolve 3, 2
  13. (AnimalLover jack)                           resolve 12, 1
  16. (not (Animal tuna)) | (not (AnimalLover jack)) resolve 4, 10
  21. (not (AnimalLover jack))                     resolve 16, 9
  26. □                                            resolve 21, 13
```

Read from line 8: if Curiosity did not kill Tuna, Jack did (10). Jack owns a
dog, so he is an animal lover (13). Tuna is a cat, so an animal (9). Animal
lovers kill no animals (16, 21), which contradicts 13.

## 5. Results

The problems are from Pelletier's
[Seventy-five problems for testing automatic theorem provers](https://doi.org/10.1007/BF02432151)
(1986) and from Russell and Norvig's *Artificial Intelligence: A Modern
Approach* (the cat). Times are on Apple Silicon with Hy 1.3.

| Problems | Result | Clauses kept | Time |
|---|---|---|---|
| P1 to P17, propositional | all 17 proved | 3 to 28 | under 1.1 ms each |
| Socrates, Curiosity, P18 to P24, drinker paradox | all 10 proved | 3 to 26 | under 1.6 ms each |
| P34, Andrews' challenge | proved with a limit of 10,000 clauses, not 2,000 | about 6,400 (47,000 generated) | 5.2 s |
| Three non-theorems | not proved; the search ends without a contradiction | 2 | under 0.1 ms |

Two independent checks:

- The tests evaluate every propositional problem with a truth table.
- During development, every problem was also given to the
  [Z3](https://github.com/Z3Prover/z3) solver. It agreed on all 31: the 28
  theorems are valid and the 3 non-theorems are not. Z3 is not a dependency.

## 6. Limits, and what real provers do instead

- **Clausal form blows up.** P34's negated goal becomes 1,296 clauses because
  distribution doubles the formula at every nested `<=>`. Real provers
  introduce a new name for each subformula (the Tseitin transformation),
  which keeps the clause set linear in the formula's size.
- **No equality.** `=` is just another predicate here. Provers handle
  equality with paramodulation or superposition, which is resolution and
  rewriting combined: equations are used as oriented rewrite rules inside
  the resolution search.
- **No indexing.** Every new clause is compared with every processed clause.
  Vampire and E find unification and subsumption candidates through term
  indexes and handle millions of clauses.
- **Unrestricted resolution.** Ordered resolution and selection functions
  cut most of the useless inferences while staying complete.
- **Clause selection by weight only.** Always taking the lightest clause can
  starve heavy ones forever. Real provers alternate between the lightest and
  the oldest clause, which makes the search fair.

## 7. Exercises

1. **Answer extraction.** Add `(Answer ?x)` to the negated goal
   `(not (Kills ?x tuna))` and stop at a clause containing only `Answer`
   literals. The prover then says who killed the cat.
2. **Fair selection.** Pick the oldest clause every fifth time and compare
   the numbers on P34.
3. **Tseitin transformation.** Replace `cnf-clauses` and measure P34 again.
4. **Equality.** Add paramodulation and prove that a group in which every
   element is its own inverse is commutative.
5. **Completion.** Implement Knuth-Bendix completion and derive a complete
   rewrite system for groups from the three group axioms.
6. **Lean.** State P20 and Peirce's law in Lean 4 and prove them there.

## 8. Next: Lean

This prover searches for proofs automatically within one fixed logic.
[Lean 4](https://lean-lang.org/) works the other way round. You write the
proof, or let tactics and automation write parts of it, and a small trusted
kernel checks every step, in a logic strong enough for all of mathematics.
That is where current work with language models happens.

- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4):
  Peano arithmetic from section 3, proved by hand in Lean.
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)

## Further reading

- J. A. Robinson, *A Machine-Oriented Logic Based on the Resolution
  Principle*, Journal of the ACM, 1965. The origin of resolution and
  unification.
- John Harrison, *Handbook of Practical Logic and Automated Reasoning*,
  Cambridge University Press, 2009. All of the above and much more, with
  code.
- Franz Baader and Tobias Nipkow, *Term Rewriting and All That*, Cambridge
  University Press, 1998.
- Peter Norvig, *Paradigms of Artificial Intelligence Programming*, 1992.
  Unification and a Prolog interpreter in Common Lisp.
