# Hylogic

Propositional and first-order logic in [Hy](https://hylang.org), a Lisp that
compiles to Python. Write formulas as Lisp code with the usual logical
symbols, then check them with truth tables, evaluate them in a finite model,
test whether an argument is valid, or prove them with a small resolution
prover that prints its proofs.

```hy
(import hylogic [truth-table prove])

(print (truth-table '(→ (∧ P (→ P Q)) Q)))
```

```
P │ Q │ (P ∧ (P → Q)) → Q
──┼───┼──────────────────
⊤ │ ⊤ │         ⊤
⊤ │ ⊥ │         ⊤
⊥ │ ⊤ │         ⊤
⊥ │ ⊥ │         ⊤
```

Hylogic is meant for learning and experimenting: the code is short enough to
read, and every step of a proof can be printed. For serious proofs, use
[Lean](https://lean-lang.org/) or an automated prover such as Vampire or E.

## Install

```bash
pip install hylogic
```

Hylogic needs Python 3.9 or newer and Hy 1.0 or newer. To run the tests and
the tour from a clone:

```bash
pip install -e ".[test]"
pytest
hy examples/tour.hy
```

## Formulas

A formula is quoted Hy code. Atoms are propositions (`P`) or predicates
applied to terms (`(Loves x (mother x))`). Every connective has a symbol and
an ASCII name, and both can be mixed freely:

| Symbol | ASCII | Name | Arguments |
|---|---|---|---|
| `¬` | `not` | Negation | 1 |
| `∧` | `and` | Conjunction | any number |
| `∨` | `or` | Disjunction | any number |
| `↑` | `nand` | Nonconjunction | any number |
| `↓` | `nor` | Nondisjunction | any number |
| `⊕` `↮` | `xor` | Exclusive or, true for an odd number of true arguments | any number |
| `≡` | `eqv` | Equivalence, true when all arguments agree | any number |
| `≢` | `neqv` | Nonequivalence | any number |
| `↔` | `<=>` | Biconditional | 2 |
| `→` | `=>` | Material implication | 2 |
| `←` | `<=` | Converse implication | 2 |
| `↛` | `nimp` | Material nonimplication | 2 |
| `↚` | `cnimp` | Converse nonimplication | 2 |
| `∀` | `forall` | Universal quantifier, `(∀ [x y] body)` | |
| `∃` | `exists` | Existential quantifier | |
| `⊤` `⊥` | `true` `false` | The constants | |

`pretty` prints a formula in the usual notation:

```hy
(import hylogic [pretty])
(pretty '(forall [x] (=> (Man x) (Mortal x))))   ; "∀x ((Man x) → (Mortal x))"
```

## Truth tables

```hy
(import hylogic.truth [truth-table tautology? satisfiable? equivalent? entails? counterexample])

(tautology? '(=> (=> (=> p q) p) p))              ; Peirce's law: True
(equivalent? '(¬ (∧ P Q)) '(∨ (¬ P) (¬ Q)))       ; De Morgan: True
(entails? ['(→ P Q) '(¬ Q)] '(¬ P))               ; modus tollens: True
(counterexample ['(→ P Q) 'Q] 'P)                 ; {"P" False "Q" True}
```

`truth-table` takes several formulas and shows them side by side. In a
Jupyter notebook it renders as an HTML table. `(print (connective-tables))`
prints the tables of all thirteen connectives.

## Arguments

`defargument` takes premises and a conclusion as written, without quoting,
and decides validity: by truth table when the argument is propositional, and
with the prover when it has quantifiers or predicates.

```hy
(require hylogic.argument [defargument])

(defargument modus-tollens
  :premises [(→ P Q) (¬ Q)]
  :conclusion (¬ P)
  :meanings {P "It rains" Q "The street is wet"})

(print (.explain modus-tollens))
```

```
  P → Q
  ¬Q
  ───────
∴ ¬P

  P: It rains
  Q: The street is wet

Valid, by truth table.
```

An invalid argument comes with a counterexample, and `Argument` builds the
same object from quoted formulas:

```hy
(import hylogic [Argument])
(.explain (Argument ['(→ P Q) 'Q] 'P))
; Invalid, by truth table.
; Counterexample: P = ⊥, Q = ⊤
```

## Models

`evaluate` finds the truth value of a formula in a model. Predicates are
Python functions or collections of the tuples they hold for, and quantifiers
range over a finite domain:

```hy
(import hylogic [evaluate])

(setv model {"Man" #{"socrates" "plato"}
             "Mortal" #{"socrates" "plato" "fido"}})
(evaluate '(∀ [x] (→ (Man x) (Mortal x))) model ["socrates" "plato" "fido"])   ; True
(evaluate '(∀ [x] (→ (Mortal x) (Man x))) model ["socrates" "plato" "fido"])   ; False
```

For quantifiers over ordinary Python data, there are macros:

```hy
(require hylogic.quantifiers [∀ ∃])
(∀ [x (range 1 10)] (> x 0))                 ; True
(∃ [x [1 2] y [-1 -2]] (= (+ x y) 0))        ; True, with x = 1, y = -1
```

## Proofs

`prove` refutes the negated goal together with the axioms by resolution, and
returns a result whose `proof` lists every step:

```hy
(import hylogic [prove])

(setv result (prove '(Kills curiosity tuna)
                    ['(∃ [x] (∧ (Dog x) (Owns jack x)))
                     '(∀ [x] (→ (∃ [y] (∧ (Dog y) (Owns x y))) (AnimalLover x)))
                     '(∀ [x] (→ (AnimalLover x) (∀ [y] (→ (Animal y) (¬ (Kills x y))))))
                     '(∨ (Kills jack tuna) (Kills curiosity tuna))
                     '(Cat tuna)
                     '(∀ [x] (→ (Cat x) (Animal x)))]))
(for [line (.proof result)] (print line))
```

```
   1. (Dog sk1)                                    axiom
   ...
   8. (not (Kills curiosity tuna))                 negated goal
  10. (Kills jack tuna)                            resolve 5, 8
  13. (AnimalLover jack)                           resolve 12, 1
  21. (not (AnimalLover jack))                     resolve 16, 9
  26. □                                            resolve 21, 13
```

`result.status` is `proved`, `saturated` (the goal does not follow) or
`gave-up` (the clause limit, `:limit 5000` by default, was reached). The
prover proves Pelletier's problems 1 to 24 in milliseconds and problem 34
(Andrews' challenge) in about five seconds. [doc/prover.md](doc/prover.md)
explains how it works, step by step, with exercises.

Term rewriting is included too:

```hy
(require hylogic.rewrite [defrules])
(import hylogic [normalize])

(defrules PEANO
  (+ 0 ?y)      -> ?y
  (+ (s ?x) ?y) -> (s (+ ?x ?y)))

(get (normalize '(+ (s (s 0)) (s 0)) PEANO) 0)    ; #("s" #("s" #("s" 0)))
```

## Teaching and exercises

`hylogic.exercises` checks the two classic kinds of exercise and explains a
wrong answer in the words of the exercise. A formalization is correct when it
is logically equivalent to the reference, however it is written. A wrong one
gets a situation where the two come apart:

```hy
(import hylogic.exercise-sets [check-answer])

(check-answer "F2" '(→ P Q))      ; "The street is wet only if it rains."
; Not quite. Suppose “it rains” is false and “the street is wet” is true.
; Then your formula is true, but the sentence is false.

(check-answer "V9" True)          ; "Everybody loves somebody. So there is somebody whom everybody loves."
; Not quite. The argument is invalid. In this world the premises are true and the conclusion is false:
; Domain: d1, d2
;   Loves holds for: (d1 d1), (d2 d2)
```

The exercise set has 16 sentences to formalize, propositional and
first-order, and 10 arguments to judge. `check-formalization` and
`check-validity-claim` work with your own exercises too, and a claim that an
argument is invalid can come with a counterexample, which is checked.

[Hylogic tutorial.ipynb](Hylogic%20tutorial.ipynb) walks through truth
tables, arguments, exercises, models and proofs. It runs on the ordinary
Python kernel with `%load_ext hylogic.ipython`, which adds a `%%hy` cell
magic.

## Larger problems, countermodels and other solvers

Truth tables double with every proposition. For larger propositional
problems, `satisfiable` and `valid?` in `hylogic.sat` use the Tseitin
transformation and the DPLL algorithm, which stay in milliseconds up to about
40 variables. Arguments switch to it on their own above 10 propositions.

```hy
(import hylogic.sat [satisfiable valid?])
(satisfiable '(∧ (∨ P Q) (¬ P)))      ; {"P" False "Q" True}
```

When a first-order argument is invalid, `countermodel` looks for a small
world that shows it, by grounding the formulas over a domain of up to four
elements and solving the result with DPLL:

```hy
(import hylogic [countermodel])
(print (countermodel ['(∀ [x] (∃ [y] (Loves x y)))] '(∃ [y] (∀ [x] (Loves x y)))))
```

```
Domain: d1, d2
  Loves holds for: (d1 d1), (d2 d2)
```

Everybody loves somebody, here themselves, but nobody is loved by everybody.

For problems beyond hylogic's reach, `to-smtlib` and `to-tptp` write the same
question for real solvers such as Z3 and cvc5, or provers such as Vampire and
E, and `to-dimacs` writes the SAT clauses for any SAT solver. With
`pip install "hylogic[z3]"`, `check-with-z3` runs Z3 directly.
[benchmarks/](benchmarks/) compares the four methods on the same problems.

## TPTP problems, E, Vampire and Lean

HyLogic reads problems in TPTP, the standard language of first-order
provers, and answers the way they do, with an SZS status line:

```bash
python -m hylogic.tptp --time-limit 10 PUZ001+1.p
# % SZS status Theorem for PUZ001+1
```

For problems beyond its own prover, HyLogic hands them to E or Vampire when
they are installed, reads the proof they print, and shows it as its own
numbered steps:

```hy
(import hylogic.external [prove-external])
(setv r (prove-external '(Mortal socrates) ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)]
                        :prover "vampire"))
(for [line (.proof r)] (print line))
```

```
   1. ∀X0 ((man X0) → (mortal X0))                 input
   2. (man socrates)                               input
  ...
  10. ¬(man socrates)                              resolution 7, 9
  11. ⊥                                            resolution 10, 8
```

`prove-external` writes the premises and the goal as a TPTP file in a
temporary directory and runs the prover on it with the time limit,
`vampire --mode casc --proof tptp` or `eprover --auto --tstp-format
--proof-object`. It reads the SZS status and the proof the prover prints in
TSTP, TPTP's format for proofs. Each step is parsed with the same reader as
TPTP problems, E's nested inferences are unwrapped to the steps they really
use, and the steps are numbered with their rule and parents. The provers are
found on the PATH as `vampire` and `eprover`, or through `HYLOGIC_VAMPIRE`
and `HYLOGIC_EPROVER`, and without them `prove-external` stops with an error
saying how to provide one. `run-prover` does the same for a TPTP file that
already exists. These proofs are shown but not checked, since `certify`
checks only HyLogic's own proofs.

`to-lean` writes a problem as a Lean 4 theorem, and `check-lean` runs Lean on
it, with `sorry` to check the statement or `grind` to let Lean's automation
prove it. `hylogic.certify` writes HyLogic's own proof as Lean theorems, one
per inference with the instances it used, and `certify` has Lean check every
step and the whole refutation from the input clauses. Lean accepted all 161
TPTP proofs of the benchmark below, 13,180 steps, without an invalid one.

On a fixed sample of 234 TPTP theorems within 10 seconds, HyLogic's own
prover proves 161 (39 before its ordered resolution, superposition,
goal-directed selection, unit deletion, grounding with clause splitting,
SAT-based ground decision with congruence closure, a schedule of strategies
and other improvements), Lean's `grind` 53 of the exported problems (103 with
20 seconds), E 207 and Vampire 231. Of 40 non-theorems HyLogic shows 31 with
countermodels, E 16, and Vampire 20 in its theorem-proving mode but 36 with
its satisfiability schedule. On 240 further problems drawn as a check, none
used in tuning, HyLogic proves 141 of 200 theorems (E 189, Vampire 197) and
shows 27 of 40 non-theorems (E 17, Vampire 18 and 32), with no wrong answer.
Answers found by SAT come with resolution proofs too. Through the bridge HyLogic presented
every one of the 440 E and Vampire proofs. [benchmarks/tptp/](benchmarks/tptp/) has the plan, every
step and the numbers.

## For AI agents

`hylogic-mcp` is a [Model Context Protocol](https://modelcontextprotocol.io)
server with one tool, `check_argument`. An agent formalizes an argument,
calls the tool, and gets the verdict with a counterexample or countermodel
when the argument is invalid. Formulas can be s-expression strings or JSON
arrays, since models write JSON most reliably.

```bash
pip install "hylogic[mcp]"
claude mcp add hylogic -- hylogic-mcp
```

```
check_argument(premises=["(=> P Q)", "Q"], conclusion="P",
               meanings={"P": "it rains", "Q": "the street is wet"})

INVALID (checked by truth table)
Read as: P → Q; Q ⊢ P
Counterexample: “it rains” is false and “the street is wet” is true. Then every premise is true and the conclusion is false.
```

A valid argument comes with the premises it needs. `detail=true` adds the
proof, and `certify=true` has Lean 4 check every step of it in a few seconds,
when the `lean` command is installed (or named by `HYLOGIC_LEAN`); without
Lean the answer says how to install it.

```
check_argument(premises=["(forall [x] (=> (Man x) (Mortal x)))", "(Man socrates)", "(Greek socrates)"],
               conclusion="(Mortal socrates)", certify=True)

VALID (checked by resolution)
Read as: ∀x ((Man x) → (Mortal x)); (Man socrates); (Greek socrates) ⊢ (Mortal socrates)
Premises needed: 1, 2 (of 3)
Proof: 4 steps, shown with detail=true
Lean check: verified, Lean 4 accepted the 1 step of the proof and how they chain from the premises to a contradiction (4.3 s). The clausal form of the premises is taken as given.
```

[benchmarks/field_test/](benchmarks/field_test/) measures whether the tool
helps agents judge arguments, and what it costs.

## From Python

Formulas are nested tuples of strings, and the Hy names that end in `?` have
Python aliases:

```python
import hylogic

hylogic.is_tautology(("or", "P", ("not", "P")))           # True
hylogic.entails([("=>", "P", "Q"), "P"], "Q")             # True
hylogic.prove(("=>", ("forall", ("x",), ("P", "x")), ("P", "a"))).proved   # True
```

## Tests

The tests check every connective against its definition, compare the
extended connectives with their rewritten forms on every assignment, and run
the prover on 300 random propositional formulas, where it must agree with
the truth tables. The first-order problems were also checked with the Z3
solver during development.

## History

Hylogic began in 2017 as a propositional logic evaluator for Hy 0.12 with an
infix notation. Version 1.0 is a rewrite for Hy 1.x: the infix notation is
gone, formulas are data, and the prover, models and arguments are new. The
2017 version is tagged `v0.1.0`.

## License

MIT
