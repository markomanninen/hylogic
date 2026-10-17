# How far a theorem prover you can read gets

*HyLogic is a small theorem prover written in Hy, a Lisp that runs on Python. It proves 161 of 234 benchmark theorems in ten seconds each, finds more counterexamples than E, and Lean checks every step of its proofs.*

---

In ten seconds per problem, HyLogic proves 161 of 234 theorems from [TPTP](https://www.tptp.org), the standard problem library for automated theorem provers. E and Vampire, two of the strongest automated provers, prove 207 and 231. On 40 problems whose conclusion does not follow, HyLogic shows 31 with a counterexample, where E shows 16. And when [Lean](https://lean-lang.org), the [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant) mathematicians use to check proofs, went one step at a time through the 161 proofs HyLogic found in the benchmark, it accepted every one of their 13,180 steps.

HyLogic is meant to be read. Its proofs are numbered lines from the premises to a contradiction, and the core of the prover is about 700 lines of Lisp. This article is about how far a prover like that gets against the real ones, which methods carried it there, and how its answers came to be trusted.

## What a theorem prover does

A theorem prover decides whether a conclusion follows from premises. Most automated provers work by refutation. They assume that the conclusion is false, rewrite the premises and that assumption as clauses, which are disjunctions of simple statements, and search for a contradiction. If one turns up, the conclusion must follow from the premises.

The basic step is [resolution](https://en.wikipedia.org/wiki/Resolution_(logic)), from [J. A. Robinson's paper of 1965](https://doi.org/10.1145/321250.321253). From "A or B" and "not A or C" it concludes "B or C". When the statements contain variables, it first finds the substitution that makes them match, which is called [unification](https://en.wikipedia.org/wiki/Unification_(computer_science)), so that "every man is mortal" can meet "Socrates is a man".

Here is a textbook puzzle. Jack owns a dog, every dog owner loves animals, no animal lover kills an animal, Tuna is a cat, every cat is an animal, and either Jack or Curiosity killed Tuna. Did Curiosity kill Tuna? In HyLogic the premises are written as formulas in [Hy](https://hylang.org) and handed to the prover.

```hy
(import hylogic.resolution [prove])

(setv premises
  ['(exists [x] (and (Dog x) (Owns jack x)))
   '(forall [x] (=> (exists [y] (and (Dog y) (Owns x y)))
                    (AnimalLover x)))
   '(forall [x] (=> (AnimalLover x)
                    (forall [y] (=> (Animal y) (not (Kills x y))))))
   '(or (Kills jack tuna) (Kills curiosity tuna))
   '(Cat tuna)
   '(forall [x] (=> (Cat x) (Animal x)))])

(print (.join "\n" (.proof (prove '(Kills curiosity tuna) premises))))
```

HyLogic prints the proof with every step and the lines it came from. Lines 1, 2, 5, 6, 8, 9 and 10 are the premises in clause form, and these are the steps that follow from them.

```
   3. (not (Kills curiosity tuna))     negated goal
   4. (Kills jack tuna)                simplification 2, 3
   7. (Animal tuna)                    resolve 5, 6
  11. (AnimalLover jack)               resolve+unit deletion 8, 9, 10
  12. □                                resolve+unit deletion 1, 4, 7, 11
```

Read from line 3. If Curiosity did not kill Tuna, Jack did (line 4). Tuna is a cat and so an animal (line 7). Jack owns a dog, so he loves animals (line 11). Animal lovers kill no animals, so line 12 is a contradiction, marked by the empty clause □, and Curiosity did it.

A prover is also a place where a Lisp still earns its keep. Formulas are trees, and in Hy a formula is simply quoted code, as in the premises above. The program receives it as data and can take it apart, transform it and prove things about it without a parser. I first wrote HyLogic in 2017, and this year rewrote it and measured it against real provers.

## Result 1. Methods mattered, speed hardly did

The benchmark is a fixed sample of 274 problems from TPTP with at most 50 formulas each, drawn with a fixed seed across easy and hard problems, with and without equality. 234 are theorems and 40 are not. Each prover gets ten seconds per problem on the same machine. The first version of HyLogic proved 39 of the theorems.

HyLogic is measured against two of the strongest automated provers. [E](https://www.eprover.org), written by Stephan Schulz and developed since the late 1990s, is built around superposition and is known for its fast rewriting and for choosing a search strategy to suit each problem. [Vampire](https://vprover.github.io), developed by Andrei Voronkov at the University of Manchester together with Laura Kovács's group at TU Wien, had won the main first-order division of [CASC](https://tptp.org/CASC/), the annual competition of automated provers, [fourteen years in a row by 2013](https://staffnet.cs.manchester.ac.uk/newsletters/CS_Newsletter_2013-07-01.htm), and in 2025 it became [the first prover to win all of the competition's divisions](https://www.tuwien.at/en/tu-wien/news/news-articles/news/riesenerfolg-fuer-vampire). Both are written in C or C++ and tuned on TPTP itself, so they set a high bar for a prover written to be read.

| Method | Theorems added |
|---|---:|
| First version, plain resolution | 39 |
| Fair choice of the next clause, by age as well as size | +9 |
| Superposition for equality, with ordered resolution | +28 |
| Naming subformulas, indexing, deciding problems without functions by SAT | +10 |
| A search that stays close to the goal | +11 |
| Ground problems decided by a SAT solver | +7 |
| Ground equality decided by congruence closure | +6 |
| Simplification as E does it | +11 |
| Splitting clauses before grounding them | +22 |
| A schedule of two search strategies | +13 |
| Smaller steps | +5 |
| HyLogic now | 161 |

*What each method added, in theorems proved of 234 within ten seconds.*

Each change was measured on its own and kept only if it helped. The largest single step was superposition with ordered resolution. [Superposition](https://en.wikipedia.org/wiki/Superposition_calculus) is how E and Vampire handle equality, by replacing equals with equals inside terms. Ordering allows only inferences on the largest literals of each clause, so the search grows far more slowly without missing proofs, a result due to [Leo Bachmair and Harald Ganzinger](https://doi.org/10.1093/logcom/4.3.217).

The second largest step came from an unexpected place. Twenty-one theorems that E proved and HyLogic did not belonged to one family, [description logic](https://en.wikipedia.org/wiki/Description_logic) translated into first-order logic. They have no functions, so replacing every variable by every constant turns them into a propositional problem that a [SAT solver](https://en.wikipedia.org/wiki/SAT_solver) decides. With 53 constants, though, a clause with three variables has 148,877 instances, too many to write down. The variables of those clauses never occur together in one statement, so each clause splits into parts with one variable each and 53 instances apiece, a technique from the Paradox model finder by Koen Claessen and Niklas Sörensson. HyLogic now decides each of these problems in a few hundredths of a second, where E needs a third of one.

Speed did little. With twenty seconds instead of ten, HyLogic proved 5 more theorems. [PyPy](https://pypy.org), a faster Python, ran the search 1.8 times faster, but it spent two of every ten seconds loading HyLogic, so it proved only 2 more theorems. The gains came from doing less work, not from doing the same work faster.

## Result 2. Two thirds of the way to E, and ahead on counterexamples

| | Theorems, of 234 | Non-theorems, of 40 | Held-out theorems, of 200 |
|---|---:|---:|---:|
| HyLogic, first version | 39 | 18 | |
| HyLogic now | 161 | 31 | 141 |
| Lean's `grind`, on HyLogic's export | 53 | | |
| E 3.2.5 | 207 | 16 | 189 |
| Vampire 5.1.0 | 231 | 20 | 197 |

*Problems solved within ten seconds each. Vampire shows 36 of the non-theorems with its schedule for finding models.*

Lean's `grind` in the table is a different kind of tool. Lean is a proof assistant, where people write proofs and Lean checks them, and `grind` is its newest automation, a tactic in the style of [SMT solvers](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) that closes goals by reasoning with equality and by case analysis. Given each problem as a Lean theorem, it proves 53 in ten seconds and 103 in twenty.

Every change was tuned on the same 274 problems, so I drew 240 new ones with another seed as a check, none of them seen before. HyLogic proved 141 of their 200 theorems, about the same share as on the first sample, and gave no wrong answer, so the tuning had not simply fitted the sample.

A non-theorem is shown by a countermodel, a small world where every premise is true and the conclusion false. HyLogic finds them the way Paradox does, by asking a SAT solver for a world of one element, then two, and so on. It shows 31 of the 40, more than E and more than Vampire in its theorem-proving mode, though Vampire shows 36 when it is set up for finding models.

Most of the remaining distance in theorems lies in reasoning with equality. Here is a small problem from group theory, GRP703+1, where the goal says that a constant op_e associates with everything. Line 1, the three goal equations negated, is left out, and the variable names are shortened.

```
   2. (= op_e (mult (mult (rd op_c (mult ?A ?B)) ?B) ?A))  axiom
   3. (= (mult ?A unit) ?A)         axiom
   4. (= (mult unit ?A) ?A)         axiom
   5. (= (mult (rd ?A ?B) ?B) ?A)   axiom
   6. (= op_e op_c)                 superposition+demod 2, 3, 4, 5
  10. □                             simplification 1, 6, 7, 8, 9
```

Line 6 is the step a person would look for. Putting unit for both variables of axiom 2 and simplifying with axioms 3 to 5 shows that op_e is the element op_c, and lines 7 to 9 say that op_c associates, which settles all three goals at once. E finds this in a hundredth of a second. HyLogic timed out on it until it learned to rewrite the clauses it had already used with every new equation. The rest of the distance is decades of tuned search strategy in E and Vampire, which a prover meant to be read has no reason to copy. HyLogic can instead hand a problem to E or Vampire, read the proof it prints and show it in the same numbered form, which worked for all 440 proofs they produced.

## Result 3. The benchmark found the bugs, not the tests

A prover that says "proved" when the conclusion does not follow is worse than no prover. HyLogic has over 200 tests, and none of them found the six bugs that could make it give a wrong answer. The benchmarks found four, and reading the code they pointed to found the other two.

- **A choice that depended on names.** Ordered resolution must pick the same literal of a clause every time. HyLogic's choice depended on the names of the variables, which change as clauses are copied, so the search could miss a proof and call a theorem unprovable.
- **One constant with two values.** The SAT encoding for finite algebra problems said that a constant had a value, but not that it had no other, so five theorems got false counterexamples.
- **Objects that are different by definition.** TPTP writes names in double quotes for objects that are distinct, so "Apple" and "Microsoft" can never be equal. Only one of HyLogic's methods knew it, and another found a world where they were. The sample drawn as a check exposed this one.
- **Searches that claimed too much.** Running each of HyLogic's methods on its own over 3,781 further TPTP problems caught a bounded search for models reporting "no model, so proved" when it had searched nothing. Reading that code showed two more ways the same kind of search could claim a proof too soon. HyLogic itself never gave those answers, because another method answered first, but the order of the methods was hiding the bugs.

Each now has a test that fails on the old code. The lesson is an old one. A wide sample of real problems tests the combinations that nobody thinks to write a test for.

## Result 4. Lean checks every step

Tests and benchmarks give confidence, but a proof checked by an independent system gives more. [Lean](https://lean-lang.org), created by Leonardo de Moura, is a proof assistant with a small trusted core that checks every proof it is given, and mathematicians use it to formalize research mathematics in its library [Mathlib](https://github.com/leanprover-community/mathlib4). HyLogic now writes each step of a proof as a small Lean theorem saying that the step's premises imply its conclusion. This is line 11 of the Tuna proof, that Jack loves animals.

```lean
theorem «$s11»
    («$h1» : ∀ «?x2» «?y3» : «$U»,
      («AnimalLover» «?x2») ∨ ¬(«Dog» «?y3») ∨ ¬(«Owns» «?x2» «?y3»))
    («$h2» : («Owns» «jack» «sk1»))
    («$h3» : («Dog» «sk1»)) :
    («AnimalLover» «jack») := by
  have «$i1» := «$h1» «jack» «sk1»
  grind
```

The work is shared. HyLogic says which values the rule was applied to, Jack and Jack's dog, and Lean's automation `grind` checks the rest. Without that hint `grind` cannot always choose the values itself, and it verified 131 of 160 proofs. With it, Lean verified all 161 proofs the benchmark produced and all 13,180 of their steps, including the steps of proofs found by the SAT solver, and a final theorem for each proof that chains the steps into a contradiction. Not one step was wrong.

One stage stays outside the check. Turning a formula into clauses introduces [Skolem constants](https://en.wikipedia.org/wiki/Skolem_normal_form), such as `sk1` for "Jack's dog", and a clause with one does not follow from its formula, it is only satisfiable whenever the formula is. Lean takes the clauses as given and checks everything from there to the contradiction.

## Result 5. For agents, a final check rather than a shortcut

AI agents reason in plain language and get it wrong now and then. HyLogic has an [MCP](https://modelcontextprotocol.io) tool, `check_argument`, so that an agent can write premises and a conclusion as formulas and have them checked. A valid argument comes back with the premises it needs, and an invalid one with a counterexample.

```
check_argument(premises=["(=> P Q)", "Q"], conclusion="P",
               meanings={"P": "it rains", "Q": "the street is wet"})

INVALID (checked by truth table)
Read as: P → Q; Q ⊢ P
Counterexample: “it rains” is false and “the street is wet” is true.
Then every premise is true and the conclusion is false.
```

To see whether agents judge better with it, I generated arguments in everyday English, each decided by both HyLogic and [Z3](https://github.com/Z3Prover/z3), an SMT solver from Microsoft Research that decides formulas mixing logic with arithmetic and other theories, and gave each one to a model once without the tool and once with it. The first round had 70 short arguments with the wording people often misread, such as "only if" and "unless". This one looks valid and is not, because the door may be locked.

> Unless the door is locked, the dog is outside. It is not the case that the alarm is set. The window is open if the alarm is set. Therefore, the dog is outside.

The second round had 40 arguments about people in an office with 25 premises each, among them distractors. A valid chain needed two steps backwards from a negative fact and two case splits, and half the arguments were broken by one change, such as a rule turned around. This is one of the broken ones, in full.

> Everyone who attends the Monday meeting mentors a trainee. Everyone who is a manager can see the payroll. Everyone who is an engineer uses the VPN or can enter the lab, or both. No one who works the night shift speaks Finnish. Everyone who is not on call this week has a badge. Anyone who reports to someone who reports to a third person also reports to that third person. No one who mentors a trainee has a key to the archive. No one who works remotely has a company laptop. Everyone who has a badge has a parking space or has done the safety training, or both. Everyone who mentors a trainee attends the Monday meeting. Everyone who has done the safety training is a manager. Everyone who speaks Finnish works the night shift. Everyone who is not a team lead is an engineer. Everyone who does not speak Finnish works the night shift. Ben attends the Monday meeting. Everyone who has a parking space is a manager. Everyone who uses the VPN is in the union. Everyone who has a key to the archive is a team lead. Everyone who can enter the lab is in the union. David reports to Eva. Everyone who reports to someone who is in the union works remotely. Everyone who is on call this week has a company laptop. Ben reports to David. Eva reports to Farid. Farid attends the Monday meeting. Therefore, David can see the payroll.

The chain runs through Farid, who attends the Monday meeting, so he mentors a trainee and has no key to the archive. To conclude that he is therefore not a team lead, it needs "every team lead has a key to the archive", but the argument says it the other way round. From there the chain would have gone on, through being an engineer, the union and David reporting to Farid by way of Eva, to working remotely, having a badge and finally seeing the payroll. All 110 arguments, the scripts that made them, the hypotheses written before the runs and the results are in the [field test folder](https://github.com/markomanninen/hylogic/tree/master/benchmarks/field_test), the short ones in [items.json](https://github.com/markomanninen/hylogic/blob/master/benchmarks/field_test/items.json) and [items_hard.json](https://github.com/markomanninen/hylogic/blob/master/benchmarks/field_test/items_hard.json) and the long ones in [items_fo_hardest.json](https://github.com/markomanninen/hylogic/blob/master/benchmarks/field_test/items_fo_hardest.json).

| | Without the tool | With the tool | Cost with the tool |
|---|---:|---:|---:|
| Short arguments, Claude Haiku | 67 of 70 | 69 of 70 | 1.7 times |
| Short arguments, Claude Opus | 70 of 70 | 70 of 70 | 1.6 times |
| 25 premises, Claude Haiku | 38 of 40 | 40 of 40 | 1.7 times |

*Generated arguments, each judged once per model and condition.*

The models were far better than I expected. On the long arguments Haiku worked through each chain at length, about 12,000 tokens an argument, and was right 38 times. Both of its errors fell on a rule turned around. Once, on the argument above, it used the reversed rule as if it were the one the chain needed, and once it decided that the premises contradicted each other, which they do not, and called the argument valid for that reason. With the tool it got all 40, but it did not reason any less. It worked the chain out first, wrote the formulas and called the tool once as a final check, and in 36 of 41 calls it asked for the whole proof.

So a model that reasons step by step is almost as accurate as the checker on problems of this size. What the checker adds is certainty. Its answer comes with a proof or a counterexample that anyone can check, and with `certify=true` Lean checks the proof as well. The remaining risk moves to the formulas the model writes, since a checker can only check what it is given.

## What I take from this

1. **Measure each method on its own.** Superposition and clause splitting each added more than doubling the speed would have.
2. **Study the problems the strong provers solve and yours does not.** One family of 21 such problems pointed to a technique that added 22 theorems.
3. **Test on problems you did not tune on.** A second sample, and a sweep over thousands of problems, found bugs that 200 tests had not.
4. **Let an independent checker check the prover.** Lean accepted every step, and now it does so for every proof HyLogic finds, not only for the ones I looked at.
5. **Readable output pays off twice.** The same numbered proofs that people can follow became the hints that let Lean check them.
6. **For agents, a checker adds certainty more than accuracy.** A model reasoning step by step was right 95 times in 100 on long chains. The checker made it 100 and showed why.

## Limits, and trying it yourself

The benchmark is 274 problems of at most 50 formulas each, with ten seconds each on one machine, a small corner of what E and Vampire are built for. The check sample of 240 problems lacks the hardest theorems without equality, because the first sample had already taken all of them. Lean checks every step from the clauses on, but not the translation from formulas into clauses. The second field test used Haiku alone, and two errors in forty are too few to measure the tool's gain precisely. HyLogic is a prover to read and learn from. For hard problems E and Vampire are the tools, and for mathematics Lean.

HyLogic installs with `pip install hylogic`. `hy examples/tour.hy` walks through truth tables, arguments, rewriting and proofs, and `python -m hylogic.tptp FILE` runs the prover on a TPTP problem and prints its proof. The benchmarks, with their plans, every measured step and the scripts to rerun them, are in the [repository](https://github.com/markomanninen/hylogic/tree/master/benchmarks), and `hylogic-mcp` gives an agent the `check_argument` tool.

GitHub: [hylogic](https://github.com/markomanninen/hylogic)

## Sources

- J. A. Robinson, [A Machine-Oriented Logic Based on the Resolution Principle](https://doi.org/10.1145/321250.321253), Journal of the ACM, 1965.
- L. Bachmair and H. Ganzinger, [Rewrite-based Equational Theorem Proving with Selection and Simplification](https://doi.org/10.1093/logcom/4.3.217), Journal of Logic and Computation, 1994.
- G. Sutcliffe, [The TPTP Problem Library and Associated Infrastructure](https://doi.org/10.1007/s10817-017-9407-7), Journal of Automated Reasoning, 2017, and [tptp.org](https://www.tptp.org).
- S. Schulz, E, a Brainiac Theorem Prover, AI Communications, 2002, and [the E prover](https://www.eprover.org).
- L. Kovács and A. Voronkov, [First-Order Theorem Proving and Vampire](https://doi.org/10.1007/978-3-642-39799-8_1), CAV 2013, and [Vampire](https://vprover.github.io).
- K. Claessen and N. Sörensson, New Techniques that Improve MACE-style Finite Model Finding, 2003, the Paradox model finder.
- N. Eén and N. Sörensson, [An Extensible SAT-solver](https://doi.org/10.1007/978-3-540-24605-3_37), SAT 2003, the MiniSat design HyLogic's SAT solver follows.
- R. Nieuwenhuis and A. Oliveras, [Proof-Producing Congruence Closure](https://doi.org/10.1007/978-3-540-32033-3_33), RTA 2005.
- L. de Moura and S. Ullrich, [The Lean 4 Theorem Prover and Programming Language](https://doi.org/10.1007/978-3-030-79876-5_37), CADE 2021, and [lean-lang.org](https://lean-lang.org).
- F. J. Pelletier, [Seventy-five problems for testing automatic theorem provers](https://doi.org/10.1007/BF02432151), Journal of Automated Reasoning, 1986.
- [Z3](https://github.com/Z3Prover/z3), the solver used to check the field test's arguments.
