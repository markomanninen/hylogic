# Closing the gap to real provers

Started 15 October 2026 on the `prover-gap` branch. The question is how much
of the distance between HyLogic's resolution prover and E and Vampire can be
closed, and how. Each step is measured on the same TPTP problems before the
next one starts, and every result is checked against the problem's known
status.

## The four steps

1. **Measure the gap.** A fixed sample of TPTP problems, run with HyLogic, E
   3.2.5 and Vampire 5.1.0 under the same time limit.
2. **Improve the search**, one change at a time, measuring after each:
   fair clause selection, definitional clause form, equality, ordered
   resolution with literal selection, and term indexing.
3. **Bridge to E and Vampire.** Run them from HyLogic when they are installed,
   read their proofs, and present them the HyLogic way.
4. **Lean export.** Write problems as Lean 4 theorems and see how many of
   them Lean accepts, and proves with its own automation.

## The sample

`draw_sample.py` draws a fixed sample from TPTP v9.3.1 FOF problems with at most
50 formulas, with a fixed random seed:

| | Rating 0.00 | Rating 0.01 to 0.20 | Rating 0.21 to 0.50 |
|---|---:|---:|---:|
| Theorems without equality (NEQ) | 40 | 40 | 34 |
| Theorems with equality (SEQ, PEQ) | 40 | 40 | 40 |

Only 34 small NEQ theorems exist in the highest band, so all of them are
used. 40 CounterSatisfiable problems, where the conjecture does not follow,
serve as a soundness check: no prover may ever report one of them as a
theorem.

The TPTP rating is the share of state-of-the-art provers that failed on the
problem in the TPTP tests, so 0.00 means every one of them solved it, with a
much longer time limit than here.

Every prover gets 10 seconds of wall-clock time per problem, one problem per
process, 8 processes in parallel, on Apple Silicon.

## Hypotheses, written before measuring

| Step | Expected |
|---|---|
| Baseline | HyLogic solves 30 to 45 % of rating-0 NEQ theorems, under 15 % at 0.01 to 0.20, a few above. Of the equality theorems, 5 to 15 % at rating 0, the ones that need no equality reasoning, and nearly none above. E and Vampire solve nearly all rating-0 problems and most of the rest. |
| Fair selection | 5 to 15 more solved problems, mostly NEQ |
| Definitional clause form | a few more, where nested equivalences blow up |
| Equality axioms | some equality theorems, 5 to 10 % more of them |
| Superposition and demodulation | two to three times as many equality theorems as with axioms |
| Ordered resolution and selection | far fewer generated clauses, 10 to 20 % more solved overall |
| Term indexing | 2 to 5 times faster on large searches, 5 to 10 % more solved |
| Bridge | HyLogic with Vampire solves what Vampire solves, and shows at least 90 % of its proofs |
| Lean export | at least 95 % of the exported theorems type-check in Lean |

No step may make HyLogic report a CounterSatisfiable problem as a Theorem,
or a Theorem as CounterSatisfiable.

## Results

Problems solved within 10 seconds. A theorem counts when the prover reports
Theorem; a CounterSatisfiable problem counts when it reports
CounterSatisfiable. "Wrong" counts answers that contradict the known status.

| Step | NEQ r0 | NEQ r1 | NEQ r2 | EQ r0 | EQ r1 | EQ r2 | Non-theorems | All | Wrong |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Vampire 5.1.0 (`--mode casc`) | 40 | 40 | 33 | 40 | 40 | 38 | 20 | 251 | 0 |
| E 3.2.5 (`--auto`) | 40 | 38 | 22 | 39 | 40 | 28 | 16 | 223 | 0 |
| HyLogic, baseline | 22 | 2 | 0 | 9 | 6 | 0 | 18 | 57 | 0 |
| Fair selection, age ratio 1 | 23 | 2 | 0 | 8 | 9 | 0 | 18 | 60 | 0 |
| Fair selection, age ratio 3 | 23 | 2 | 0 | 10 | 11 | 0 | 18 | 64 | 0 |
| Fair selection, age ratio 5 | 23 | 2 | 0 | 11 | 11 | 0 | 18 | 65 | 0 |
| Fair selection, age ratio 10 | 24 | 2 | 0 | 11 | 11 | 0 | 18 | 66 | 0 |
| Definitional clause form, threshold 8 or 64 | 22 | 2 | 0 | 9 | 6 | 0 | 18 | 57 | 0 |
| Equality axioms | 22 | 2 | 0 | 8 | 2 | 0 | 15 | 49 | 0 |
| Superposition | 22 | 2 | 0 | 12 | 10 | 0 | 18 | 64 | 0 |
| Fair 10 + superposition + ordered resolution | 28 | 4 | 0 | 17 | 25 | 2 | 18 | 94 | 0 |
| + feature indexing | 29 | 4 | 0 | 18 | 25 | 3 | 18 | 97 | 0 |
| + definitional clause form | 31 | 5 | 0 | 20 | 26 | 3 | 18 | 103 | 0 |
| + EPR grounding (the new defaults) | 31 | 5 | 0 | 21 | 26 | 3 | 18 | 104 | 0 |

Out of 40 (34 for NEQ r2).

## Log

**Baseline.** HyLogic proved 39 of the 234 theorems and timed out on 190
problems; Vampire proved 231 and E 207. The rating-0 rows were better than
expected (22 of 40 without equality, 9 of 40 with), everything above them
worse. On the non-theorems HyLogic nearly matched Vampire, 18 against 20,
because the finite model finder settles small counter-satisfiable problems
quickly. The median HyLogic run used the whole 10 seconds, Vampire's took
0.04 seconds.

**Step 2, round 1: one change at a time.** Fair selection helped a little,
more with more weight on age: 66 at ratio 10, nine more than the baseline,
mostly equality problems (the hypothesis said NEQ). Definitional clause form
changed nothing, because these small problems have no nested equivalences to
blow up; on Andrews' challenge it cut the clauses from 1,296 to 47 but made
the search slower. Equality axioms made things worse, 49, as the textbooks
warn: they resolve with almost everything. Superposition alone gave 64, seven
more, all of them equality theorems.

**Step 2, round 2: together.** Ordered resolution with literal selection is
the change that mattered most: with fair selection and superposition it
lifted the total to 94, and the rating 0.01 to 0.20 equality theorems from 6
to 25. Feature indexing added 3 more by saving time, and definitional clause
form 6 more once the rest was in place: 103 in all, 81 more theorems than the
baseline's 39 plus the same 18 non-theorems. No step gave a wrong answer.

Two bugs turned up on the way and were fixed: matching applied with chained
substitution looped when a rule and a term shared variable names, and the
model finder built every function interpretation before checking its time
limit. A third failure was not in HyLogic: a zsh command passed all options
as one argument, so the first round 2 run failed on every problem.

**Step 2, round 3: grounding.** Function-free problems can be decided exactly
by substituting every constant for every variable and handing the result to
the SAT solver. It added one problem, not the thirteen EPR problems still
open: those algebra problems are EPR in TPTP's sense because an axiom limits
the domain to their constants, but they have functions, so grounding over
constants alone does not apply. A Paradox-style model finder that turns
functions into predicates is the method for them, and is left for later.

**Step 3: the bridge.** `hylogic.external` runs E or Vampire on a problem and
reads the proof they print in TSTP, the TPTP proof format, into HyLogic's
numbered steps with rules and parents; E's nested inferences are unwrapped
into chains such as `cn ∘ rw ∘ spm`. On the sample, Vampire proved 231
problems and E 209, every one of them printed a proof, and HyLogic read all
of them to the final contradiction: 100 % against a target of 90 %. With the
bridge, HyLogic solves what Vampire solves and still shows the proof its own
way.

**Step 4: Lean.** `hylogic.lean` writes a problem as a Lean 4 theorem over an
arbitrary nonempty type, with predicates as functions into Prop, and checks
it with Lean 4.35.0. The first runs failed on name clashes, which guillemets
did not prevent because «U» and U are the same name in Lean: TPTP variables
named U clashed with the domain type, and TPTP functions named h1 with the
hypotheses. After renaming both with a $, which no TPTP name can start with,
and raising Lean's recursion limit for the largest formulas, all 274
statements type-check (target 95 %). Lean's own automation, `grind`, proved
103 of the 234 theorems within 20 seconds and none of the non-theorems.

## Where the gap stands

| Theorems proved, of 234 | |
|---|---:|
| HyLogic, baseline | 39 |
| HyLogic, with the step 2 improvements | 86 |
| Lean 4.35 `grind`, on HyLogic's export | 103 |
| HyLogic or Lean | 134 |
| E 3.2.5 | 207 |
| Vampire 5.1.0, and HyLogic through the bridge | 231 |

HyLogic's own prover more than doubled, from 39 to 86 theorems, with fair
selection, superposition, ordered resolution, feature indexing, definitional
clause form and grounding, and it never gave a wrong answer. It is still far
from E and Vampire: in Python, and without their decades of strategy tuning,
it times out on most harder problems. Lean's automation is a useful second
opinion with different strengths: only 55 theorems were proved by both, and
Lean proved 14 of the hardest NEQ theorems where HyLogic proved none.
Neither proved anything Vampire did not.

The gap closes in practice through the bridge: HyLogic hands the problem to
Vampire, reads the proof, and presents it as its own, which it did for every
one of the 440 proofs in the sample.

Left for later: a Paradox-style finite model finder for the EPR algebra
problems, better clause selection heuristics, and proper term indexing.
