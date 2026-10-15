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

Out of 40 (34 for NEQ r2).

## Log

**Baseline.** HyLogic proved 39 of the 234 theorems and timed out on 190
problems; Vampire proved 231 and E 207. The rating-0 rows were better than
expected (22 of 40 without equality, 9 of 40 with), everything above them
worse. On the non-theorems HyLogic nearly matched Vampire, 18 against 20,
because the finite model finder settles small counter-satisfiable problems
quickly. The median HyLogic run used the whole 10 seconds, Vampire's took
0.04 seconds.
