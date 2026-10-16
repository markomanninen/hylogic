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

## Round two: the items left for later

Started on the `prover-gap-2` branch, the same sample and time limit.

| Change | Expected |
|---|---|
| Finite model finder in the Paradox style: functions flattened into predicates with totality and functionality clauses, models searched with SAT for growing domain sizes. For problems whose axioms bound the domain (the EPR algebra problems), no model up to the bound means a theorem | most of the 13 unsolved EPR theorems, and a few more non-theorems |
| Goal-directed clause selection: prefer clauses descended from the negated goal, as the set-of-support idea and E's heuristics do | 5 to 15 more theorems, mostly NEQ |
| Term indexing for unification and subsumption candidates | faster searches, a few more theorems at the margin |

### Results of round two

| Step | NEQ r0 | NEQ r1 | NEQ r2 | EQ r0 | EQ r1 | EQ r2 | Non-theorems | All | Wrong |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Round one's defaults | 31 | 5 | 0 | 21 | 26 | 3 | 18 | 104 | 0 |
| + flattening model finder, prover keeps 80 % of the time | 31 | 5 | 0 | 21 | 26 | 3 | 20 | 106 | 0 |
| + goal-directed selection, bias 3 | 31 | 5 | 0 | 20 | 29 | 7 | 20 | 112 | 0 |
| + goal-directed selection, bias 6 (the new default) | 31 | 5 | 2 | 19 | 31 | 9 | 20 | 117 | 0 |
| + goal-directed selection, bias 10 | 31 | 5 | 1 | 21 | 30 | 7 | 20 | 115 | 0 |
| Bias 6 + symbol filter, cheaper superposition and grounding | 31 | 5 | 2 | 19 | 31 | 9 | 20 | 117 | 0 |
| The same with 20 seconds instead of 10 | 31 | 5 | 2 | 20 | 31 | 9 | 20 | 118 | 0 |
| + portfolio, 50 % main search, then plain resolution | 30 | 5 | 2 | 20 | 30 | 9 | 20 | 116 | 0 |
| + portfolio, 65 % main search | 31 | 5 | 2 | 19 | 32 | 9 | 20 | 118 | 0 |
| + portfolio, 80 % main search (the new default) | 31 | 5 | 2 | 19 | 32 | 9 | 20 | 118 | 0 |

**Finite models.** The flattening model finder (`hylogic.finite`, after
Paradox) did not solve the EPR algebra problems: they are ground problems
with functions defined only on the constants of one algebra, so neither a
domain axiom nor closure under the functions bounds their models, and
deciding them needs ground equality reasoning (congruence closure inside the
SAT search, as in Z3), which is a larger piece of work. As a model finder it
pays off: it finds 17 of the 40 countermodels, the old finder 18, and the two
together 20, as many as Vampire. Giving it more time at the prover's expense
cost two theorems, so the prover keeps 80 % of the time and the finders
share the rest.

**A soundness bug.** The first goal-directed runs answered
CounterSatisfiable for SWB020+2, a theorem. The prover had saturated without
a proof: ordered resolution chose the selected literal by size with ties
broken by the printed literal, which includes variable names, and a partner
clause was renamed before its eligible literals were computed, so one clause
could select different literals at different times. Ordered resolution is
complete only with a fixed selection. Eligibility is now computed before
renaming, every combination proves SWB020+2, and a regression test covers
it. The earlier rounds had no wrong answers, so their numbers stand.

**Goal-directed selection.** Making clauses that do not descend from the
negated goal look heavier (6/2 = 3 times) kept the search near the goal and
helped where the hypothesis did not expect it: the harder equality theorems,
from 26 to 31 and from 3 to 9, not the NEQ ones.

**Speed and indexing.** Profiling the problems that still time out showed
three kinds of waste, none of them the classic indexing case: superposition
renamed the partner clause before noticing there was no equation to use,
grounding spent up to half the time on problems too large for it, and
subsumption compared clauses that could not match. Fixing these let the
prover keep about 20 % more clauses in the same time, and solved no new
problem. Doubling the time limit to 20 seconds solved one. So a faster
implementation, term indexing included, would add at most a problem or two
at this size: the bottleneck is the search strategy, not speed.

**Portfolio.** The 24 HyLogic runs together solved 126 problems, nine more
than the best single setting, so the settings fail on different problems.
The best pair was the default and plain resolution with fair selection, no
ordering, no superposition: ordering prunes away some proofs that plain
resolution finds at once. Running the default first and plain resolution
with the time left added one problem.

## Where the gap stands after round two

| Theorems proved, of 234 | |
|---|---:|
| HyLogic, baseline | 39 |
| HyLogic after round one | 86 |
| HyLogic after round two | 98 |
| Lean 4.35 `grind`, on HyLogic's export | 103 |
| HyLogic or Lean | 141 |
| E 3.2.5 | 207 |
| Vampire 5.1.0, and HyLogic through the bridge | 231 |

and 20 of the 40 non-theorems shown with countermodels, as many as Vampire
(E: 16). Round two's biggest gain came from goal-directed selection, and it
found and fixed a real soundness bug. The remaining distance to E and
Vampire is strategy: decades of tuned heuristics, clause splitting and
large strategy schedules, which this study does not attempt to copy.

## Round three: the algebra theorems

The thirteen unsolved EPR theorems were finite algebra problems: ground
clauses, no variables, with operations tabulated on named elements, and
questions about those tables. Neither resolution nor grounding over
constants fits them. Two additions did:

| Step | NEQ r0 | NEQ r1 | NEQ r2 | EQ r0 | EQ r1 | EQ r2 | Non-theorems | All | Wrong |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Round two's defaults | 31 | 5 | 2 | 19 | 32 | 9 | 20 | 118 | 0 |
| + ground decision with SAT | 31 | 5 | 2 | 23 | 32 | 9 | 20 | 122 | 0 |
| + CDCL instead of DPLL (first run) | 31 | 5 | 2 | 26 | 32 | 9 | 23 | 128 | **5** |
| + the encoding fixed | 31 | 5 | 2 | 26 | 32 | 9 | 23 | 128 | 0 |

**Ground decision** (`hylogic.ground`). Every ground term gets a value
variable in a domain {1..n}, functions share one table each, and equality
literals become auxiliary variables. When every term is forced to equal a
constant, through closure clauses such as `op(e1, e2) = e0 | ... | = e4` and,
for nested terms, through the values their arguments can take, no model up to
the number of constants proves the problem. On 500 random ground problems it
agreed with Z3 every time. It decided 10 of the 17 algebra problems; the
other 7 are about isomorphisms whose mapping functions are defined only on
part of the elements, so their bound grows to hundreds and they stay open.

**CDCL** (`hylogic.cdcl`). The DPLL solver scanned every clause on every
step. A conflict-driven clause learning solver with two watched literals,
first-UIP learning, backjumping, VSIDS and restarts agreed with DPLL on 600
random instances and was 7 times faster on pigeonhole 8->7 and over 100
times faster on random 3-SAT with 160 variables. The algebra problems went
from 9 seconds to 0.3, and the model finders, which use the same solver, now
show 23 non-theorems, more than the 20 Vampire shows in its theorem-proving
mode. That comparison flatters HyLogic: in its satisfiability schedule
(`--mode portfolio --schedule casc_sat`) Vampire shows 36 of the 40, and its
finite model builder alone (`-sa fmb`) 34. The baseline runs used the
theorem-proving mode for every problem, which is the right setting for the
theorems but not for the non-theorems.

**A soundness bug, again found by the benchmark.** The first CDCL run
reported five isomorphism theorems as CounterSatisfiable. A constant fixed to
its own element (symmetry breaking) got the clause "has value k" but not "has
no other value", so in a larger domain it could take two values, and the SAT
solver found a "model". DPLL had hidden this by timing out first. Constants
now get exactly one value, and every model is checked against the original
clauses before it is reported. The random comparison with Z3 had not caught
it, because its domains stay small, so ALG105+1 itself is now a regression
test. The export to SMT-LIB and TPTP also turned out to declare = as an
ordinary predicate, so the Z3 check failed on every problem with equality;
it is now SMT-LIB's and TPTP's own equality.

## Where the gap stands after round three

| | Theorems, of 234 | Non-theorems, of 40 |
|---|---:|---:|
| HyLogic, baseline | 39 | 18 |
| HyLogic after round one | 86 | 18 |
| HyLogic after round two | 98 | 20 |
| HyLogic after round three | 105 | 23 |
| Lean 4.35 `grind`, on HyLogic's export | 103 | |
| E 3.2.5 | 207 | 16 |
| Vampire 5.1.0 (`casc`), and HyLogic through the bridge | 231 | 20 |
| Vampire 5.1.0, satisfiability schedule (`casc_sat`) | | 36 |
| Vampire 5.1.0, finite model builder only (`-sa fmb`) | | 34 |

## Round four: exact ground equality and smaller models

Round three left the isomorphism problems and two thirds of the gap in
non-theorems. Four changes closed most of both, each measured on its own.

| Step | NEQ r0 | NEQ r1 | NEQ r2 | EQ r0 | EQ r1 | EQ r2 | Non-theorems | All | Wrong |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Round three's defaults | 31 | 5 | 2 | 26 | 32 | 9 | 23 | 128 | 0 |
| + SAT with congruence closure, 30 % of the time | 31 | 5 | 2 | 30 | 32 | 9 | 23 | 132 | 0 |
| + 256 lemmas per round, 75 % of the time | 31 | 5 | 2 | 32 | 32 | 9 | 23 | 134 | 0 |
| + clause splitting, inner Skolemization, scoped definitions | 31 | 6 | 2 | 32 | 32 | 9 | 27 | 139 | 0 |
| + model search first, 15 % of the time | 31 | 6 | 3 | 32 | 32 | 9 | 30 | 143 | 0 |
| + model search first, 30 % (the new default) | 31 | 6 | 3 | 32 | 32 | 9 | 31 | 144 | 0 |
| + model search first, 50 % | 31 | 4 | 3 | 32 | 32 | 9 | 31 | 142 | 0 |

**Ground equality decided exactly** (`hylogic.euf`). Equality with
uninterpreted functions is decidable for ground clauses, with no bound on
the domain. The SAT solver proposes truth values for the equations, a
congruence closure checks them, and each violated equation comes back as a
lemma whose premises are read off the closure's merge history (a proof
forest). This is how SMT solvers such as Z3 work. It agreed with Z3 on 500
random problems, and the CDCL solver learned to take new clauses between
calls so that lemmas no longer rebuild it. The isomorphism problems that
round three's bounded search could not reach fell one by one, from minutes
to under a second for most of them. Six of the seven are solved in the
10 seconds. ALG026+1, where both group tables are unknown, needs about 16.

**Smaller models.** The model finder failed on non-theorems whose models
have two elements, which Vampire finds in milliseconds. The clauses were too
wide to ground. Three changes narrowed them from up to 76 variables to 3.
Clause splitting turns A ∨ B, whose parts share the variables I, into
A ∨ s(I) and ¬s(I) ∨ B, as Paradox does. Skolem functions now take only the
universal variables free under their quantifier, which cut their arity from
21 to 1 on the modal logic problems. Definitions introduced to keep the
clause form small took every variable of the named part, including those
bound inside it; they now take only its free variables. All three preserve
satisfiability over the same domain, so a model found is a model of the
problem.

**Model search first.** The finders ran last, on what resolution left, so
models that take half a second were missed. A short search before resolution
found them. At 30 % of the time no theorem was lost; at 50 % two were.

## Where the gap stands after round four

| | Theorems, of 234 | Non-theorems, of 40 |
|---|---:|---:|
| HyLogic after round three | 105 | 23 |
| HyLogic after round four | 113 | 31 |
| E 3.2.5 | 207 | 16 |
| Vampire 5.1.0 (`casc`) | 231 | 20 |
| Vampire 5.1.0, satisfiability schedule (`casc_sat`) | | 36 |
| Vampire 5.1.0, finite model builder only (`-sa fmb`) | | 34 |

Nine non-theorems remain. GRA021+1 needs a model of about 12 elements,
SWW897+1 and SWW919+1 still have clauses of 29 to 38 variables after
splitting, and the other six have no finite model that Vampire's builder
finds in 10 seconds either.
