# Field test: does a logic checker help an agent judge arguments?

The question is whether an agent decides more arguments correctly when it can
formalize them and ask hylogic's `check_argument` tool, and what that costs.

## Items

`items.json` has 40 arguments, made by `make_items.hy` and checked with Z3.
`items_hard.json` (`make_items.hy --hard`) has 30 harder propositional ones,
added after the first round: six sentences, five to seven premises, and
invalid arguments whose conclusion holds in at least four fifths of the
situations the premises allow.

- 32 propositional arguments in English about everyday facts, half valid. A
  valid one needs every premise. An invalid one is tempting: the conclusion
  is true in at least two thirds of the situations the premises allow. The
  phrasing includes "only if" and "unless", which people often misread.
- 8 syllogisms that test belief bias: a believable conclusion that does not
  follow ("some roses fade quickly"), or an absurd one that does ("all whales
  can fly").

## Conditions

Each item is given once to each model in each condition, through `claude -p`.

| Condition | Tools |
|---|---|
| `plain` | none; the model answers directly |
| `tool` | only hylogic's MCP server with `check_argument` |

Both prompts state the same conventions: "or" is inclusive, "unless" means
"or", and "A only if B" means "if A, then B".

## Hypotheses, written before running

| | Hypothesis | Expected |
|---|---|---|
| H1 | Without the tool, the small model misjudges some propositional items, the large one fewer | Haiku 70 to 85 %, Opus 85 to 95 % |
| H2 | With the tool, accuracy rises, most for the small model; the remaining errors are formalization mistakes | Haiku 90 % or more |
| H3 | Without the tool, errors on syllogisms concentrate on the belief-bias items | errors on S1, S3, S5, S6 more than others |
| H4 | The tool costs more | 1.5 to 3 times the tokens and money |

## Running

```bash
benchmarks/field_test/run_agents.sh          # every item, both conditions, haiku and opus
python benchmarks/field_test/score.py benchmarks/field_test/runs/<run>
```

Every run makes real model calls. Results go to `runs/`, which is not committed.

## Results

Run on 14 October 2026 with Claude Haiku and Claude Opus through `claude -p`.
Each cell is one answer per item.

| | First set (40) | Cost | Hard set (30) | Cost |
|---|---:|---:|---:|---:|
| Haiku, no tool | 38 | $0.36 | 29 | $0.36 |
| Haiku, with tool | 40 | $0.61 | 29 | $0.62 |
| Opus, no tool | 40 | $0.67 | 30 | $0.56 |
| Opus, with tool | 40 | $1.07 | 30 | $0.93 |

All field test runs, including the reruns below, cost $8.31 in total.

### What the hypotheses came to

| | Hypothesis | Outcome |
|---|---|---|
| H1 | Haiku 70 to 85 %, Opus 85 to 95 % without the tool | Wrong. Haiku got 67 of 70 right (96 %), Opus all 70. |
| H2 | The tool raises accuracy, most for Haiku | Not shown. Haiku went from 67 to 69 of 70, within the variation between runs: an earlier tool run of the first set had 39 of 40. Opus had no room to improve. |
| H3 | Belief-bias syllogisms cause errors without the tool | Not supported. Neither model missed a syllogism without the tool. |
| H4 | The tool costs 1.5 to 3 times as much | Held. 1.6 to 1.7 times the cost for both models. |

### Where the errors came from

Every error Haiku made, with or without the tool, was on an argument with
"Unless A, B", which Haiku formalized or read as "not A or B", although the
prompt says that "unless" means "or". With the tool, the check is only as
good as the formalization: hylogic faithfully confirmed the misread
argument. The bottleneck at this size is reading the English, not the
reasoning, and a logic checker does not help with that.

### Bugs the field test found in the tool

The first runs showed two ways the tool misread what Haiku sent, both now
fixed and covered by tests:

- a formula sent as a JSON string inside a string, `"\"(=> A S)\""`, was read
  as a single proposition with that name;
- a one-element array, `["R"]`, was read as a predicate without arguments.

Replaying every logged call through the fixed tool changed only the affected
verdicts. The results above come from runs with the fixed tool; the Haiku
tool condition was run again for both sets, and Opus never sent either form.

### Conclusion

For arguments of this size, current models do not need a logic checker:
Haiku is right 96 % of the time on its own and Opus every time, and the tool
adds 60 to 70 % to the cost. A checker would pay off only where the reasoning
itself is the hard part, with longer or first-order arguments, and only if
the model formalizes the sentences correctly, which is where Haiku's errors
were.

## Round two: first-order arguments

The first round's arguments were short and mostly propositional, and the
models judged them well without the tool. `items_fo.json` (made by
`make_items_fo.py`) has 40 longer first-order arguments about people in an
office: chains of three to seven premises with "everyone who", "no one who",
"only someone who", "someone who" and relations such as "reports to". Half
are valid, and a valid one needs every premise (HyLogic's proof uses all of
them). An invalid one is a valid chain with one change a hasty reader can
miss, recorded as its trap.

| Trap | Change |
|---|---|
| `converse` | one rule turned around, "everyone who has a badge works remotely" where the chain needs the converse |
| `some` | one "everyone who" weakened to "at least one person who" |
| `scope` | "everyone trusts someone" taken as "someone is trusted by everyone" |
| `other` | the chain starts from a fact about another person |

Validity is decided by HyLogic and checked with Z3. With the tool the prompt
asks for predicates and quantifiers. The tool answers with the verdict, the
premises a valid argument needs and the length of the proof, and returns the
proof itself only with `detail=true`, since the agent pays for every line.

    ITEMS_FILE=items_fo.json run_agents.sh haiku

### Hypotheses, written before running

| | Hypothesis | Expected |
|---|---|---|
| H5 | Without the tool, longer chains and the traps cost the small model more than the first round did | Haiku below 90 % |
| H6 | Most errors without the tool fall on `some` and `scope` | more than on `converse` and `other` |
| H7 | With the tool, accuracy rises; the remaining errors are formalization mistakes | Haiku 95 % or more |
| H8 | The tool costs less here than in the first round, relative to answering without it, because the model can stop reasoning once the tool decides | less than 1.6 times |
