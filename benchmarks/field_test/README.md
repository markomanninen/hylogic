# Field test: does a logic checker help an agent judge arguments?

The question is whether an agent decides more arguments correctly when it can
formalize them and ask hylogic's `check_argument` tool, and what that costs.

## Items

`items.json` has 40 arguments, made by `make_items.hy` and checked with Z3.

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

Not run yet.
