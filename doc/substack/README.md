# Article: How far a theorem prover you can read gets

A Substack article on HyLogic's prover: which methods took it from 39 to 161
of 234 TPTP theorems, how it compares with E and Vampire, the bugs the
benchmarks found, Lean checking every step of its proofs, and the logic
checker for AI agents.

| File | Contents |
|---|---|
| [readable_prover.md](readable_prover.md) | The article, with its tables as markdown |
| [readable_prover_substack.md](readable_prover_substack.md) | The same text for Substack, with the tables as images |
| [readable_prover_substack.html](readable_prover_substack.html) | Its body as HTML, the source the Substack draft is pasted from |
| [article_images/](article_images/) | Header image and the three table images |
| [header_image_prompts.md](header_image_prompts.md) | The prompt used to generate the header image with ChatGPT |
| [make_table_images.py](make_table_images.py) | Renders the table images with HyML and headless Chrome |

The data behind it is in [benchmarks/](../../benchmarks/): the TPTP comparison
with every measured step in [benchmarks/tptp/](../../benchmarks/tptp/), and the
logic field test with all its arguments in
[benchmarks/field_test/](../../benchmarks/field_test/).
