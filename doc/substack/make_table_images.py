"""Render the article's tables as PNG images for Substack, which has no tables.

Each table becomes an HTML page, written with HyML's data mode like the HyML
article's tables, and is captured with headless Chrome and trimmed.

    python make_table_images.py      (needs hyml and pillow, and Google Chrome)
"""
import subprocess
import tempfile
from pathlib import Path

import hyml
from PIL import Image, ImageChops

HERE = Path(__file__).resolve().parent
OUT = HERE / "article_images"
CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
CSS = """
body { margin: 0; background: #fff; font: 17px/1.45 -apple-system, "Helvetica Neue", Arial, sans-serif; color: #1f2933; }
figure { margin: 0; padding: 28px 32px; width: 1040px; }
figcaption { font-weight: 600; font-size: 19px; margin-bottom: 14px; }
table { border-collapse: collapse; width: 100%; }
th, td { padding: 8px 12px; border-bottom: 1px solid #e3e8ee; text-align: left; }
th { font-size: 14px; text-transform: uppercase; letter-spacing: .03em; color: #52606d; border-bottom: 2px solid #9aa5b1; }
td.num, th.num { text-align: right; font-variant-numeric: tabular-nums; }
tr.hl td { background: #fbf6ec; }
td.worse { color: #b0412e; font-weight: 600; }
p.note { color: #616e7c; font-size: 14px; margin-top: 10px; }
"""


def table(name, title, headers, rows, note, highlight=lambda row: False, worse=()):
    """rows: lists of cells; the first column is text, the others numbers."""
    head = ["tr", ["th", headers[0]]] + [["th", {"class": "num"}, h] for h in headers[1:]]
    body = []
    for r, row in enumerate(rows):
        cells = [["td", row[0]]]
        for c, value in enumerate(row[1:], 1):
            cells.append(["td", {"class": "num worse" if (r, c) in worse else "num"}, value])
        body.append(["tr", {"class": "hl"} if highlight(row) else {}] + cells)
    figure = ["figure", ["figcaption", title], ["table", ["thead", head], ["tbody"] + body],
              ["p", {"class": "note"}, note]]
    html = f'<!doctype html><meta charset="utf-8"><style>{CSS}</style>{hyml.render_data(figure)}'
    with tempfile.TemporaryDirectory() as tmp:
        page, shot = Path(tmp) / "t.html", Path(tmp) / "t.png"
        page.write_text(html, encoding="utf-8")
        subprocess.run([CHROME, "--headless=new", "--hide-scrollbars", "--force-device-scale-factor=2",
                        "--window-size=1104,900", f"--screenshot={shot}", page.as_uri()],
                       check=True, capture_output=True)
        image = Image.open(shot).convert("RGB")
    # trim the white space below and to the right of the figure, keeping a margin
    box = ImageChops.difference(image, Image.new("RGB", image.size, "white")).getbbox()
    image.crop((0, 0, min(image.width, box[2] + 64), min(image.height, box[3] + 56))).save(OUT / f"{name}.png")


OUT.mkdir(exist_ok=True)
table("prover_methods", "What each method added, in theorems proved of 234",
      ["Method", "Theorems"],
      [["First version, plain resolution", "39"],
       ["Fair choice of the next clause, by age as well as size", "+9"],
       ["Superposition for equality, with ordered resolution", "+28"],
       ["Naming subformulas, indexing, deciding problems without functions by SAT", "+10"],
       ["A search that stays close to the goal", "+11"],
       ["Ground problems decided by a SAT solver", "+7"],
       ["Ground equality decided by congruence closure", "+6"],
       ["Simplification as E does it", "+11"],
       ["Splitting clauses before grounding them", "+22"],
       ["A schedule of two search strategies", "+13"],
       ["Smaller steps", "+5"],
       ["HyLogic now", "161"]],
      "TPTP v9.3.1 problems with at most 50 formulas, ten seconds each. Each change measured on its own and kept only if it helped.",
      highlight=lambda row: row[0] in ("First version, plain resolution", "HyLogic now"))
table("prover_results", "Problems solved within ten seconds each",
      ["", "Theorems, of 234", "Non-theorems, of 40", "Held-out theorems, of 200"],
      [["HyLogic, first version", "39", "18", ""], ["HyLogic now", "161", "31", "141"],
       ["Lean's grind, on HyLogic's export", "53", "", ""], ["E 3.2.5", "207", "16", "189"],
       ["Vampire 5.1.0", "231", "20", "197"]],
      "Vampire shows 36 of the non-theorems with its schedule for finding models. The held-out sample was drawn with "
      "another seed and never used in tuning. Apple Silicon, one problem per process.",
      highlight=lambda row: row[0].startswith("HyLogic"))
table("field_checker", "Arguments judged correctly, with and without HyLogic's checker",
      ["", "Without the tool", "With the tool", "Cost with the tool"],
      [["Short arguments, Claude Haiku", "67 of 70", "69 of 70", "1.7 times"],
       ["Short arguments, Claude Opus", "70 of 70", "70 of 70", "1.6 times"],
       ["25 premises, Claude Haiku", "38 of 40", "40 of 40", "1.7 times"]],
      "Generated arguments in English, each decided by HyLogic and Z3, judged once per model and condition.")
print(sorted(p.name for p in OUT.iterdir()))
