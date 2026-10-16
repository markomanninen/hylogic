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
table("table1_camel", "Python plans against Hy plans in CaMeL, on the same runs",
      ["", "Python plans", "Hy plans"],
      [["Tasks solved, no attack (16)", "11", "10"], ["Tasks solved, under attack (39)", "38", "32"],
       ["Attacks that succeeded", "0", "0"], ["Retries per run, no attack", "1.25", "1.56"],
       ["Model cost, no-attack run", "$0.74", "$1.08"]],
      "AgentDojo banking suite, Claude Haiku through claude -p, CaMeL's own interpreter and policies.",
      worse={(0, 2), (1, 2), (3, 2), (4, 2)})
table("table2_tokens", "Tokens to describe a page's interactive elements to a model",
      ["Format", "Tokens", "Relative to HTML"],
      [["HTML", "51,950", "1.00"], ["HyML s-expressions", "53,995", "1.04"], ["HyML as JSON", "62,015", "1.19"],
       ["JSON, compact", "78,730", "1.52"], ["JSON, indented", "99,246", "1.91"]],
      "1,661 elements from Wikipedia, Hacker News and GitHub's login page, counted with OpenAI's o200k tokenizer.",
      highlight=lambda row: row[0].startswith("HyML"))
table("table3_checker", "Arguments judged correctly, with and without HyLogic's checker",
      ["", "Without tool", "With tool", "Cost with the tool"],
      [["Claude Haiku", "67 of 70", "69 of 70", "1.7 times"], ["Claude Opus", "70 of 70", "70 of 70", "1.6 times"]],
      "70 generated arguments in English, each checked with HyLogic and Z3, judged once per model and condition.")
table("table4_provers", "Theorems from the TPTP library proved within ten seconds each",
      ["", "Theorems, of 234"],
      [["HyLogic, first version", "39"], ["HyLogic, after the measured changes", "146"],
       ["Lean's grind, on HyLogic's export", "103"], ["E 3.2.5", "207"], ["Vampire 5.1.0", "231"]],
      "Problems with at most 50 formulas from TPTP v9.3.1, drawn with a fixed seed. Apple Silicon, one problem per process.",
      highlight=lambda row: row[0].startswith("HyLogic"))
print(sorted(p.name for p in OUT.iterdir()))
