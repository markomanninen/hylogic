"""Summarize benchmark results per prover and sample cell, and check soundness.

    python score.py results/*.jsonl
"""
import json
import sys
from collections import defaultdict
from pathlib import Path

CELLS = ["neq-r0", "neq-r1", "neq-r2", "eq-r0", "eq-r1", "eq-r2", "csat"]
SOLVED = {"Theorem", "Unsatisfiable", "CounterSatisfiable", "Satisfiable"}
WRONG = {("Theorem", "CounterSatisfiable"), ("Theorem", "Satisfiable"),
         ("CounterSatisfiable", "Theorem"), ("CounterSatisfiable", "Unsatisfiable")}

print("| Prover | " + " | ".join(CELLS) + " | All | Wrong |")
print("|---|" + "---:|" * (len(CELLS) + 2))
for path in sys.argv[1:]:
    rows = [json.loads(l) for l in open(path)]
    by_cell = defaultdict(list)
    for r in rows:
        by_cell[r["cell"]].append(r)
    wrong = [r["problem"] for r in rows if (r["expected"], r["status"]) in WRONG]
    cells = []
    for c in CELLS:
        rs = by_cell[c]
        ok = sum(r["status"] == r["expected"] or (r["expected"] == "Theorem" and r["status"] == "Unsatisfiable") for r in rs)
        cells.append(f"{ok}/{len(rs)}")
    total = sum(r["status"] in SOLVED and (r["expected"], r["status"]) not in WRONG for r in rows)
    print(f"| {Path(path).stem} | " + " | ".join(cells) + f" | {total}/{len(rows)} | {len(wrong)} |")
    if wrong:
        print("  WRONG:", ", ".join(wrong))
