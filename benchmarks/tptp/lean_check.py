"""Step 4: export the sample to Lean 4 and check it there.

    TPTP=... python lean_check.py [--time-limit 20]

Every problem is written as a Lean theorem twice: with `sorry`, to check that
the statement is well formed, and with `grind`, Lean's own automation.
"""
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import hy  # noqa: F401
from hylogic.lean import to_lean, check_lean
from hylogic.tptp import read_problem

HERE = Path(__file__).resolve().parent
ROOT = os.environ["TPTP"]
LIMIT = float(sys.argv[sys.argv.index("--time-limit") + 1]) if "--time-limit" in sys.argv else 20


def check(line):
    cell, expected, rating, eq, rel = line.split()
    p = read_problem(os.path.join(ROOT, rel))
    ok_statement, msg = check_lean(to_lean(p.premises, p.goal, name="problem", tactic="sorry"), 60)
    proved, _ = check_lean(to_lean(p.premises, p.goal, name="problem", tactic="grind"), LIMIT)
    return {"problem": Path(rel).stem, "cell": cell, "expected": expected,
            "well_formed": ok_statement, "grind": proved, "error": "" if ok_statement else msg[:300]}


rows = list(ThreadPoolExecutor(8).map(check, (HERE / "sample.txt").read_text().splitlines()))
(HERE / "results" / "lean.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
theorems = [r for r in rows if r["expected"] == "Theorem"]
print(f"well formed: {sum(r['well_formed'] for r in rows)}/{len(rows)}")
print(f"grind proved: {sum(r['grind'] for r in theorems)}/{len(theorems)} theorems")
print(f"grind 'proved' non-theorems (must be 0): {sum(r['grind'] for r in rows if r['expected'] != 'Theorem')}")
for cell in ["neq-r0", "neq-r1", "neq-r2", "eq-r0", "eq-r1", "eq-r2"]:
    rs = [r for r in rows if r["cell"] == cell]
    print(f"  {cell}: {sum(r['grind'] for r in rs)}/{len(rs)}")
bad = [r for r in rows if not r["well_formed"]]
for r in bad[:5]:
    print("NOT WELL FORMED", r["problem"], r["error"].replace("\n", " ")[:200])
