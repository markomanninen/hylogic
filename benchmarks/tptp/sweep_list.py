"""List every eligible TPTP problem outside the two benchmark samples.

    TPTP=/path/to/TPTP-v9.3.1 python sweep_list.py > sweep.txt

Eligible means what draw_sample.py draws from, FOF problems with a Status,
Rating and SPC header and at most 50 formulas, here with any of the statuses
Theorem, CounterSatisfiable, Unsatisfiable and Satisfiable. Problems in
sample.txt and holdout.txt are left out. The lines have the format of
sample.txt, with the cell named sweep-thm, sweep-csat, sweep-unsat or
sweep-sat, and PRP in the equality column for propositional problems.

    python run.py hylogic --sample sweep.txt --label sweep --jobs 6
    python score.py results/sweep.jsonl

runs HyLogic on all of them and lists any wrong answers.
"""
import glob
import os
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
CELLS = {"Theorem": "sweep-thm", "CounterSatisfiable": "sweep-csat",
         "Unsatisfiable": "sweep-unsat", "Satisfiable": "sweep-sat"}

root = os.environ["TPTP"]
used = set()
for name in ["sample.txt", "holdout.txt"]:
    used |= {line.split()[-1] for line in open(HERE / name) if line.strip()}
for path in sorted(glob.glob(f"{root}/Problems/*/*+*.p")):
    head = open(path, errors="replace").read(6000)
    status = re.search(r"% Status\s*:\s*(\w+)", head)
    rating = re.search(r"% Rating\s*:\s*([\d.]+)", head)
    spc = re.search(r"% SPC\s*:\s*(\S+)", head)
    formulas = re.search(r"Number of formulae\s*:\s*(\d+)", head)
    if not (status and rating and spc and formulas) or int(formulas.group(1)) > 50:
        continue
    rel = os.path.relpath(path, root)
    if status.group(1) not in CELLS or rel in used:
        continue
    parts = spc.group(1).split("_")
    eq = parts[3] if len(parts) > 3 else "PRP"
    print(CELLS[status.group(1)], status.group(1), float(rating.group(1)), eq, rel)
