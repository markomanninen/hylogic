"""Draw the fixed TPTP sample for the prover benchmarks.

    TPTP=/path/to/TPTP-v9.3.1 python draw_sample.py > sample.txt

FOF problems with at most 50 formulas: 40 theorems (or all, where fewer exist) per cell of
{without equality, with equality} x {rating 0, 0.01-0.20, 0.21-0.50}, and 40
CounterSatisfiable problems, drawn with a fixed seed.
"""
import glob
import os
import random
import re

root = os.environ["TPTP"]
rows = []
for path in sorted(glob.glob(f"{root}/Problems/*/*+*.p")):
    head = open(path, errors="replace").read(6000)
    status = re.search(r"% Status\s*:\s*(\w+)", head)
    rating = re.search(r"% Rating\s*:\s*([\d.]+)", head)
    spc = re.search(r"% SPC\s*:\s*(\S+)", head)
    formulas = re.search(r"Number of formulae\s*:\s*(\d+)", head)
    if not (status and rating and spc and formulas) or int(formulas.group(1)) > 50:
        continue
    parts = spc.group(1).split("_")
    rows.append((os.path.relpath(path, root), status.group(1), float(rating.group(1)), parts[3] if len(parts) > 3 else ""))

rng = random.Random(2026)
cells = []
for eq_name, eq in [("neq", {"NEQ"}), ("eq", {"SEQ", "PEQ"})]:
    for band, lo, hi in [("r0", 0.0, 0.0), ("r1", 0.01, 0.20), ("r2", 0.21, 0.50)]:
        pool = [r for r in rows if r[1] == "Theorem" and r[3] in eq and lo <= r[2] <= hi]
        cells += [(f"{eq_name}-{band}", r) for r in rng.sample(pool, min(40, len(pool)))]
pool = [r for r in rows if r[1] == "CounterSatisfiable"]
cells += [("csat", r) for r in rng.sample(pool, 40)]
for cell, (path, status, rating, eq) in cells:
    print(cell, status, rating, eq, path)
