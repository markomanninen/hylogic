"""Which search strategies prove which of the theorems the default leaves open.

    TPTP=... python strategies.py RESULTS.jsonl [--time-limit 6] [--jobs 8]

Runs hylogic.resolution.prove with each strategy below on every theorem the
given run did not prove, one process per attempt, and writes
results/strategies.jsonl. The union and a greedy cover show what a schedule of
strategies could gain before one is built.
"""
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = os.environ["TPTP"]
LIMIT = float(sys.argv[sys.argv.index("--time-limit") + 1]) if "--time-limit" in sys.argv else 6
JOBS = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 8
BASE = {"superposition": 1, "ordered": 1, "index": 1, "definitional": 8, "age_ratio": 10, "goal_bias": 6}
STRATEGIES = {
    "default": {},
    "unordered": {"ordered": 0},
    "no-goal-bias": {"goal_bias": 2, "age_ratio": 3},
    "plain": {"ordered": 0, "superposition": 0, "goal_bias": 0},
    "strong-goal-bias": {"goal_bias": 12},
    "fifo-heavy": {"age_ratio": 1},
    "no-definitions": {"definitional": 0},
}
CODE = """
import hy, sys, json
from hylogic.tptp import read_problem
from hylogic.resolution import prove
p = read_problem(sys.argv[1])
r = prove(p.goal, p.premises, limit=10**7, timeout=float(sys.argv[2]), **json.loads(sys.argv[3]))
print(r.status)
"""


def attempt(rel, name):
    opts = dict(BASE, **STRATEGIES[name])
    try:
        out = subprocess.run([sys.executable, "-c", CODE, os.path.join(ROOT, rel), str(LIMIT), json.dumps(opts)],
                             capture_output=True, text=True, timeout=LIMIT + 10,
                             env=dict(os.environ, PYTHONPATH=str(HERE.parent.parent))).stdout.strip()
    except subprocess.TimeoutExpired:
        out = "timeout"
    return {"problem": Path(rel).stem, "strategy": name, "status": out.splitlines()[-1] if out else "error"}


def main():
    done = {json.loads(l)["problem"]: json.loads(l) for l in open(sys.argv[1])}
    sample = [l.split() for l in (HERE / "sample.txt").read_text().splitlines()]
    open_ = [rel for cell, status, *_, rel in sample
             if status == "Theorem" and done[Path(rel).stem]["status"] != "Theorem"]
    with ThreadPoolExecutor(JOBS) as pool:
        rows = list(pool.map(lambda a: attempt(*a), [(rel, s) for rel in open_ for s in STRATEGIES]))
    (HERE / "results" / "strategies.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
    solved = {s: {r["problem"] for r in rows if r["strategy"] == s and r["status"] == "proved"} for s in STRATEGIES}
    print(f"{len(open_)} open theorems, {LIMIT} s each")
    for s, ps in solved.items():
        print(f"  {s:18} {len(ps)}")
    print(f"  union              {len(set().union(*solved.values()))}")
    left, cover = set().union(*solved.values()), []
    while left:
        best = max(solved, key=lambda s: len(solved[s] & left))
        cover.append((best, len(solved[best] & left)))
        left -= solved[best]
    print("  greedy cover:", cover)


if __name__ == "__main__":
    main()
