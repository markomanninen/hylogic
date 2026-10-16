"""Lean checks HyLogic's own proofs, step by step.

    TPTP=... python lean_proofs.py [--results results/28-final.jsonl] [--jobs 4]
                                   [--time-limit 10] [--lean-limit 120] [--only NAME,...]
                                   [--no-instances] [--out FILE]

For every problem HyLogic proved in the results file, the proof is found again
with the command line's defaults (hylogic.tptp.DEFAULTS), written as a Lean file
with one theorem per inference (hylogic.certify), and checked by Lean. Results
go to results/lean_proofs.jsonl, one line per problem. With --no-instances the
instances HyLogic's replay finds are left out, to measure grind on its own.
"""
import argparse
import json
import os
import sys
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent))

import hy  # noqa: F401,E402
from hylogic.certify import certify  # noqa: E402
from hylogic.tptp import solve, DEFAULTS  # noqa: E402

ROOT = os.environ["TPTP"]


def check(job):
    name, rel, time_limit, lean_limit, instances = job
    started = time.monotonic()
    status, result, _ = solve(os.path.join(ROOT, rel), time_limit=time_limit, **DEFAULTS)
    row = {"problem": name, "status": status, "solve_seconds": round(time.monotonic() - started, 3)}
    if not result.proved or result.clause is None:
        return row | {"proved": False}
    try:
        c = certify(result, timeout=lean_limit, instances=instances)
    except Exception as e:  # a bug in the export: recorded, not fatal
        return row | {"proved": True, "verified": False, "lean_status": "export error", "steps": 0,
                      "steps_verified": 0, "rules": {}, "rules_verified": {}, "not_replayed": [],
                      "failed": [{"step": None, "rule": "export", "error": repr(e)[:400]}],
                      "lean_seconds": 0}
    steps = [s for s in c["steps"] if s["number"] is not None]
    return row | {
        "proved": True, "verified": c["verified"], "lean_status": c["status"],
        "steps": len(steps), "steps_verified": sum(s["ok"] for s in steps),
        "rules": dict(Counter(s["rule"] for s in steps)),
        "rules_verified": dict(Counter(s["rule"] for s in steps if s["ok"])),
        "not_replayed": [s["number"] for s in steps if not s["replayed"]],
        "failed": [{"step": s["number"], "rule": s["rule"], "error": s["error"]}
                   for s in c["steps"] if not s["ok"]],
        "lean_seconds": c["seconds"]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", default=str(HERE / "results" / "28-final.jsonl"))
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--time-limit", type=float, default=10)
    ap.add_argument("--lean-limit", type=float, default=120)
    ap.add_argument("--only", default="")
    ap.add_argument("--no-instances", action="store_true")
    ap.add_argument("--out", default=str(HERE / "results" / "lean_proofs.jsonl"))
    args = ap.parse_args()
    paths = {Path(line.split()[-1]).stem: line.split()[-1]
             for line in (HERE / "sample.txt").read_text().splitlines()}
    proved = [json.loads(line) for line in Path(args.results).read_text().splitlines()]
    proved = [r["problem"] for r in proved if r["status"] in ("Theorem", "Unsatisfiable")]
    if args.only:
        proved = [p for p in proved if p in args.only.split(",")]
    jobs = [(p, paths[p], args.time_limit, args.lean_limit, not args.no_instances) for p in proved]
    started = time.monotonic()
    rows = []
    with ProcessPoolExecutor(args.jobs) as pool, open(args.out, "w") as out:
        for row in pool.map(check, jobs):
            rows.append(row)
            out.write(json.dumps(row) + "\n")
            out.flush()
            print(row["problem"], row.get("verified"), row.get("steps_verified"), "/", row.get("steps"),
                  [(f["step"], f["rule"]) for f in row.get("failed", [])][:5], flush=True)
    summarize(rows, time.monotonic() - started)


def summarize(rows, seconds):
    found = [r for r in rows if r["proved"]]
    print(f"\nproblems: {len(rows)}, proof found again: {len(found)}")
    print(f"proofs fully verified by Lean: {sum(r['verified'] for r in found)}/{len(found)}")
    print(f"steps verified: {sum(r['steps_verified'] for r in found)}/{sum(r['steps'] for r in found)}")
    total, ok = Counter(), Counter()
    for r in found:
        total.update(r["rules"])
        ok.update(r["rules_verified"])
    for rule, n in total.most_common():
        print(f"  {rule}: {ok[rule]}/{n}")
    print(f"Lean seconds: {sum(r['lean_seconds'] for r in found):.0f}, wall: {seconds:.0f}")


if __name__ == "__main__":
    main()
