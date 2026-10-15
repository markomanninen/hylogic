"""Run provers on the TPTP sample and record their SZS status and time.

    TPTP=/path/to/TPTP-v9.3.1 python run.py PROVER [--time-limit 10] [--label NAME]

PROVER is hylogic, eprover or vampire. HyLogic runs as `python -m hylogic.tptp`
with the Python running this script. Results are appended to results/LABEL.jsonl.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = os.environ["TPTP"]
VAMPIRE = os.environ.get("VAMPIRE", "vampire")


def command(prover, path, limit):
    if prover == "hylogic":
        return [sys.executable, "-m", "hylogic.tptp", "--time-limit", str(limit), path]
    if prover == "eprover":
        return ["eprover", "--auto", "--silent", "--tstp-format", "--proof-object", f"--cpu-limit={limit}", path]
    if prover == "vampire":
        return [VAMPIRE, "--mode", "casc", "-t", f"{limit}s", "--proof", "tptp", path]
    raise ValueError(prover)


def run_one(prover, cell, expected, rel, limit):
    path = os.path.join(ROOT, rel)
    start = time.monotonic()
    env = dict(os.environ, PYTHONPATH=str(HERE.parent.parent))
    try:
        out = subprocess.run(command(prover, path, limit), capture_output=True, text=True,
                             timeout=limit + 5, env=env, cwd=HERE).stdout
        m = re.search(r"SZS status (\w+)", out)
        status = m.group(1) if m else "Error"
    except subprocess.TimeoutExpired:
        status, out = "Timeout", ""
    return {"problem": Path(rel).stem, "cell": cell, "expected": expected, "status": status,
            "seconds": round(time.monotonic() - start, 3), "proof_lines": out.count("\n")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("prover")
    ap.add_argument("--time-limit", type=float, default=10)
    ap.add_argument("--label")
    ap.add_argument("--jobs", type=int, default=8)
    args = ap.parse_args()
    label = args.label or args.prover
    sample = [line.split() for line in (HERE / "sample.txt").read_text().splitlines()]
    out_path = HERE / "results" / f"{label}.jsonl"
    out_path.parent.mkdir(exist_ok=True)
    out_path.write_text("")
    with ThreadPoolExecutor(args.jobs) as pool:
        futures = [pool.submit(run_one, args.prover, cell, status, rel, args.time_limit)
                   for cell, status, rating, eq, rel in sample]
        with open(out_path, "a") as f:
            for fut in futures:
                f.write(json.dumps(fut.result()) + "\n")
                f.flush()
    print(f"wrote {out_path}")


if __name__ == "__main__":
    main()
