"""Step 3: how many of E's and Vampire's proofs HyLogic reads and presents.

    TPTP=... HYLOGIC_VAMPIRE=... python bridge_check.py [--time-limit 10]

For every sample problem, runs each prover through hylogic.external, and counts
a proof as read when every step parses and the last step is a contradiction.
"""
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import hy  # noqa: F401
from hylogic.external import run_prover

HERE = Path(__file__).resolve().parent
ROOT = os.environ["TPTP"]
LIMIT = float(sys.argv[sys.argv.index("--time-limit") + 1]) if "--time-limit" in sys.argv else 10


def check(prover, line):
    cell, expected, rating, eq, rel = line.split()
    r = run_prover(os.path.join(ROOT, rel), prover, LIMIT)
    has_proof = "SZS output start" in r.output
    read = bool(r.steps) and r.steps[-1].formula == "false"
    return {"prover": prover, "problem": Path(rel).stem, "cell": cell, "status": r.status,
            "proof_in_output": has_proof, "steps": len(r.steps), "read": read}


sample = (HERE / "sample.txt").read_text().splitlines()
rows = []
with ThreadPoolExecutor(8) as pool:
    for prover in ["vampire", "eprover"]:
        rows += list(pool.map(lambda line: check(prover, line), sample))
(HERE / "results" / "bridge.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
for prover in ["vampire", "eprover"]:
    rs = [r for r in rows if r["prover"] == prover]
    proved = [r for r in rs if r["status"] in ("Theorem", "Unsatisfiable")]
    with_proof = [r for r in proved if r["proof_in_output"]]
    read = [r for r in with_proof if r["read"]]
    print(f"{prover}: {len(proved)} proved, {len(with_proof)} printed a proof, "
          f"{len(read)} read completely ({100 * len(read) / max(1, len(with_proof)):.0f} %)")
    bad = [r["problem"] for r in with_proof if not r["read"]]
    if bad:
        print("  not read:", " ".join(bad[:20]))
