"""Score a field test run: accuracy, cost and tool use per model and condition.

    python benchmarks/field_test/score.py benchmarks/field_test/runs/RUN
"""

import json
import re
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent


def answer(text):
    """VALID, INVALID or None, from the last line that says one of them."""
    for line in reversed((text or "").strip().splitlines()):
        m = re.search(r"\b(INVALID|VALID)\b", line.upper())
        if m:
            return m.group(1)
    return None


def main(run, items_file=HERE / "items.json"):
    items = {i["id"]: i for i in json.load(open(items_file))}
    rows = []
    for result_path in sorted(Path(run).glob("*/*/*/result.json")):
        condition, model, item_id = result_path.parent.relative_to(run).parts
        item = items[item_id]
        result = json.loads(result_path.read_text() or "{}")
        usage = result.get("usage", {})
        calls_path = result_path.parent / "tool_calls.jsonl"
        calls = [json.loads(l) for l in calls_path.read_text().splitlines()] if calls_path.exists() else []
        expected = "VALID" if item["valid"] else "INVALID"
        given = answer(result.get("result"))
        tool_verdicts = [answer(c.get("result")) for c in calls if "result" in c]
        rows.append({
            "condition": condition, "model": model, "id": item_id, "kind": item["kind"],
            "expected": expected, "given": given, "correct": given == expected,
            "tool_calls": len(calls), "tool_errors": sum("error" in c for c in calls),
            "last_tool_verdict": tool_verdicts[-1] if tool_verdicts else None,
            "followed_tool": bool(tool_verdicts) and given == tool_verdicts[-1],
            "output_tokens": usage.get("output_tokens", 0),
            "input_tokens": usage.get("input_tokens", 0) + usage.get("cache_read_input_tokens", 0)
            + usage.get("cache_creation_input_tokens", 0),
            "cost": result.get("total_cost_usd", 0.0), "seconds": result.get("duration_ms", 0) / 1000,
        })
    (Path(run) / "summary.json").write_text(json.dumps(rows, indent=1))

    groups = defaultdict(list)
    for r in rows:
        groups[(r["model"], r["condition"])].append(r)
    print("| Model | Condition | Correct | Propositional | Syllogisms | No answer | Tool calls | Tool errors | Output tokens | Cost $ | Seconds |")
    print("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for (model, condition), rs in sorted(groups.items()):
        n = len(rs)
        prop = [r for r in rs if r["kind"] == "propositional"]
        syl = [r for r in rs if r["kind"] == "syllogism"]
        print(f"| {model} | {condition} | {sum(r['correct'] for r in rs)}/{n} "
              f"| {sum(r['correct'] for r in prop)}/{len(prop)} | {sum(r['correct'] for r in syl)}/{len(syl)} "
              f"| {sum(r['given'] is None for r in rs)} | {sum(r['tool_calls'] for r in rs)} "
              f"| {sum(r['tool_errors'] for r in rs)} | {sum(r['output_tokens'] for r in rs)} "
              f"| {sum(r['cost'] for r in rs):.2f} | {sum(r['seconds'] for r in rs):.0f} |")
    print()
    for (model, condition), rs in sorted(groups.items()):
        wrong = [r["id"] for r in rs if not r["correct"]]
        print(f"{model} {condition} wrong: {', '.join(wrong) or 'none'}")
        if condition == "tool":
            ignored = [r["id"] for r in rs if r["last_tool_verdict"] and not r["followed_tool"]]
            wrong_tool = [r["id"] for r in rs if r["last_tool_verdict"] and r["last_tool_verdict"] != r["expected"]]
            print(f"  answer differs from the tool's last verdict: {', '.join(ignored) or 'none'}")
            print(f"  tool's last verdict wrong (formalization mistakes): {', '.join(wrong_tool) or 'none'}")


if __name__ == "__main__":
    main(*sys.argv[1:])
