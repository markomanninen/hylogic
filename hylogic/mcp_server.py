# -*- coding: utf-8 -*-
"""MCP server: let agents check whether an argument is logically valid.

    pip install "hylogic[mcp]"
    hylogic-mcp

One tool, ``check_argument``. It takes premises and a conclusion as
formulas, decides validity with a truth table, a SAT solver or the
resolution prover, and returns the verdict with a counterexample or a small
countermodel when the argument is invalid. A valid argument comes with the
premises it needs; the proof itself is returned only with detail=true,
since it can be long and the agent pays for every line. With certify=true
Lean 4 checks every step of the proof (hylogic.certify), when the lean
command is installed; otherwise the answer says how to install it.

HYLOGIC_MCP_LOG  file to append every call and its result to, as JSON lines
"""

import json
import os
import re
import shutil
import time

import hy
from mcp.server.fastmcp import FastMCP
from mcp.server.fastmcp.exceptions import ToolError

from hylogic.argument import Argument
from hylogic.exercises import describe
from hylogic.formulas import formula, pretty
from hylogic.terms import term

QUANTIFIER_WORDS = {"forall", "exists", "∀", "∃"}

INSTRUCTIONS = """\
check_argument decides whether premises logically entail a conclusion. \
Write each formula as an s-expression string or a JSON array. Connectives: \
not, and, or, => (if-then), <=> (iff), xor; quantifiers (forall [x] body) and \
(exists [x] body); predicates (Man x) or ["Man", "x"]. Example: premises \
["(=> P Q)", "P"], conclusion "Q". Use one letter or name per simple sentence, \
and give their meanings to get the explanation in words.
"""

mcp = FastMCP("hylogic", instructions=INSTRUCTIONS)


_CALL = re.compile(r"(?<![\w(\[-])([A-Za-z_][\w-]*)\(([^()]*)\)")


def _calls_to_lists(text):
    """Atoms written as calls, ReportsTo(Carla, Eva), as s-expressions:
    (ReportsTo Carla Eva). Models write this form often, and it is unambiguous."""
    while True:
        new = _CALL.sub(lambda m: "(" + m.group(1) + " " + m.group(2).replace(",", " ") + ")", text)
        if new == text:
            return text
        text = new


def _nest_quantifiers(form):
    """(forall [x] forall [y] body) as (forall [x] (forall [y] body))."""
    if isinstance(form, hy.models.Expression):
        items = [_nest_quantifiers(x) for x in form]
        if (len(items) > 3 and isinstance(items[0], hy.models.Symbol)
                and str(items[0]) in QUANTIFIER_WORDS and isinstance(items[1], hy.models.List)):
            return hy.models.Expression([items[0], items[1], _nest_quantifiers(hy.models.Expression(items[2:]))])
        return hy.models.Expression(items)
    return form


def _read(text):
    """One formula read from s-expression text."""
    try:
        forms = list(hy.read_many(text))
    except Exception:
        forms = []
    if len(forms) != 1 and _CALL.search(text):
        forms = list(hy.read_many(_calls_to_lists(text)))
    elif len(forms) == 1 and _CALL.search(text) and not isinstance(forms[0], hy.models.Expression):
        forms = list(hy.read_many(_calls_to_lists(text)))
    forms = [_nest_quantifiers(f) for f in forms]
    if len(forms) != 1:
        raise ValueError(f"expected one formula, found {len(forms)}")
    form = forms[0]
    # a formula sent as a JSON string inside a string, "\"(=> P Q)\"", reads
    # as a Hy string; it is the formula itself, not a proposition named so
    if isinstance(form, hy.models.String):
        return _read(str(form))
    return form


def _formula(value, where):
    """A formula from an s-expression string or a JSON array."""
    try:
        if isinstance(value, str):
            return formula(_read(value))
        if isinstance(value, list):
            # ["P"] is the proposition P, not a predicate without arguments
            if len(value) == 1:
                return _formula(value[0], where)
            return formula(_tuples(value))
    except Exception as e:  # reader and shape errors go back to the agent
        raise ToolError(f"{where}: cannot read {value!r}: {e}") from None
    raise ToolError(f"{where}: a formula must be a string like \"(=> P Q)\" or an array like [\"=>\", \"P\", \"Q\"]")


def _tuples(value):
    if isinstance(value, list):
        return tuple(_tuples(v) for v in value)
    if isinstance(value, str) and value.lstrip().startswith(("(", '"')):
        # an s-expression inside a JSON array
        return term(_read(value))
    return term(value) if not isinstance(value, str) else value


def lean_available():
    """Is the lean command installed? HYLOGIC_LEAN names it when it is not on PATH."""
    return shutil.which(os.environ.get("HYLOGIC_LEAN", "lean")) is not None


def _certify(argument, premises, conclusion):
    """One line on whether Lean 4 accepted every step of the proof."""
    if not lean_available():
        return ("Lean check: not run, Lean 4 is not installed here. Install it with elan "
                "(https://lean-lang.org/install), or set HYLOGIC_LEAN to the lean command.")
    from hylogic.certify import certify
    from hylogic.resolution import prove
    result = argument.result
    if result is None:
        # a propositional argument was decided by truth table or SAT: find a
        # resolution proof of it for Lean to check
        result = prove(conclusion, premises, limit=100000, timeout=5)
        if not result.proved:
            return "Lean check: not run, no resolution proof was found within 5 seconds."
    report = certify(result)
    steps = [s for s in report["steps"] if s.get("theorem") != "$refutation"]
    passed = sum(1 for s in steps if s.get("ok"))
    if report["verified"]:
        return (f"Lean check: verified, Lean 4 accepted all {passed} steps of the proof and how they "
                f"chain from the premises to a contradiction ({report.get('seconds', 0):.1f} s). "
                "The clausal form of the premises is taken as given.")
    failed = [s for s in steps if not s.get("ok")]
    first = failed[0] if failed else {}
    return (f"Lean check: NOT verified ({report.get('status')}), {passed} of {len(steps)} steps accepted; "
            f"first failure at step {first.get('number')} ({first.get('rule')}): {str(first.get('error', ''))[:200]}")


def _log(entry):
    path = os.environ.get("HYLOGIC_MCP_LOG")
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry, ensure_ascii=False) + "\n")


@mcp.tool()
def check_argument(premises: list, conclusion: str | list, meanings: dict | None = None,
                   detail: bool = False, certify: bool = False) -> str:
    """Decide whether the premises entail the conclusion. Formulas are s-expressions like "(=> P Q)" or JSON arrays like ["=>", "P", "Q"]. meanings maps letters or predicate names to the sentences they stand for. A valid argument comes with the premises it needs; detail=true adds the full proof for arguments with quantifiers; certify=true has Lean 4 check every step of the proof (a few seconds more), if Lean is installed."""
    started = time.time()
    entry = {"premises": premises, "conclusion": conclusion, "meanings": meanings,
             "detail": detail, "certify": certify}
    try:
        ps = [_formula(p, f"premise {i + 1}") for i, p in enumerate(premises)]
        c = _formula(conclusion, "conclusion")
        argument = Argument(ps, c, meanings=meanings, limit=100000, timeout=5)
        argument.check()
        verdict = {True: "VALID", False: "INVALID", None: "UNDECIDED"}[argument.valid]
        lines = [f"{verdict} (checked by {argument.method})",
                 "Read as: " + "; ".join(pretty(p) for p in ps) + " ⊢ " + pretty(c)]
        if argument.valid and argument.used is not None:
            lines.append("Premises needed: " + (", ".join(map(str, argument.used)) or "none, the conclusion holds by itself")
                         + f" (of {len(ps)})")
        if argument.valid and argument.proof:
            if detail:
                lines.append("Proof:\n" + "\n".join(argument.proof))
            else:
                lines.append(f"Proof: {len(argument.proof)} steps, shown with detail=true")
        if certify and argument.valid:
            lines.append(_certify(argument, ps, c))
        if argument.counterexample:
            lines.append("Counterexample: " + describe(argument.counterexample, meanings)
                         + ". Then every premise is true and the conclusion is false.")
        elif argument.countermodel:
            lines.append("Countermodel, where every premise is true and the conclusion is false:\n"
                         + str(argument.countermodel))
        result = "\n".join(lines)
    except ToolError as e:
        entry.update(error=str(e), seconds=round(time.time() - started, 3))
        _log(entry)
        raise
    entry.update(result=result, seconds=round(time.time() - started, 3))
    _log(entry)
    return result


def main():
    mcp.run()


if __name__ == "__main__":
    main()
