# -*- coding: utf-8 -*-
"""MCP server: let agents check whether an argument is logically valid.

    pip install "hylogic[mcp]"
    hylogic-mcp

One tool, ``check_argument``. It takes premises and a conclusion as
formulas, decides validity with a truth table, a SAT solver or the
resolution prover, and returns the verdict with a counterexample or a small
countermodel when the argument is invalid.

HYLOGIC_MCP_LOG  file to append every call and its result to, as JSON lines
"""

import json
import os
import time

import hy
from mcp.server.fastmcp import FastMCP
from mcp.server.fastmcp.exceptions import ToolError

from hylogic.argument import Argument
from hylogic.exercises import describe
from hylogic.formulas import formula, pretty
from hylogic.terms import term

INSTRUCTIONS = """\
check_argument decides whether premises logically entail a conclusion. \
Write each formula as an s-expression string or a JSON array. Connectives: \
not, and, or, => (if-then), <=> (iff), xor; quantifiers (forall [x] body) and \
(exists [x] body); predicates (Man x) or ["Man", "x"]. Example: premises \
["(=> P Q)", "P"], conclusion "Q". Use one letter or name per simple sentence, \
and give their meanings to get the explanation in words.
"""

mcp = FastMCP("hylogic", instructions=INSTRUCTIONS)


def _read(text):
    """One formula read from s-expression text."""
    forms = list(hy.read_many(text))
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


def _log(entry):
    path = os.environ.get("HYLOGIC_MCP_LOG")
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry, ensure_ascii=False) + "\n")


@mcp.tool()
def check_argument(premises: list, conclusion: str | list, meanings: dict | None = None) -> str:
    """Decide whether the premises entail the conclusion. Formulas are s-expressions like "(=> P Q)" or JSON arrays like ["=>", "P", "Q"]. meanings maps letters or predicate names to the sentences they stand for."""
    started = time.time()
    entry = {"premises": premises, "conclusion": conclusion, "meanings": meanings}
    try:
        ps = [_formula(p, f"premise {i + 1}") for i, p in enumerate(premises)]
        c = _formula(conclusion, "conclusion")
        argument = Argument(ps, c, meanings=meanings, limit=3000)
        argument.check()
        verdict = {True: "VALID", False: "INVALID", None: "UNDECIDED"}[argument.valid]
        lines = [f"{verdict} (checked by {argument.method})",
                 "Read as: " + "; ".join(pretty(p) for p in ps) + " ⊢ " + pretty(c)]
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
