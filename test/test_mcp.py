"""The MCP tool, called directly."""

import pytest

pytest.importorskip("mcp")

from mcp.server.fastmcp.exceptions import ToolError  # noqa: E402

from hylogic.mcp_server import check_argument  # noqa: E402


def test_valid_argument():
    out = check_argument(["(=> P Q)", "P"], "Q")
    assert out.startswith("VALID (checked by truth table)")
    assert "P → Q; P ⊢ Q" in out


def test_invalid_argument_with_meanings_and_json():
    out = check_argument([["=>", "P", "Q"], "Q"], "P", {"P": "it rains", "Q": "the street is wet"})
    assert out.startswith("INVALID")
    assert "“it rains” is false" in out


def test_first_order_countermodel():
    out = check_argument(["(forall [x] (exists [y] (Loves x y)))"], "(exists [y] (forall [x] (Loves x y)))")
    assert out.startswith("INVALID (checked by countermodel)")
    assert "Domain:" in out


def test_unreadable_formula_is_reported():
    with pytest.raises(ToolError, match="premise 1"):
        check_argument(["(=> P Q"], "Q")


def test_double_encoded_and_mixed_formulas():
    # seen in the field test: a formula sent as a JSON string inside a string
    out = check_argument(["(=> (and W A) R)", "(=> R S)", "(or W S)"], '"(=> A S)"')
    assert out.startswith("VALID")
    assert "⊢ A → S" in out
    out = check_argument([["=>", "(and P Q)", "R"], "P", "Q"], "R")
    assert out.startswith("VALID")
