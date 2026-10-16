"""The MCP tool, called directly."""

import pytest

# the server uses the mcp 1.x API (FastMCP); skip where mcp 2.x is installed
pytest.importorskip("mcp.server.fastmcp")

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


def test_one_element_array_is_the_proposition():
    # also seen in the field test: the conclusion R sent as ["R"]
    out = check_argument(["(=> P R)", "P"], ["R"])
    assert out.startswith("VALID (checked by truth table)")


def test_valid_argument_names_the_premises_it_needs():
    # R plays no part: the answer says which premises carry the conclusion
    out = check_argument(["(=> P Q)", "R", "P"], "Q")
    assert "Premises needed: 1, 3 (of 3)" in out


def test_first_order_proof_only_with_detail():
    premises = ["(forall [x] (=> (Man x) (Mortal x)))", "(Man socrates)", "(Greek socrates)"]
    short = check_argument(premises, "(Mortal socrates)")
    assert short.startswith("VALID (checked by resolution)")
    assert "Premises needed: 1, 2 (of 3)" in short
    assert "shown with detail=true" in short and "□" not in short
    full = check_argument(premises, "(Mortal socrates)", detail=True)
    assert "Proof:" in full and "□" in full
    assert len(full) > len(short)


def test_first_order_with_equality():
    # superposition: from a = b and P(a), P(b)
    out = check_argument(["(= a b)", "(P a)"], "(P b)")
    assert out.startswith("VALID")
    assert "Premises needed: 1, 2" in out
