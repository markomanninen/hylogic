"""Hylogic: propositional and first-order logic in Hy.

Formulas are quoted Hy code with logical symbols or ASCII names. From Hy::

    (import hylogic [truth-table prove])
    (print (truth-table '(→ (∧ P (→ P Q)) Q)))

From Python, formulas are nested tuples of strings, and the Hy names ending
in ``?`` have Python aliases such as ``is_tautology``.
"""

import hy

from hylogic.formulas import formula, pretty, basic
from hylogic.evaluate import evaluate
from hylogic.truth import truth_table, propositions, counterexample, connective_tables
from hylogic.resolution import prove, clausify
from hylogic.rewrite import normalize, make_rule
from hylogic.argument import Argument
from hylogic.connectives import CONNECTIVES
from hylogic import truth as _truth

is_tautology = getattr(_truth, hy.mangle("tautology?"))
is_satisfiable = getattr(_truth, hy.mangle("satisfiable?"))
is_contradiction = getattr(_truth, hy.mangle("contradiction?"))
is_equivalent = getattr(_truth, hy.mangle("equivalent?"))
entails = getattr(_truth, hy.mangle("entails?"))

__version__ = "1.0.0"

__all__ = [
    "formula", "pretty", "basic", "evaluate", "truth_table", "propositions",
    "counterexample", "connective_tables", "prove", "clausify", "normalize",
    "make_rule", "Argument", "CONNECTIVES", "is_tautology", "is_satisfiable",
    "is_contradiction", "is_equivalent", "entails",
]
