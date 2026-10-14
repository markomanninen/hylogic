"""The tutorial notebook runs from start to finish without errors."""

import os
from pathlib import Path

import pytest

nbformat = pytest.importorskip("nbformat")
nbclient = pytest.importorskip("nbclient")
pytest.importorskip("ipykernel")

ROOT = Path(__file__).resolve().parent.parent


def test_tutorial_notebook_runs():
    nb = nbformat.read(ROOT / "Hylogic tutorial.ipynb", as_version=4)
    # the kernel imports hylogic from the working tree
    os.environ["PYTHONPATH"] = os.pathsep.join(filter(None, [str(ROOT), os.environ.get("PYTHONPATH")]))
    nbclient.NotebookClient(nb, timeout=120, kernel_name="python3").execute()
    errors = [o for c in nb.cells if c.cell_type == "code" for o in c.get("outputs", []) if o.output_type == "error"]
    assert not errors
