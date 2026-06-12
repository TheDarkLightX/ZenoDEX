"""Validate the shared SPARK/Rust/Python burn-rail vectors.

The vectors in ``spark-kernels/burn_rails/test_vectors.json`` are generated
from the authoritative Python burn rails. The SPARK kernel is advisory until
`gnatprove` evidence exists, so this test only pins the shared oracle file and
the Python-side conservation identity.
"""

from __future__ import annotations

import json
import importlib.util
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
VECTORS = REPO / "spark-kernels" / "burn_rails" / "test_vectors.json"
GEN = REPO / "spark-kernels" / "burn_rails"

if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

_SPEC = importlib.util.spec_from_file_location(
    "burn_rails_export_test_vectors",
    GEN / "export_test_vectors.py",
)
assert _SPEC is not None and _SPEC.loader is not None
export_test_vectors = importlib.util.module_from_spec(_SPEC)
sys.modules[_SPEC.name] = export_test_vectors
_SPEC.loader.exec_module(export_test_vectors)


def test_vectors_match_python_rails():
    data = json.loads(VECTORS.read_text(encoding="utf-8"))
    assert data["kernel"] == "burn_rail_conservation"
    assert data["cases"], "vector file is empty"
    for case in data["cases"]:
        expected = case["expected"]
        assert export_test_vectors._burn_accepts(
            case["supply_before"],
            case["burn_amount"],
            case["batch_before"],
            case["burn_budget"],
            expected["supply_after"],
            expected["batch_after"],
        ), case
        assert (
            case["supply_before"] - expected["supply_after"]
            == expected["batch_after"] - case["batch_before"]
            == case["burn_amount"]
        ), case


def test_vectors_file_is_up_to_date():
    on_disk = VECTORS.read_text(encoding="utf-8")
    fresh = export_test_vectors.serialize(export_test_vectors.build_vectors())
    assert on_disk == fresh, (
        "spark-kernels/burn_rails/test_vectors.json is stale; regenerate with:\n"
        "  python3 spark-kernels/burn_rails/export_test_vectors.py"
    )
