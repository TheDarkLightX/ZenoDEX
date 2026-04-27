from __future__ import annotations

import importlib.util
import os
from pathlib import Path

import pytest

from src.fire.verifier.esso_kernels_v1 import (
    FIRE_ESSO_KERNEL_CHECK_REPORT_SCHEMA,
    verify_fire_esso_kernels,
)


ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "fire_burn_boost_call_v1.yaml"


def _esso_available() -> bool:
    return importlib.util.find_spec("ESSO") is not None


@pytest.mark.skipif(
    os.environ.get("ZENO_SKIP_ESSO") == "1" or not _esso_available(),
    reason="ESSO checks disabled or ESSO module unavailable",
)
def test_esso_fire_burn_boost_call_v1_verifies() -> None:
    ok, err, payload = verify_fire_esso_kernels(model_paths=[MODEL], repo_root=ROOT)
    assert ok, err or payload
    assert payload["schema"] == FIRE_ESSO_KERNEL_CHECK_REPORT_SCHEMA
    assert payload["ok"] is True
    assert payload["case_count"] == 1

    case = payload["cases"][0]
    assert case["model_path"] == str(MODEL.resolve())
    assert case["validate_ok"] is True
    assert case["verify_ok"] is True
    assert case["determinism"] is True
    assert case["verdict"] == "VERIFIED"
    assert case["inconclusive_queries"] == 0
    assert case["solvers_agreed"] is True
