# [TESTER] v1

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from typing import Any

import pytest


def _import_kernel(module_name: str, rel_path: str) -> Any:
    try:
        return __import__(module_name, fromlist=["*"])
    except ModuleNotFoundError:
        root = Path(__file__).resolve().parents[2]
        abs_path = root / rel_path
        if not abs_path.exists():
            pytest.skip(f"Reference kernel not found at {abs_path}")
        spec = importlib.util.spec_from_file_location(module_name, abs_path)
        assert spec and spec.loader, f"Could not load spec for {module_name} from {abs_path}"
        module = importlib.util.module_from_spec(spec)
        sys.modules[module_name] = module
        spec.loader.exec_module(module)
        return module


cpmm = _import_kernel("generated.cpmm_python.cpmm_swap_ref", "generated/cpmm_python/cpmm_swap_ref.py")


def test_generated_cpmm_swap_canonicalizes_history_vars_at_boundary() -> None:
    # If `*_before` vars are user-controlled, pre-invariants can be bypassed / made meaningless.
    # Treat them as internal-only snapshot vars by canonicalizing them at the step boundary.
    state = cpmm.State(
        fee_bps=0,
        reserve_x=10,
        reserve_x_before=50,  # inconsistent on purpose (would fail inv_k_non_decreasing without canonicalization)
        reserve_y=10,
        reserve_y_before=50,
    )
    res = cpmm.step(
        state,
        cpmm.Command(tag="swap_x_for_y", args={"amount_in_x": 2, "min_amount_out": 0}),
    )
    assert res.ok, res.error
