"""Smoke tests for generated Python reference models of derivative kernels.

These reference implementations are generated from YAML kernel specs and checked
into `generated/` so CI can sanity-check codegen without requiring the external
verification/codegen toolchain to be installed.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest


def _ref_dir() -> Path:
    return Path(__file__).resolve().parents[2] / "generated" / "derivatives_python"


def _maybe_add_ref_dir() -> None:
    ref_dir = _ref_dir()
    if not ref_dir.is_dir():
        pytest.skip(f"generated refs not found at {ref_dir}", allow_module_level=True)
    if str(ref_dir) not in sys.path:
        sys.path.insert(0, str(ref_dir))


_maybe_add_ref_dir()


def test_funding_rate_market_ref_import_and_one_step() -> None:
    import funding_rate_market_v1_ref as ref  # type: ignore

    s = ref.init_state()
    ok, failed = ref.check_invariants(s)
    assert ok, failed

    cmd = ref.Command(
        tag="open_rate_long",
        args={"amount": 1, "new_implied_rate_bps": 0, "auth_ok": True},
    )
    res = ref.step(s, cmd)
    assert res.ok, res.error
    assert res.state is not None


def test_funding_rate_market_v1_1_ref_import_and_one_step() -> None:
    import funding_rate_market_v1_1_ref as ref  # type: ignore

    s = ref.init_state()
    ok, failed = ref.check_invariants(s)
    assert ok, failed

    cmd = ref.Command(tag="open_rate_long", args={"amount": 1, "auth_ok": True})
    res = ref.step(s, cmd)
    assert res.ok, res.error
    assert res.state is not None


def test_il_futures_market_ref_import_and_one_step() -> None:
    import il_futures_market_v1_ref as ref  # type: ignore

    s = ref.init_state()
    ok, failed = ref.check_invariants(s)
    assert ok, failed

    cmd = ref.Command(tag="open_short_il", args={"amount": 1, "auth_ok": True})
    res = ref.step(s, cmd)
    assert res.ok, res.error
    assert res.state is not None


def test_curve_selection_market_ref_import_and_one_step() -> None:
    import curve_selection_market_v1_ref as ref  # type: ignore

    s = ref.init_state()
    ok, failed = ref.check_invariants(s)
    assert ok, failed

    cmd = ref.Command(
        tag="stake_on_curve", args={"amount": 1, "curve_id": 0, "auth_ok": True}
    )
    res = ref.step(s, cmd)
    assert res.ok, res.error
    assert res.state is not None
