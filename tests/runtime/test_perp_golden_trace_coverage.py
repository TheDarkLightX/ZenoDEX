"""Coverage guard for isolated-perps golden traces.

The per-op conformance suites replay these traces through the Rust CLI. This
meta-test keeps the inventory honest: a new committed perps trace must be wired
into a conformance test instead of silently relying on ad hoc replay.
"""

from __future__ import annotations

import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
TRACE_DIR = REPO / "tests" / "runtime" / "golden_traces"

PERP_TRACE_TESTS = {
    "account_op_smoke.json": "tests/runtime/test_perp_account_ops_conformance.py",
    "advance_epoch_smoke.json": "tests/runtime/test_perp_advance_epoch_conformance.py",
    "funding_auto_smoke.json": "tests/runtime/test_perp_funding_auto_conformance.py",
    "partial_liquidate_smoke.json": "tests/runtime/test_perp_partial_liquidate_conformance.py",
    "publish_clearing_price_smoke.json": "tests/runtime/test_perp_publish_clearing_price_conformance.py",
    "set_market_params_smoke.json": "tests/runtime/test_perp_set_market_params_conformance.py",
    "settle_epoch_smoke.json": "tests/runtime/test_perp_settle_epoch_conformance.py",
}


def _kernel(trace_path: Path) -> str:
    return str(json.loads(trace_path.read_text(encoding="utf-8")).get("kernel", ""))


def test_all_perp_golden_traces_are_conformance_wired() -> None:
    committed_perp_traces = {
        trace_path.name
        for trace_path in TRACE_DIR.glob("*.json")
        if _kernel(trace_path).startswith("perp_")
    }
    assert committed_perp_traces == set(PERP_TRACE_TESTS)

    for trace_name, test_relpath in PERP_TRACE_TESTS.items():
        test_path = REPO / test_relpath
        assert test_path.is_file()
        assert trace_name in test_path.read_text(encoding="utf-8")
