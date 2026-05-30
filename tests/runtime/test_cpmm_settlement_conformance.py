"""Python/Rust conformance regressions for CPMM settlement.

The golden smoke trace covers the normal settlement lifecycle. This file keeps
small boundary traces that are too specific to bury in the smoke corpus.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.kernels.python.settlement_swap_runtime_v1 import (
    DEX_POOL_RESERVE_MAX,
    DEX_SWAP_AMOUNT_MAX,
)
from tools.runtime import cpmm_settlement_lib as cpmm
from tools.runtime import rust_shadow_replay as shadow


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return shadow.locate_or_build_cli()
    except shadow.ShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _trace_from_txs(txs: list[dict]) -> dict:
    pool = cpmm.Pool()
    initial_root = pool.state_root()
    steps = []
    for tx in txs:
        step, pool = cpmm._record_step(pool, tx)
        steps.append(step)
    return {
        "version": cpmm.SCHEMA_VERSION,
        "kernel": cpmm.KERNEL,
        "initial_state_root": initial_root,
        "steps": steps,
        "final_state_root": pool.state_root(),
    }


def _write_trace(tmp_path: Path, trace: dict) -> Path:
    path = tmp_path / "cpmm_boundary_trace.json"
    path.write_text(json.dumps(trace, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    return path


def test_exact_out_reserve_domain_rejection_matches_rust(tmp_path, rust_bin):
    trace = _trace_from_txs(
        [
            {
                "kind": "init_pool",
                "reserve0": DEX_POOL_RESERVE_MAX,
                "reserve1": 1_000_000,
                "fee_bps": 30,
            },
            {
                "kind": "swap_exact_out",
                "zero_for_one": True,
                "amount_out": 1,
                "max_amount_in": DEX_SWAP_AMOUNT_MAX,
            },
        ]
    )
    assert trace["steps"][1]["expected_reject_reason"] == cpmm.REJ_RESERVE_DOMAIN_EXCEEDED

    rust = shadow.run_rust_replay(rust_bin, _write_trace(tmp_path, trace))
    assert shadow.diff_trace_against_rust(trace, rust) == []


def test_exact_out_reserve_domain_takes_precedence_over_gap_policy(tmp_path, rust_bin):
    trace = _trace_from_txs(
        [
            {
                "kind": "init_pool",
                "reserve0": 1_000_000,
                "reserve1": 2_613_288_063,
                "fee_bps": 9_999,
            },
            {
                "kind": "swap_exact_out",
                "zero_for_one": True,
                "amount_out": 884_635_356,
                "max_amount_in": DEX_SWAP_AMOUNT_MAX,
                "max_overdelivery_gap_bps": 0,
            },
        ]
    )
    assert trace["steps"][1]["expected_reject_reason"] == cpmm.REJ_RESERVE_DOMAIN_EXCEEDED

    rust = shadow.run_rust_replay(rust_bin, _write_trace(tmp_path, trace))
    assert shadow.diff_trace_against_rust(trace, rust) == []


def test_exact_out_overdelivery_policy_rejection_matches_rust(tmp_path, rust_bin):
    trace = _trace_from_txs(
        [
            {
                "kind": "init_pool",
                "reserve0": 1,
                "reserve1": 4,
                "fee_bps": 30,
            },
            {
                "kind": "swap_exact_out",
                "zero_for_one": True,
                "amount_out": 1,
                "max_amount_in": 1_000_000,
                "max_overdelivery_gap_bps": 200,
            },
        ]
    )
    assert trace["steps"][1]["expected_reject_reason"] == cpmm.REJ_OVERDELIVERY_GAP

    rust = shadow.run_rust_replay(rust_bin, _write_trace(tmp_path, trace))
    assert shadow.diff_trace_against_rust(trace, rust) == []
