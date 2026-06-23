"""Phase 6 acceptance: Python/Rust zUSD conformance (differential).

The Rust shadow must agree with the authoritative ``src/core/zusd.py`` on every
input. The randomized corpus deliberately includes amounts above ``u128`` and at
the ``1e30`` bound -- the exact edge a u128-only port would get wrong -- so the
differential exercises the bignum path. Skipped when no Rust toolchain/binary.

Paired with (never a substitute for) the semantic invariants in
``test_zusd_semantic_invariants.py``.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE = REPO / "tests" / "runtime" / "golden_traces" / "zusd_smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import zusd_kernel_lib  # noqa: E402
from rust_shadow_replay import (  # noqa: E402
    ShadowError,
    diff_trace_against_rust,
    locate_or_build_cli,
    run_rust_replay,
)

E8 = 100_000_000
MAX_AMOUNT_E8 = 10**30


@pytest.fixture(scope="session")
def rust_bin() -> Path:
    try:
        return locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _run_rust_on_txs(rust_bin: Path, txs: list, tmp_path: Path) -> dict:
    trace = {"version": 1, "kernel": "zusd", "steps": [{"tx": tx} for tx in txs]}
    trace_path = tmp_path / "z_diff.json"
    trace_path.write_text(json.dumps(trace), encoding="utf-8")
    return run_rust_replay(rust_bin, trace_path)


def test_rust_matches_recorded_smoke_trace(rust_bin):
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    rust = run_rust_replay(rust_bin, TRACE)
    diffs = diff_trace_against_rust(trace, rust)
    assert diffs == [], "\n\n".join(diffs)


def _amount(rng: random.Random):
    return rng.choice(
        [
            1,
            100 * E8,
            rng.randint(1, 5000 * E8),
            MAX_AMOUNT_E8,  # exactly the bound
            MAX_AMOUNT_E8 + 1,  # just over -> bounded / downstream reject
            10**40,  # far beyond u128 -> exercises bignum ordering
            0,  # not positive
            -1,  # not positive
            "5",  # non-integer type
            1.5,  # float
        ]
    )


def _random_tx(rng: random.Random) -> dict:
    tag = rng.choice(
        [
            "advance_epoch",
            "bootstrap_oracle",
            "oracle_report",
            "oracle_commit",
            "deposit_collateral",
            "withdraw_collateral",
            "mint_zusd",
            "repay_zusd",
            "deposit_sp",
            "withdraw_sp",
            "redeem_zusd",
            "liquidate",
            "frobnicate",  # unknown
        ]
    )
    tx: dict = {"kind": tag}
    if tag == "advance_epoch":
        tx["delta"] = rng.choice([1, 5, 0, -1, 10**40])
    elif tag in ("bootstrap_oracle", "oracle_report"):
        tx["auth_ok"] = rng.choice([True, False])
        tx["price_e8"] = rng.choice([E8, E8 // 2, 0, MAX_AMOUNT_E8 + 1])
    elif tag == "oracle_commit":
        tx["auth_ok"] = rng.choice([True, False])
    elif tag != "liquidate":
        tx["amount_e8"] = _amount(rng)
    return tx


def test_randomized_differential(rust_bin, tmp_path):
    rng = random.Random(20260528)
    # Seed a workable lifecycle so mint/redeem can sometimes succeed.
    txs: list = [
        {"kind": "bootstrap_oracle", "auth_ok": True, "price_e8": E8},
        {"kind": "deposit_collateral", "amount_e8": 1_000_000_000_000},
        {"kind": "mint_zusd", "amount_e8": 500 * E8},
    ]
    txs += [_random_tx(rng) for _ in range(500)]

    python_out = zusd_kernel_lib.replay_txs([json.loads(json.dumps(tx)) for tx in txs])
    rust_out = _run_rust_on_txs(rust_bin, txs, tmp_path)

    if python_out != rust_out:
        for i, (p, r) in enumerate(zip(python_out["results"], rust_out["results"], strict=False)):
            if p != r:
                raise AssertionError(
                    f"differential mismatch at step {i}:\n"
                    f"  tx     = {json.dumps(txs[i])}\n"
                    f"  python = {json.dumps(p)}\n"
                    f"  rust   = {json.dumps(r)}"
                )
        assert python_out["final_state_root"] == rust_out["final_state_root"]
        raise AssertionError("documents differ but per-step results matched")

    # The corpus must exercise both accepts and a spread of rejects.
    accepts = sum(1 for r in rust_out["results"] if r["accept"])
    reject_reasons = {r["reject_reason"] for r in rust_out["results"] if not r["accept"]}
    assert accepts > 0
    assert len(reject_reasons) >= 5
    assert not any(r and r.startswith("unmapped:") for r in reject_reasons)
