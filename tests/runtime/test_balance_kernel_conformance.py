"""Phase 6 acceptance: Python/Rust balance-kernel conformance (differential).

Skipped (not failed) when neither a prebuilt binary nor ``cargo`` is available.
Paired with — never a substitute for — the semantic invariants in
``test_balance_kernel_semantic_invariants.py``.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE = REPO / "tests" / "runtime" / "golden_traces" / "balance_smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import balance_kernel_lib  # noqa: E402
from rust_shadow_replay import (  # noqa: E402
    ShadowError,
    diff_trace_against_rust,
    locate_or_build_cli,
    run_rust_replay,
)

PKS = ["0x" + f"{t:02x}" * 48 for t in (0x11, 0x22, 0x33)]
ASSETS = ["0x" + f"{t:02x}" * 32 for t in (0xAA, 0xBB)]
MAX = (1 << 112) - 1


@pytest.fixture(scope="session")
def rust_bin() -> Path:
    try:
        return locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _run_rust_on_txs(rust_bin: Path, txs: list, tmp_path: Path) -> dict:
    trace = {"version": 1, "kernel": "balances", "steps": [{"tx": tx} for tx in txs]}
    trace_path = tmp_path / "b_diff.json"
    trace_path.write_text(json.dumps(trace), encoding="utf-8")
    return run_rust_replay(rust_bin, trace_path)


def test_rust_matches_recorded_smoke_trace(rust_bin):
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    rust = run_rust_replay(rust_bin, TRACE)
    diffs = diff_trace_against_rust(trace, rust)
    assert diffs == [], "\n\n".join(diffs)


def test_info_separator_whitespace_canonicalization_matches_python(rust_bin, tmp_path):
    txs = [
        {
            "kind": "credit",
            "recipient": f"\x1c{PKS[0]}\x1f",
            "asset": f"\x1d{ASSETS[0][2:]}\x1e",
            "amount": 100,
        }
    ]
    python_out = balance_kernel_lib.replay_txs(txs)
    rust_out = _run_rust_on_txs(rust_bin, txs, tmp_path)
    assert python_out == rust_out


def _pk(rng):
    return rng.choice(PKS + ["0x11", "", 123, PKS[0].upper(), PKS[1][2:], f"  {PKS[2].upper()}  "])


def _asset(rng):
    return rng.choice(ASSETS + ["0xbb", "", 1, ASSETS[0][2:], f"  {ASSETS[1].upper()}  "])


def _amount(rng):
    return rng.choice([1, 10, 500, 5000, 0, -1, MAX, MAX + 1, 1 << 120, "5", 1.5, True])


def _random_tx(rng: random.Random) -> dict:
    if rng.random() < 0.45:
        tx = {"kind": "credit", "recipient": _pk(rng), "asset": _asset(rng), "amount": _amount(rng)}
    else:
        tx = {
            "kind": "transfer",
            "sender": _pk(rng),
            "recipient": _pk(rng),
            "asset": _asset(rng),
            "amount": _amount(rng),
        }
    roll = rng.random()
    if roll < 0.05:
        tx["kind"] = "mint"
    elif roll < 0.10:
        tx["extra"] = 1
    elif roll < 0.13 and "amount" in tx:
        del tx["amount"]
    return tx


def test_randomized_differential(rust_bin, tmp_path):
    rng = random.Random(20260528)
    # Seed a few valid credits up front so transfers can sometimes succeed.
    txs = [
        {"kind": "credit", "recipient": PKS[0], "asset": ASSETS[0], "amount": 10_000},
        {"kind": "credit", "recipient": PKS[1], "asset": ASSETS[1], "amount": 10_000},
    ]
    txs += [_random_tx(rng) for _ in range(400)]

    python_out = balance_kernel_lib.replay_txs([json.loads(json.dumps(tx)) for tx in txs])
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

    accepts = sum(1 for r in rust_out["results"] if r["accept"])
    assert 0 < accepts < len(txs)


def test_reject_precedence_parity(rust_bin, tmp_path):
    """Deterministic reject-precedence parity — the differential complement to the
    Kani ``transfer_reject_precedence`` proof on the Rust core.

    Each boundary tx trips multiple reject conditions at once; Python and Rust
    must agree on the full result, and the FIRST reject in the fixed order
    (sender, recipient, asset, amount, self-transfer, insufficient, overflow)
    must win — pinning reject-code parity, not just accept/reject parity.
    """
    a, b, x = PKS[0], PKS[1], ASSETS[0]
    bad_pk, bad_ast = "0x11", "0xbb"
    cases: list[tuple[list, dict, str]] = [
        # invalid sender beats invalid recipient + invalid asset + amount=0
        ([], _t(bad_pk, bad_pk, bad_ast, 0), "invalid_sender"),
        # invalid recipient beats invalid asset + amount=0
        ([], _t(a, bad_pk, bad_ast, 0), "invalid_recipient"),
        # invalid asset beats amount=0 + self-transfer
        ([], _t(a, b, bad_ast, 0), "invalid_asset"),
        # invalid amount beats self-transfer (snd==rcp, amount=0)
        ([], _t(a, a, x, 0), "invalid_amount"),
        # self-transfer beats insufficient (valid amount, snd==rcp)
        ([], _t(a, a, x, 5), "self_transfer"),
        # insufficient beats overflow: sender balance 0 < amount, AND recipient
        # is at MAX so overflow WOULD fire (5 + MAX > MAX) were insufficient not
        # checked first — pinning the insufficient-before-overflow order.
        ([_c(b, x, MAX)], _t(a, b, x, 5), "insufficient_balance"),
        # overflow: sender sufficient, recipient at MAX -> r + amount > MAX
        (
            [_c(a, x, MAX), _c(b, x, MAX)],
            _t(a, b, x, MAX),
            "balance_overflow",
        ),
    ]
    for setup, boundary, expected in cases:
        txs = setup + [boundary]
        py = balance_kernel_lib.replay_txs([json.loads(json.dumps(t)) for t in txs])
        ru = _run_rust_on_txs(rust_bin, txs, tmp_path)
        assert py == ru, (
            f"python/rust diverged for {expected}:\n"
            f"  python={json.dumps(py['results'][-1])}\n"
            f"  rust  ={json.dumps(ru['results'][-1])}"
        )
        last = ru["results"][-1]
        assert last["accept"] is False
        assert last["reject_reason"] == expected, (
            f"expected first-in-order {expected!r}, got "
            f"{last['reject_reason']!r} for {json.dumps(boundary)}"
        )


def _c(recipient: str, asset: str, amount: int) -> dict:
    return {"kind": "credit", "recipient": recipient, "asset": asset, "amount": amount}


def _t(sender: str, recipient: str, asset: str, amount: int) -> dict:
    return {
        "kind": "transfer",
        "sender": sender,
        "recipient": recipient,
        "asset": asset,
        "amount": amount,
    }
