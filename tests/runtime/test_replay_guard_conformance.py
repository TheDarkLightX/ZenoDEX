"""Phase 6 acceptance: Python/Rust replay-guard conformance (differential).

Asserts the Rust shadow admits/rejects identical (sender, nonce) inputs to
identical receipts and state roots as the Python authority. Skipped (not failed)
when neither a prebuilt binary nor ``cargo`` is available.

Per the lessons learned, this differential is paired with — never a substitute
for — the independent semantic invariants in
``test_replay_guard_semantic_invariants.py``.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE = REPO / "tests" / "runtime" / "golden_traces" / "replay_guard_smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import replay_guard_lib  # noqa: E402
from rust_shadow_replay import (  # noqa: E402
    ShadowError,
    diff_trace_against_rust,
    locate_or_build_cli,
    run_rust_replay,
)

VALID_SENDERS = ["0x" + f"{tag:02x}" * 48 for tag in (0x11, 0x22, 0x33)]


@pytest.fixture(scope="session")
def rust_bin() -> Path:
    try:
        return locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _run_rust_on_txs(rust_bin: Path, txs: list, tmp_path: Path) -> dict:
    trace = {"version": 1, "kernel": "replay_guard", "steps": [{"tx": tx} for tx in txs]}
    trace_path = tmp_path / "rg_diff.json"
    trace_path.write_text(json.dumps(trace), encoding="utf-8")
    return run_rust_replay(rust_bin, trace_path)


def test_rust_matches_recorded_smoke_trace(rust_bin):
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    rust = run_rust_replay(rust_bin, TRACE)
    diffs = diff_trace_against_rust(trace, rust)
    assert diffs == [], "\n\n".join(diffs)


def _random_nonce(rng: random.Random):
    return rng.choice([1, 2, 3, 4, 5, 6, 0, -1, 1 << 40, "5", 1.5, True])


def _random_sender(rng: random.Random):
    return rng.choice(
        VALID_SENDERS
        + [
            "0xzz" + "11" * 47,
            "0x11",
            "",
            12345,
            VALID_SENDERS[0].upper(),
            f"\u001c0X{VALID_SENDERS[1][2:].upper()}\u001f",
        ]
    )


def _random_tx(rng: random.Random) -> dict:
    tx = {"kind": "admit", "sender": _random_sender(rng), "nonce": _random_nonce(rng)}
    roll = rng.random()
    if roll < 0.05:
        tx["kind"] = "transfer"
    elif roll < 0.10:
        tx["extra"] = 1
    elif roll < 0.13:
        del tx["nonce"]
    return tx


def test_randomized_differential(rust_bin, tmp_path):
    rng = random.Random(20260528)
    txs = [_random_tx(rng) for _ in range(400)]

    python_out = replay_guard_lib.replay_txs([json.loads(json.dumps(tx)) for tx in txs])
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


def _admit(sender, nonce) -> dict:
    return {"kind": "admit", "sender": sender, "nonce": nonce}


def test_reject_code_parity(rust_bin, tmp_path):
    """Deterministic reject-code + precedence parity — the differential complement
    to the Kani ``classify_sequence`` proof.

    Covers the accept path and all five reject codes (invalid_sender,
    invalid_nonce, duplicate_nonce, stale_nonce, nonce_gap) plus the
    sender-before-nonce precedence. Python and the Rust CLI must agree on the full
    result AND the exact reject code — pinning reject-code parity, not just
    accept/reject parity.
    """
    a, b = VALID_SENDERS[0], VALID_SENDERS[1]
    bad_sender = "0xzz" + "11" * 47  # 96-wide but non-hex -> invalid_sender
    u32_max = 0xFFFFFFFF
    cases: list[tuple[list, dict, object]] = [
        ([], _admit(a, 1), None),  # accept: fresh sender, strict successor
        ([_admit(a, 1)], _admit(a, 1), "duplicate_nonce"),  # re-admit last
        ([_admit(a, 1), _admit(a, 2), _admit(a, 3)], _admit(a, 1), "stale_nonce"),  # below last
        ([], _admit(b, 3), "nonce_gap"),  # fresh sender, skips last+1
        ([], _admit(bad_sender, 1), "invalid_sender"),  # bad sender, valid nonce
        ([], _admit(a, 0), "invalid_nonce"),  # nonce below range
        ([], _admit(a, u32_max + 1), "invalid_nonce"),  # nonce above range
        ([], _admit(bad_sender, 0), "invalid_sender"),  # sender checked before nonce
        ([], _admit(f"\u001c0X{a[2:].upper()}\u001f", 1), None),  # Python strip parity
    ]
    for setup, boundary, expected in cases:
        txs = setup + [boundary]
        py = replay_guard_lib.replay_txs([json.loads(json.dumps(t)) for t in txs])
        ru = _run_rust_on_txs(rust_bin, txs, tmp_path)
        assert py == ru, (
            f"python/rust diverged for {expected}:\n"
            f"  python={json.dumps(py['results'][-1])}\n"
            f"  rust  ={json.dumps(ru['results'][-1])}"
        )
        last = ru["results"][-1]
        if expected is None:
            assert last["accept"] is True, f"expected accept, got {json.dumps(last)}"
        else:
            assert last["accept"] is False
            assert last["reject_reason"] == expected, (
                f"expected {expected!r}, got {last['reject_reason']!r} "
                f"for {json.dumps(boundary)}"
            )
