"""
Shared logic for ZenoDEX replay-guard golden-trace export / replay.

Sibling of ``golden_trace_lib`` for the ``replay_guard`` kernel (Phase 6,
surface 1). The trace schema is identical (version / kernel / steps with
``tx`` / ``expected_accept`` / ``expected_reject_reason`` / ``post_state_root`` /
``receipt_hash``); only the ``tx`` shape and the transition differ:

    "tx": { "kind": "admit", "sender": "0x<96 hex>", "nonce": 3 }

Callers must ensure the repo root is on ``sys.path``.
"""

from __future__ import annotations

from typing import Any

from src.core.replay_guard import (
    AdmitAccepted,
    AdmitRejected,
    AdmitResult,
    ReplayGuardState,
    admit,
)

SCHEMA_VERSION = 1
KERNEL = "replay_guard"

REJ_MALFORMED_TX = "malformed_tx"
REJ_UNKNOWN_TX_KIND = "unknown_tx_kind"
REJ_UNKNOWN_FIELD = "unknown_field"

_TX_FIELDS = frozenset({"kind", "sender", "nonce"})


def reason_str(rejected: AdmitRejected) -> str:
    if rejected.detail is None:
        return rejected.reason
    return f"{rejected.reason}:{rejected.detail}"


def apply_tx(state: ReplayGuardState, tx: Any) -> AdmitResult:
    """Apply one trace ``tx`` to ``state``; never raises on malformed input."""
    if not isinstance(tx, dict):
        return AdmitRejected(REJ_MALFORMED_TX)
    if tx.get("kind") != "admit":
        return AdmitRejected(REJ_UNKNOWN_TX_KIND)
    extra = set(tx) - _TX_FIELDS
    if extra:
        return AdmitRejected(REJ_UNKNOWN_FIELD, sorted(extra)[0])
    if "sender" not in tx or "nonce" not in tx:
        return AdmitRejected(REJ_MALFORMED_TX)
    # admit validates sender (format) before nonce (range), then the policy.
    return admit(state=state, sender=tx["sender"], nonce=tx["nonce"])


def _record_step(state: ReplayGuardState, tx: dict) -> tuple[dict, ReplayGuardState]:
    pre_root = state.state_root()
    result = apply_tx(state, tx)
    if isinstance(result, AdmitAccepted):
        return (
            {
                "tx": tx,
                "expected_accept": True,
                "expected_reject_reason": None,
                "post_state_root": result.state.state_root(),
                "receipt_hash": result.receipt.receipt_hash(),
            },
            result.state,
        )
    return (
        {
            "tx": tx,
            "expected_accept": False,
            "expected_reject_reason": reason_str(result),
            "post_state_root": pre_root,  # rejected => state unchanged
            "receipt_hash": None,
        },
        state,
    )


def _admit_tx(sender: str, nonce: Any) -> dict:
    return {"kind": "admit", "sender": sender, "nonce": nonce}


# Two valid 48-byte (96 hex char) senders for the corpus.
_A = "0x" + "11" * 48
_B = "0x" + "22" * 48


def smoke_tx_sequence() -> list[dict]:
    """Deterministic replay-guard corpus: sequential accept, duplicate/replay/gap
    rejection, cross-sender independence, and invalid/structural rejections."""
    return [
        _admit_tx(_A, 1),  # accept
        _admit_tx(_B, 1),  # accept (independent of A)
        _admit_tx(_A, 2),  # accept
        _admit_tx(_B[2:], 2),  # accept: raw hex canonicalizes like NonceTable
        _admit_tx(_A, 2),  # duplicate_nonce
        _admit_tx(_A, 1),  # stale_nonce (replay of older)
        _admit_tx(_B, 2),  # duplicate_nonce after raw-hex B nonce 2
        _admit_tx(_A, 4),  # nonce_gap (last A = 2)
        _admit_tx(_A, 3),  # accept
        _admit_tx("0xzz" + "11" * 47, 1),  # invalid_sender
        _admit_tx(_A, 0),  # invalid_nonce (below range)
        _admit_tx(_A, (1 << 40)),  # invalid_nonce (above u32)
        {"kind": "admit", "sender": _A, "nonce": 4, "memo": "x"},  # unknown_field
        {"kind": "transfer", "sender": _A, "nonce": 4},  # unknown_tx_kind
        {"kind": "admit", "sender": _A},  # malformed_tx (missing nonce)
        _admit_tx(_B, 3),  # accept (B independent, last B = 2)
        _admit_tx(_A, 4),  # accept (A last = 3)
    ]


def build_smoke_trace() -> dict:
    state = ReplayGuardState()
    initial_root = state.state_root()
    steps: list[dict] = []
    for tx in smoke_tx_sequence():
        step, state = _record_step(state, tx)
        steps.append(step)
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": initial_root,
        "steps": steps,
        "final_state_root": state.state_root(),
    }


def replay_txs(txs: list) -> dict:
    """Replay a bare ``tx`` list; return a doc shaped like the Rust CLI output."""
    state = ReplayGuardState()
    initial_root = state.state_root()
    results: list[dict] = []
    for i, tx in enumerate(txs):
        pre_root = state.state_root()
        result = apply_tx(state, tx)
        if isinstance(result, AdmitAccepted):
            state = result.state
            results.append(
                {
                    "index": i,
                    "accept": True,
                    "reject_reason": None,
                    "receipt_hash": result.receipt.receipt_hash(),
                    "pre_state_root": pre_root,
                    "post_state_root": state.state_root(),
                }
            )
        else:
            results.append(
                {
                    "index": i,
                    "accept": False,
                    "reject_reason": reason_str(result),
                    "receipt_hash": None,
                    "pre_state_root": pre_root,
                    "post_state_root": pre_root,
                }
            )
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": initial_root,
        "final_state_root": state.state_root(),
        "results": results,
    }


class ReplayMismatch(Exception):
    """Raised when a replay disagrees with the recorded golden trace."""


def replay_trace(trace: dict) -> dict:
    """Replay ``trace`` through the Python authority and verify every field."""
    if not isinstance(trace, dict):
        raise ReplayMismatch("trace must be a JSON object")
    if trace.get("version") != SCHEMA_VERSION:
        raise ReplayMismatch(f"unsupported trace version: {trace.get('version')!r}")
    if trace.get("kernel") != KERNEL:
        raise ReplayMismatch(f"unsupported kernel: {trace.get('kernel')!r}")

    state = ReplayGuardState()
    initial_root = state.state_root()
    if trace.get("initial_state_root") != initial_root:
        raise ReplayMismatch(
            f"initial_state_root mismatch: trace={trace.get('initial_state_root')} "
            f"computed={initial_root}"
        )

    steps = trace.get("steps")
    if not isinstance(steps, list):
        raise ReplayMismatch("steps must be a list")

    n_accept = 0
    n_reject = 0
    for i, step in enumerate(steps):
        pre_root = state.state_root()
        tx = step.get("tx")
        result = apply_tx(state, tx)
        if isinstance(result, AdmitAccepted):
            n_accept += 1
            if step.get("expected_accept") is not True:
                raise ReplayMismatch(f"step {i}: accepted but trace expected reject; tx={tx}")
            if step.get("receipt_hash") != result.receipt.receipt_hash():
                raise ReplayMismatch(f"step {i}: receipt_hash mismatch; tx={tx}")
            if step.get("post_state_root") != result.state.state_root():
                raise ReplayMismatch(f"step {i}: post_state_root mismatch; tx={tx}")
            state = result.state
        else:
            n_reject += 1
            if step.get("expected_accept") is not False:
                raise ReplayMismatch(
                    f"step {i}: rejected ({reason_str(result)}) but trace expected accept; tx={tx}"
                )
            if step.get("expected_reject_reason") != reason_str(result):
                raise ReplayMismatch(
                    f"step {i}: reject reason mismatch trace={step.get('expected_reject_reason')} "
                    f"computed={reason_str(result)}; tx={tx}"
                )
            if step.get("post_state_root") != pre_root:
                raise ReplayMismatch(f"step {i}: rejected step changed post_state_root; tx={tx}")
            if step.get("receipt_hash") is not None:
                raise ReplayMismatch(f"step {i}: rejected step has non-null receipt_hash; tx={tx}")

    final_root = state.state_root()
    if trace.get("final_state_root") != final_root:
        raise ReplayMismatch(
            f"final_state_root mismatch: trace={trace.get('final_state_root')} "
            f"computed={final_root}"
        )

    return {
        "steps": len(steps),
        "accepted": n_accept,
        "rejected": n_reject,
        "final_state_root": final_root,
    }
