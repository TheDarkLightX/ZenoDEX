"""
Shared logic for ZenoDEX balance-kernel golden-trace export / replay.

Sibling of ``golden_trace_lib`` / ``replay_guard_lib`` for the ``balances``
kernel (Phase 6, surface 2). Same trace schema; the ``tx`` shapes are:

    {"kind": "credit",   "recipient": "0x<96>", "asset": "0x<64>", "amount": N}
    {"kind": "transfer", "sender": "0x<96>", "recipient": "0x<96>",
     "asset": "0x<64>", "amount": N}

Callers must ensure the repo root is on ``sys.path``.
"""

from __future__ import annotations

from typing import Any

from src.core.balance_kernel import (
    BalanceAccepted,
    BalanceRejected,
    BalanceResult,
    BalanceState,
    credit,
    transfer,
)

SCHEMA_VERSION = 1
KERNEL = "balances"

REJ_MALFORMED_TX = "malformed_tx"
REJ_UNKNOWN_TX_KIND = "unknown_tx_kind"
REJ_UNKNOWN_FIELD = "unknown_field"

_CREDIT_FIELDS = frozenset({"kind", "recipient", "asset", "amount"})
_TRANSFER_FIELDS = frozenset({"kind", "sender", "recipient", "asset", "amount"})
_CREDIT_REQUIRED = frozenset({"recipient", "asset", "amount"})
_TRANSFER_REQUIRED = frozenset({"sender", "recipient", "asset", "amount"})


def reason_str(rejected: BalanceRejected) -> str:
    if rejected.detail is None:
        return rejected.reason
    return f"{rejected.reason}:{rejected.detail}"


def apply_tx(state: BalanceState, tx: Any) -> BalanceResult:
    """Apply one trace ``tx`` to ``state``; never raises on malformed input."""
    if not isinstance(tx, dict):
        return BalanceRejected(REJ_MALFORMED_TX)
    kind = tx.get("kind")
    if kind == "credit":
        extra = set(tx) - _CREDIT_FIELDS
        if extra:
            return BalanceRejected(REJ_UNKNOWN_FIELD, sorted(extra)[0])
        if not _CREDIT_REQUIRED <= set(tx):
            return BalanceRejected(REJ_MALFORMED_TX)
        return credit(state=state, recipient=tx["recipient"], asset=tx["asset"], amount=tx["amount"])
    if kind == "transfer":
        extra = set(tx) - _TRANSFER_FIELDS
        if extra:
            return BalanceRejected(REJ_UNKNOWN_FIELD, sorted(extra)[0])
        if not _TRANSFER_REQUIRED <= set(tx):
            return BalanceRejected(REJ_MALFORMED_TX)
        return transfer(
            state=state,
            sender=tx["sender"],
            recipient=tx["recipient"],
            asset=tx["asset"],
            amount=tx["amount"],
        )
    return BalanceRejected(REJ_UNKNOWN_TX_KIND)


def _record_step(state: BalanceState, tx: dict) -> tuple[dict, BalanceState]:
    pre_root = state.state_root()
    result = apply_tx(state, tx)
    if isinstance(result, BalanceAccepted):
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
            "post_state_root": pre_root,
            "receipt_hash": None,
        },
        state,
    )


_A = "0x" + "11" * 48
_B = "0x" + "22" * 48
_C = "0x" + "33" * 48
_X = "0x" + "aa" * 32
_Y = "0x" + "bb" * 32
_MAX = (1 << 112) - 1


def _credit(recipient: str, asset: str, amount: Any) -> dict:
    return {"kind": "credit", "recipient": recipient, "asset": asset, "amount": amount}


def _transfer(sender: str, recipient: str, asset: str, amount: Any) -> dict:
    return {
        "kind": "transfer",
        "sender": sender,
        "recipient": recipient,
        "asset": asset,
        "amount": amount,
    }


def smoke_tx_sequence() -> list[dict]:
    """Deterministic balance corpus: credit/transfer happy paths, supply
    conservation, sparse zeroing, cross-account + cross-asset cases, and every
    rejection code."""
    return [
        _credit(_A, _X, 1000),  # accept
        _credit(_B, _Y, 500),  # accept (different account + asset)
        _transfer(_A, _B, _X, 300),  # accept (A:700, B:300)
        _transfer(_A, _C, _X, 700),  # accept (A:0 -> sparse, C:700)
        _transfer(_A, _B, _X, 1),  # insufficient_balance (A has 0 X)
        _transfer(_B, _A, _Y, 100),  # accept (cross: B Y 400, A Y 100)
        _transfer(_C, _C, _X, 10),  # self_transfer
        _transfer(_A, _B, "0x" + "bb" * 48, 10),  # invalid_asset (48 bytes)
        _transfer("0x11", _B, _X, 10),  # invalid_sender
        _transfer(_C, "0x22", _X, 10),  # invalid_recipient
        _transfer(_C, _A, _X, 0),  # invalid_amount
        _credit(_A, _X, _MAX + 1),  # invalid_amount (above MAX)
        _credit(_B, _Y, _MAX),  # balance_overflow (500 + MAX > MAX)
        {"kind": "credit", "recipient": _A, "asset": _X, "amount": 1, "memo": "x"},  # unknown_field
        {"kind": "mint", "recipient": _A, "asset": _X, "amount": 1},  # unknown_tx_kind
        {"kind": "transfer", "sender": _C, "recipient": _A, "asset": _X},  # malformed_tx
        _transfer(_C, _A, _X, 700),  # accept (C:0 -> sparse, A X:700)
        _credit(_A, _Y, 50),  # accept (A holds both X and Y)
    ]


def build_smoke_trace() -> dict:
    state = BalanceState()
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
    state = BalanceState()
    initial_root = state.state_root()
    results: list[dict] = []
    for i, tx in enumerate(txs):
        pre_root = state.state_root()
        result = apply_tx(state, tx)
        if isinstance(result, BalanceAccepted):
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

    state = BalanceState()
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
        result = apply_tx(state, step.get("tx"))
        if isinstance(result, BalanceAccepted):
            n_accept += 1
            if step.get("expected_accept") is not True:
                raise ReplayMismatch(f"step {i}: accepted but trace expected reject; tx={step.get('tx')}")
            if step.get("receipt_hash") != result.receipt.receipt_hash():
                raise ReplayMismatch(f"step {i}: receipt_hash mismatch; tx={step.get('tx')}")
            if step.get("post_state_root") != result.state.state_root():
                raise ReplayMismatch(f"step {i}: post_state_root mismatch; tx={step.get('tx')}")
            state = result.state
        else:
            n_reject += 1
            if step.get("expected_accept") is not False:
                raise ReplayMismatch(
                    f"step {i}: rejected ({reason_str(result)}) but trace expected accept; "
                    f"tx={step.get('tx')}"
                )
            if step.get("expected_reject_reason") != reason_str(result):
                raise ReplayMismatch(
                    f"step {i}: reject reason mismatch trace={step.get('expected_reject_reason')} "
                    f"computed={reason_str(result)}; tx={step.get('tx')}"
                )
            if step.get("post_state_root") != pre_root:
                raise ReplayMismatch(f"step {i}: rejected step changed post_state_root")
            if step.get("receipt_hash") is not None:
                raise ReplayMismatch(f"step {i}: rejected step has non-null receipt_hash")

    final_root = state.state_root()
    if trace.get("final_state_root") != final_root:
        raise ReplayMismatch(
            f"final_state_root mismatch: trace={trace.get('final_state_root')} computed={final_root}"
        )

    return {
        "steps": len(steps),
        "accepted": n_accept,
        "rejected": n_reject,
        "final_state_root": final_root,
    }
