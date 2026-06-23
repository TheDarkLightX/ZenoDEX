"""
Golden-trace harness for the buyback/burn **accounting rails** (Phase 6,
surface 4).

The authority is ``src/core/burn_receipts.py``. This harness drives that
module's four rail functions directly (``_rail_replay_guard``,
``_rail_amount_guard``, ``_rail_supply_guard``, ``_rail_batch_sum_guard``) -- the
buyback-accounting heart: amount/budget (burn floor), supply conservation, and
the public burn accumulator (batch sum). The Rust shadow
(``zenodex-runtime-core::burn_receipts``) mirrors these rails.

The verifier is **stateless** (each ``tx`` is a self-contained rail tuple), so
``post_state_root`` equals ``initial_state_root`` for every step.

Scope: the receipt structural envelope (canonical-JSON ``receipt_hash`` and the
verifier's lenient ``int()`` coercion in ``verify_burn_receipt``) stays
Python-only; this surface shadows the integer rails. See
``docs/runtime/RUNTIME_TRUSTED_CORE_BOUNDARY.md``.

Callers must ensure the repo root is on ``sys.path``.
"""

from __future__ import annotations

from typing import Any

from src.core.burn_receipts import (
    _rail_amount_guard,
    _rail_batch_sum_guard,
    _rail_replay_guard,
    _rail_supply_guard,
)
from src.state.canonical import domain_sep_bytes, encode_uvarint, sha256_hex

SCHEMA_VERSION = 1
KERNEL = "burn_receipts"

REJ_BAD_NUMERIC_FIELD = "bad_numeric_field"
REJ_REPLAY = "replay_guard_failed"
REJ_AMOUNT = "amount_guard_failed"
REJ_SUPPLY = "supply_guard_failed"
REJ_BATCH = "batch_sum_guard_failed"

# Field order (must match the Rust BURN_RAIL_FIELDS order).
_FIELDS = [
    "do_burn",
    "receipt_bound",
    "nullifier_unused",
    "policy_ok",
    "burn_amount",
    "receipt_amount",
    "burn_budget",
    "supply_before",
    "supply_after",
    "batch_burn_sum_before",
    "batch_burn_sum_after",
]


def _is_plain_int(v: object) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def stateless_root() -> str:
    return sha256_hex(domain_sep_bytes("burn_rails_state", version=1))


def rail_receipt_hash(vals: list[int]) -> str:
    payload = bytearray(domain_sep_bytes("burn_rails_receipt", version=1))
    for v in vals:
        payload += encode_uvarint(max(0, v))
    return sha256_hex(bytes(payload))


def apply_tx(tx: Any) -> tuple[bool, str | None, list[int] | None]:
    """Verify the rails of one tuple. Returns (accept, reject_code, vals)."""
    if not isinstance(tx, dict):
        return (False, REJ_BAD_NUMERIC_FIELD, None)
    vals: list[int] = []
    for key in _FIELDS:
        v = tx.get(key)
        if not _is_plain_int(v):
            return (False, REJ_BAD_NUMERIC_FIELD, None)
        vals.append(v)
    d = dict(zip(_FIELDS, vals, strict=True))
    if not _rail_replay_guard(
        do_burn=d["do_burn"],
        receipt_bound=d["receipt_bound"],
        nullifier_unused=d["nullifier_unused"],
        policy_ok=d["policy_ok"],
    ):
        return (False, REJ_REPLAY, None)
    if not _rail_amount_guard(
        do_burn=d["do_burn"],
        burn_amount=d["burn_amount"],
        receipt_amount=d["receipt_amount"],
        burn_budget=d["burn_budget"],
    ):
        return (False, REJ_AMOUNT, None)
    if not _rail_supply_guard(
        do_burn=d["do_burn"],
        burn_amount=d["burn_amount"],
        supply_before=d["supply_before"],
        supply_after=d["supply_after"],
    ):
        return (False, REJ_SUPPLY, None)
    if not _rail_batch_sum_guard(
        do_burn=d["do_burn"],
        burn_amount=d["burn_amount"],
        batch_burn_sum_before=d["batch_burn_sum_before"],
        batch_burn_sum_after=d["batch_burn_sum_after"],
    ):
        return (False, REJ_BATCH, None)
    return (True, None, vals)


def _record_step(tx: dict) -> dict:
    root = stateless_root()
    accept, code, vals = apply_tx(tx)
    if accept:
        assert vals is not None
        return {
            "tx": tx,
            "expected_accept": True,
            "expected_reject_reason": None,
            "post_state_root": root,
            "receipt_hash": rail_receipt_hash(vals),
        }
    return {
        "tx": tx,
        "expected_accept": False,
        "expected_reject_reason": code,
        "post_state_root": root,
        "receipt_hash": None,
    }


def _tuple(**kwargs) -> dict:
    return {k: kwargs[k] for k in _FIELDS}


def _no_burn(supply: int = 100, batch: int = 0) -> dict:
    return _tuple(
        do_burn=0,
        receipt_bound=0,
        nullifier_unused=0,
        policy_ok=0,
        burn_amount=0,
        receipt_amount=0,
        burn_budget=0,
        supply_before=supply,
        supply_after=supply,
        batch_burn_sum_before=batch,
        batch_burn_sum_after=batch,
    )


def _burn(amount: int, *, budget: int | None = None, supply: int = 100, batch: int = 0) -> dict:
    return _tuple(
        do_burn=1,
        receipt_bound=1,
        nullifier_unused=1,
        policy_ok=1,
        burn_amount=amount,
        receipt_amount=amount,
        burn_budget=amount if budget is None else budget,
        supply_before=supply,
        supply_after=supply - amount,
        batch_burn_sum_before=batch,
        batch_burn_sum_after=batch + amount,
    )


def smoke_tx_sequence() -> list[dict]:
    """Deterministic burn-rail corpus: valid no-burn/burn + each rail failure."""
    seq = [
        _no_burn(),  # accept
        _burn(10),  # accept (budget == amount)
        _burn(10, budget=50),  # accept (budget > amount)
        {**_burn(10), "receipt_bound": 0},  # replay_guard_failed
        {**_burn(10), "do_burn": 2},  # replay_guard_failed (not a bit)
        _burn(10, budget=5),  # amount_guard_failed (budget < amount)
        {**_no_burn(), "burn_amount": 5},  # amount_guard_failed (no-burn must be 0)
        {**_burn(10), "receipt_amount": 9},  # amount_guard_failed (mismatch)
        _burn(0x8000),  # amount_guard_failed (out of range)
        {**_burn(10), "supply_after": 95},  # supply_guard_failed (should be 90)
        {**_burn(10, supply=5), "supply_after": -5},  # supply_guard_failed (before < amount handled)
        {**_burn(10), "batch_burn_sum_after": 5},  # batch_sum_guard_failed (should be 10)
        _burn(20, batch=100),  # accept (batch 100 -> 120)
    ]
    # bad_numeric_field: drop a field, and a non-int field.
    missing = _burn(10)
    del missing["burn_budget"]
    seq.append(missing)
    seq.append({**_burn(10), "burn_amount": "10"})
    return seq


def build_smoke_trace() -> dict:
    root = stateless_root()
    steps = [_record_step(tx) for tx in smoke_tx_sequence()]
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": root,
        "steps": steps,
        "final_state_root": root,
    }


def replay_txs(txs: list) -> dict:
    root = stateless_root()
    results: list[dict] = []
    for i, tx in enumerate(txs):
        accept, code, vals = apply_tx(tx)
        results.append(
            {
                "index": i,
                "accept": accept,
                "reject_reason": None if accept else code,
                "receipt_hash": rail_receipt_hash(vals) if accept and vals is not None else None,
                "pre_state_root": root,
                "post_state_root": root,
            }
        )
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": root,
        "final_state_root": root,
        "results": results,
    }


class ReplayMismatch(Exception):
    """Raised when a replay disagrees with the recorded golden trace."""


def replay_trace(trace: dict) -> dict:
    if not isinstance(trace, dict):
        raise ReplayMismatch("trace must be a JSON object")
    if trace.get("version") != SCHEMA_VERSION:
        raise ReplayMismatch(f"unsupported trace version: {trace.get('version')!r}")
    if trace.get("kernel") != KERNEL:
        raise ReplayMismatch(f"unsupported kernel: {trace.get('kernel')!r}")
    root = stateless_root()
    if trace.get("initial_state_root") != root:
        raise ReplayMismatch("initial_state_root mismatch")

    steps = trace.get("steps")
    if not isinstance(steps, list):
        raise ReplayMismatch("steps must be a list")

    n_accept = 0
    n_reject = 0
    for i, rec in enumerate(steps):
        accept, code, vals = apply_tx(rec.get("tx"))
        if accept:
            n_accept += 1
            assert vals is not None
            if rec.get("expected_accept") is not True:
                raise ReplayMismatch(f"step {i}: accepted but trace expected reject")
            if rec.get("receipt_hash") != rail_receipt_hash(vals):
                raise ReplayMismatch(f"step {i}: receipt_hash mismatch")
        else:
            n_reject += 1
            if rec.get("expected_accept") is not False:
                raise ReplayMismatch(f"step {i}: rejected ({code}) but trace expected accept")
            if rec.get("expected_reject_reason") != code:
                raise ReplayMismatch(
                    f"step {i}: reject reason mismatch trace={rec.get('expected_reject_reason')} "
                    f"computed={code}"
                )
        if rec.get("post_state_root") != root:
            raise ReplayMismatch(f"step {i}: post_state_root must equal the stateless root")

    if trace.get("final_state_root") != root:
        raise ReplayMismatch("final_state_root mismatch")
    return {"steps": len(steps), "accepted": n_accept, "rejected": n_reject, "final_state_root": root}
