"""
Shared logic for ZenoDEX golden-trace export / replay (fee-router kernel).

A *golden trace* is a deterministic record of a transition sequence produced by
the authoritative Python runtime. It is the conformance anchor for the Rust
shadow runtime: replaying the same ``tx`` list must reproduce every recorded
``post_state_root`` and ``receipt_hash`` exactly.

This module is deliberately small and import-light: it only depends on
``src.core.fee_router`` (which in turn only uses the stdlib + the repo's
canonical encoder). Callers must ensure the repo root is on ``sys.path``.

Trace schema (version 1)::

    {
      "version": 1,
      "kernel": "fee_router",
      "initial_state_root": "0x...",
      "steps": [
        {
          "tx": { "kind": "route_fee", "source": "dex", "asset": "zUSD",
                  "amount": 12347,
                  "split_table": {"buyburn_bps": 6000, "stakers_bps": 0,
                                  "reserve_bps": 2000, "hosts_bps": 2000} },
          "expected_accept": true,
          "expected_reject_reason": null,
          "post_state_root": "0x...",
          "receipt_hash": "0x..."
        }
      ],
      "final_state_root": "0x..."
    }

On a rejected step the accumulator is unchanged, so ``post_state_root`` equals
the pre-step root and ``receipt_hash`` is ``null``. ``expected_reject_reason``
is the stable rejection code, with the domain sub-code appended after ``:`` when
present (e.g. ``"domain_constraint_violated:redemption_buyburn_must_be_zero"``).
"""

from __future__ import annotations

from typing import Any, Union

from src.core.fee_router import (
    FeeAccumulator,
    FeeSplitTable,
    RouteAccepted,
    RouteRejected,
    RouteResult,
    canonical_split_table,
    route_fee,
)

SCHEMA_VERSION = 1
KERNEL = "fee_router"

# Structural rejection codes (produced before the semantic transition runs).
# These are mirrored exactly by the Rust CLI so traces replay identically.
REJ_MALFORMED_TX = "malformed_tx"
REJ_UNKNOWN_TX_KIND = "unknown_tx_kind"
REJ_UNKNOWN_FIELD = "unknown_field"

_TX_FIELDS = frozenset({"kind", "source", "asset", "amount", "split_table"})
_SPLIT_FIELDS = frozenset({"buyburn_bps", "stakers_bps", "reserve_bps", "hosts_bps"})


def _is_plain_int(v: object) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def reject_reason_str(rejected: RouteRejected) -> str:
    """Canonical string form of a rejection: ``reason`` or ``reason:detail``."""
    if rejected.detail is None:
        return rejected.reason
    return f"{rejected.reason}:{rejected.detail}"


def _parse_split_table(value: Any) -> Union[FeeSplitTable, RouteRejected]:
    if not isinstance(value, dict):
        return RouteRejected(REJ_MALFORMED_TX)
    extra = set(value) - _SPLIT_FIELDS
    if extra:
        return RouteRejected(REJ_UNKNOWN_FIELD, sorted(extra)[0])
    missing = _SPLIT_FIELDS - set(value)
    if missing:
        return RouteRejected(REJ_MALFORMED_TX)
    for k in _SPLIT_FIELDS:
        if not _is_plain_int(value[k]):
            return RouteRejected(REJ_MALFORMED_TX)
    return FeeSplitTable(
        buyburn_bps=value["buyburn_bps"],
        stakers_bps=value["stakers_bps"],
        reserve_bps=value["reserve_bps"],
        hosts_bps=value["hosts_bps"],
    )


def apply_tx(accumulator: FeeAccumulator, tx: Any) -> RouteResult:
    """
    Apply one trace ``tx`` to ``accumulator`` and return a :class:`RouteResult`.

    Structural problems map to stable structural codes; otherwise the semantic
    :func:`route_fee` transition runs. Never raises on malformed input.
    """
    if not isinstance(tx, dict):
        return RouteRejected(REJ_MALFORMED_TX)
    if tx.get("kind") != "route_fee":
        return RouteRejected(REJ_UNKNOWN_TX_KIND)
    extra = set(tx) - _TX_FIELDS
    if extra:
        return RouteRejected(REJ_UNKNOWN_FIELD, sorted(extra)[0])

    source = tx.get("source")
    asset = tx.get("asset")
    amount = tx.get("amount")
    if not isinstance(source, str) or not isinstance(asset, str) or not _is_plain_int(amount):
        return RouteRejected(REJ_MALFORMED_TX)

    table = _parse_split_table(tx.get("split_table"))
    if isinstance(table, RouteRejected):
        return table

    return route_fee(
        source=source, asset=asset, amount=amount, split_table=table, accumulator=accumulator
    )


def _record_step(accumulator: FeeAccumulator, tx: dict) -> tuple[dict, FeeAccumulator]:
    """Run ``tx`` and produce the recorded step + the next accumulator."""
    pre_root = accumulator.state_root()
    result = apply_tx(accumulator, tx)
    if isinstance(result, RouteAccepted):
        step = {
            "tx": tx,
            "expected_accept": True,
            "expected_reject_reason": None,
            "post_state_root": result.accumulator.state_root(),
            "receipt_hash": result.receipt.receipt_hash(),
        }
        return step, result.accumulator
    step = {
        "tx": tx,
        "expected_accept": False,
        "expected_reject_reason": reject_reason_str(result),
        "post_state_root": pre_root,  # rejected => state unchanged
        "receipt_hash": None,
    }
    return step, accumulator


def _split_dict(table: FeeSplitTable) -> dict:
    return {
        "buyburn_bps": table.buyburn_bps,
        "stakers_bps": table.stakers_bps,
        "reserve_bps": table.reserve_bps,
        "hosts_bps": table.hosts_bps,
    }


def _tx(source: str, amount: int, split: FeeSplitTable, asset: str = "zUSD") -> dict:
    return {
        "kind": "route_fee",
        "source": source,
        "asset": asset,
        "amount": amount,
        "split_table": _split_dict(split),
    }


def smoke_tx_sequence() -> list[dict]:
    """The fixed, deterministic tx list for the ``smoke`` corpus.

    Covers (in-scope for the fee-router kernel): fee-split conservation across
    all four domains, host fee routing, buyback (buyburn) accrual, dust carry,
    and the rejection paths (domain floors, malformed splits, range, structural).
    """
    dex = canonical_split_table("dex")
    perps = canonical_split_table("perps")
    borrow = canonical_split_table("borrow")
    redemption = canonical_split_table("redemption")
    huge = (1 << 112)  # MAX_FEE_AMOUNT + 1

    return [
        # --- happy: conservation + host routing + buyburn accrual ---
        _tx("dex", 1_000_000, dex),
        _tx("perps", 12_347, perps),  # produces dust
        _tx("borrow", 10_000, borrow),
        _tx("redemption", 10_000, redemption),
        # --- happy: dust carry then release ---
        _tx("dex", 3, dex),
        _tx("dex", 9_999, dex),
        # --- happy: dust is scoped by source and asset ---
        _tx("dex", 1, dex, asset="tZUSD"),
        _tx("dex", 9_999, dex, asset="tAGRS"),
        _tx("perps", 9_999, perps, asset="tZUSD"),
        # --- disaster: domain safety floors ---
        _tx("redemption", 1_000, FeeSplitTable(1, 5_999, 4_000, 0)),
        _tx("redemption", 1_000, FeeSplitTable(0, 5_999, 4_000, 1)),
        _tx("redemption", 1_000, FeeSplitTable(0, 8_001, 1_999, 0)),
        _tx("dex", 1_000, FeeSplitTable(4_999, 1, 3_000, 2_000)),
        _tx("borrow", 1_000, FeeSplitTable(0, 4_999, 3_001, 2_000)),
        # --- disaster: split validity + amount range ---
        _tx("dex", 1_000, FeeSplitTable(6_000, 0, 2_000, 1_999)),  # sum != 10000
        _tx("dex", 1_000, FeeSplitTable(10_001, 0, 0, 0)),  # component out of range
        _tx("dex", -1, dex),  # negative amount
        _tx("dex", huge, dex),  # amount too large
        _tx("lending", 1_000, FeeSplitTable(2_500, 2_500, 2_500, 2_500)),  # unknown domain
        # --- disaster: structural ---
        {"kind": "route_fee", "source": "dex", "asset": "zUSD", "amount": 1,
         "split_table": _split_dict(dex), "memo": "nope"},  # unknown field
        {"kind": "transfer", "source": "dex", "asset": "zUSD", "amount": 1,
         "split_table": _split_dict(dex)},  # unknown tx kind
        # --- happy again: confirm rejections did not perturb threaded state ---
        _tx("dex", 7, dex),
        _tx("perps", 10_000, perps),
    ]


def build_smoke_trace() -> dict:
    """Build the full ``smoke`` golden trace from the authoritative Python runtime."""
    accumulator = FeeAccumulator()
    initial_root = accumulator.state_root()
    steps: list[dict] = []
    for tx in smoke_tx_sequence():
        step, accumulator = _record_step(accumulator, tx)
        steps.append(step)
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": initial_root,
        "steps": steps,
        "final_state_root": accumulator.state_root(),
    }


def replay_txs(txs: list) -> dict:
    """
    Replay a bare ``tx`` list through the authoritative Python runtime and
    return a result document with the **same shape** the Rust CLI emits
    (``initial_state_root`` / ``final_state_root`` / per-step ``results``).

    Used by the Python/Rust differential conformance test so both sides can be
    compared field-by-field with a plain ``==``.
    """
    accumulator = FeeAccumulator()
    initial_root = accumulator.state_root()
    results: list[dict] = []
    for i, tx in enumerate(txs):
        pre_root = accumulator.state_root()
        result = apply_tx(accumulator, tx)
        if isinstance(result, RouteAccepted):
            accumulator = result.accumulator
            results.append(
                {
                    "index": i,
                    "accept": True,
                    "reject_reason": None,
                    "receipt_hash": result.receipt.receipt_hash(),
                    "pre_state_root": pre_root,
                    "post_state_root": accumulator.state_root(),
                }
            )
        else:
            results.append(
                {
                    "index": i,
                    "accept": False,
                    "reject_reason": reject_reason_str(result),
                    "receipt_hash": None,
                    "pre_state_root": pre_root,
                    "post_state_root": pre_root,
                }
            )
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": initial_root,
        "final_state_root": accumulator.state_root(),
        "results": results,
    }


class ReplayMismatch(Exception):
    """Raised when a replay disagrees with the recorded golden trace."""


def replay_trace(trace: dict) -> dict:
    """
    Replay ``trace`` through the authoritative Python runtime and verify every
    recorded field. Returns a small summary dict on success; raises
    :class:`ReplayMismatch` (with a precise message) on the first disagreement.
    """
    if not isinstance(trace, dict):
        raise ReplayMismatch("trace must be a JSON object")
    if trace.get("version") != SCHEMA_VERSION:
        raise ReplayMismatch(f"unsupported trace version: {trace.get('version')!r}")
    if trace.get("kernel") != KERNEL:
        raise ReplayMismatch(f"unsupported kernel: {trace.get('kernel')!r}")

    accumulator = FeeAccumulator()
    initial_root = accumulator.state_root()
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
        pre_root = accumulator.state_root()
        tx = step.get("tx")
        result = apply_tx(accumulator, tx)

        if isinstance(result, RouteAccepted):
            n_accept += 1
            if step.get("expected_accept") is not True:
                raise ReplayMismatch(f"step {i}: accepted but trace expected reject; tx={tx}")
            got_receipt = result.receipt.receipt_hash()
            if step.get("receipt_hash") != got_receipt:
                raise ReplayMismatch(
                    f"step {i}: receipt_hash mismatch trace={step.get('receipt_hash')} "
                    f"computed={got_receipt}; tx={tx}"
                )
            got_root = result.accumulator.state_root()
            if step.get("post_state_root") != got_root:
                raise ReplayMismatch(
                    f"step {i}: post_state_root mismatch trace={step.get('post_state_root')} "
                    f"computed={got_root}; tx={tx}"
                )
            accumulator = result.accumulator
        else:
            n_reject += 1
            if step.get("expected_accept") is not False:
                raise ReplayMismatch(
                    f"step {i}: rejected ({reject_reason_str(result)}) but trace expected accept; "
                    f"tx={tx}"
                )
            got_reason = reject_reason_str(result)
            if step.get("expected_reject_reason") != got_reason:
                raise ReplayMismatch(
                    f"step {i}: reject reason mismatch trace={step.get('expected_reject_reason')} "
                    f"computed={got_reason}; tx={tx}"
                )
            # State must be unchanged on rejection.
            if step.get("post_state_root") != pre_root:
                raise ReplayMismatch(
                    f"step {i}: rejected step changed post_state_root; tx={tx}"
                )
            if step.get("receipt_hash") is not None:
                raise ReplayMismatch(f"step {i}: rejected step has non-null receipt_hash; tx={tx}")

    final_root = accumulator.state_root()
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
