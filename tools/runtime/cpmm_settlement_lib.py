"""
Golden-trace harness for the CPMM settlement swap kernel (Phase 6, surface 5 —
the batch-clearing settlement primitive).

Authority: ``quote_cpmm_swap_exact_in`` / ``quote_cpmm_swap_exact_out`` in
``src/kernels/python/settlement_swap_runtime_v1.py`` (backed by the v8 CPMM
kernel). This harness drives those directly and threads a single pool's reserves
across a batch order, which is exactly what batch clearing does per-pool once an
ordering is chosen. The Rust shadow is ``zenodex-runtime-core::cpmm_swap``.

``init_pool`` is a setup primitive defined by this surface (not the authority);
its validation is mirrored byte-for-byte in Rust. The swap rejections are mapped
from the authority's exception messages to stable codes.

Scope: single-pool settlement *arithmetic* + per-swap admission (domain bounds,
trade-too-small, slippage). Multi-pool aggregation, the swap-ordering heuristics,
liquidity ops, and CoW netting in ``src/core/batch_clearing.py`` are staged.

Callers must ensure the repo root is on ``sys.path``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.kernels.python.settlement_swap_runtime_v1 import (
    DEX_POOL_RESERVE_MAX,
    DEX_SWAP_AMOUNT_MAX,
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from src.state.canonical import domain_sep_bytes, encode_bytes, encode_uvarint, sha256_hex

SCHEMA_VERSION = 1
KERNEL = "cpmm_settlement"
BPS_DENOM = 10_000

STATE_LABEL = "cpmm_pool"
RECEIPT_LABEL = "cpmm_swap_receipt"

REJ_MALFORMED_TX = "malformed_tx"
REJ_UNKNOWN_TX_KIND = "unknown_tx_kind"
REJ_UNKNOWN_FIELD = "unknown_field"
REJ_ALREADY_INITIALIZED = "already_initialized"
REJ_INVALID_RESERVE = "invalid_reserve"
REJ_INVALID_FEE_BPS = "invalid_fee_bps"
REJ_POOL_NOT_INITIALIZED = "pool_not_initialized"
REJ_SLIPPAGE = "slippage"

_INIT_FIELDS = frozenset({"kind", "reserve0", "reserve1", "fee_bps"})
_EXACT_IN_FIELDS = frozenset({"kind", "zero_for_one", "amount_in", "min_amount_out"})
_EXACT_OUT_FIELDS = frozenset({"kind", "zero_for_one", "amount_out", "max_amount_in"})


def _is_plain_int(v: object) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


@dataclass(frozen=True)
class Pool:
    initialized: bool = False
    reserve0: int = 0
    reserve1: int = 0
    fee_bps: int = 0

    def state_root(self) -> str:
        buf = bytearray(domain_sep_bytes(STATE_LABEL, version=1))
        buf += encode_uvarint(1 if self.initialized else 0)
        buf += encode_uvarint(self.reserve0)
        buf += encode_uvarint(self.reserve1)
        buf += encode_uvarint(self.fee_bps)
        return sha256_hex(bytes(buf))


def receipt_hash(
    kind: str,
    zero_for_one: bool,
    amount_in: int,
    amount_out: int,
    fee_total: int,
    new_r0: int,
    new_r1: int,
) -> str:
    buf = bytearray(domain_sep_bytes(RECEIPT_LABEL, version=1))
    buf += b"KND" + encode_bytes(kind.encode("ascii"))
    buf += b"DIR" + encode_uvarint(1 if zero_for_one else 0)
    buf += b"AIN" + encode_uvarint(amount_in)
    buf += b"AOU" + encode_uvarint(amount_out)
    buf += b"FEE" + encode_uvarint(fee_total)
    buf += b"R0" + encode_uvarint(new_r0)
    buf += b"R1" + encode_uvarint(new_r1)
    return sha256_hex(bytes(buf))


def _map_quote_error(msg: str) -> str:
    """Map an authority quote ValueError message to a stable reject code."""
    if "swap would exceed reserve_in domain max" in msg:
        return "reserve_domain_exceeded"
    if msg.startswith("reserve_in ") or msg.startswith("reserve_out "):
        return "reserve_out_of_domain"
    if msg.startswith("amount_in ") or msg.startswith("amount_out must be >= 1") or (
        msg.startswith("amount_out") and "kernel domain max" in msg
    ):
        return "invalid_amount"
    if "net_in must be positive" in msg or "amount_out is zero" in msg:
        return "trade_too_small"
    if "cannot drain full reserve_out" in msg:
        return "amount_out_ge_reserve"
    if "cannot compute with 100% fee" in msg:
        return "fee_full"
    return f"unmapped:{msg}"


def _directed(pool: Pool, zero_for_one: bool) -> tuple[int, int]:
    return (pool.reserve0, pool.reserve1) if zero_for_one else (pool.reserve1, pool.reserve0)


def apply_tx(pool: Pool, tx: Any) -> tuple[bool, Pool, str | None, str | None]:
    """Apply one tx; returns (accept, new_pool, reject_code, receipt_hash)."""
    if not isinstance(tx, dict):
        return (False, pool, REJ_MALFORMED_TX, None)
    kind = tx.get("kind")
    if kind == "init_pool":
        extra = set(tx) - _INIT_FIELDS
        if extra:
            return (False, pool, f"{REJ_UNKNOWN_FIELD}:{sorted(extra)[0]}", None)
        if pool.initialized:
            return (False, pool, REJ_ALREADY_INITIALIZED, None)
        r0, r1, fee = tx.get("reserve0"), tx.get("reserve1"), tx.get("fee_bps")
        if not (_is_plain_int(r0) and _is_plain_int(r1) and _is_plain_int(fee)):
            return (False, pool, REJ_MALFORMED_TX, None)
        if not (1 <= r0 <= DEX_POOL_RESERVE_MAX) or not (1 <= r1 <= DEX_POOL_RESERVE_MAX):
            return (False, pool, REJ_INVALID_RESERVE, None)
        if not (0 <= fee <= BPS_DENOM):
            return (False, pool, REJ_INVALID_FEE_BPS, None)
        new_pool = Pool(initialized=True, reserve0=r0, reserve1=r1, fee_bps=fee)
        rh = receipt_hash("init_pool", False, 0, 0, 0, r0, r1)
        return (True, new_pool, None, rh)

    if kind in ("swap_exact_in", "swap_exact_out"):
        allowed = _EXACT_IN_FIELDS if kind == "swap_exact_in" else _EXACT_OUT_FIELDS
        extra = set(tx) - allowed
        if extra:
            return (False, pool, f"{REJ_UNKNOWN_FIELD}:{sorted(extra)[0]}", None)
        if not pool.initialized:
            return (False, pool, REJ_POOL_NOT_INITIALIZED, None)
        zfo = tx.get("zero_for_one")
        if not isinstance(zfo, bool):
            return (False, pool, REJ_MALFORMED_TX, None)
        reserve_in, reserve_out = _directed(pool, zfo)

        if kind == "swap_exact_in":
            amount_in = tx.get("amount_in")
            min_out = tx.get("min_amount_out")
            if not (_is_plain_int(amount_in) and _is_plain_int(min_out) and min_out >= 0):
                return (False, pool, REJ_MALFORMED_TX, None)
            try:
                q = quote_cpmm_swap_exact_in(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_in=amount_in,
                    fee_bps=pool.fee_bps,
                )
            except (ValueError, TypeError) as exc:
                return (False, pool, _map_quote_error(str(exc)), None)
            if q.amount_out < min_out:
                return (False, pool, REJ_SLIPPAGE, None)
            new_in, new_out = q.reserve_in_after, q.reserve_out_after
            new_r0, new_r1 = (new_in, new_out) if zfo else (new_out, new_in)
            new_pool = Pool(True, new_r0, new_r1, pool.fee_bps)
            rh = receipt_hash("swap_exact_in", zfo, amount_in, q.amount_out, q.fee_paid, new_r0, new_r1)
            return (True, new_pool, None, rh)

        amount_out = tx.get("amount_out")
        max_in = tx.get("max_amount_in")
        if not (_is_plain_int(amount_out) and _is_plain_int(max_in) and max_in >= 0):
            return (False, pool, REJ_MALFORMED_TX, None)
        try:
            q = quote_cpmm_swap_exact_out(
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_out=amount_out,
                fee_bps=pool.fee_bps,
            )
        except (ValueError, TypeError) as exc:
            return (False, pool, _map_quote_error(str(exc)), None)
        if q.amount_in > max_in:
            return (False, pool, REJ_SLIPPAGE, None)
        new_in, new_out = q.reserve_in_after, q.reserve_out_after
        new_r0, new_r1 = (new_in, new_out) if zfo else (new_out, new_in)
        new_pool = Pool(True, new_r0, new_r1, pool.fee_bps)
        rh = receipt_hash("swap_exact_out", zfo, q.amount_in, amount_out, q.fee_paid, new_r0, new_r1)
        return (True, new_pool, None, rh)

    return (False, pool, REJ_UNKNOWN_TX_KIND, None)


def _record_step(pool: Pool, tx: dict) -> tuple[dict, Pool]:
    pre_root = pool.state_root()
    accept, new_pool, code, rh = apply_tx(pool, tx)
    if accept:
        return (
            {
                "tx": tx,
                "expected_accept": True,
                "expected_reject_reason": None,
                "post_state_root": new_pool.state_root(),
                "receipt_hash": rh,
            },
            new_pool,
        )
    return (
        {
            "tx": tx,
            "expected_accept": False,
            "expected_reject_reason": code,
            "post_state_root": pre_root,
            "receipt_hash": None,
        },
        pool,
    )


def _ein(zfo: bool, amount_in: int, min_out: int = 0) -> dict:
    return {"kind": "swap_exact_in", "zero_for_one": zfo, "amount_in": amount_in, "min_amount_out": min_out}


def _eout(zfo: bool, amount_out: int, max_in: int) -> dict:
    return {"kind": "swap_exact_out", "zero_for_one": zfo, "amount_out": amount_out, "max_amount_in": max_in}


def smoke_tx_sequence() -> list[dict]:
    """Deterministic settlement lifecycle: init, a batch of swaps threaded
    against evolving reserves, plus disaster paths."""
    return [
        {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 10, "min_amount_out": 0},  # pool_not_initialized
        {"kind": "init_pool", "reserve0": 1_000_000, "reserve1": 1_000_000, "fee_bps": 30},  # accept
        {"kind": "init_pool", "reserve0": 1, "reserve1": 1, "fee_bps": 0},  # already_initialized
        _ein(True, 10_000, 0),  # accept (asset0 -> asset1)
        _ein(False, 5_000, 0),  # accept (asset1 -> asset0)
        _eout(True, 5_000, 10_000_000),  # accept (exact out)
        _ein(True, 10_000, 1_000_000_000),  # slippage
        _eout(True, 5_000, 1),  # slippage (max_in too low)
        _ein(True, 0, 0),  # invalid_amount
        _ein(True, DEX_SWAP_AMOUNT_MAX, 0),  # reserve_domain_exceeded
        _eout(True, 2_000_000, 10_000_000),  # amount_out_ge_reserve (>= reserve_out)
        {"kind": "init_pool", "reserve0": 0, "reserve1": 1, "fee_bps": 0},  # already_initialized (init once)
        {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 1, "min_amount_out": 0, "x": 1},  # unknown_field
        {"kind": "frobnicate"},  # unknown_tx_kind
        _ein(True, 50_000, 0),  # accept (continue threading)
        _eout(False, 1_000, 10_000_000),  # accept
    ]


def build_smoke_trace() -> dict:
    pool = Pool()
    initial_root = pool.state_root()
    steps: list[dict] = []
    for tx in smoke_tx_sequence():
        rec, pool = _record_step(pool, tx)
        steps.append(rec)
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": initial_root,
        "steps": steps,
        "final_state_root": pool.state_root(),
    }


def replay_txs(txs: list) -> dict:
    pool = Pool()
    initial_root = pool.state_root()
    results: list[dict] = []
    for i, tx in enumerate(txs):
        pre_root = pool.state_root()
        accept, new_pool, code, rh = apply_tx(pool, tx)
        if accept:
            pool = new_pool
            results.append(
                {
                    "index": i,
                    "accept": True,
                    "reject_reason": None,
                    "receipt_hash": rh,
                    "pre_state_root": pre_root,
                    "post_state_root": pool.state_root(),
                }
            )
        else:
            results.append(
                {
                    "index": i,
                    "accept": False,
                    "reject_reason": code,
                    "receipt_hash": None,
                    "pre_state_root": pre_root,
                    "post_state_root": pre_root,
                }
            )
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": initial_root,
        "final_state_root": pool.state_root(),
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
    pool = Pool()
    if trace.get("initial_state_root") != pool.state_root():
        raise ReplayMismatch("initial_state_root mismatch")
    steps = trace.get("steps")
    if not isinstance(steps, list):
        raise ReplayMismatch("steps must be a list")
    n_accept = 0
    n_reject = 0
    for i, rec in enumerate(steps):
        pre_root = pool.state_root()
        accept, new_pool, code, rh = apply_tx(pool, rec.get("tx"))
        if accept:
            n_accept += 1
            if rec.get("expected_accept") is not True:
                raise ReplayMismatch(f"step {i}: accepted but trace expected reject")
            if rec.get("receipt_hash") != rh:
                raise ReplayMismatch(f"step {i}: receipt_hash mismatch")
            if rec.get("post_state_root") != new_pool.state_root():
                raise ReplayMismatch(f"step {i}: post_state_root mismatch")
            pool = new_pool
        else:
            n_reject += 1
            if rec.get("expected_accept") is not False:
                raise ReplayMismatch(f"step {i}: rejected ({code}) but trace expected accept")
            if rec.get("expected_reject_reason") != code:
                raise ReplayMismatch(
                    f"step {i}: reject reason mismatch trace={rec.get('expected_reject_reason')} "
                    f"computed={code}"
                )
            if rec.get("post_state_root") != pre_root:
                raise ReplayMismatch(f"step {i}: rejected step changed post_state_root")
    if trace.get("final_state_root") != pool.state_root():
        raise ReplayMismatch("final_state_root mismatch")
    return {"steps": len(steps), "accepted": n_accept, "rejected": n_reject, "final_state_root": pool.state_root()}
