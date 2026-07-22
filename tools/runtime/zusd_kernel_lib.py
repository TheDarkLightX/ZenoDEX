"""
Golden-trace harness for the zUSD kernel (Phase 6, surface 3).

Unlike the other surfaces, zUSD already has an authoritative pure transition in
``src/core/zusd.py`` (single-vault ``step``). This harness **drives that
authority directly** -- it does not define a second semantics (Hard Rule #5).
It adds only what the trace format needs: a canonical state root over
``ZUSDState`` and a receipt hash, plus a mapping from ``zusd.py``'s human error
prose to the stable reject codes the Rust shadow emits.

``tx`` shape: ``{"kind": <command>, ...args}`` (e.g.
``{"kind": "mint_zusd", "amount_e8": 20000000000}``,
``{"kind": "bootstrap_oracle", "auth_ok": true, "price_e8": 100000000}``).

Callers must ensure the repo root is on ``sys.path``.
"""

from __future__ import annotations

from typing import Any

from src.core.zusd import ZUSDCommand, ZUSDState, init_state
from src.core.zusd import _step_python as step
from src.state.canonical import domain_sep_bytes, encode_bytes, encode_uvarint, sha256_hex

SCHEMA_VERSION = 1
KERNEL = "zusd"

STATE_DOMAIN_SEP_LABEL = "zusd_state"
RECEIPT_DOMAIN_SEP_LABEL = "zusd_receipt"
STATE_VERSION = 1
RECEIPT_VERSION = 1

REJ_MALFORMED_TX = "malformed_tx"

# ``ZUSDState`` field order (must match the Rust ``ZusdState::fields`` order).
_STATE_FIELD_ORDER = [
    "now_epoch",
    "oracle_seen",  # encoded as 0/1
    "oracle_last_update_epoch",
    "price_e8",
    "price_pending_e8",
    "max_oracle_staleness_epochs",
    "collateral_e8",
    "debt_e8",
    "free_debt_e8",
    "sp_debt_e8",
    "sp_coll_e8",
    "protocol_collateral_e8",
    "protocol_revenue_zusd_cum_e8",
    "liquidator_compensation_collateral_cum_e8",
    "mcr_bps",
    "ccr_bps",
    "min_debt_open_e8",
    "max_debt_e8",
    "max_debt_supply_e8",
    "max_sp_coll_e8",
    "max_protocol_coll_e8",
    "base_rate_bps",
    "base_rate_last_epoch",
    "base_rate_decay_per_epoch_bps",
    "base_rate_borrow_bump_bps",
    "base_rate_redeem_bump_bps",
    "borrow_fee_floor_bps",
    "borrow_fee_max_bps",
    "redemption_fee_floor_bps",
    "redemption_fee_max_bps",
    "liquidation_gas_comp_fixed_collateral_e8",
    "liquidation_gas_comp_bps",
]

# Numeric args per command (everything else, e.g. auth_ok, is a flag).
_COMMAND_TAGS = frozenset(
    {
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
    }
)

# Exact zusd.py error string -> stable code (mirrored by the Rust shadow).
_ERROR_CODE = {
    "oracle already bootstrapped": "oracle_already_bootstrapped",
    "bootstrap_oracle requires auth_ok=true": "bootstrap_requires_auth",
    "oracle not bootstrapped": "oracle_not_bootstrapped",
    "oracle_report requires auth_ok=true": "report_requires_auth",
    "oracle_report requires non-increasing pending price": "report_price_not_non_increasing",
    "oracle_commit requires auth_ok=true": "commit_requires_auth",
    "oracle_commit blocked: vault below MCR at pending price": "commit_below_mcr",
    "insufficient collateral": "insufficient_collateral",
    "withdraw blocked by oracle freeze/staleness/recovery mode": "withdraw_blocked_oracle",
    "withdraw would violate MCR": "withdraw_violates_mcr",
    "mint blocked by oracle freeze/staleness/recovery mode": "mint_blocked_oracle",
    "mint below min_debt_open_e8": "mint_below_min_debt",
    "mint exceeds per-vault max_debt_e8": "mint_exceeds_max_debt",
    "mint exceeds max_debt_supply_e8": "mint_exceeds_max_supply",
    "mint would violate MCR": "mint_violates_mcr",
    "repay exceeds debt": "repay_exceeds_debt",
    "repay exceeds free debt balance": "repay_exceeds_free_debt",
    "repay would leave debt below min_debt_open_e8": "repay_below_min_debt",
    "deposit_sp exceeds free debt balance": "deposit_sp_exceeds_free_debt",
    "deposit_sp exceeds max_debt_supply_e8": "deposit_sp_exceeds_max_supply",
    "withdraw_sp exceeds sp_debt": "withdraw_sp_exceeds_sp_debt",
    "withdraw_sp blocked by oracle freeze/staleness/recovery mode": "withdraw_sp_blocked_oracle",
    "withdraw_sp blocked: vault not at MCR": "withdraw_sp_below_mcr",
    "redemption requires initialized oracle": "redeem_oracle_uninitialized",
    "redemption blocked by oracle pending mismatch": "redeem_pending_mismatch",
    "redemption blocked by stale oracle": "redeem_stale_oracle",
    "redemption exceeds debt": "redeem_exceeds_debt",
    "redemption exceeds free debt": "redeem_exceeds_free_debt",
    "redemption amount too small at current price": "redeem_amount_too_small",
    "insufficient vault collateral for redemption": "redeem_insufficient_collateral",
    "redemption fee consumes all collateral": "redeem_fee_consumes_all",
    "protocol collateral cap exceeded": "redeem_protocol_cap_exceeded",
    "redemption would leave debt below min_debt_open_e8": "redeem_below_min_debt",
    "redemption would violate MCR": "redeem_violates_mcr",
    "liquidation requires initialized pending oracle price": "liquidate_oracle_uninitialized",
    "no debt to liquidate": "liquidate_no_debt",
    "vault not under MCR at pending price": "liquidate_not_under_mcr",
    "stability pool cannot absorb debt": "liquidate_sp_cannot_absorb",
    "stability pool collateral cap exceeded": "liquidate_sp_cap_exceeded",
}


def error_to_code(error: str) -> str:
    """Map a zusd.py error string to a stable reject code (mirrored in Rust)."""
    if error in _ERROR_CODE:
        return _ERROR_CODE[error]
    if error.endswith("must be a positive int"):
        return "not_positive_int"
    if error.endswith("exceeds MAX_AMOUNT_E8") or error.endswith("must be non-negative"):
        return "bounded_check_failed"
    if error.startswith("invariant violation:"):
        return "invariant_violation"
    if error.startswith("unknown action:"):
        return "unknown_action"
    # Surface (rather than hide) anything unmapped; the differential will flag it.
    return f"unmapped:{error}"


def state_root(state: ZUSDState) -> str:
    payload = bytearray(domain_sep_bytes(STATE_DOMAIN_SEP_LABEL, version=STATE_VERSION))
    for name in _STATE_FIELD_ORDER:
        value = getattr(state, name)
        payload += encode_uvarint(1 if value is True else (0 if value is False else int(value)))
    return sha256_hex(bytes(payload))


def receipt_hash(tag: str, post_state_root: str) -> str:
    root_bytes = bytes.fromhex(post_state_root[2:])
    payload = (
        domain_sep_bytes(RECEIPT_DOMAIN_SEP_LABEL, version=RECEIPT_VERSION)
        + b"TAG"
        + encode_bytes(tag.encode("ascii"))
        + b"RT"
        + encode_bytes(root_bytes)
    )
    return sha256_hex(payload)


def apply_tx(state: ZUSDState, tx: Any) -> tuple[bool, ZUSDState | None, str | None, str | None]:
    """Apply one trace ``tx``. Returns (ok, new_state, tag, reject_code)."""
    if not isinstance(tx, dict):
        return (False, None, None, REJ_MALFORMED_TX)
    tag = tx.get("kind")
    args = {k: v for k, v in tx.items() if k != "kind"}
    result = step(state, ZUSDCommand(tag=tag, args=args))
    if result.ok:
        assert result.state is not None
        return (True, result.state, str(tag), None)
    return (False, None, None, error_to_code(result.error or ""))


def _record_step(state: ZUSDState, tx: dict) -> tuple[dict, ZUSDState]:
    pre_root = state_root(state)
    ok, ns, tag, code = apply_tx(state, tx)
    if ok:
        assert ns is not None and tag is not None
        post_root = state_root(ns)
        return (
            {
                "tx": tx,
                "expected_accept": True,
                "expected_reject_reason": None,
                "post_state_root": post_root,
                "receipt_hash": receipt_hash(tag, post_root),
            },
            ns,
        )
    return (
        {
            "tx": tx,
            "expected_accept": False,
            "expected_reject_reason": code,
            "post_state_root": pre_root,
            "receipt_hash": None,
        },
        state,
    )


_PRICE = 100_000_000  # $1.00 in e8
_COLL = 100_000_000_000  # 1000 collateral units (e8)
_MINT = 20_000_000_000  # 200 zUSD (>= min_debt_open 100e8)


def smoke_tx_sequence() -> list[dict]:
    """Deterministic zUSD lifecycle: oracle bootstrap, deposit, mint, repay,
    redeem, plus disaster paths (auth, MCR, min-debt, oracle freeze, ...)."""
    return [
        {"kind": "mint_zusd", "amount_e8": _MINT},  # mint_blocked_oracle (no oracle)
        {
            "kind": "bootstrap_oracle",
            "auth_ok": False,
            "price_e8": _PRICE,
        },  # bootstrap_requires_auth
        {"kind": "bootstrap_oracle", "auth_ok": True, "price_e8": _PRICE},  # accept
        {
            "kind": "bootstrap_oracle",
            "auth_ok": True,
            "price_e8": _PRICE,
        },  # oracle_already_bootstrapped
        {"kind": "mint_zusd", "amount_e8": _MINT},  # mint_violates_mcr (no collateral)
        {"kind": "deposit_collateral", "amount_e8": _COLL},  # accept
        {"kind": "mint_zusd", "amount_e8": 1},  # mint_below_min_debt
        {"kind": "mint_zusd", "amount_e8": _MINT},  # accept
        {"kind": "repay_zusd", "amount_e8": 5_000_000_000},  # accept (repay 50)
        {"kind": "redeem_zusd", "amount_e8": 1_000_000_000},  # accept (redeem 10)
        {"kind": "withdraw_collateral", "amount_e8": _COLL},  # withdraw_violates_mcr (debt open)
        {"kind": "advance_epoch", "delta": 5},  # accept
        {"kind": "advance_epoch", "delta": 0},  # not_positive_int
        {
            "kind": "oracle_report",
            "auth_ok": True,
            "price_e8": 90_000_000,
        },  # accept (pending <= active)
        {
            "kind": "oracle_report",
            "auth_ok": True,
            "price_e8": 200_000_000,
        },  # report_price_not_non_increasing
        {"kind": "mint_zusd", "amount_e8": _MINT},  # mint_blocked_oracle (pending != active)
        {"kind": "oracle_commit", "auth_ok": True},  # accept (commit pending)
        {"kind": "frobnicate", "amount_e8": 1},  # unknown_action
        {"kind": "repay_zusd", "amount_e8": 999_000_000_000},  # repay_exceeds_debt
        {"kind": "redeem_zusd", "amount_e8": 999_000_000_000},  # redeem_exceeds_debt
    ]


def build_smoke_trace() -> dict:
    state = init_state()
    initial_root = state_root(state)
    steps: list[dict] = []
    for tx in smoke_tx_sequence():
        step_rec, state = _record_step(state, tx)
        steps.append(step_rec)
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": initial_root,
        "steps": steps,
        "final_state_root": state_root(state),
    }


def replay_txs(txs: list) -> dict:
    """Replay a bare ``tx`` list; return a doc shaped like the Rust CLI output."""
    state = init_state()
    initial_root = state_root(state)
    results: list[dict] = []
    for i, tx in enumerate(txs):
        pre_root = state_root(state)
        ok, ns, tag, code = apply_tx(state, tx)
        if ok:
            assert ns is not None and tag is not None
            post_root = state_root(ns)
            results.append(
                {
                    "index": i,
                    "accept": True,
                    "reject_reason": None,
                    "receipt_hash": receipt_hash(tag, post_root),
                    "pre_state_root": pre_root,
                    "post_state_root": post_root,
                }
            )
            state = ns
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
        "final_state_root": state_root(state),
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

    state = init_state()
    if trace.get("initial_state_root") != state_root(state):
        raise ReplayMismatch("initial_state_root mismatch")

    steps = trace.get("steps")
    if not isinstance(steps, list):
        raise ReplayMismatch("steps must be a list")

    n_accept = 0
    n_reject = 0
    for i, rec in enumerate(steps):
        pre_root = state_root(state)
        ok, ns, tag, code = apply_tx(state, rec.get("tx"))
        if ok:
            n_accept += 1
            assert ns is not None and tag is not None
            post_root = state_root(ns)
            if rec.get("expected_accept") is not True:
                raise ReplayMismatch(f"step {i}: accepted but trace expected reject")
            if rec.get("receipt_hash") != receipt_hash(tag, post_root):
                raise ReplayMismatch(f"step {i}: receipt_hash mismatch")
            if rec.get("post_state_root") != post_root:
                raise ReplayMismatch(f"step {i}: post_state_root mismatch")
            state = ns
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

    if trace.get("final_state_root") != state_root(state):
        raise ReplayMismatch("final_state_root mismatch")

    return {
        "steps": len(steps),
        "accepted": n_accept,
        "rejected": n_reject,
        "final_state_root": state_root(state),
    }
