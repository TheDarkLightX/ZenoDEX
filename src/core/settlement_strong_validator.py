"""
Strong settlement validation (proof-carrying friendly).

The legacy validator in `src/core/batch_clearing.py` checks conservation and
non-negativity of the *net* deltas, but it does not bind those deltas to:
  - the user intents (min_out / max_in constraints, recipient rules, etc.)
  - the verified swap kernels (no "k decreases" / free value leaks)

This module treats the settlement as an *untrusted certificate* and replay-
verifies the batch by re-executing each filled intent against local copies of
state using the verified kernels (`amm_dispatch`, `lp_math_v7`, etc). It then
recomputes canonical deltas/events and requires exact match.
"""

from __future__ import annotations

from dataclasses import replace
from typing import Dict, List, Optional, Tuple

from ..state.balances import AssetId, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import PoolState, PoolStatus
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .batch_clearing import validate_settlement as validate_settlement_legacy
from .cpmm import MIN_LP_LOCK, compute_fee_total
from .domain_limits import is_strict_int
from .liquidity import add_liquidity, create_pool, remove_liquidity
from .quote_receipts import pool_state_fingerprint
from .settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement

LP_LOCK_PUBKEY: PubKey = "0x" + "00" * 48

_MODE_STRONG_REPLAY = "strong_replay"
_MODE_STRONG_PROOF_CARRYING = "strong_proof_carrying"
_VALIDATION_MODES = frozenset({_MODE_STRONG_REPLAY, _MODE_STRONG_PROOF_CARRYING})


def _format_error_details(**kwargs: object) -> str:
    parts: list[str] = []
    for key, value in kwargs.items():
        if value is None:
            continue
        parts.append(f"{key}={value!r}")
    return ", ".join(parts)


def _quote_binding_error(reason: str, **kwargs: object) -> str:
    details = _format_error_details(**kwargs)
    if not details:
        return reason
    return f"{reason}: {details}"


def _quote_binding_context(intent: Intent) -> dict[str, object]:
    return {
        "intent_id": intent.intent_id,
        "quote_hash": intent.get_field("quote_receipt_hash"),
        "quote_pool_fingerprint": intent.get_field("quote_pool_fingerprint"),
        "leg_index": intent.get_field("quote_receipt_leg_index"),
        "pool_id": intent.get_field("pool_id"),
    }


def validate_settlement_strong(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable] = None,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
) -> Tuple[bool, Optional[str]]:
    """
    Fail-closed wrapper around the strong validator implementation.

    This validator is used on untrusted settlement proposals; it must return `(False, reason)`
    rather than crash on malformed inputs.
    """
    try:
        return _validate_settlement_strong_impl(
            settlement=settlement,
            intents=intents,
            pre_balances=pre_balances,
            pre_pools=pre_pools,
            pre_lp_balances=pre_lp_balances,
            mode=mode,
            allow_cow_netting=allow_cow_netting,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
        )
    except Exception as exc:
        detail = str(exc).strip()
        if "\n" in detail or "\r" in detail:
            detail = " ".join(detail.split())
        if len(detail) > 200:
            detail = detail[:200]
        if detail:
            return False, f"strong validator crashed: {type(exc).__name__}: {detail}"
        return False, f"strong validator crashed: {type(exc).__name__}"


def _validate_settlement_strong_impl(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable] = None,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
) -> Tuple[bool, Optional[str]]:
    """
    Strong settlement validation.

    This is intended to be used in `dex.step` as a fail-closed acceptance gate.
    """
    if mode not in _VALIDATION_MODES:
        return False, f"unsupported validation mode: {mode!r}"

    # Intents must have unique ids (otherwise settlement semantics are ambiguous).
    intent_ids = [it.intent_id for it in intents]
    if len(intent_ids) != len(set(intent_ids)):
        return False, "duplicate intent_id in input intents"

    intents_by_id: Dict[str, Intent] = {it.intent_id: it for it in intents}

    included_ids = [intent_id for intent_id, _action in settlement.included_intents]
    if set(included_ids) != set(intent_ids):
        missing = sorted(set(intent_ids) - set(included_ids))
        extra = sorted(set(included_ids) - set(intent_ids))
        return False, f"settlement included_intents mismatch: missing={missing} extra={extra}"
    if len(included_ids) != len(set(included_ids)):
        return False, "settlement included_intents contains duplicate intent_id entries"

    # Build fill map. NOTE: Reject actions are allowed to omit fill details.
    fill_ids = [f.intent_id for f in settlement.fills]
    if len(fill_ids) != len(set(fill_ids)):
        return False, "settlement fills contains duplicate intent_id entries"
    extra_fill_ids = sorted(set(fill_ids) - set(intent_ids))
    if extra_fill_ids:
        return False, f"settlement fills contains intent_ids not in input intents: {extra_fill_ids}"
    fill_by_id: Dict[str, Fill] = {f.intent_id: f for f in settlement.fills}
    for intent_id, action in settlement.included_intents:
        f = fill_by_id.get(intent_id)
        if f is None:
            if action == FillAction.FILL:
                return False, f"missing Fill for filled intent_id: {intent_id}"
            continue
        if f.action != action:
            return False, f"Fill.action mismatch for intent_id={intent_id}: {f.action} != {action}"

    # Replay state (pure local copies).
    balances = _copy_balance_table(pre_balances)
    pools: Dict[str, PoolState] = {pool_id: replace(pool) for pool_id, pool in pre_pools.items()}
    lp = _copy_lp_table(pre_lp_balances) if pre_lp_balances is not None else LPTable()

    expected_events: List[dict] = []
    bal_deltas: List[BalanceDelta] = []
    res_deltas: List[ReserveDelta] = []
    lp_deltas: List[LPDelta] = []

    def fail(msg: str) -> Tuple[bool, Optional[str]]:
        return False, msg

    for intent_id, action in settlement.included_intents:
        it = intents_by_id[intent_id]
        quote_receipt_hash = it.get_field("quote_receipt_hash")
        quote_pool_fp = it.get_field("quote_pool_fingerprint")
        quote_leg_index = it.get_field("quote_receipt_leg_index")
        has_quote_binding = (
            quote_receipt_hash is not None
            or quote_pool_fp is not None
            or quote_leg_index is not None
        )
        if has_quote_binding and it.kind not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            return fail(
                _quote_binding_error(
                    "quote receipt binding only supported for swap intents",
                    **_quote_binding_context(it),
                    intent_kind=it.kind.value,
                )
            )
        if quote_leg_index is not None and (
            not is_strict_int(quote_leg_index) or int(quote_leg_index) < 0
        ):
            return fail(_quote_binding_error("invalid quote_receipt_leg_index", **_quote_binding_context(it)))
        if quote_leg_index is not None:
            return fail(
                _quote_binding_error(
                    "quote receipt transport metadata requires validated engine witness",
                    **_quote_binding_context(it),
                    guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
                )
            )
        if quote_receipt_hash is not None:
            if not isinstance(quote_receipt_hash, str) or not quote_receipt_hash:
                return fail(_quote_binding_error("invalid quote_receipt_hash", **_quote_binding_context(it)))
            return fail(
                _quote_binding_error(
                    "quote receipt transport metadata requires validated engine witness",
                    **_quote_binding_context(it),
                    guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
                )
            )
        if quote_pool_fp is not None and (not isinstance(quote_pool_fp, str) or not quote_pool_fp):
            return fail(_quote_binding_error("missing quote_pool_fingerprint", **_quote_binding_context(it)))
        if quote_pool_fp is not None and not allow_snapshot_bound_quote_bindings:
            return fail(
                _quote_binding_error(
                    "quote receipt snapshot binding requires validated engine witness",
                    **_quote_binding_context(it),
                    guidance="only pass sanitized quote_pool_fingerprint through the validated engine path",
                )
            )

        if action == FillAction.REJECT:
            continue

        f = fill_by_id[intent_id]

        sender: PubKey = it.sender_pubkey
        recipient: PubKey = it.get_field("recipient", sender)
        if not isinstance(recipient, str) or not recipient:
            return fail(f"invalid recipient for intent_id={intent_id}")

        if it.kind == IntentKind.CREATE_POOL:
            asset0 = it.get_field("asset0")
            asset1 = it.get_field("asset1")
            fee_bps = it.get_field("fee_bps")
            amount0 = it.get_field("amount0")
            amount1 = it.get_field("amount1")
            created_at = it.get_field("created_at", 0)
            curve_tag = it.get_field("curve_tag", None)
            curve_params = it.get_field("curve_params", None)
            if any(v is None for v in (asset0, asset1, fee_bps, amount0, amount1)):
                return fail(f"missing CREATE_POOL fields for intent_id={intent_id}")
            if not isinstance(asset0, str) or not isinstance(asset1, str):
                return fail(f"invalid CREATE_POOL asset ids for intent_id={intent_id}")
            if not is_strict_int(fee_bps) or not (0 <= fee_bps <= 10000):
                return fail(f"invalid CREATE_POOL fee_bps for intent_id={intent_id}")
            if not is_strict_int(amount0) or amount0 <= 0:
                return fail(f"invalid CREATE_POOL amount0 for intent_id={intent_id}")
            if not is_strict_int(amount1) or amount1 <= 0:
                return fail(f"invalid CREATE_POOL amount1 for intent_id={intent_id}")
            if created_at is not None and (not is_strict_int(created_at) or created_at < 0):
                return fail(f"invalid CREATE_POOL created_at for intent_id={intent_id}")
            created_at_value = 0 if created_at is None else created_at

            try:
                pool_id, created_pool, lp_minted = create_pool(
                    asset0=asset0,
                    asset1=asset1,
                    amount0=amount0,
                    amount1=amount1,
                    fee_bps=fee_bps,
                    creator_pubkey=sender,
                    created_at=created_at_value,
                    curve_tag=curve_tag,
                    curve_params=curve_params,
                )
            except Exception as exc:
                return fail(f"CREATE_POOL computation error for intent_id={intent_id}: {exc}")

            if pool_id in pools:
                return fail(f"CREATE_POOL duplicates existing pool_id={pool_id}")

            # Fill must match the create_pool kernel.
            if int(f.amount0_used or 0) != int(amount0):
                return fail(f"CREATE_POOL fill.amount0_used mismatch for intent_id={intent_id}")
            if int(f.amount1_used or 0) != int(amount1):
                return fail(f"CREATE_POOL fill.amount1_used mismatch for intent_id={intent_id}")
            if int(f.lp_minted or 0) != int(lp_minted):
                return fail(f"CREATE_POOL fill.lp_minted mismatch for intent_id={intent_id}")

            # Apply semantics.
            try:
                balances.subtract(sender, asset0, int(amount0))
                balances.subtract(sender, asset1, int(amount1))
                # LP mint to creator, plus lock.
                lp.add(sender, pool_id, int(lp_minted))
                lp.add(LP_LOCK_PUBKEY, pool_id, int(MIN_LP_LOCK))
            except Exception as exc:
                return fail(f"CREATE_POOL balance/LP apply error for intent_id={intent_id}: {exc}")

            pools[pool_id] = created_pool

            # Expected events and deltas (canonicalized later).
            expected_events.append(
                {
                    "type": "CREATE_POOL",
                    "pool_id": pool_id,
                    "asset0": asset0,
                    "asset1": asset1,
                    "fee_bps": int(fee_bps),
                    "curve_tag": created_pool.curve_tag,
                    "curve_params": created_pool.curve_params,
                    "status": PoolStatus.ACTIVE.value,
                    "created_at": int(created_pool.created_at),
                }
            )

            bal_deltas.append(BalanceDelta(pubkey=sender, asset=asset0, delta_add=0, delta_sub=int(amount0)))
            bal_deltas.append(BalanceDelta(pubkey=sender, asset=asset1, delta_add=0, delta_sub=int(amount1)))

            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=int(amount0), delta_sub=0))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=int(amount1), delta_sub=0))

            lp_deltas.append(LPDelta(pubkey=sender, pool_id=pool_id, delta_add=int(lp_minted), delta_sub=0))
            lp_deltas.append(LPDelta(pubkey=LP_LOCK_PUBKEY, pool_id=pool_id, delta_add=int(MIN_LP_LOCK), delta_sub=0))
            continue

        pool_id = it.get_field("pool_id")
        if not isinstance(pool_id, str) or not pool_id:
            return fail(f"missing pool_id for intent_id={intent_id}")
        if pool_id not in pools:
            return fail(f"pool not found for intent_id={intent_id}: {pool_id}")
        pool = pools[pool_id]

        if it.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            asset_in = it.get_field("asset_in")
            asset_out = it.get_field("asset_out")
            if not isinstance(asset_in, str) or not isinstance(asset_out, str):
                return fail(f"invalid asset_in/out for intent_id={intent_id}")
            if pool.status != PoolStatus.ACTIVE:
                return fail(f"pool not active for intent_id={intent_id}: {pool.status}")
            if {asset_in, asset_out} != {pool.asset0, pool.asset1} or asset_in == asset_out:
                return fail(f"swap asset mismatch for intent_id={intent_id}")
            if quote_pool_fp is not None:
                actual_pool_fp = pool_state_fingerprint(pool)
                if actual_pool_fp != quote_pool_fp:
                    return fail(
                        _quote_binding_error(
                            "quote receipt pool snapshot mismatch",
                            **_quote_binding_context(it),
                            actual_pool_fingerprint=actual_pool_fp,
                        )
                    )

            # CoW netting semantics (optional): direct user-to-user swap, no pool reserve changes.
            if f.reason == "COW_NETTED":
                if not allow_cow_netting:
                    return fail(f"COW_NETTED not allowed for intent_id={intent_id}")
                if it.kind != IntentKind.SWAP_EXACT_IN:
                    return fail(f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}")
                amount_in = it.get_field("amount_in")
                min_out = it.get_field("min_amount_out", 0)
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    return fail(f"invalid amount_in for intent_id={intent_id}")
                if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
                    return fail(f"invalid min_amount_out for intent_id={intent_id}")
                if int(f.fee_paid or 0) != 0:
                    return fail(f"COW_NETTED fee_paid must be 0: intent_id={intent_id}")
                if int(f.amount_in_filled or 0) != int(amount_in):
                    return fail(f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}")
                out_amt = int(f.amount_out_filled or 0)
                if out_amt < int(min_out):
                    return fail(f"COW_NETTED slippage: intent_id={intent_id}")
                try:
                    balances.subtract(sender, asset_in, int(amount_in))
                    balances.add(recipient, asset_out, out_amt)
                except Exception as exc:
                    return fail(f"COW_NETTED apply error for intent_id={intent_id}: {exc}")

                bal_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=int(amount_in)))
                bal_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=out_amt, delta_sub=0))
                continue

            if asset_in == pool.asset0 and asset_out == pool.asset1:
                reserve_in = int(pool.reserve0)
                reserve_out = int(pool.reserve1)
                dir_is_0_to_1 = True
            else:
                reserve_in = int(pool.reserve1)
                reserve_out = int(pool.reserve0)
                dir_is_0_to_1 = False

            if mode == _MODE_STRONG_PROOF_CARRYING:
                if f.reserve_in_before is None or f.reserve_out_before is None:
                    return fail(f"missing swap witness reserves for intent_id={intent_id}")
                if int(f.reserve_in_before) != int(reserve_in) or int(f.reserve_out_before) != int(reserve_out):
                    return fail(f"swap witness reserve mismatch for intent_id={intent_id}")

            if it.kind == IntentKind.SWAP_EXACT_IN:
                amount_in = it.get_field("amount_in")
                min_out = it.get_field("min_amount_out", 0)
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    return fail(f"invalid amount_in for intent_id={intent_id}")
                if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
                    return fail(f"invalid min_amount_out for intent_id={intent_id}")

                if int(f.amount_in_filled or 0) != int(amount_in):
                    return fail(f"swap amount_in_filled mismatch for intent_id={intent_id}")

                try:
                    amount_out, (new_in, new_out) = swap_exact_in_for_pool(
                        pool,
                        reserve_in=int(reserve_in),
                        reserve_out=int(reserve_out),
                        amount_in=int(amount_in),
                    )
                except Exception as exc:
                    return fail(f"swap_exact_in kernel error for intent_id={intent_id}: {exc}")

                if int(f.amount_out_filled or 0) != int(amount_out):
                    return fail(f"swap amount_out_filled mismatch for intent_id={intent_id}")
                if int(amount_out) < int(min_out):
                    return fail(f"swap slippage for intent_id={intent_id}")

                fee = compute_fee_total(int(amount_in), int(pool.fee_bps))
                if int(f.fee_paid or 0) != int(fee):
                    return fail(f"swap fee_paid mismatch for intent_id={intent_id}")

                try:
                    balances.subtract(sender, asset_in, int(amount_in))
                    balances.add(recipient, asset_out, int(amount_out))
                except Exception as exc:
                    return fail(f"swap apply error for intent_id={intent_id}: {exc}")

                # Apply reserve updates.
                if dir_is_0_to_1:
                    pool.reserve0 = int(new_in)
                    pool.reserve1 = int(new_out)
                else:
                    pool.reserve1 = int(new_in)
                    pool.reserve0 = int(new_out)

                bal_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=int(amount_in)))
                bal_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=int(amount_out), delta_sub=0))
                res_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_in, delta_add=int(amount_in), delta_sub=0))
                res_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_out, delta_add=0, delta_sub=int(amount_out)))
                continue

            # SWAP_EXACT_OUT
            amount_out_req = it.get_field("amount_out")
            max_in = it.get_field("max_amount_in")
            if not isinstance(amount_out_req, int) or isinstance(amount_out_req, bool) or amount_out_req <= 0:
                return fail(f"invalid amount_out for intent_id={intent_id}")
            if not isinstance(max_in, int) or isinstance(max_in, bool) or max_in < 0:
                return fail(f"invalid max_amount_in for intent_id={intent_id}")

            if int(f.amount_out_filled or 0) != int(amount_out_req):
                return fail(f"swap amount_out_filled mismatch for intent_id={intent_id}")

            try:
                amount_in_req, (new_in, new_out) = swap_exact_out_for_pool(
                    pool,
                    reserve_in=int(reserve_in),
                    reserve_out=int(reserve_out),
                    amount_out=int(amount_out_req),
                )
            except Exception as exc:
                return fail(f"swap_exact_out kernel error for intent_id={intent_id}: {exc}")

            if int(f.amount_in_filled or 0) != int(amount_in_req):
                return fail(f"swap amount_in_filled mismatch for intent_id={intent_id}")
            if int(amount_in_req) > int(max_in):
                return fail(f"swap slippage for intent_id={intent_id}")

            fee = compute_fee_total(int(amount_in_req), int(pool.fee_bps))
            if int(f.fee_paid or 0) != int(fee):
                return fail(f"swap fee_paid mismatch for intent_id={intent_id}")

            try:
                balances.subtract(sender, asset_in, int(amount_in_req))
                balances.add(recipient, asset_out, int(amount_out_req))
            except Exception as exc:
                return fail(f"swap apply error for intent_id={intent_id}: {exc}")

            if dir_is_0_to_1:
                pool.reserve0 = int(new_in)
                pool.reserve1 = int(new_out)
            else:
                pool.reserve1 = int(new_in)
                pool.reserve0 = int(new_out)

            bal_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=int(amount_in_req)))
            bal_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=int(amount_out_req), delta_sub=0))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_in, delta_add=int(amount_in_req), delta_sub=0))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_out, delta_add=0, delta_sub=int(amount_out_req)))
            continue

        if it.kind == IntentKind.ADD_LIQUIDITY:
            if pool.status != PoolStatus.ACTIVE:
                return fail(f"pool not active for intent_id={intent_id}: {pool.status}")
            amount0_desired = it.get_field("amount0_desired")
            amount1_desired = it.get_field("amount1_desired")
            amount0_min = it.get_field("amount0_min", 0)
            amount1_min = it.get_field("amount1_min", 0)
            if any(v is None for v in (amount0_desired, amount1_desired)):
                return fail(f"missing ADD_LIQUIDITY fields for intent_id={intent_id}")
            if not is_strict_int(amount0_desired) or amount0_desired <= 0:
                return fail(f"invalid amount0_desired for intent_id={intent_id}")
            if not is_strict_int(amount1_desired) or amount1_desired <= 0:
                return fail(f"invalid amount1_desired for intent_id={intent_id}")
            if not is_strict_int(amount0_min) or amount0_min < 0:
                return fail(f"invalid amount0_min for intent_id={intent_id}")
            if not is_strict_int(amount1_min) or amount1_min < 0:
                return fail(f"invalid amount1_min for intent_id={intent_id}")

            try:
                amount0_used, amount1_used, lp_minted = add_liquidity(
                    pool_state=pool,
                    amount0_desired=amount0_desired,
                    amount1_desired=amount1_desired,
                    amount0_min=amount0_min,
                    amount1_min=amount1_min,
                )
            except Exception as exc:
                return fail(f"ADD_LIQUIDITY computation error for intent_id={intent_id}: {exc}")

            if int(f.amount0_used or 0) != int(amount0_used):
                return fail(f"ADD_LIQUIDITY fill.amount0_used mismatch for intent_id={intent_id}")
            if int(f.amount1_used or 0) != int(amount1_used):
                return fail(f"ADD_LIQUIDITY fill.amount1_used mismatch for intent_id={intent_id}")
            if int(f.lp_minted or 0) != int(lp_minted):
                return fail(f"ADD_LIQUIDITY fill.lp_minted mismatch for intent_id={intent_id}")

            try:
                balances.subtract(sender, pool.asset0, int(amount0_used))
                balances.subtract(sender, pool.asset1, int(amount1_used))
                lp.add(recipient, pool_id, int(lp_minted))
            except Exception as exc:
                return fail(f"ADD_LIQUIDITY apply error for intent_id={intent_id}: {exc}")

            pool.reserve0 += int(amount0_used)
            pool.reserve1 += int(amount1_used)
            pool.lp_supply += int(lp_minted)

            bal_deltas.append(BalanceDelta(pubkey=sender, asset=pool.asset0, delta_add=0, delta_sub=int(amount0_used)))
            bal_deltas.append(BalanceDelta(pubkey=sender, asset=pool.asset1, delta_add=0, delta_sub=int(amount1_used)))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset0, delta_add=int(amount0_used), delta_sub=0))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset1, delta_add=int(amount1_used), delta_sub=0))
            lp_deltas.append(LPDelta(pubkey=recipient, pool_id=pool_id, delta_add=int(lp_minted), delta_sub=0))
            continue

        if it.kind == IntentKind.REMOVE_LIQUIDITY:
            if pool.status != PoolStatus.ACTIVE:
                return fail(f"pool not active for intent_id={intent_id}: {pool.status}")
            lp_amount = it.get_field("lp_amount")
            amount0_min = it.get_field("amount0_min", 0)
            amount1_min = it.get_field("amount1_min", 0)
            if lp_amount is None:
                return fail(f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent_id}")
            if not is_strict_int(lp_amount) or lp_amount <= 0:
                return fail(f"invalid lp_amount for intent_id={intent_id}")
            if not is_strict_int(amount0_min) or amount0_min < 0:
                return fail(f"invalid amount0_min for intent_id={intent_id}")
            if not is_strict_int(amount1_min) or amount1_min < 0:
                return fail(f"invalid amount1_min for intent_id={intent_id}")

            try:
                amount0_out, amount1_out = remove_liquidity(
                    pool_state=pool,
                    lp_amount=lp_amount,
                    amount0_min=amount0_min,
                    amount1_min=amount1_min,
                )
            except Exception as exc:
                return fail(f"REMOVE_LIQUIDITY computation error for intent_id={intent_id}: {exc}")

            if int(f.lp_burned or 0) != int(lp_amount):
                return fail(f"REMOVE_LIQUIDITY fill.lp_burned mismatch for intent_id={intent_id}")
            if int(f.amount0_out or 0) != int(amount0_out):
                return fail(f"REMOVE_LIQUIDITY fill.amount0_out mismatch for intent_id={intent_id}")
            if int(f.amount1_out or 0) != int(amount1_out):
                return fail(f"REMOVE_LIQUIDITY fill.amount1_out mismatch for intent_id={intent_id}")

            try:
                lp.subtract(sender, pool_id, int(lp_amount))
                balances.add(recipient, pool.asset0, int(amount0_out))
                balances.add(recipient, pool.asset1, int(amount1_out))
            except Exception as exc:
                return fail(f"REMOVE_LIQUIDITY apply error for intent_id={intent_id}: {exc}")

            pool.reserve0 -= int(amount0_out)
            pool.reserve1 -= int(amount1_out)
            pool.lp_supply -= int(lp_amount)

            lp_deltas.append(LPDelta(pubkey=sender, pool_id=pool_id, delta_add=0, delta_sub=int(lp_amount)))
            bal_deltas.append(BalanceDelta(pubkey=recipient, asset=pool.asset0, delta_add=int(amount0_out), delta_sub=0))
            bal_deltas.append(BalanceDelta(pubkey=recipient, asset=pool.asset1, delta_add=int(amount1_out), delta_sub=0))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset0, delta_add=0, delta_sub=int(amount0_out)))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset1, delta_add=0, delta_sub=int(amount1_out)))
            continue

        return fail(f"unsupported intent kind for strong validation: {it.kind}")

    # Canonicalize and compare the settlement payloads.
    expected_balance = _aggregate_balance_deltas(bal_deltas)
    expected_reserve = _aggregate_reserve_deltas(res_deltas)
    expected_lp = _aggregate_lp_deltas(lp_deltas)

    ok, err = _check_canonical_deltas(settlement)
    if not ok:
        return False, err

    if settlement.balance_deltas != expected_balance:
        return False, "balance_deltas mismatch vs replay"
    if settlement.reserve_deltas != expected_reserve:
        return False, "reserve_deltas mismatch vs replay"
    if settlement.lp_deltas != expected_lp:
        return False, "lp_deltas mismatch vs replay"

    exp_events_norm = expected_events
    got_events_norm = settlement.events or []
    if got_events_norm != exp_events_norm:
        return False, "events mismatch vs replay"

    # Defense-in-depth: ensure basic conservation/non-negativity in addition to replay checks.
    # This is essential when a fill type does not touch pool reserves (e.g. COW_NETTED),
    # where conservation must be enforced globally across balance deltas.
    ok_legacy, err_legacy = validate_settlement_legacy(
        settlement=settlement,
        pre_balances=pre_balances,
        pre_pools=pre_pools,
        pre_lp_balances=pre_lp_balances,
    )
    if not ok_legacy:
        return False, f"legacy validation failed: {err_legacy}"

    return True, None


def _copy_balance_table(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, amount)
    return copied


def _copy_lp_table(lp_balances: LPTable) -> LPTable:
    copied = LPTable()
    for (pubkey, pool_id), amount in lp_balances.get_all_balances().items():
        copied.set(pubkey, pool_id, amount)
    return copied


def _aggregate_balance_deltas(deltas: List[BalanceDelta]) -> List[BalanceDelta]:
    acc: Dict[Tuple[PubKey, AssetId], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pubkey, d.asset)
        add_prev, sub_prev = acc.get(key, (0, 0))
        acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
    out: List[BalanceDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(BalanceDelta(pubkey=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _aggregate_reserve_deltas(deltas: List[ReserveDelta]) -> List[ReserveDelta]:
    acc: Dict[Tuple[str, AssetId], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pool_id, d.asset)
        add_prev, sub_prev = acc.get(key, (0, 0))
        acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
    out: List[ReserveDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(ReserveDelta(pool_id=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _aggregate_lp_deltas(deltas: List[LPDelta]) -> List[LPDelta]:
    acc: Dict[Tuple[PubKey, str], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pubkey, d.pool_id)
        add_prev, sub_prev = acc.get(key, (0, 0))
        acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
    out: List[LPDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(LPDelta(pubkey=key[0], pool_id=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _check_canonical_deltas(settlement: Settlement) -> Tuple[bool, Optional[str]]:
    # Ensure deltas are canonical (one entry per key, sorted, and with non-negative fields).
    def _check_unique_sorted(keys: List[Tuple], what: str) -> Tuple[bool, Optional[str]]:
        if keys != sorted(keys):
            return False, f"{what} not sorted canonically"
        if len(keys) != len(set(keys)):
            return False, f"{what} contains duplicate keys"
        return True, None

    # Balance deltas
    bal_keys: List[Tuple[PubKey, AssetId]] = []
    for balance_delta in settlement.balance_deltas:
        if (
            not isinstance(balance_delta.delta_add, int)
            or isinstance(balance_delta.delta_add, bool)
            or balance_delta.delta_add < 0
        ):
            return False, "balance_deltas contains invalid delta_add"
        if (
            not isinstance(balance_delta.delta_sub, int)
            or isinstance(balance_delta.delta_sub, bool)
            or balance_delta.delta_sub < 0
        ):
            return False, "balance_deltas contains invalid delta_sub"
        if balance_delta.delta_add == 0 and balance_delta.delta_sub == 0:
            return False, "balance_deltas contains a zero entry"
        bal_keys.append((balance_delta.pubkey, balance_delta.asset))
    ok, err = _check_unique_sorted(bal_keys, "balance_deltas")
    if not ok:
        return ok, err

    # Reserve deltas
    res_keys: List[Tuple[str, AssetId]] = []
    for reserve_delta in settlement.reserve_deltas:
        if (
            not isinstance(reserve_delta.delta_add, int)
            or isinstance(reserve_delta.delta_add, bool)
            or reserve_delta.delta_add < 0
        ):
            return False, "reserve_deltas contains invalid delta_add"
        if (
            not isinstance(reserve_delta.delta_sub, int)
            or isinstance(reserve_delta.delta_sub, bool)
            or reserve_delta.delta_sub < 0
        ):
            return False, "reserve_deltas contains invalid delta_sub"
        if reserve_delta.delta_add == 0 and reserve_delta.delta_sub == 0:
            return False, "reserve_deltas contains a zero entry"
        res_keys.append((reserve_delta.pool_id, reserve_delta.asset))
    ok, err = _check_unique_sorted(res_keys, "reserve_deltas")
    if not ok:
        return ok, err

    # LP deltas
    lp_keys: List[Tuple[PubKey, str]] = []
    for lp_delta in settlement.lp_deltas:
        if (
            not isinstance(lp_delta.delta_add, int)
            or isinstance(lp_delta.delta_add, bool)
            or lp_delta.delta_add < 0
        ):
            return False, "lp_deltas contains invalid delta_add"
        if (
            not isinstance(lp_delta.delta_sub, int)
            or isinstance(lp_delta.delta_sub, bool)
            or lp_delta.delta_sub < 0
        ):
            return False, "lp_deltas contains invalid delta_sub"
        if lp_delta.delta_add == 0 and lp_delta.delta_sub == 0:
            return False, "lp_deltas contains a zero entry"
        lp_keys.append((lp_delta.pubkey, lp_delta.pool_id))
    ok, err = _check_unique_sorted(lp_keys, "lp_deltas")
    if not ok:
        return ok, err

    return True, None
