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

from collections.abc import Mapping
from dataclasses import dataclass
from typing import List, Optional, Tuple

from ..state.balances import BalanceTable, PubKey
from ..state.intents import Intent, IntentKind, require_exact_intent
from ..state.lp import LPTable
from ..state.pools import PoolState
from .batch_clearing import validate_settlement as validate_settlement_legacy
from .domain_limits import is_strict_int
from .settlement import Fill, FillAction, Settlement
from .settlement_canonical_deltas import aggregate_balance_deltas as _aggregate_balance_deltas
from .settlement_canonical_deltas import aggregate_lp_deltas as _aggregate_lp_deltas
from .settlement_canonical_deltas import aggregate_reserve_deltas as _aggregate_reserve_deltas
from .settlement_canonical_deltas import check_canonical_deltas as _check_canonical_deltas
from .settlement_cow_pairs import (
    validate_cow_pair_index as _validate_cow_pair_index,
)
from .settlement_quote_binding import (
    validate_quote_binding_transport as _validate_quote_binding_transport,
)
from .settlement_replay_add_liquidity import AddLiquidityReplayRequest as _AddLiquidityReplayRequest
from .settlement_replay_add_liquidity import replay_add_liquidity_fill as _replay_add_liquidity_fill
from .settlement_replay_context import ReplayContext as _ReplayContext
from .settlement_replay_context import SettlementPreState as _SettlementPreState
from .settlement_replay_context import build_replay_context as _build_replay_context
from .settlement_replay_create_pool import replay_create_pool_fill as _replay_create_pool_fill
from .settlement_replay_index import SettlementIndex as _SettlementIndex
from .settlement_replay_index import (
    build_settlement_index as _build_settlement_index,
)
from .settlement_replay_remove_liquidity import (
    RemoveLiquidityReplayRequest as _RemoveLiquidityReplayRequest,
)
from .settlement_replay_remove_liquidity import (
    replay_remove_liquidity_fill as _replay_remove_liquidity_fill,
)
from .settlement_replay_swaps import ProtocolFeeReplayConfig as _ProtocolFeeReplayConfig
from .settlement_replay_swaps import SwapIntentReplayRequest as _SwapIntentReplayRequest
from .settlement_replay_swaps import replay_swap_intent as _run_swap_intent_replay

_MODE_STRONG_REPLAY = "strong_replay"
_MODE_STRONG_PROOF_CARRYING = "strong_proof_carrying"
_VALIDATION_MODES = frozenset({_MODE_STRONG_REPLAY, _MODE_STRONG_PROOF_CARRYING})
_FAIL_CLOSED_VALIDATOR_ERRORS = (
    TypeError,
    ValueError,
    ArithmeticError,
    LookupError,
    AttributeError,
    RuntimeError,
    AssertionError,
)


@dataclass(frozen=True)
class _StrongValidationRequest:
    settlement: Settlement
    intents: List[Intent]
    pre_state: _SettlementPreState
    mode: str
    allow_cow_netting: bool
    allow_snapshot_bound_quote_bindings: bool
    protocol_fee_share_bps: int
    protocol_fee_recipient_pubkey: Optional[PubKey]


@dataclass(frozen=True)
class _IntentReplayEnvironment:
    request: _StrongValidationRequest
    settlement_index: _SettlementIndex
    replay: _ReplayContext
    protocol_fee: _ProtocolFeeReplayConfig


@dataclass(frozen=True)
class _PoolIntentReplayRequest:
    intent: Intent
    fill: Fill
    pool_target: _PoolReplayTarget
    quote_pool_fp: object
    env: _IntentReplayEnvironment


@dataclass(frozen=True)
class _PoolReplayTarget:
    pool_id: str
    pool: PoolState
    recipient: PubKey


def _validate_replayed_payload(
    *,
    settlement: Settlement,
    replay: _ReplayContext,
    pre_state: _SettlementPreState,
) -> Tuple[bool, Optional[str]]:
    expected_balance = _aggregate_balance_deltas(replay.bal_deltas)
    expected_reserve = _aggregate_reserve_deltas(replay.res_deltas)
    expected_lp = _aggregate_lp_deltas(replay.lp_deltas)

    ok, err = _check_canonical_deltas(settlement)
    if not ok:
        return False, err

    if settlement.balance_deltas != expected_balance:
        return False, "balance_deltas mismatch vs replay"
    if settlement.reserve_deltas != expected_reserve:
        return False, "reserve_deltas mismatch vs replay"
    if settlement.lp_deltas != expected_lp:
        return False, "lp_deltas mismatch vs replay"

    got_events_norm = settlement.events or []
    if got_events_norm != replay.expected_events:
        return False, "events mismatch vs replay"

    # Defense-in-depth: ensure basic conservation/non-negativity in addition to replay checks.
    # This is essential when a fill type does not touch pool reserves (e.g. COW_NETTED),
    # where conservation must be enforced globally across balance deltas.
    ok_legacy, err_legacy = validate_settlement_legacy(
        settlement=settlement,
        pre_balances=pre_state.balances,
        pre_pools=pre_state.pools,
        pre_lp_balances=pre_state.lp_balances,
    )
    if not ok_legacy:
        return False, f"legacy validation failed: {err_legacy}"

    return True, None


def _replay_included_intents(env: _IntentReplayEnvironment) -> Tuple[bool, Optional[str]]:
    for intent_id, action in env.request.settlement.included_intents:
        err = _replay_included_intent(intent_id=intent_id, action=action, env=env)
        if err is not None:
            return False, err
    return True, None


def _replay_included_intent(
    *,
    intent_id: str,
    action: FillAction,
    env: _IntentReplayEnvironment,
) -> Optional[str]:
    intent = env.settlement_index.intents_by_id[intent_id]
    quote_binding_error = _validate_quote_binding_transport(
        intent,
        allow_snapshot_bound_quote_bindings=env.request.allow_snapshot_bound_quote_bindings,
    )
    if quote_binding_error is not None:
        return quote_binding_error
    if action == FillAction.REJECT:
        return None

    fill = env.settlement_index.fill_by_id[intent_id]
    recipient: PubKey = intent.get_field("recipient", intent.sender_pubkey)
    if not isinstance(recipient, str) or not recipient:
        return f"invalid recipient for intent_id={intent_id}"

    if intent.kind == IntentKind.CREATE_POOL:
        return _replay_create_pool_fill(intent=intent, fill=fill, replay=env.replay)

    pool_id = intent.get_field("pool_id")
    if not isinstance(pool_id, str) or not pool_id:
        return f"missing pool_id for intent_id={intent_id}"
    if pool_id not in env.replay.pools:
        return f"pool not found for intent_id={intent_id}: {pool_id}"

    pool_target = _PoolReplayTarget(pool_id=pool_id, pool=env.replay.pools[pool_id], recipient=recipient)
    return _replay_pool_intent(
        request=_PoolIntentReplayRequest(
            intent=intent,
            fill=fill,
            pool_target=pool_target,
            quote_pool_fp=intent.get_field("quote_pool_fingerprint"),
            env=env,
        ),
    )


def _replay_pool_intent(*, request: _PoolIntentReplayRequest) -> Optional[str]:
    if request.intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        return _replay_swap_intent(request=request)
    if request.intent.kind == IntentKind.ADD_LIQUIDITY:
        return _replay_add_liquidity_fill(
            request=_AddLiquidityReplayRequest(
                intent=request.intent,
                fill=request.fill,
                pool=request.pool_target.pool,
                pool_id=request.pool_target.pool_id,
                recipient=request.pool_target.recipient,
                replay=request.env.replay,
            )
        )
    if request.intent.kind == IntentKind.REMOVE_LIQUIDITY:
        return _replay_remove_liquidity_fill(
            request=_RemoveLiquidityReplayRequest(
                intent=request.intent,
                fill=request.fill,
                pool=request.pool_target.pool,
                pool_id=request.pool_target.pool_id,
                recipient=request.pool_target.recipient,
                replay=request.env.replay,
            )
        )
    return f"unsupported intent kind for strong validation: {request.intent.kind}"


def _replay_swap_intent(*, request: _PoolIntentReplayRequest) -> Optional[str]:
    return _run_swap_intent_replay(
        request=_SwapIntentReplayRequest(
            intent=request.intent,
            fill=request.fill,
            pool=request.pool_target.pool,
            pool_id=request.pool_target.pool_id,
            recipient=request.pool_target.recipient,
            quote_pool_fp=request.quote_pool_fp,
            require_reserve_witness=request.env.request.mode == _MODE_STRONG_PROOF_CARRYING,
            allow_cow_netting=request.env.request.allow_cow_netting,
            protocol_fee=request.env.protocol_fee,
            replay=request.env.replay,
        )
    )


def _validate_strong_request_preflight(request: _StrongValidationRequest) -> Optional[str]:
    if request.mode not in _VALIDATION_MODES:
        return f"unsupported validation mode: {request.mode!r}"
    if not is_strict_int(request.protocol_fee_share_bps) or not (0 <= request.protocol_fee_share_bps <= 10000):
        return "protocol_fee_share_bps must be an int in [0, 10000]"
    if request.protocol_fee_share_bps > 0 and not request.protocol_fee_recipient_pubkey:
        return "protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0"
    return None


def _build_validated_settlement_index(
    request: _StrongValidationRequest,
) -> Tuple[Optional[_SettlementIndex], Optional[str]]:
    settlement_index, err_index = _build_settlement_index(
        settlement=request.settlement,
        intents=request.intents,
    )
    if settlement_index is None:
        return None, err_index or "settlement index construction failed"

    ok_cow, err_cow = _validate_cow_pair_index(
        settlement=request.settlement,
        intents_by_id=settlement_index.intents_by_id,
        fill_by_id=settlement_index.fill_by_id,
        allow_cow_netting=request.allow_cow_netting,
    )
    if not ok_cow:
        return None, err_cow
    return settlement_index, None


def _build_intent_replay_environment(
    *,
    request: _StrongValidationRequest,
    settlement_index: _SettlementIndex,
) -> _IntentReplayEnvironment:
    replay = _build_replay_context(
        pre_balances=request.pre_state.balances,
        pre_pools=request.pre_state.pools,
        pre_lp_balances=request.pre_state.lp_balances,
    )
    return _IntentReplayEnvironment(
        request=request,
        settlement_index=settlement_index,
        replay=replay,
        protocol_fee=_ProtocolFeeReplayConfig(
            share_bps=int(request.protocol_fee_share_bps),
            recipient_pubkey=request.protocol_fee_recipient_pubkey,
        ),
    )


def validate_settlement_strong(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: BalanceTable,
    pre_pools: Mapping[str, PoolState],
    pre_lp_balances: Optional[LPTable] = None,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> Tuple[bool, Optional[str]]:
    """
    Fail-closed wrapper around the strong validator implementation.

    This validator is used on untrusted settlement proposals; it must return `(False, reason)`
    rather than crash on malformed inputs.
    """
    try:
        for intent in intents:
            require_exact_intent(intent)
        request = _StrongValidationRequest(
            settlement=settlement,
            intents=intents,
            pre_state=_SettlementPreState(
                balances=pre_balances,
                pools=pre_pools,
                lp_balances=pre_lp_balances,
            ),
            mode=mode,
            allow_cow_netting=allow_cow_netting,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        )
        return _validate_settlement_strong_impl(request=request)
    except _FAIL_CLOSED_VALIDATOR_ERRORS as exc:
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
    request: _StrongValidationRequest,
) -> Tuple[bool, Optional[str]]:
    """
    Strong settlement validation.

    This is intended to be used in `dex.step` as a fail-closed acceptance gate.
    """
    err = _validate_strong_request_preflight(request)
    if err is not None:
        return False, err
    settlement_index, err = _build_validated_settlement_index(request)
    if settlement_index is None:
        return False, err
    env = _build_intent_replay_environment(request=request, settlement_index=settlement_index)
    ok_replay, err_replay = _replay_included_intents(env)
    if not ok_replay:
        return False, err_replay

    return _validate_replayed_payload(
        settlement=request.settlement,
        replay=env.replay,
        pre_state=request.pre_state,
    )
