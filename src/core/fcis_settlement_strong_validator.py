"""Exact-only strong settlement composition for the unmounted FCIS path.

The public boundary recursively revalidates the command, settlement, state,
and context graphs once.  The private evaluator then composes source-owned
exact leaves.  It never imports the mixed validator or a mutable legacy state
type.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, cast, final

from ..state.fcis_curve_config import (
    CURVE_TAG_CPMM,
    canonical_curve_config_fields_v1,
    create_pool_curve_config_v1,
)
from ..state.fcis_execution_context_values import settlement_mode_label_v1
from ..state.fcis_pool_identity import compute_pool_id
from ..state.fcis_spot_replay import (
    FCISSpotDeltaBatchV1,
    FCISSpotReplayDeltaBatchV1,
    FCISSpotReplayOkV1,
    FCISSpotReplayReadSetV1,
    FCISSpotTransitionOkV1,
    apply_fcis_spot_deltas_observed_v1,
    apply_fcis_spot_replay_observed_v1,
)
from ..state.intent_snapshots import (
    OwnedIntentV1,
    admit_intent_batch,
    owned_intent_field_v1,
    owned_intent_kind_text_v1,
    owned_intent_optional_field_v1,
)
from ..state.lp_duration_transitions import (
    LPDurationEventV1,
    LPDurationTransitionRejectV1,
)
from ..state.owned_collections import OwnedMapV1
from ..state.owned_json import OwnedJsonObjectV1
from ..state.pool_creation_transition import PoolCreationV1
from ..state.state_snapshot_values import (
    POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1,
    POOL_STATUS_MEMBER_VALUES_V1,
    CommittedBalanceTableV1,
    CommittedLPTableV1,
    CommittedPoolStateV1,
)
from ..state.state_transitions import (
    BalanceDeltaV1,
    BalancePatchRejectV1,
    LPPositionDeltaV1,
    LPPositionPatchRejectV1,
    PoolPatchRejectV1,
    PoolReserveDeltaV1,
)
from .fcis_amm_dispatch import (
    CommittedPoolSwapQuoteV1,
    quote_exact_in_for_committed_pool_v1,
    quote_exact_out_for_committed_pool_v1,
)
from .fcis_create_pool_event import (
    ExactCreatePoolEventV1,
    create_pool_event_matches_owned_v1,
    exact_create_pool_event_v1,
)
from .fcis_liquidity_kernels import (
    MIN_LP_LOCK,
    AddLiquidityKernelInputV1,
    RemoveLiquidityKernelInputV1,
    add_liquidity_for_committed_pool_v1,
    initial_liquidity_for_pool_creation_v1,
    remove_liquidity_for_committed_pool_v1,
)
from .fcis_pool_fingerprint import pool_state_fingerprint_committed_v1
from .fcis_route_binding import (
    derive_exact_route_binding_v1,
    replay_exact_route_observed_v1,
    route_binding_pins_exact_snapshot_observed_v1,
)
from .fcis_route_binding_values import (
    RouteBindingOkV1,
    RouteBindingRejectV1,
    RouteBindingV1,
    RouteReplayOkV1,
    RouteReplayRejectCodeV1,
    RouteReplayRejectV1,
)
from .fcis_settlement_index import (
    ExactSettlementIndexEntryV1,
    ExactSettlementIndexRejectV1,
    derive_exact_settlement_index_admitted_v1,
)
from .fcis_settlement_strong_values import (
    ExactSpotPreStateV1,
    ExactStrongSettlementObservedV1,
    StrongSettlementContextV1,
    _candidate_from_exact_strong_validator_v1,
    _observed_from_exact_strong_validator_v1,
    _reject_from_exact_strong_validator_v1,
)
from .fcis_state_read_trace_v5 import (
    FCISStateReadTraceV5,
    extend_fcis_state_read_trace_v5,
)
from .fcis_support_profile_constants_v5 import FCIS_LP_LOCK_PUBKEY_V5
from .settlement_schema import fill_action_text_v1
from .settlement_snapshots import (
    OwnedBalanceDeltaV1,
    OwnedFillV1,
    OwnedLPDeltaV1,
    OwnedReserveDeltaV1,
    OwnedSettlementV1,
    snapshot_settlement,
)

_KIND_CREATE_POOL = "CREATE_POOL"
_KIND_ADD_LIQUIDITY = "ADD_LIQUIDITY"
_KIND_REMOVE_LIQUIDITY = "REMOVE_LIQUIDITY"
_KIND_SWAP_EXACT_IN = "SWAP_EXACT_IN"
_KIND_SWAP_EXACT_OUT = "SWAP_EXACT_OUT"
_KIND_ROUTE_EXACT_IN = "ROUTE_EXACT_IN"
_KIND_ROUTE_EXACT_OUT = "ROUTE_EXACT_OUT"
_ROUTE_KINDS = (_KIND_ROUTE_EXACT_IN, _KIND_ROUTE_EXACT_OUT)
_SWAP_KINDS = (_KIND_SWAP_EXACT_IN, _KIND_SWAP_EXACT_OUT)
_MODE_STRONG_PROOF_CARRYING = "strong_proof_carrying"
_SWAP_FILL_FIELDS_V1 = (
    "reason",
    "amount_in_filled",
    "amount_out_filled",
    "fee_paid",
    "protocol_fee_paid",
    "reserve_in_before",
    "reserve_out_before",
)


@final
@dataclass(frozen=True, slots=True)
class _ReplayStateV1:
    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1


@final
@dataclass(frozen=True, slots=True)
class _BalanceAtomV1:
    pubkey: str
    asset: str
    delta_add: int
    delta_sub: int


@final
@dataclass(frozen=True, slots=True)
class _ReserveAtomV1:
    pool_id: str
    asset: str
    delta_add: int
    delta_sub: int


@final
@dataclass(frozen=True, slots=True)
class _LPAtomV1:
    pubkey: str
    pool_id: str
    delta_add: int
    delta_sub: int


@final
@dataclass(frozen=True, slots=True)
class _ReplayAccumV1:
    state: _ReplayStateV1
    balance_atoms: tuple[_BalanceAtomV1, ...]
    reserve_atoms: tuple[_ReserveAtomV1, ...]
    lp_atoms: tuple[_LPAtomV1, ...]
    events: tuple[ExactCreatePoolEventV1, ...]
    pool_creations: tuple[PoolCreationV1, ...]
    trace: FCISStateReadTraceV5


@final
@dataclass(frozen=True, slots=True)
class _AtomProjectionV1:
    balances: tuple[_BalanceAtomV1, ...] = ()
    reserves: tuple[_ReserveAtomV1, ...] = ()
    lps: tuple[_LPAtomV1, ...] = ()
    event: ExactCreatePoolEventV1 | None = None
    creation: PoolCreationV1 | None = None


@final
@dataclass(frozen=True, slots=True)
class _EntryRejectV1:
    reason: str
    trace: FCISStateReadTraceV5


_EntryResultV1: TypeAlias = _ReplayAccumV1 | _EntryRejectV1


@final
@dataclass(frozen=True, slots=True)
class _PinnedRouteV1:
    binding: RouteBindingV1
    trace: FCISStateReadTraceV5


@final
@dataclass(frozen=True, slots=True)
class _RouteReplayPlanV1:
    replay: RouteReplayOkV1
    trace: FCISStateReadTraceV5


@final
@dataclass(frozen=True, slots=True)
class _CreatePoolPlanV1:
    asset0: str
    asset1: str
    amount0: int
    amount1: int
    pool_id: str
    lp_minted: int
    creation: PoolCreationV1


@final
@dataclass(frozen=True, slots=True)
class _AddLiquidityPlanV1:
    amount0: int
    amount1: int
    lp_minted: int
    recipient: str


@final
@dataclass(frozen=True, slots=True)
class _RemoveLiquidityPlanV1:
    amount0: int
    amount1: int
    lp_amount: int
    recipient: str


@final
@dataclass(frozen=True, slots=True)
class _SwapShapeV1:
    kind: str
    asset_in: str
    asset_out: str
    recipient: str
    reserve_in: int
    reserve_out: int
    zero_for_one: bool


@final
@dataclass(frozen=True, slots=True)
class _QuotedSwapPlanV1:
    shape: _SwapShapeV1
    quote: CommittedPoolSwapQuoteV1
    fee_recipient: str | None


def _reject_observed_v1(
    reason: str,
    trace: FCISStateReadTraceV5,
) -> ExactStrongSettlementObservedV1:
    return _observed_from_exact_strong_validator_v1(
        _reject_from_exact_strong_validator_v1(reason),
        trace,
    )


def _read_pool_v1(
    state: _ReplayStateV1,
    trace: FCISStateReadTraceV5,
    pool_id: str,
) -> tuple[CommittedPoolStateV1 | None, FCISStateReadTraceV5]:
    next_trace = extend_fcis_state_read_trace_v5(trace, pool_ids=(pool_id,))
    return state.pools.get(pool_id), next_trace


def _read_balance_v1(
    state: _ReplayStateV1,
    trace: FCISStateReadTraceV5,
    pubkey: str,
    asset: str,
) -> tuple[int, FCISStateReadTraceV5]:
    next_trace = extend_fcis_state_read_trace_v5(
        trace,
        balance_keys=((pubkey, asset),),
    )
    return state.balances.get(pubkey, asset), next_trace


def _extend_spot_reads_v1(
    trace: FCISStateReadTraceV5,
    reads: FCISSpotReplayReadSetV1,
) -> FCISStateReadTraceV5:
    return extend_fcis_state_read_trace_v5(
        trace,
        balance_keys=reads.balance_keys,
        pool_ids=reads.pool_ids,
        lp_keys=reads.lp_keys,
    )


def _spot_reject_text_v1(
    reject: BalancePatchRejectV1
    | LPPositionPatchRejectV1
    | LPDurationTransitionRejectV1
    | PoolPatchRejectV1,
) -> str:
    path = ".".join(_rejection_path_part_v1(part) for part in reject.path)
    return reject.code.value if not path else f"{reject.code.value}:{path}"


def _apply_replay_v1(
    accum: _ReplayAccumV1,
    deltas: FCISSpotReplayDeltaBatchV1,
) -> _ReplayAccumV1 | _EntryRejectV1:
    result, reads = apply_fcis_spot_replay_observed_v1(
        accum.state.balances,
        accum.state.pools,
        accum.state.lp_balances,
        deltas,
    )
    trace = _extend_spot_reads_v1(accum.trace, reads)
    if type(result) is not FCISSpotReplayOkV1:
        return _EntryRejectV1(_spot_reject_text_v1(result), trace)
    return _ReplayAccumV1(
        _ReplayStateV1(result.balances, result.pools, result.lp_balances),
        accum.balance_atoms,
        accum.reserve_atoms,
        accum.lp_atoms,
        accum.events,
        accum.pool_creations,
        trace,
    )


def _field_text_v1(intent: OwnedIntentV1, name: str) -> str:
    value = owned_intent_field_v1(intent, name)
    if type(value) is not str:
        raise TypeError(f"admitted intent field {name} must be an exact string")
    return value


def _field_int_v1(intent: OwnedIntentV1, name: str) -> int:
    value = owned_intent_field_v1(intent, name)
    if type(value) is not int:
        raise TypeError(f"admitted intent field {name} must be an exact integer")
    return value


def _optional_text_v1(intent: OwnedIntentV1, name: str) -> str | None:
    value = owned_intent_optional_field_v1(intent, name)
    if value is not None and type(value) is not str:
        raise TypeError(f"admitted intent field {name} must be an exact optional string")
    return value


def _optional_int_v1(intent: OwnedIntentV1, name: str) -> int | None:
    value = owned_intent_optional_field_v1(intent, name)
    if value is not None and type(value) is not int:
        raise TypeError(f"admitted intent field {name} must be an exact optional integer")
    return value


def _rejection_path_part_v1(part: str | int) -> str:
    if type(part) is str:
        return part
    if type(part) is int:
        return f"{part:d}"
    raise TypeError("exact rejection path contains an unsupported part")


def _recipient_v1(intent: OwnedIntentV1) -> str:
    recipient = _optional_text_v1(intent, "recipient")
    return intent.sender_pubkey if recipient is None else recipient


def _pool_status_text_v1(pool: CommittedPoolStateV1) -> str:
    return POOL_STATUS_MEMBER_VALUES_V1[pool.status.member_ordinal]


def _fill_has_only_v1(fill: OwnedFillV1, allowed: tuple[str, ...]) -> bool:
    fields = (
        ("reason", fill.reason),
        ("amount_in_filled", fill.amount_in_filled),
        ("amount_out_filled", fill.amount_out_filled),
        ("fee_paid", fill.fee_paid),
        ("protocol_fee_paid", fill.protocol_fee_paid),
        ("amount0_used", fill.amount0_used),
        ("amount1_used", fill.amount1_used),
        ("lp_minted", fill.lp_minted),
        ("amount0_out", fill.amount0_out),
        ("amount1_out", fill.amount1_out),
        ("lp_burned", fill.lp_burned),
        ("reserve_in_before", fill.reserve_in_before),
        ("reserve_out_before", fill.reserve_out_before),
    )
    return all(name in allowed or value is None for name, value in fields)


def _with_atoms_v1(
    accum: _ReplayAccumV1,
    projection: _AtomProjectionV1,
) -> _ReplayAccumV1:
    return _ReplayAccumV1(
        accum.state,
        accum.balance_atoms + projection.balances,
        accum.reserve_atoms + projection.reserves,
        accum.lp_atoms + projection.lps,
        accum.events + (() if projection.event is None else (projection.event,)),
        accum.pool_creations + (() if projection.creation is None else (projection.creation,)),
        accum.trace,
    )


def _quote_binding_error_v1(
    intent: OwnedIntentV1,
    context: StrongSettlementContextV1,
) -> str | None:
    kind = owned_intent_kind_text_v1(intent)
    receipt_hash = _optional_text_v1(intent, "quote_receipt_hash")
    pool_fingerprint = _optional_text_v1(intent, "quote_pool_fingerprint")
    leg_index = _optional_int_v1(intent, "quote_receipt_leg_index")
    has_binding = receipt_hash is not None or pool_fingerprint is not None or leg_index is not None
    if has_binding and kind not in _SWAP_KINDS:
        return (
            f"quote receipt binding only supported for swap intents: intent_id={intent.intent_id}"
        )
    if leg_index is not None:
        if type(leg_index) is not int or leg_index < 0:
            return f"invalid quote_receipt_leg_index: intent_id={intent.intent_id}"
        return (
            "quote receipt transport metadata requires validated engine witness: "
            f"intent_id={intent.intent_id}"
        )
    if receipt_hash is not None:
        return (
            "quote receipt transport metadata requires validated engine witness: "
            f"intent_id={intent.intent_id}"
        )
    if pool_fingerprint is not None and not context.settlement.allow_snapshot_bound_quote_bindings:
        return (
            "quote receipt snapshot binding requires validated engine witness: "
            f"intent_id={intent.intent_id}"
        )
    return None


def _route_fields_present_v1(intent: OwnedIntentV1) -> bool:
    return (
        owned_intent_optional_field_v1(intent, "route_legs") is not None
        or owned_intent_optional_field_v1(intent, "route_pool_fingerprints") is not None
    )


def _binding_reject_text_v1(reject: RouteBindingRejectV1) -> str:
    path = ".".join(_rejection_path_part_v1(part) for part in reject.path)
    return reject.code.value if not path else f"{reject.code.value}:{path}"


def _extend_route_reads_v1(
    trace: FCISStateReadTraceV5,
    pool_ids: tuple[str, ...],
) -> FCISStateReadTraceV5:
    return extend_fcis_state_read_trace_v5(trace, pool_ids=pool_ids)


def _derive_pinned_route_v1(
    entry: ExactSettlementIndexEntryV1,
    trace: FCISStateReadTraceV5,
    pre_state: ExactSpotPreStateV1,
    label: str,
) -> _PinnedRouteV1 | _EntryRejectV1:
    derived = derive_exact_route_binding_v1(entry.intent)
    if type(derived) is RouteBindingRejectV1:
        return _EntryRejectV1(
            f"{label} binding invalid for intent_id={entry.intent_id}: "
            f"{_binding_reject_text_v1(derived)}",
            trace,
        )
    binding = cast(RouteBindingOkV1, derived).binding
    pins, pin_reads = route_binding_pins_exact_snapshot_observed_v1(
        entry.intent,
        binding,
        pre_state.pools,
    )
    traced = _extend_route_reads_v1(trace, pin_reads)
    if not pins:
        return _EntryRejectV1(
            f"{label} binding does not pin the pre-state snapshot for intent_id={entry.intent_id}",
            traced,
        )
    return _PinnedRouteV1(binding, traced)


def _handle_rejected_route_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pre_state: ExactSpotPreStateV1,
    context: StrongSettlementContextV1,
) -> _EntryResultV1:
    intent = entry.intent
    if not context.settlement.allow_snapshot_bound_quote_bindings:
        return accum
    if not _route_fields_present_v1(intent):
        return _EntryRejectV1(
            f"route reject missing engine binding: intent_id={entry.intent_id}",
            accum.trace,
        )
    pinned = _derive_pinned_route_v1(entry, accum.trace, pre_state, "route reject")
    if type(pinned) is _EntryRejectV1:
        return pinned
    exact_pinned = pinned
    replay, replay_reads = replay_exact_route_observed_v1(
        intent,
        exact_pinned.binding,
        accum.state.pools,
    )
    trace = _extend_route_reads_v1(exact_pinned.trace, replay_reads)
    if type(replay) is RouteReplayOkV1:
        sender_balance, trace = _read_balance_v1(
            accum.state,
            trace,
            intent.sender_pubkey,
            exact_pinned.binding.asset_in,
        )
        if sender_balance >= replay.total_amount_in:
            return _EntryRejectV1(
                "route reject not justified — canonical clearing would fill "
                f"intent_id={entry.intent_id}",
                trace,
            )
        return _ReplayAccumV1(
            accum.state,
            accum.balance_atoms,
            accum.reserve_atoms,
            accum.lp_atoms,
            accum.events,
            accum.pool_creations,
            trace,
        )
    exact_reject = cast(RouteReplayRejectV1, replay)
    if exact_reject.code is not RouteReplayRejectCodeV1.POOL_STATE_DRIFT:
        return _EntryRejectV1(
            "route reject binding inconsistent with pinned snapshot "
            f"for intent_id={entry.intent_id}: {exact_reject.code.value}",
            trace,
        )
    return _ReplayAccumV1(
        accum.state,
        accum.balance_atoms,
        accum.reserve_atoms,
        accum.lp_atoms,
        accum.events,
        accum.pool_creations,
        trace,
    )


def _derive_create_pool_plan_v1(
    entry: ExactSettlementIndexEntryV1,
    trace: FCISStateReadTraceV5,
) -> _CreatePoolPlanV1 | _EntryRejectV1:
    intent = entry.intent
    asset0 = _field_text_v1(intent, "asset0")
    asset1 = _field_text_v1(intent, "asset1")
    fee_bps = _field_int_v1(intent, "fee_bps")
    amount0 = _field_int_v1(intent, "amount0")
    amount1 = _field_int_v1(intent, "amount1")
    created_at_value = _optional_int_v1(intent, "created_at")
    created_at = 0 if created_at_value is None else created_at_value
    curve_tag = _optional_text_v1(intent, "curve_tag")
    curve_params = _optional_text_v1(intent, "curve_params")
    try:
        config = create_pool_curve_config_v1(curve_tag, curve_params)
        canonical_tag, canonical_params = canonical_curve_config_fields_v1(config)
        pool_id = compute_pool_id(
            asset0,
            asset1,
            fee_bps,
            curve_tag=canonical_tag,
            curve_params=canonical_params,
        )
        lp_minted = initial_liquidity_for_pool_creation_v1(amount0, amount1)
        creation = PoolCreationV1(
            pool_id,
            asset0,
            asset1,
            fee_bps,
            created_at,
            canonical_tag,
            canonical_params,
        )
    except (ArithmeticError, TypeError, ValueError) as exc:
        return _EntryRejectV1(
            f"CREATE_POOL computation error for intent_id={entry.intent_id}: {exc}",
            trace,
        )
    return _CreatePoolPlanV1(
        asset0,
        asset1,
        amount0,
        amount1,
        pool_id,
        lp_minted,
        creation,
    )


def _create_pool_fill_error_v1(
    entry: ExactSettlementIndexEntryV1,
    fill: OwnedFillV1,
    plan: _CreatePoolPlanV1,
) -> str | None:
    if fill.amount0_used != plan.amount0:
        return f"CREATE_POOL fill.amount0_used mismatch for intent_id={entry.intent_id}"
    if fill.amount1_used != plan.amount1:
        return f"CREATE_POOL fill.amount1_used mismatch for intent_id={entry.intent_id}"
    if fill.lp_minted != plan.lp_minted:
        return f"CREATE_POOL fill.lp_minted mismatch for intent_id={entry.intent_id}"
    return None


def _create_pool_replay_batch_v1(
    intent: OwnedIntentV1,
    plan: _CreatePoolPlanV1,
) -> FCISSpotReplayDeltaBatchV1:
    return FCISSpotReplayDeltaBatchV1(
        balance_deltas=(
            BalanceDeltaV1((intent.sender_pubkey, plan.asset0), -plan.amount0),
            BalanceDeltaV1((intent.sender_pubkey, plan.asset1), -plan.amount1),
        ),
        reserve_deltas=(
            PoolReserveDeltaV1(plan.pool_id, plan.asset0, plan.amount0),
            PoolReserveDeltaV1(plan.pool_id, plan.asset1, plan.amount1),
        ),
        lp_deltas=(
            LPPositionDeltaV1((intent.sender_pubkey, plan.pool_id), plan.lp_minted),
            LPPositionDeltaV1((FCIS_LP_LOCK_PUBKEY_V5, plan.pool_id), MIN_LP_LOCK),
        ),
        pool_creations=(plan.creation,),
    )


def _create_pool_projection_v1(
    intent: OwnedIntentV1,
    plan: _CreatePoolPlanV1,
    event: ExactCreatePoolEventV1,
) -> _AtomProjectionV1:
    return _AtomProjectionV1(
        balances=(
            _BalanceAtomV1(intent.sender_pubkey, plan.asset0, 0, plan.amount0),
            _BalanceAtomV1(intent.sender_pubkey, plan.asset1, 0, plan.amount1),
        ),
        reserves=(
            _ReserveAtomV1(plan.pool_id, plan.asset0, plan.amount0, 0),
            _ReserveAtomV1(plan.pool_id, plan.asset1, plan.amount1, 0),
        ),
        lps=(
            _LPAtomV1(intent.sender_pubkey, plan.pool_id, plan.lp_minted, 0),
            _LPAtomV1(FCIS_LP_LOCK_PUBKEY_V5, plan.pool_id, MIN_LP_LOCK, 0),
        ),
        event=event,
        creation=plan.creation,
    )


def _apply_create_pool_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
) -> _EntryResultV1:
    fill = cast(OwnedFillV1, entry.fill)
    if not _fill_has_only_v1(fill, ("amount0_used", "amount1_used", "lp_minted")):
        return _EntryRejectV1(
            f"CREATE_POOL fill contains wrong-variant fields for intent_id={entry.intent_id}",
            accum.trace,
        )
    plan = _derive_create_pool_plan_v1(entry, accum.trace)
    if type(plan) is _EntryRejectV1:
        return plan
    exact_plan = plan
    existing, trace = _read_pool_v1(accum.state, accum.trace, exact_plan.pool_id)
    if existing is not None:
        return _EntryRejectV1(
            f"CREATE_POOL duplicates existing pool_id={exact_plan.pool_id}",
            trace,
        )
    fill_error = _create_pool_fill_error_v1(entry, fill, exact_plan)
    if fill_error is not None:
        return _EntryRejectV1(fill_error, trace)
    with_trace = _ReplayAccumV1(
        accum.state,
        accum.balance_atoms,
        accum.reserve_atoms,
        accum.lp_atoms,
        accum.events,
        accum.pool_creations,
        trace,
    )
    applied = _apply_replay_v1(
        with_trace,
        _create_pool_replay_batch_v1(entry.intent, exact_plan),
    )
    if type(applied) is _EntryRejectV1:
        return _EntryRejectV1(
            f"CREATE_POOL balance/LP apply error for intent_id={entry.intent_id}: {applied.reason}",
            applied.trace,
        )
    created_pool, trace = _read_pool_v1(
        applied.state,
        applied.trace,
        exact_plan.pool_id,
    )
    if created_pool is None:
        return _EntryRejectV1(
            f"CREATE_POOL result missing pool_id={exact_plan.pool_id}",
            trace,
        )
    exact_event = exact_create_pool_event_v1(created_pool)
    traced = _ReplayAccumV1(
        applied.state,
        applied.balance_atoms,
        applied.reserve_atoms,
        applied.lp_atoms,
        applied.events,
        applied.pool_creations,
        trace,
    )
    return _with_atoms_v1(
        traced,
        _create_pool_projection_v1(entry.intent, exact_plan, exact_event),
    )


def _derive_route_replay_plan_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pre_state: ExactSpotPreStateV1,
) -> _RouteReplayPlanV1 | _EntryRejectV1:
    pinned = _derive_pinned_route_v1(entry, accum.trace, pre_state, "route fill")
    if type(pinned) is _EntryRejectV1:
        return pinned
    exact_pinned = pinned
    replay, replay_reads = replay_exact_route_observed_v1(
        entry.intent,
        exact_pinned.binding,
        accum.state.pools,
    )
    trace = _extend_route_reads_v1(exact_pinned.trace, replay_reads)
    if type(replay) is RouteReplayRejectV1:
        return _EntryRejectV1(
            f"route replay failed for intent_id={entry.intent_id}: {replay.code.value}",
            trace,
        )
    return _RouteReplayPlanV1(cast(RouteReplayOkV1, replay), trace)


def _route_fill_error_v1(
    entry: ExactSettlementIndexEntryV1,
    fill: OwnedFillV1,
    replay: RouteReplayOkV1,
) -> str | None:
    if fill.amount_in_filled != replay.total_amount_in:
        return f"route amount_in_filled mismatch for intent_id={entry.intent_id}"
    if fill.amount_out_filled != replay.total_amount_out:
        return f"route amount_out_filled mismatch for intent_id={entry.intent_id}"
    if fill.fee_paid != replay.total_fee_paid:
        return f"route fee_paid mismatch for intent_id={entry.intent_id}"
    return None


def _route_replay_batch_v1(
    intent: OwnedIntentV1,
    replay: RouteReplayOkV1,
    recipient: str,
) -> FCISSpotReplayDeltaBatchV1:
    return FCISSpotReplayDeltaBatchV1(
        balance_deltas=tuple(
            delta
            for leg in replay.legs
            for delta in (
                BalanceDeltaV1((intent.sender_pubkey, leg.asset_in), -leg.amount_in),
                BalanceDeltaV1((recipient, leg.asset_out), leg.amount_out),
            )
        ),
        reserve_deltas=tuple(
            delta
            for leg in replay.legs
            for delta in (
                PoolReserveDeltaV1(leg.pool_id, leg.asset_in, leg.amount_in),
                PoolReserveDeltaV1(leg.pool_id, leg.asset_out, -leg.amount_out),
            )
        ),
        lp_deltas=(),
        pool_creations=(),
    )


def _route_projection_v1(
    intent: OwnedIntentV1,
    replay: RouteReplayOkV1,
    recipient: str,
) -> _AtomProjectionV1:
    return _AtomProjectionV1(
        balances=tuple(
            atom
            for leg in replay.legs
            for atom in (
                _BalanceAtomV1(intent.sender_pubkey, leg.asset_in, 0, leg.amount_in),
                _BalanceAtomV1(recipient, leg.asset_out, leg.amount_out, 0),
            )
        ),
        reserves=tuple(
            atom
            for leg in replay.legs
            for atom in (
                _ReserveAtomV1(leg.pool_id, leg.asset_in, leg.amount_in, 0),
                _ReserveAtomV1(leg.pool_id, leg.asset_out, 0, leg.amount_out),
            )
        ),
    )


def _apply_route_fill_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pre_state: ExactSpotPreStateV1,
) -> _EntryResultV1:
    fill = cast(OwnedFillV1, entry.fill)
    if not _fill_has_only_v1(
        fill,
        ("amount_in_filled", "amount_out_filled", "fee_paid"),
    ):
        return _EntryRejectV1(
            f"route fill contains wrong-variant fields for intent_id={entry.intent_id}",
            accum.trace,
        )
    plan = _derive_route_replay_plan_v1(entry, accum, pre_state)
    if type(plan) is _EntryRejectV1:
        return plan
    exact_plan = plan
    fill_error = _route_fill_error_v1(entry, fill, exact_plan.replay)
    if fill_error is not None:
        return _EntryRejectV1(fill_error, exact_plan.trace)
    recipient = _recipient_v1(entry.intent)
    traced = _ReplayAccumV1(
        accum.state,
        accum.balance_atoms,
        accum.reserve_atoms,
        accum.lp_atoms,
        accum.events,
        accum.pool_creations,
        exact_plan.trace,
    )
    applied = _apply_replay_v1(
        traced,
        _route_replay_batch_v1(entry.intent, exact_plan.replay, recipient),
    )
    if type(applied) is _EntryRejectV1:
        return _EntryRejectV1(
            f"route apply error for intent_id={entry.intent_id}: {applied.reason}",
            applied.trace,
        )
    return _with_atoms_v1(
        applied,
        _route_projection_v1(entry.intent, exact_plan.replay, recipient),
    )


def _quote_single_swap_v1(
    shape: _SwapShapeV1,
    intent: OwnedIntentV1,
    pool: CommittedPoolStateV1,
    context: StrongSettlementContextV1,
) -> CommittedPoolSwapQuoteV1:
    if shape.kind == _KIND_SWAP_EXACT_IN:
        return quote_exact_in_for_committed_pool_v1(
            pool,
            reserve_in=shape.reserve_in,
            reserve_out=shape.reserve_out,
            amount_in=_field_int_v1(intent, "amount_in"),
            protocol_fee_share_bps=context.settlement.protocol_fee_share_bps,
        )
    return quote_exact_out_for_committed_pool_v1(
        pool,
        reserve_in=shape.reserve_in,
        reserve_out=shape.reserve_out,
        amount_out=_field_int_v1(intent, "amount_out"),
        protocol_fee_share_bps=context.settlement.protocol_fee_share_bps,
    )


def _pool_orientation_v1(
    pool: CommittedPoolStateV1,
    asset_in: str,
    asset_out: str,
) -> tuple[int, int, bool] | None:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return pool.reserve0, pool.reserve1, True
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return pool.reserve1, pool.reserve0, False
    return None


def _swap_fill_error_v1(
    entry: ExactSettlementIndexEntryV1,
    fill: OwnedFillV1,
    quote: CommittedPoolSwapQuoteV1,
    intent: OwnedIntentV1,
) -> str | None:
    if fill.amount_in_filled != quote.amount_in:
        return f"swap amount_in_filled mismatch for intent_id={entry.intent_id}"
    if fill.amount_out_filled != quote.amount_out:
        return f"swap amount_out_filled mismatch for intent_id={entry.intent_id}"
    kind = owned_intent_kind_text_v1(intent)
    if kind == _KIND_SWAP_EXACT_IN and quote.amount_out < _field_int_v1(intent, "min_amount_out"):
        return f"swap slippage for intent_id={entry.intent_id}"
    if kind == _KIND_SWAP_EXACT_OUT and quote.amount_in > _field_int_v1(intent, "max_amount_in"):
        return f"swap slippage for intent_id={entry.intent_id}"
    if fill.fee_paid != quote.fee_paid:
        return f"swap fee_paid mismatch for intent_id={entry.intent_id}"
    if fill.protocol_fee_paid != quote.protocol_fee_paid:
        return f"swap protocol_fee_paid mismatch for intent_id={entry.intent_id}"
    return None


def _apply_cow_swap_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    shape: _SwapShapeV1,
) -> _EntryResultV1:
    intent = entry.intent
    fill = cast(OwnedFillV1, entry.fill)
    amount_in = _field_int_v1(intent, "amount_in")
    minimum_out = _field_int_v1(intent, "min_amount_out")
    if fill.fee_paid != 0:
        return _EntryRejectV1(
            f"COW_NETTED fee_paid must be 0: intent_id={entry.intent_id}",
            accum.trace,
        )
    if fill.amount_in_filled != amount_in:
        return _EntryRejectV1(
            f"COW_NETTED amount_in_filled mismatch: intent_id={entry.intent_id}",
            accum.trace,
        )
    if type(fill.amount_out_filled) is not int:
        return _EntryRejectV1(
            f"COW_NETTED amount_out_filled invalid: intent_id={entry.intent_id}",
            accum.trace,
        )
    amount_out = fill.amount_out_filled
    if amount_out < minimum_out:
        return _EntryRejectV1(
            f"COW_NETTED slippage: intent_id={entry.intent_id}",
            accum.trace,
        )
    applied = _apply_replay_v1(
        accum,
        FCISSpotReplayDeltaBatchV1(
            balance_deltas=(
                BalanceDeltaV1((intent.sender_pubkey, shape.asset_in), -amount_in),
                BalanceDeltaV1((shape.recipient, shape.asset_out), amount_out),
            ),
            reserve_deltas=(),
            lp_deltas=(),
            pool_creations=(),
        ),
    )
    if type(applied) is _EntryRejectV1:
        return _EntryRejectV1(
            f"COW_NETTED apply error for intent_id={entry.intent_id}: {applied.reason}",
            applied.trace,
        )
    return _with_atoms_v1(
        applied,
        _AtomProjectionV1(
            balances=(
                _BalanceAtomV1(intent.sender_pubkey, shape.asset_in, 0, amount_in),
                _BalanceAtomV1(shape.recipient, shape.asset_out, amount_out, 0),
            ),
        ),
    )


def _derive_swap_shape_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pool: CommittedPoolStateV1,
) -> _SwapShapeV1 | _EntryRejectV1:
    intent = entry.intent
    kind = owned_intent_kind_text_v1(intent)
    asset_in = _field_text_v1(intent, "asset_in")
    asset_out = _field_text_v1(intent, "asset_out")
    orientation = _pool_orientation_v1(pool, asset_in, asset_out)
    if orientation is None:
        return _EntryRejectV1(
            f"swap asset mismatch for intent_id={entry.intent_id}",
            accum.trace,
        )
    if pool.status.member_ordinal != POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1:
        return _EntryRejectV1(
            f"pool not active for intent_id={entry.intent_id}: {_pool_status_text_v1(pool)}",
            accum.trace,
        )
    quote_fingerprint = _optional_text_v1(intent, "quote_pool_fingerprint")
    if (
        quote_fingerprint is not None
        and pool_state_fingerprint_committed_v1(pool) != quote_fingerprint
    ):
        return _EntryRejectV1(
            f"quote receipt pool snapshot mismatch: intent_id={entry.intent_id}",
            accum.trace,
        )
    reserve_in, reserve_out, zero_for_one = orientation
    return _SwapShapeV1(
        kind,
        asset_in,
        asset_out,
        _recipient_v1(intent),
        reserve_in,
        reserve_out,
        zero_for_one,
    )


def _swap_witness_error_v1(
    entry: ExactSettlementIndexEntryV1,
    fill: OwnedFillV1,
    shape: _SwapShapeV1,
    context: StrongSettlementContextV1,
) -> str | None:
    if settlement_mode_label_v1(context.settlement.mode) == _MODE_STRONG_PROOF_CARRYING:
        if fill.reserve_in_before is None or fill.reserve_out_before is None:
            return f"missing swap witness reserves for intent_id={entry.intent_id}"
        if (fill.reserve_in_before, fill.reserve_out_before) != (
            shape.reserve_in,
            shape.reserve_out,
        ):
            return f"swap witness reserve mismatch for intent_id={entry.intent_id}"
    elif fill.reserve_in_before is not None or fill.reserve_out_before is not None:
        return f"swap fill contains proof-only reserves for intent_id={entry.intent_id}"
    return None


def _swap_replay_batch_v1(
    intent: OwnedIntentV1,
    pool: CommittedPoolStateV1,
    plan: _QuotedSwapPlanV1,
) -> FCISSpotReplayDeltaBatchV1:
    balance_deltas: tuple[BalanceDeltaV1, ...] = (
        BalanceDeltaV1((intent.sender_pubkey, plan.shape.asset_in), -plan.quote.amount_in),
        BalanceDeltaV1((plan.shape.recipient, plan.shape.asset_out), plan.quote.amount_out),
    )
    if plan.quote.protocol_fee_paid:
        balance_deltas += (
            BalanceDeltaV1(
                (cast(str, plan.fee_recipient), plan.shape.asset_in),
                plan.quote.protocol_fee_paid,
            ),
        )
    return FCISSpotReplayDeltaBatchV1(
        balance_deltas=balance_deltas,
        reserve_deltas=(
            PoolReserveDeltaV1(
                pool.pool_id,
                plan.shape.asset_in,
                plan.quote.amount_in - plan.quote.protocol_fee_paid,
            ),
            PoolReserveDeltaV1(
                pool.pool_id,
                plan.shape.asset_out,
                -plan.quote.amount_out,
            ),
        ),
        lp_deltas=(),
        pool_creations=(),
    )


def _swap_projection_v1(
    intent: OwnedIntentV1,
    pool: CommittedPoolStateV1,
    plan: _QuotedSwapPlanV1,
) -> _AtomProjectionV1:
    balance_atoms: tuple[_BalanceAtomV1, ...] = (
        _BalanceAtomV1(
            intent.sender_pubkey,
            plan.shape.asset_in,
            0,
            plan.quote.amount_in,
        ),
        _BalanceAtomV1(
            plan.shape.recipient,
            plan.shape.asset_out,
            plan.quote.amount_out,
            0,
        ),
    )
    if plan.quote.protocol_fee_paid:
        balance_atoms += (
            _BalanceAtomV1(
                cast(str, plan.fee_recipient),
                plan.shape.asset_in,
                plan.quote.protocol_fee_paid,
                0,
            ),
        )
    return _AtomProjectionV1(
        balances=balance_atoms,
        reserves=(
            _ReserveAtomV1(
                pool.pool_id,
                plan.shape.asset_in,
                plan.quote.amount_in - plan.quote.protocol_fee_paid,
                0,
            ),
            _ReserveAtomV1(
                pool.pool_id,
                plan.shape.asset_out,
                0,
                plan.quote.amount_out,
            ),
        ),
    )


def _apply_quoted_swap_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pool: CommittedPoolStateV1,
    plan: _QuotedSwapPlanV1,
) -> _EntryResultV1:
    applied = _apply_replay_v1(
        accum,
        _swap_replay_batch_v1(entry.intent, pool, plan),
    )
    if type(applied) is _EntryRejectV1:
        return _EntryRejectV1(
            f"swap apply error for intent_id={entry.intent_id}: {applied.reason}",
            applied.trace,
        )
    post_pool, trace = _read_pool_v1(applied.state, applied.trace, pool.pool_id)
    expected = (
        (plan.quote.new_reserve_in, plan.quote.new_reserve_out)
        if plan.shape.zero_for_one
        else (plan.quote.new_reserve_out, plan.quote.new_reserve_in)
    )
    if post_pool is None or (post_pool.reserve0, post_pool.reserve1) != expected:
        return _EntryRejectV1(
            f"swap apply error for intent_id={entry.intent_id}: "
            "spot transition disagrees with swap kernel reserves",
            trace,
        )
    traced = _ReplayAccumV1(
        applied.state,
        applied.balance_atoms,
        applied.reserve_atoms,
        applied.lp_atoms,
        applied.events,
        applied.pool_creations,
        trace,
    )
    return _with_atoms_v1(traced, _swap_projection_v1(entry.intent, pool, plan))


def _apply_single_swap_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    context: StrongSettlementContextV1,
    pool: CommittedPoolStateV1,
) -> _EntryResultV1:
    fill = cast(OwnedFillV1, entry.fill)
    if not _fill_has_only_v1(fill, _SWAP_FILL_FIELDS_V1):
        return _EntryRejectV1(
            f"swap fill contains wrong-variant fields for intent_id={entry.intent_id}",
            accum.trace,
        )
    shape = _derive_swap_shape_v1(entry, accum, pool)
    if type(shape) is _EntryRejectV1:
        return shape
    exact_shape = shape
    if fill.reason == "COW_NETTED":
        if exact_shape.kind != _KIND_SWAP_EXACT_IN:
            return _EntryRejectV1(
                f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={entry.intent_id}",
                accum.trace,
            )
        if fill.protocol_fee_paid not in (None, 0):
            return _EntryRejectV1(
                f"COW_NETTED protocol_fee_paid must be 0: intent_id={entry.intent_id}",
                accum.trace,
            )
        return _apply_cow_swap_v1(entry, accum, exact_shape)
    plan = _derive_quoted_swap_plan_v1(entry, accum, context, pool, exact_shape)
    if type(plan) is _EntryRejectV1:
        return plan
    return _apply_quoted_swap_v1(entry, accum, pool, plan)


def _derive_quoted_swap_plan_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    context: StrongSettlementContextV1,
    pool: CommittedPoolStateV1,
    shape: _SwapShapeV1,
) -> _QuotedSwapPlanV1 | _EntryRejectV1:
    fill = cast(OwnedFillV1, entry.fill)
    if fill.reason is not None:
        return _EntryRejectV1(
            f"swap fill contains unsupported reason for intent_id={entry.intent_id}",
            accum.trace,
        )
    witness_error = _swap_witness_error_v1(entry, fill, shape, context)
    if witness_error is not None:
        return _EntryRejectV1(witness_error, accum.trace)
    if context.settlement.protocol_fee_share_bps and pool.curve_tag != CURVE_TAG_CPMM:
        return _EntryRejectV1(
            f"protocol fee unsupported for curve intent_id={entry.intent_id}",
            accum.trace,
        )
    try:
        quote = _quote_single_swap_v1(shape, entry.intent, pool, context)
    except (ArithmeticError, TypeError, ValueError) as exc:
        label = "swap_exact_in" if shape.kind == _KIND_SWAP_EXACT_IN else "swap_exact_out"
        return _EntryRejectV1(
            f"{label} kernel error for intent_id={entry.intent_id}: {exc}",
            accum.trace,
        )
    fill_error = _swap_fill_error_v1(entry, fill, quote, entry.intent)
    if fill_error is not None:
        return _EntryRejectV1(fill_error, accum.trace)
    fee_recipient = context.settlement.protocol_fee_recipient_pubkey
    if quote.protocol_fee_paid and fee_recipient is None:
        return _EntryRejectV1(
            f"protocol_fee present without recipient for intent_id={entry.intent_id}",
            accum.trace,
        )
    return _QuotedSwapPlanV1(shape, quote, fee_recipient)


def _derive_add_liquidity_plan_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pool: CommittedPoolStateV1,
) -> _AddLiquidityPlanV1 | _EntryRejectV1:
    fill = cast(OwnedFillV1, entry.fill)
    if not _fill_has_only_v1(fill, ("amount0_used", "amount1_used", "lp_minted")):
        return _EntryRejectV1(
            f"ADD_LIQUIDITY fill contains wrong-variant fields for intent_id={entry.intent_id}",
            accum.trace,
        )
    if pool.status.member_ordinal != POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1:
        return _EntryRejectV1(
            f"pool not active for intent_id={entry.intent_id}: {_pool_status_text_v1(pool)}",
            accum.trace,
        )
    intent = entry.intent
    try:
        amount0, amount1, lp_minted = add_liquidity_for_committed_pool_v1(
            pool,
            AddLiquidityKernelInputV1(
                amount0_desired=_field_int_v1(intent, "amount0_desired"),
                amount1_desired=_field_int_v1(intent, "amount1_desired"),
                amount0_min=_field_int_v1(intent, "amount0_min"),
                amount1_min=_field_int_v1(intent, "amount1_min"),
            ),
        )
    except (ArithmeticError, TypeError, ValueError) as exc:
        return _EntryRejectV1(
            f"ADD_LIQUIDITY computation error for intent_id={entry.intent_id}: {exc}",
            accum.trace,
        )
    if fill.amount0_used != amount0:
        return _EntryRejectV1(
            f"ADD_LIQUIDITY fill.amount0_used mismatch for intent_id={entry.intent_id}",
            accum.trace,
        )
    if fill.amount1_used != amount1:
        return _EntryRejectV1(
            f"ADD_LIQUIDITY fill.amount1_used mismatch for intent_id={entry.intent_id}",
            accum.trace,
        )
    if fill.lp_minted != lp_minted:
        return _EntryRejectV1(
            f"ADD_LIQUIDITY fill.lp_minted mismatch for intent_id={entry.intent_id}",
            accum.trace,
        )
    return _AddLiquidityPlanV1(
        amount0,
        amount1,
        lp_minted,
        _recipient_v1(intent),
    )


def _add_liquidity_replay_batch_v1(
    intent: OwnedIntentV1,
    pool: CommittedPoolStateV1,
    plan: _AddLiquidityPlanV1,
) -> FCISSpotReplayDeltaBatchV1:
    return FCISSpotReplayDeltaBatchV1(
        balance_deltas=(
            BalanceDeltaV1((intent.sender_pubkey, pool.asset0), -plan.amount0),
            BalanceDeltaV1((intent.sender_pubkey, pool.asset1), -plan.amount1),
        ),
        reserve_deltas=(
            PoolReserveDeltaV1(pool.pool_id, pool.asset0, plan.amount0),
            PoolReserveDeltaV1(pool.pool_id, pool.asset1, plan.amount1),
        ),
        lp_deltas=(LPPositionDeltaV1((plan.recipient, pool.pool_id), plan.lp_minted),),
        pool_creations=(),
    )


def _add_liquidity_projection_v1(
    intent: OwnedIntentV1,
    pool: CommittedPoolStateV1,
    plan: _AddLiquidityPlanV1,
) -> _AtomProjectionV1:
    return _AtomProjectionV1(
        balances=(
            _BalanceAtomV1(intent.sender_pubkey, pool.asset0, 0, plan.amount0),
            _BalanceAtomV1(intent.sender_pubkey, pool.asset1, 0, plan.amount1),
        ),
        reserves=(
            _ReserveAtomV1(pool.pool_id, pool.asset0, plan.amount0, 0),
            _ReserveAtomV1(pool.pool_id, pool.asset1, plan.amount1, 0),
        ),
        lps=(_LPAtomV1(plan.recipient, pool.pool_id, plan.lp_minted, 0),),
    )


def _pool_matches_liquidity_result_v1(
    pool: CommittedPoolStateV1 | None,
    expected: tuple[int, int, int],
) -> bool:
    return pool is not None and (pool.reserve0, pool.reserve1, pool.lp_supply) == expected


def _apply_add_liquidity_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pool: CommittedPoolStateV1,
) -> _EntryResultV1:
    plan = _derive_add_liquidity_plan_v1(entry, accum, pool)
    if type(plan) is _EntryRejectV1:
        return plan
    exact_plan = plan
    applied = _apply_replay_v1(
        accum,
        _add_liquidity_replay_batch_v1(entry.intent, pool, exact_plan),
    )
    if type(applied) is _EntryRejectV1:
        return _EntryRejectV1(
            f"ADD_LIQUIDITY apply error for intent_id={entry.intent_id}: {applied.reason}",
            applied.trace,
        )
    post_pool, trace = _read_pool_v1(applied.state, applied.trace, pool.pool_id)
    expected = (
        pool.reserve0 + exact_plan.amount0,
        pool.reserve1 + exact_plan.amount1,
        pool.lp_supply + exact_plan.lp_minted,
    )
    if not _pool_matches_liquidity_result_v1(post_pool, expected):
        return _EntryRejectV1(
            f"ADD_LIQUIDITY apply error for intent_id={entry.intent_id}: "
            "spot transition disagrees with liquidity kernel",
            trace,
        )
    traced = _ReplayAccumV1(
        applied.state,
        applied.balance_atoms,
        applied.reserve_atoms,
        applied.lp_atoms,
        applied.events,
        applied.pool_creations,
        trace,
    )
    return _with_atoms_v1(
        traced,
        _add_liquidity_projection_v1(entry.intent, pool, exact_plan),
    )


def _derive_remove_liquidity_plan_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pool: CommittedPoolStateV1,
) -> _RemoveLiquidityPlanV1 | _EntryRejectV1:
    fill = cast(OwnedFillV1, entry.fill)
    if not _fill_has_only_v1(fill, ("amount0_out", "amount1_out", "lp_burned")):
        return _EntryRejectV1(
            f"REMOVE_LIQUIDITY fill contains wrong-variant fields for intent_id={entry.intent_id}",
            accum.trace,
        )
    if pool.status.member_ordinal != POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1:
        return _EntryRejectV1(
            f"pool not active for intent_id={entry.intent_id}: {_pool_status_text_v1(pool)}",
            accum.trace,
        )
    intent = entry.intent
    lp_amount = _field_int_v1(intent, "lp_amount")
    try:
        amount0, amount1 = remove_liquidity_for_committed_pool_v1(
            pool,
            RemoveLiquidityKernelInputV1(
                lp_amount=lp_amount,
                amount0_min=_field_int_v1(intent, "amount0_min"),
                amount1_min=_field_int_v1(intent, "amount1_min"),
            ),
        )
    except (ArithmeticError, TypeError, ValueError) as exc:
        return _EntryRejectV1(
            f"REMOVE_LIQUIDITY computation error for intent_id={entry.intent_id}: {exc}",
            accum.trace,
        )
    if fill.lp_burned != lp_amount:
        return _EntryRejectV1(
            f"REMOVE_LIQUIDITY fill.lp_burned mismatch for intent_id={entry.intent_id}",
            accum.trace,
        )
    if fill.amount0_out != amount0:
        return _EntryRejectV1(
            f"REMOVE_LIQUIDITY fill.amount0_out mismatch for intent_id={entry.intent_id}",
            accum.trace,
        )
    if fill.amount1_out != amount1:
        return _EntryRejectV1(
            f"REMOVE_LIQUIDITY fill.amount1_out mismatch for intent_id={entry.intent_id}",
            accum.trace,
        )
    return _RemoveLiquidityPlanV1(
        amount0,
        amount1,
        lp_amount,
        _recipient_v1(intent),
    )


def _remove_liquidity_replay_batch_v1(
    intent: OwnedIntentV1,
    pool: CommittedPoolStateV1,
    plan: _RemoveLiquidityPlanV1,
) -> FCISSpotReplayDeltaBatchV1:
    amounts = ((pool.asset0, plan.amount0), (pool.asset1, plan.amount1))
    return FCISSpotReplayDeltaBatchV1(
        balance_deltas=tuple(
            BalanceDeltaV1((plan.recipient, asset), amount) for asset, amount in amounts if amount
        ),
        reserve_deltas=tuple(
            PoolReserveDeltaV1(pool.pool_id, asset, -amount) for asset, amount in amounts if amount
        ),
        lp_deltas=(LPPositionDeltaV1((intent.sender_pubkey, pool.pool_id), -plan.lp_amount),),
        pool_creations=(),
    )


def _remove_liquidity_projection_v1(
    intent: OwnedIntentV1,
    pool: CommittedPoolStateV1,
    plan: _RemoveLiquidityPlanV1,
) -> _AtomProjectionV1:
    amounts = ((pool.asset0, plan.amount0), (pool.asset1, plan.amount1))
    return _AtomProjectionV1(
        balances=tuple(
            _BalanceAtomV1(plan.recipient, asset, amount, 0) for asset, amount in amounts if amount
        ),
        reserves=tuple(
            _ReserveAtomV1(pool.pool_id, asset, 0, amount) for asset, amount in amounts if amount
        ),
        lps=(_LPAtomV1(intent.sender_pubkey, pool.pool_id, 0, plan.lp_amount),),
    )


def _apply_remove_liquidity_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pool: CommittedPoolStateV1,
) -> _EntryResultV1:
    plan = _derive_remove_liquidity_plan_v1(entry, accum, pool)
    if type(plan) is _EntryRejectV1:
        return plan
    exact_plan = plan
    applied = _apply_replay_v1(
        accum,
        _remove_liquidity_replay_batch_v1(entry.intent, pool, exact_plan),
    )
    if type(applied) is _EntryRejectV1:
        return _EntryRejectV1(
            f"REMOVE_LIQUIDITY apply error for intent_id={entry.intent_id}: {applied.reason}",
            applied.trace,
        )
    post_pool, trace = _read_pool_v1(applied.state, applied.trace, pool.pool_id)
    expected = (
        pool.reserve0 - exact_plan.amount0,
        pool.reserve1 - exact_plan.amount1,
        pool.lp_supply - exact_plan.lp_amount,
    )
    if not _pool_matches_liquidity_result_v1(post_pool, expected):
        return _EntryRejectV1(
            f"REMOVE_LIQUIDITY apply error for intent_id={entry.intent_id}: "
            "spot transition disagrees with liquidity kernel",
            trace,
        )
    traced = _ReplayAccumV1(
        applied.state,
        applied.balance_atoms,
        applied.reserve_atoms,
        applied.lp_atoms,
        applied.events,
        applied.pool_creations,
        trace,
    )
    return _with_atoms_v1(
        traced,
        _remove_liquidity_projection_v1(entry.intent, pool, exact_plan),
    )


def _apply_entry_v1(
    entry: ExactSettlementIndexEntryV1,
    accum: _ReplayAccumV1,
    pre_state: ExactSpotPreStateV1,
    context: StrongSettlementContextV1,
) -> _EntryResultV1:
    intent = entry.intent
    kind = owned_intent_kind_text_v1(intent)
    quote_error = _quote_binding_error_v1(intent, context)
    if quote_error is not None:
        return _EntryRejectV1(quote_error, accum.trace)
    if (
        kind in _ROUTE_KINDS
        and _route_fields_present_v1(intent)
        and not context.settlement.allow_snapshot_bound_quote_bindings
    ):
        return _EntryRejectV1(
            f"route binding requires validated engine witness: intent_id={entry.intent_id}",
            accum.trace,
        )
    if fill_action_text_v1(entry.action) == "REJECT":
        if kind in _ROUTE_KINDS:
            return _handle_rejected_route_v1(entry, accum, pre_state, context)
        return accum
    if type(entry.fill) is not OwnedFillV1:
        return _EntryRejectV1(
            f"missing Fill for filled intent_id: {entry.intent_id}",
            accum.trace,
        )
    if kind == _KIND_CREATE_POOL:
        return _apply_create_pool_v1(entry, accum)
    if kind in _ROUTE_KINDS:
        return _apply_route_fill_v1(entry, accum, pre_state)
    pool_id = _field_text_v1(intent, "pool_id")
    pool, trace = _read_pool_v1(accum.state, accum.trace, pool_id)
    if pool is None:
        return _EntryRejectV1(
            f"pool not found for intent_id={entry.intent_id}: {pool_id}",
            trace,
        )
    traced = _ReplayAccumV1(
        accum.state,
        accum.balance_atoms,
        accum.reserve_atoms,
        accum.lp_atoms,
        accum.events,
        accum.pool_creations,
        trace,
    )
    if kind in _SWAP_KINDS:
        return _apply_single_swap_v1(entry, traced, context, pool)
    if kind == _KIND_ADD_LIQUIDITY:
        return _apply_add_liquidity_v1(entry, traced, pool)
    if kind == _KIND_REMOVE_LIQUIDITY:
        return _apply_remove_liquidity_v1(entry, traced, pool)
    return _EntryRejectV1(
        f"unsupported intent kind for strong validation: {kind}",
        trace,
    )


def _aggregate_balance_atoms_v1(
    atoms: tuple[_BalanceAtomV1, ...],
) -> tuple[OwnedBalanceDeltaV1, ...]:
    totals: dict[tuple[str, str], tuple[int, int]] = {}
    for atom in atoms:
        previous_add, previous_sub = totals.get((atom.pubkey, atom.asset), (0, 0))
        totals[(atom.pubkey, atom.asset)] = (
            previous_add + atom.delta_add,
            previous_sub + atom.delta_sub,
        )
    return tuple(
        OwnedBalanceDeltaV1(key[0], key[1], delta_add, delta_sub)
        for key, (delta_add, delta_sub) in sorted(totals.items())
        if delta_add or delta_sub
    )


def _aggregate_reserve_atoms_v1(
    atoms: tuple[_ReserveAtomV1, ...],
) -> tuple[OwnedReserveDeltaV1, ...]:
    totals: dict[tuple[str, str], tuple[int, int]] = {}
    for atom in atoms:
        previous_add, previous_sub = totals.get((atom.pool_id, atom.asset), (0, 0))
        totals[(atom.pool_id, atom.asset)] = (
            previous_add + atom.delta_add,
            previous_sub + atom.delta_sub,
        )
    return tuple(
        OwnedReserveDeltaV1(key[0], key[1], delta_add, delta_sub)
        for key, (delta_add, delta_sub) in sorted(totals.items())
        if delta_add or delta_sub
    )


def _aggregate_lp_atoms_v1(
    atoms: tuple[_LPAtomV1, ...],
) -> tuple[OwnedLPDeltaV1, ...]:
    totals: dict[tuple[str, str], tuple[int, int]] = {}
    for atom in atoms:
        previous_add, previous_sub = totals.get((atom.pubkey, atom.pool_id), (0, 0))
        totals[(atom.pubkey, atom.pool_id)] = (
            previous_add + atom.delta_add,
            previous_sub + atom.delta_sub,
        )
    return tuple(
        OwnedLPDeltaV1(key[0], key[1], delta_add, delta_sub)
        for key, (delta_add, delta_sub) in sorted(totals.items())
        if delta_add or delta_sub
    )


def _balance_certificate_error_v1(
    values: tuple[OwnedBalanceDeltaV1, ...],
) -> str | None:
    keys = tuple((value.pubkey, value.asset) for value in values)
    if keys != tuple(sorted(keys)):
        return "balance_deltas not sorted canonically"
    if len(keys) != len(set(keys)):
        return "balance_deltas contains duplicate keys"
    if any(value.delta_add == 0 and value.delta_sub == 0 for value in values):
        return "balance_deltas contains a zero entry"
    return None


def _reserve_certificate_error_v1(
    values: tuple[OwnedReserveDeltaV1, ...],
) -> str | None:
    keys = tuple((value.pool_id, value.asset) for value in values)
    if keys != tuple(sorted(keys)):
        return "reserve_deltas not sorted canonically"
    if len(keys) != len(set(keys)):
        return "reserve_deltas contains duplicate keys"
    if any(value.delta_add == 0 and value.delta_sub == 0 for value in values):
        return "reserve_deltas contains a zero entry"
    return None


def _lp_certificate_error_v1(
    values: tuple[OwnedLPDeltaV1, ...],
) -> str | None:
    keys = tuple((value.pubkey, value.pool_id) for value in values)
    if keys != tuple(sorted(keys)):
        return "lp_deltas not sorted canonically"
    if len(keys) != len(set(keys)):
        return "lp_deltas contains duplicate keys"
    if any(value.delta_add == 0 and value.delta_sub == 0 for value in values):
        return "lp_deltas contains a zero entry"
    return None


def _events_match_v1(
    expected: tuple[ExactCreatePoolEventV1, ...],
    supplied: tuple[OwnedJsonObjectV1, ...] | None,
) -> bool:
    if not expected:
        return supplied is None
    if supplied is None or len(supplied) != len(expected):
        return False
    return all(
        create_pool_event_matches_owned_v1(expected_event, supplied_event)
        for expected_event, supplied_event in zip(expected, supplied, strict=True)
    )


def _asset_conservation_error_v1(
    balances: tuple[OwnedBalanceDeltaV1, ...],
    reserves: tuple[OwnedReserveDeltaV1, ...],
) -> str | None:
    totals: dict[str, int] = {}
    for delta in balances:
        totals[delta.asset] = totals.get(delta.asset, 0) + delta.delta_add - delta.delta_sub
    for delta in reserves:
        totals[delta.asset] = totals.get(delta.asset, 0) + delta.delta_add - delta.delta_sub
    for asset in sorted(totals):
        if totals[asset]:
            return f"Asset conservation violation: {asset}, net_delta = {totals[asset]}"
    return None


def _certificate_result_v1(
    settlement: OwnedSettlementV1,
    accum: _ReplayAccumV1,
) -> (
    tuple[
        tuple[OwnedBalanceDeltaV1, ...],
        tuple[OwnedReserveDeltaV1, ...],
        tuple[OwnedLPDeltaV1, ...],
    ]
    | _EntryRejectV1
):
    expected_balance = _aggregate_balance_atoms_v1(accum.balance_atoms)
    expected_reserve = _aggregate_reserve_atoms_v1(accum.reserve_atoms)
    expected_lp = _aggregate_lp_atoms_v1(accum.lp_atoms)
    for error in (
        _balance_certificate_error_v1(settlement.balance_deltas),
        _reserve_certificate_error_v1(settlement.reserve_deltas),
        _lp_certificate_error_v1(settlement.lp_deltas),
    ):
        if error is not None:
            return _EntryRejectV1(error, accum.trace)
    if settlement.balance_deltas != expected_balance:
        return _EntryRejectV1("balance_deltas mismatch vs replay", accum.trace)
    if settlement.reserve_deltas != expected_reserve:
        return _EntryRejectV1("reserve_deltas mismatch vs replay", accum.trace)
    if settlement.lp_deltas != expected_lp:
        return _EntryRejectV1("lp_deltas mismatch vs replay", accum.trace)
    if not _events_match_v1(accum.events, settlement.events):
        return _EntryRejectV1("events mismatch vs replay", accum.trace)
    conservation = _asset_conservation_error_v1(expected_balance, expected_reserve)
    if conservation is not None:
        return _EntryRejectV1(
            f"legacy validation failed: {conservation}",
            accum.trace,
        )
    return expected_balance, expected_reserve, expected_lp


def _authoritative_batch_v1(
    balances: tuple[OwnedBalanceDeltaV1, ...],
    reserves: tuple[OwnedReserveDeltaV1, ...],
    lps: tuple[OwnedLPDeltaV1, ...],
    creations: tuple[PoolCreationV1, ...],
) -> FCISSpotDeltaBatchV1:
    return FCISSpotDeltaBatchV1(
        balance_deltas=tuple(
            BalanceDeltaV1(
                (delta.pubkey, delta.asset),
                delta.delta_add - delta.delta_sub,
            )
            for delta in balances
            if delta.delta_add != delta.delta_sub
        ),
        reserve_deltas=tuple(
            PoolReserveDeltaV1(
                delta.pool_id,
                delta.asset,
                delta.delta_add - delta.delta_sub,
            )
            for delta in reserves
            if delta.delta_add != delta.delta_sub
        ),
        lp_events=tuple(
            LPDurationEventV1(
                (delta.pubkey, delta.pool_id),
                delta.delta_add,
                delta.delta_sub,
            )
            for delta in lps
        ),
        pool_creations=creations,
    )


def _build_candidate_v1(
    pre_state: ExactSpotPreStateV1,
    context: StrongSettlementContextV1,
    accum: _ReplayAccumV1,
    certificate: tuple[
        tuple[OwnedBalanceDeltaV1, ...],
        tuple[OwnedReserveDeltaV1, ...],
        tuple[OwnedLPDeltaV1, ...],
    ],
) -> ExactStrongSettlementObservedV1:
    balance_deltas, reserve_deltas, lp_deltas = certificate
    try:
        batch = _authoritative_batch_v1(
            balance_deltas,
            reserve_deltas,
            lp_deltas,
            accum.pool_creations,
        )
    except (TypeError, ValueError) as exc:
        return _reject_observed_v1(
            f"exact spot batch construction failed: {exc}",
            accum.trace,
        )
    result, reads = apply_fcis_spot_deltas_observed_v1(
        pre_state.balances,
        pre_state.pools,
        pre_state.lp_balances,
        batch,
        now=context.settlement.now,
        min_age_seconds=context.settlement.min_lp_position_age_seconds,
        policy=context.lp_duration_policy,
    )
    trace = _extend_spot_reads_v1(accum.trace, reads)
    if type(result) is not FCISSpotTransitionOkV1:
        return _reject_observed_v1(
            f"authoritative spot transition rejected: {_spot_reject_text_v1(result)}",
            trace,
        )
    if (
        result.balances != accum.state.balances
        or result.pools != accum.state.pools
        or (result.lp_balances.balance_entries != accum.state.lp_balances.balance_entries)
    ):
        return _reject_observed_v1(
            "aggregate spot candidate disagrees with sequential replay state",
            trace,
        )
    candidate = _candidate_from_exact_strong_validator_v1(
        balances=result.balances,
        pools=result.pools,
        lp_balances=result.lp_balances,
        balance_patch=result.balance_patch,
        pool_patch=result.pool_patch,
        lp_patch=result.lp_patch,
    )
    return _observed_from_exact_strong_validator_v1(candidate, trace)


def _evaluate_settlement_strong_exact_admitted_v1(
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    pre_state: ExactSpotPreStateV1,
    context: StrongSettlementContextV1,
) -> ExactStrongSettlementObservedV1:
    trace = FCISStateReadTraceV5()
    index = derive_exact_settlement_index_admitted_v1(
        settlement,
        intents,
        allow_cow_netting=context.settlement.allow_cow_netting,
    )
    if type(index) is ExactSettlementIndexRejectV1:
        return _reject_observed_v1(index.reason, trace)
    exact_index = index
    accum = _ReplayAccumV1(
        _ReplayStateV1(
            pre_state.balances,
            pre_state.pools,
            pre_state.lp_balances,
        ),
        (),
        (),
        (),
        (),
        (),
        trace,
    )
    for entry in exact_index.entries:
        applied = _apply_entry_v1(entry, accum, pre_state, context)
        if type(applied) is _EntryRejectV1:
            return _reject_observed_v1(applied.reason, applied.trace)
        accum = applied
    certificate = _certificate_result_v1(settlement, accum)
    if type(certificate) is _EntryRejectV1:
        return _reject_observed_v1(certificate.reason, certificate.trace)
    return _build_candidate_v1(pre_state, context, accum, certificate)


def evaluate_settlement_strong_exact_v1(
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    pre_state: ExactSpotPreStateV1,
    context: StrongSettlementContextV1,
) -> ExactStrongSettlementObservedV1:
    """Revalidate one exact graph and evaluate the unmounted P4B4 relation."""

    empty_trace = FCISStateReadTraceV5()
    raw_pre_state: object = pre_state
    if type(raw_pre_state) is not ExactSpotPreStateV1:
        return _reject_observed_v1("invalid exact pre-state", empty_trace)
    exact_pre_state = raw_pre_state
    try:
        exact_pre_state.__post_init__()
    except (AttributeError, TypeError, ValueError):
        return _reject_observed_v1("invalid exact pre-state", empty_trace)
    raw_context: object = context
    if type(raw_context) is not StrongSettlementContextV1:
        return _reject_observed_v1("invalid exact settlement context", empty_trace)
    exact_context = raw_context
    try:
        exact_context.__post_init__()
    except (AttributeError, TypeError, ValueError):
        return _reject_observed_v1("invalid exact settlement context", empty_trace)
    raw_settlement: object = settlement
    raw_intents: object = intents
    if type(raw_settlement) is not OwnedSettlementV1 or type(raw_intents) is not tuple:
        return _reject_observed_v1("invalid exact settlement command graph", empty_trace)
    try:
        exact_settlement = snapshot_settlement(raw_settlement)
        exact_intents = admit_intent_batch(raw_intents)
    except (AttributeError, TypeError, ValueError):
        return _reject_observed_v1("invalid exact settlement command graph", empty_trace)
    return _evaluate_settlement_strong_exact_admitted_v1(
        exact_settlement,
        exact_intents,
        exact_pre_state,
        exact_context,
    )


__all__ = ("evaluate_settlement_strong_exact_v1",)
