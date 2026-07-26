"""Pure typed state-read combinators for FCIS support profile v5.

Every function couples one semantic read or state application with the exact
immutable trace returned to its caller.  The declared support set is derived
elsewhere from command and context, so observed reads cannot be populated from
the declaration they are intended to check.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import final

from ..state.fcis_execution_context_schema import (
    FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1,
    FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1,
    FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1,
)
from ..state.fcis_execution_context_values import (
    FCISFeeSplitPolicyV1,
    FCISStepExecutionContextV1,
)
from ..state.lp_duration_transitions import LPDurationRiskPolicyV1
from ..state.owned_collections import OwnedEnumV1, OwnedMapV1
from ..state.spot_state_transitions import (
    SpotDeltaBatchV1,
    SpotTransitionResultV1,
    _apply_spot_replay_deltas_observed_v1,
    _SpotReplayDeltaBatchV1,
    _SpotReplayResultV1,
    apply_spot_deltas_observed_v1,
)
from ..state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedPoolStateV1,
)
from .fcis_state_read_trace_v5 import (
    FCISContextReadTraceV5,
    FCISStateReadTraceV5,
    extend_fcis_state_read_trace_v5,
)
from .route_settlement import (
    RouteBinding,
    RouteReplayResult,
    replay_route_legs_committed_observed_v1,
    route_binding_pins_committed_snapshot_observed_v1,
)

_CONTEXT_PATHS_FROM_SCHEMA_V5 = tuple(
    sorted(
        tuple(f"settlement.{name}" for name in FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1)
        + (
            "require_all_nonces",
            "reject_settlements_with_rejected_intents",
            "snapshot_version",
            "fee_split_policy",
        )
        + tuple(f"fee_split_policy.{name}" for name in FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1)
        + ("lp_duration_policy",)
        + tuple(f"lp_duration_policy.{name}" for name in FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1)
    )
)


FCIS_CONTEXT_PROJECTION_PATHS_V5 = (
    "fee_split_policy",
    "fee_split_policy.buyback_bps",
    "fee_split_policy.rewards_bps",
    "fee_split_policy.treasury_bps",
    "lp_duration_policy",
    "lp_duration_policy.base_age_seconds",
    "lp_duration_policy.churn_window_seconds",
    "lp_duration_policy.decay_seconds",
    "lp_duration_policy.max_age_seconds",
    "lp_duration_policy.max_churn_tier",
    "lp_duration_policy.multiplier",
    "reject_settlements_with_rejected_intents",
    "require_all_nonces",
    "settlement.allow_cow_netting",
    "settlement.allow_snapshot_bound_quote_bindings",
    "settlement.min_lp_position_age_seconds",
    "settlement.mode",
    "settlement.now",
    "settlement.protocol_fee_recipient_pubkey",
    "settlement.protocol_fee_share_bps",
    "snapshot_version",
)
if FCIS_CONTEXT_PROJECTION_PATHS_V5 != _CONTEXT_PATHS_FROM_SCHEMA_V5:
    raise RuntimeError("FCIS v5 context projection does not cover the closed schema")


@final
@dataclass(frozen=True, slots=True)
class FCISStepContextProjectionV5:
    """Exact scalar and policy values projected once before evaluation."""

    now: int
    min_lp_position_age_seconds: int
    mode: OwnedEnumV1
    allow_cow_netting: bool
    allow_snapshot_bound_quote_bindings: bool
    protocol_fee_share_bps: int
    protocol_fee_recipient_pubkey: str | None
    require_all_nonces: bool
    reject_settlements_with_rejected_intents: bool
    fee_split_policy: FCISFeeSplitPolicyV1 | None
    lp_duration_policy: LPDurationRiskPolicyV1 | None
    snapshot_version: int


def read_step_execution_context_v5(
    context: FCISStepExecutionContextV1,
) -> tuple[FCISStepContextProjectionV5, FCISContextReadTraceV5]:
    """Project every closed context field and emit its exact path set."""

    if type(context) is not FCISStepExecutionContextV1:
        raise TypeError("context projection requires an exact step context")
    settlement = context.settlement
    fee_policy = context.fee_split_policy
    if fee_policy is not None:
        _fee_components = (
            fee_policy.buyback_bps,
            fee_policy.treasury_bps,
            fee_policy.rewards_bps,
        )
    lp_policy = context.lp_duration_policy
    if lp_policy is not None:
        _lp_components = (
            lp_policy.base_age_seconds,
            lp_policy.max_age_seconds,
            lp_policy.churn_window_seconds,
            lp_policy.decay_seconds,
            lp_policy.multiplier,
            lp_policy.max_churn_tier,
        )
    projection = FCISStepContextProjectionV5(
        now=settlement.now,
        min_lp_position_age_seconds=settlement.min_lp_position_age_seconds,
        mode=settlement.mode,
        allow_cow_netting=settlement.allow_cow_netting,
        allow_snapshot_bound_quote_bindings=settlement.allow_snapshot_bound_quote_bindings,
        protocol_fee_share_bps=settlement.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=settlement.protocol_fee_recipient_pubkey,
        require_all_nonces=context.require_all_nonces,
        reject_settlements_with_rejected_intents=(context.reject_settlements_with_rejected_intents),
        fee_split_policy=fee_policy,
        lp_duration_policy=lp_policy,
        snapshot_version=context.snapshot_version,
    )
    return projection, FCISContextReadTraceV5(FCIS_CONTEXT_PROJECTION_PATHS_V5)


def read_balance_v5(
    balances: CommittedBalanceTableV1,
    trace: FCISStateReadTraceV5,
    *,
    pubkey: str,
    asset: str,
) -> tuple[int, FCISStateReadTraceV5]:
    """Read one exact balance and return the correspondingly extended trace."""

    if type(balances) is not CommittedBalanceTableV1:
        raise TypeError("balance read requires exact committed balances")
    next_trace = extend_fcis_state_read_trace_v5(
        trace,
        balance_keys=((pubkey, asset),),
    )
    return balances.get(pubkey, asset), next_trace


def read_pool_v5(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    trace: FCISStateReadTraceV5,
    *,
    pool_id: str,
) -> tuple[CommittedPoolStateV1 | None, FCISStateReadTraceV5]:
    """Read one exact pool presence/value and return the extended trace."""

    if type(pools) is not OwnedMapV1:
        raise TypeError("pool read requires an exact committed pool map")
    next_trace = extend_fcis_state_read_trace_v5(trace, pool_ids=(pool_id,))
    pool = pools.get(pool_id)
    if pool is not None and type(pool) is not CommittedPoolStateV1:
        raise TypeError("pool read returned a non-committed pool value")
    return pool, next_trace


def read_nonce_v5(
    nonces: CommittedNonceTableV1,
    trace: FCISStateReadTraceV5,
    *,
    pubkey: str,
) -> tuple[int, FCISStateReadTraceV5]:
    """Read one exact nonce and return the correspondingly extended trace."""

    if type(nonces) is not CommittedNonceTableV1:
        raise TypeError("nonce read requires exact committed nonces")
    next_trace = extend_fcis_state_read_trace_v5(trace, nonce_keys=(pubkey,))
    return nonces.get_last(pubkey), next_trace


def read_fee_accumulator_v5(
    fee_accumulator: CommittedFeeAccumulatorStateV1,
    trace: FCISStateReadTraceV5,
) -> tuple[CommittedFeeAccumulatorStateV1, FCISStateReadTraceV5]:
    """Read the active fee accumulator and return the extended trace."""

    if type(fee_accumulator) is not CommittedFeeAccumulatorStateV1:
        raise TypeError("fee read requires an exact committed accumulator")
    next_trace = extend_fcis_state_read_trace_v5(
        trace,
        reads_fee_accumulator=True,
    )
    return fee_accumulator, next_trace


def route_binding_pins_snapshot_traced_v5(
    *,
    binding: RouteBinding,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    trace: FCISStateReadTraceV5,
) -> tuple[bool, FCISStateReadTraceV5]:
    """Check a route binding while recording every fingerprint pool read."""

    if type(binding) is not RouteBinding:
        raise TypeError("route pin check requires an exact binding")
    result, pool_ids = route_binding_pins_committed_snapshot_observed_v1(
        binding,
        pools,
    )
    next_trace = extend_fcis_state_read_trace_v5(trace, pool_ids=pool_ids)
    return result, next_trace


def replay_route_legs_traced_v5(
    *,
    binding: RouteBinding,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    trace: FCISStateReadTraceV5,
) -> tuple[RouteReplayResult, FCISStateReadTraceV5]:
    """Replay a route while recording all fingerprint and leg pool reads."""

    if type(binding) is not RouteBinding:
        raise TypeError("route replay requires an exact binding")
    result, pool_ids = replay_route_legs_committed_observed_v1(
        binding=binding,
        pools=pools,
    )
    next_trace = extend_fcis_state_read_trace_v5(trace, pool_ids=pool_ids)
    return result, next_trace


def apply_spot_deltas_traced_v5(
    *,
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: SpotDeltaBatchV1,
    now: int,
    min_age_seconds: int,
    policy: LPDurationRiskPolicyV1 | None,
    trace: FCISStateReadTraceV5,
) -> tuple[SpotTransitionResultV1, FCISStateReadTraceV5]:
    """Apply one atomic spot batch and return its complete pre-cell trace."""

    result, state_reads = apply_spot_deltas_observed_v1(
        pre_balances=pre_balances,
        pre_pools=pre_pools,
        pre_lp_balances=pre_lp_balances,
        deltas=deltas,
        now=now,
        min_age_seconds=min_age_seconds,
        policy=policy,
    )
    next_trace = extend_fcis_state_read_trace_v5(
        trace,
        balance_keys=state_reads.balance_keys,
        pool_ids=state_reads.pool_ids,
        lp_keys=state_reads.lp_keys,
    )
    return result, next_trace


def apply_spot_replay_deltas_traced_v5(
    *,
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: _SpotReplayDeltaBatchV1,
    trace: FCISStateReadTraceV5,
) -> tuple[_SpotReplayResultV1, FCISStateReadTraceV5]:
    """Apply one sequential replay leaf and retain every observed read prefix."""

    result, state_reads = _apply_spot_replay_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
        deltas,
    )
    next_trace = extend_fcis_state_read_trace_v5(
        trace,
        balance_keys=state_reads.balance_keys,
        pool_ids=state_reads.pool_ids,
        lp_keys=state_reads.lp_keys,
    )
    return result, next_trace


__all__ = (
    "FCISStepContextProjectionV5",
    "apply_spot_deltas_traced_v5",
    "apply_spot_replay_deltas_traced_v5",
    "read_balance_v5",
    "read_fee_accumulator_v5",
    "read_nonce_v5",
    "read_pool_v5",
    "read_step_execution_context_v5",
    "replay_route_legs_traced_v5",
    "route_binding_pins_snapshot_traced_v5",
)
