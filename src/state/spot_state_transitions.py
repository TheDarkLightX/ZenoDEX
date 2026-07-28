"""Compatibility facade for exact FCIS spot transitions.

The closure-clean aggregate and sequential replay implementations live in
``fcis_spot_replay``.  This module preserves the established public spot API
and the private replay symbols consumed by the unmounted mixed validator while
delegating every transition to that single exact implementation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, final

from .fcis_spot_replay import (
    FCISSpotDeltaBatchV1,
    FCISSpotReplayDeltaBatchV1,
    FCISSpotReplayOkV1,
    FCISSpotReplayTransitionRejectV1,
    FCISSpotStateReadSetV1,
    FCISSpotTransitionOkV1,
    FCISSpotTransitionRejectV1,
    FCISSpotTransitionResultV1,
    apply_fcis_spot_deltas_observed_v1,
    apply_fcis_spot_replay_observed_v1,
)
from .lp_duration_transitions import LPDurationRiskPolicyV1
from .owned_collections import OwnedMapV1
from .state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedLPTableV1,
    CommittedPoolStateV1,
)

SpotStateReadSetV1 = FCISSpotStateReadSetV1
SpotTransitionOkV1 = FCISSpotTransitionOkV1
SpotTransitionRejectV1: TypeAlias = FCISSpotTransitionRejectV1
SpotTransitionResultV1: TypeAlias = FCISSpotTransitionResultV1
SpotDeltaBatchV1 = FCISSpotDeltaBatchV1

_SpotReplayDeltaBatchV1 = FCISSpotReplayDeltaBatchV1
_SpotReplayTransitionRejectV1: TypeAlias = FCISSpotReplayTransitionRejectV1


@final
@dataclass(frozen=True, slots=True)
class _SpotReplayOkV1:
    """Compatibility result that cannot be used as public candidate authority."""

    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1


_SpotReplayResultV1: TypeAlias = _SpotReplayOkV1 | _SpotReplayTransitionRejectV1


def _apply_spot_replay_deltas_observed_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: FCISSpotReplayDeltaBatchV1,
) -> tuple[_SpotReplayResultV1, FCISSpotStateReadSetV1]:
    """Delegate replay while preserving the established private result type."""

    result, reads = apply_fcis_spot_replay_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
        deltas,
    )
    if type(result) is FCISSpotReplayOkV1:
        return (
            _SpotReplayOkV1(
                balances=result.balances,
                pools=result.pools,
                lp_balances=result.lp_balances,
            ),
            reads,
        )
    return result, reads


def _apply_spot_replay_deltas_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: FCISSpotReplayDeltaBatchV1,
) -> _SpotReplayResultV1:
    """Delegate replay and discard non-authoritative read evidence."""

    result, _state_reads = _apply_spot_replay_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
        deltas,
    )
    return result


def apply_spot_deltas_observed_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: FCISSpotDeltaBatchV1,
    *,
    now: int,
    min_age_seconds: int,
    policy: LPDurationRiskPolicyV1 | None,
) -> tuple[FCISSpotTransitionResultV1, FCISSpotStateReadSetV1]:
    """Delegate one aggregate spot transition to the exact implementation."""

    return apply_fcis_spot_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
        deltas,
        now=now,
        min_age_seconds=min_age_seconds,
        policy=policy,
    )


def apply_spot_deltas_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: FCISSpotDeltaBatchV1,
    *,
    now: int,
    min_age_seconds: int,
    policy: LPDurationRiskPolicyV1 | None,
) -> FCISSpotTransitionResultV1:
    """Delegate one aggregate spot transition and discard read evidence."""

    result, _state_reads = apply_spot_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
        deltas,
        now=now,
        min_age_seconds=min_age_seconds,
        policy=policy,
    )
    return result


__all__ = [
    "SpotDeltaBatchV1",
    "SpotStateReadSetV1",
    "SpotTransitionOkV1",
    "SpotTransitionRejectV1",
    "SpotTransitionResultV1",
    "apply_spot_deltas_observed_v1",
    "apply_spot_deltas_v1",
]
