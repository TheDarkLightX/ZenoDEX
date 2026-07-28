"""Exact immutable values for the unmounted FCIS strong-settlement relation."""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from typing import TypeAlias, final

from ..state.fcis_execution_context_values import FCISSettlementExecutionContextV1
from ..state.lp_duration_policy_values import LPDurationRiskPolicyV1
from ..state.owned_collections import OwnedMapV1, owned_map_structure_is_exact_v1
from ..state.state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
    POOL_MAP_SCHEMA_ID_V1,
    CommittedBalanceTableV1,
    CommittedLPTableV1,
    CommittedPoolStateV1,
)
from ..state.state_transitions import (
    CanonicalBalancePatchV1,
    CanonicalLPPositionPatchV1,
    CanonicalPoolPatchV1,
)
from .fcis_state_read_trace_v5 import FCISStateReadTraceV5

_STRONG_SETTLEMENT_CONSTRUCTION_TOKEN_V1 = object()


def _revalidate_pool_map_v1(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> None:
    if type(pools) is not OwnedMapV1:
        raise TypeError("strong-settlement pools must be an exact owned map")
    if not owned_map_structure_is_exact_v1(pools):
        raise TypeError("strong-settlement pool map structure mismatch")
    if (
        pools.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or pools.schema_id != POOL_MAP_SCHEMA_ID_V1
    ):
        raise TypeError("strong-settlement pool map schema mismatch")
    keys = tuple(key for key, _pool in pools.entries)
    if keys != tuple(sorted(keys)) or len(keys) != len(set(keys)):
        raise ValueError("strong-settlement pool map is not canonical")
    for key, pool in pools.entries:
        if type(key) is not str or not key:
            raise TypeError("strong-settlement pool key must be an exact string")
        if type(pool) is not CommittedPoolStateV1:
            raise TypeError("strong-settlement pool value must be exact")
        pool.__post_init__()
        if pools.get(key) != pool:
            raise TypeError("strong-settlement pool map index mismatch")


def _revalidate_settlement_context_v1(
    context: FCISSettlementExecutionContextV1,
) -> None:
    if type(context) is not FCISSettlementExecutionContextV1:
        raise TypeError("strong-settlement context must be exact")
    context.__post_init__()


def _revalidate_lp_duration_policy_v1(
    policy: LPDurationRiskPolicyV1 | None,
) -> None:
    if policy is None:
        return
    if type(policy) is not LPDurationRiskPolicyV1:
        raise TypeError("strong-settlement LP duration policy must be exact or None")
    policy.__post_init__()


@final
@dataclass(frozen=True, slots=True)
class StrongSettlementContextV1:
    """Existing exact settlement context plus its duration-risk policy."""

    settlement: FCISSettlementExecutionContextV1
    lp_duration_policy: LPDurationRiskPolicyV1 | None

    def __post_init__(self) -> None:
        _revalidate_settlement_context_v1(self.settlement)
        _revalidate_lp_duration_policy_v1(self.lp_duration_policy)


@final
@dataclass(frozen=True, slots=True)
class ExactSpotPreStateV1:
    """Exact three-field state projection used by spot settlement replay."""

    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1

    def __post_init__(self) -> None:
        if type(self.balances) is not CommittedBalanceTableV1:
            raise TypeError("strong-settlement balances must be exact")
        if type(self.lp_balances) is not CommittedLPTableV1:
            raise TypeError("strong-settlement LP state must be exact")
        self.balances.__post_init__()
        _revalidate_pool_map_v1(self.pools)
        self.lp_balances.__post_init__()


@final
@dataclass(frozen=True, slots=True)
class ExactStrongSettlementCandidateV1:
    """One exact successor and its canonical patches from the same replay."""

    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1
    balance_patch: CanonicalBalancePatchV1 | None
    pool_patch: CanonicalPoolPatchV1 | None
    lp_patch: CanonicalLPPositionPatchV1 | None
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _STRONG_SETTLEMENT_CONSTRUCTION_TOKEN_V1:
            raise TypeError("strong-settlement candidate requires controlled derivation")
        ExactSpotPreStateV1(
            balances=self.balances,
            pools=self.pools,
            lp_balances=self.lp_balances,
        )
        if (
            self.balance_patch is not None
            and type(self.balance_patch) is not CanonicalBalancePatchV1
        ):
            raise TypeError("strong-settlement balance patch must be exact or None")
        if self.balance_patch is not None:
            self.balance_patch.__post_init__()
        if self.pool_patch is not None and type(self.pool_patch) is not CanonicalPoolPatchV1:
            raise TypeError("strong-settlement pool patch must be exact or None")
        if self.pool_patch is not None:
            self.pool_patch.__post_init__()
        if self.lp_patch is not None and type(self.lp_patch) is not CanonicalLPPositionPatchV1:
            raise TypeError("strong-settlement LP patch must be exact or None")
        if self.lp_patch is not None:
            self.lp_patch.__post_init__()


@final
@dataclass(frozen=True, slots=True)
class ExactStrongSettlementRejectV1:
    """Stable ordinary rejection with no successor authority."""

    reason: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _STRONG_SETTLEMENT_CONSTRUCTION_TOKEN_V1:
            raise TypeError("strong-settlement rejection requires controlled derivation")
        if type(self.reason) is not str or not self.reason:
            raise TypeError("strong-settlement rejection requires an exact reason")


ExactStrongSettlementResultV1: TypeAlias = (
    ExactStrongSettlementCandidateV1 | ExactStrongSettlementRejectV1
)


@final
@dataclass(frozen=True, slots=True)
class ExactStrongSettlementObservedV1:
    """One exact result paired with its completed semantic read prefix."""

    result: ExactStrongSettlementResultV1
    state_read_trace: FCISStateReadTraceV5
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _STRONG_SETTLEMENT_CONSTRUCTION_TOKEN_V1:
            raise TypeError("observed strong-settlement result requires controlled derivation")
        if type(self.result) not in (
            ExactStrongSettlementCandidateV1,
            ExactStrongSettlementRejectV1,
        ):
            raise TypeError("observed strong-settlement result must be exact")
        if type(self.state_read_trace) is not FCISStateReadTraceV5:
            raise TypeError("observed strong-settlement trace must be exact")
        self.state_read_trace.__post_init__()


def _candidate_from_exact_strong_validator_v1(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    balance_patch: CanonicalBalancePatchV1 | None,
    pool_patch: CanonicalPoolPatchV1 | None,
    lp_patch: CanonicalLPPositionPatchV1 | None,
) -> ExactStrongSettlementCandidateV1:
    return ExactStrongSettlementCandidateV1(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        balance_patch=balance_patch,
        pool_patch=pool_patch,
        lp_patch=lp_patch,
        _construction_token=_STRONG_SETTLEMENT_CONSTRUCTION_TOKEN_V1,
    )


def _reject_from_exact_strong_validator_v1(
    reason: str,
) -> ExactStrongSettlementRejectV1:
    return ExactStrongSettlementRejectV1(
        reason=reason,
        _construction_token=_STRONG_SETTLEMENT_CONSTRUCTION_TOKEN_V1,
    )


def _observed_from_exact_strong_validator_v1(
    result: ExactStrongSettlementResultV1,
    state_read_trace: FCISStateReadTraceV5,
) -> ExactStrongSettlementObservedV1:
    return ExactStrongSettlementObservedV1(
        result=result,
        state_read_trace=state_read_trace,
        _construction_token=_STRONG_SETTLEMENT_CONSTRUCTION_TOKEN_V1,
    )


__all__ = (
    "ExactSpotPreStateV1",
    "ExactStrongSettlementCandidateV1",
    "ExactStrongSettlementObservedV1",
    "ExactStrongSettlementRejectV1",
    "ExactStrongSettlementResultV1",
    "StrongSettlementContextV1",
)
