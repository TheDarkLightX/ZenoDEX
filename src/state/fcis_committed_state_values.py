"""Exact eight-field committed state aggregate for the FCIS transition."""

from __future__ import annotations

from dataclasses import dataclass
from typing import final

from .owned_collections import OwnedMapV1
from .state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedOracleStateV1,
    CommittedPerpsStateV1,
    CommittedPoolStateV1,
    CommittedVaultStateV1,
)

FCIS_COMMITTED_STATE_SCHEMA_ID_V1 = "zenodex/fcis/state/committed-dex-state/v1"


@final
@dataclass(frozen=True, slots=True)
class FCISCommittedStateSourceV1:
    """Exact source carrier; the closed profile owns every field."""

    balances: object
    pools: object
    lp_balances: object
    nonces: object
    vault: object
    oracle: object
    fee_accumulator: object
    perps: object


@final
@dataclass(frozen=True, slots=True)
class FCISCommittedStateV1:
    """One transitively owned committed DEX state in normative field order."""

    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1
    nonces: CommittedNonceTableV1
    vault: CommittedVaultStateV1 | None
    oracle: CommittedOracleStateV1 | None
    fee_accumulator: CommittedFeeAccumulatorStateV1
    perps: CommittedPerpsStateV1 | None

    def __post_init__(self) -> None:
        exact_required = (
            ("balances", self.balances, CommittedBalanceTableV1),
            ("pools", self.pools, OwnedMapV1),
            ("lp_balances", self.lp_balances, CommittedLPTableV1),
            ("nonces", self.nonces, CommittedNonceTableV1),
            (
                "fee_accumulator",
                self.fee_accumulator,
                CommittedFeeAccumulatorStateV1,
            ),
        )
        for field_name, value, expected_type in exact_required:
            if type(value) is not expected_type:
                raise TypeError(f"{field_name} must be an exact committed value")
        exact_optional = (
            ("vault", self.vault, CommittedVaultStateV1),
            ("oracle", self.oracle, CommittedOracleStateV1),
            ("perps", self.perps, CommittedPerpsStateV1),
        )
        for field_name, value, expected_type in exact_optional:
            if value is not None and type(value) is not expected_type:
                raise TypeError(f"{field_name} must be None or an exact committed value")


__all__ = (
    "FCIS_COMMITTED_STATE_SCHEMA_ID_V1",
    "FCISCommittedStateSourceV1",
    "FCISCommittedStateV1",
)
