"""Closed tokenomics state for same-occurrence ZDEX buy-and-burn."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final

from .global_settlement_types_v1 import hash_global_v1
from .zdex_buyback_spend_v1 import ZDEXBuybackSpendStateV1
from .zdex_fee_allocation_types_v1 import ZDEXFeeStateV1
from .zdex_tokenomics_lane_v1 import ZDEXTokenomicsLaneStateV1

ZDEX_ATOMIC_BUYBACK_TOKENOMICS_STATE_SCHEMA_V1: Final = (
    "zenodex/zdex-atomic-buyback-tokenomics-state/v1"
)


def zdex_atomic_buyback_tokenomics_state_schema_root_v1() -> str:
    return hash_global_v1(
        "zdex-tokenomics-state-schema-v1",
        {"schema": ZDEX_ATOMIC_BUYBACK_TOKENOMICS_STATE_SCHEMA_V1},
    )


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackTokenomicsStateV1:
    """One state root owns supply, fee reserves, and buyback cadence."""

    tokenomics: ZDEXTokenomicsLaneStateV1
    buyback_spend_states: tuple[ZDEXBuybackSpendStateV1, ...]

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.tokenomics) is not ZDEXTokenomicsLaneStateV1:
            raise TypeError("atomic buyback tokenomics state must be exact typed data")
        self.tokenomics.validate()
        if type(self.buyback_spend_states) is not tuple or any(
            type(state) is not ZDEXBuybackSpendStateV1 for state in self.buyback_spend_states
        ):
            raise TypeError("atomic buyback cadence states must be an exact tuple")
        for state in self.buyback_spend_states:
            state.validate()
        fee_assets = tuple(state.fee_asset_id for state in self.tokenomics.fee_allocation_states)
        cadence_assets = tuple(state.quote_asset_id for state in self.buyback_spend_states)
        if cadence_assets != fee_assets:
            raise ValueError("atomic buyback cadence must cover every fee asset in canonical order")

    @property
    def state_root(self) -> str:
        self.validate()
        return hash_global_v1(
            "zdex-atomic-buyback-tokenomics-state-v1",
            self.to_canonical(),
        )

    def fee_state_for(self, quote_asset_id: str) -> ZDEXFeeStateV1:
        for state in self.tokenomics.fee_allocation_states:
            if state.fee_asset_id == quote_asset_id:
                return state
        raise ValueError("atomic buyback quote asset has no fee state")

    def cadence_state_for(self, quote_asset_id: str) -> ZDEXBuybackSpendStateV1:
        for state in self.buyback_spend_states:
            if state.quote_asset_id == quote_asset_id:
                return state
        raise ValueError("atomic buyback quote asset has no cadence state")

    def with_buyback_result(
        self,
        *,
        fee_state: ZDEXFeeStateV1,
        cadence_state: ZDEXBuybackSpendStateV1,
    ) -> ZDEXAtomicBuybackTokenomicsStateV1:
        if type(fee_state) is not ZDEXFeeStateV1:
            raise TypeError("atomic buyback fee post-state must be exact typed data")
        if type(cadence_state) is not ZDEXBuybackSpendStateV1:
            raise TypeError("atomic buyback cadence post-state must be exact typed data")
        if fee_state.fee_asset_id != cadence_state.quote_asset_id:
            raise ValueError("atomic buyback fee and cadence assets differ")
        fee_states = tuple(
            fee_state if row.fee_asset_id == fee_state.fee_asset_id else row
            for row in self.tokenomics.fee_allocation_states
        )
        cadence_states = tuple(
            cadence_state if row.quote_asset_id == cadence_state.quote_asset_id else row
            for row in self.buyback_spend_states
        )
        if fee_state not in fee_states or cadence_state not in cadence_states:
            raise ValueError("atomic buyback post-state asset is outside the registry")
        return ZDEXAtomicBuybackTokenomicsStateV1(
            replace(self.tokenomics, fee_allocation_states=fee_states),
            cadence_states,
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_ATOMIC_BUYBACK_TOKENOMICS_STATE_SCHEMA_V1,
            "tokenomics": self.tokenomics,
            "buyback_spend_states": self.buyback_spend_states,
        }


__all__ = [
    "ZDEXAtomicBuybackTokenomicsStateV1",
    "ZDEX_ATOMIC_BUYBACK_TOKENOMICS_STATE_SCHEMA_V1",
    "zdex_atomic_buyback_tokenomics_state_schema_root_v1",
]
