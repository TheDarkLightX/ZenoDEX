"""Minimal acyclic quote port for a same-occurrence ZDEX buy-and-burn."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    _require_atoms_u128,
    _require_root,
    hash_global_v1,
)
from .zdex_fee_allocation_types_v1 import FEE_BUYBACK_PRINCIPAL_V1
from .zdex_purchase_burn_route_types_v1 import zdex_pool_reserve_principal_v1

ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2: Final = (
    "zenodex/zdex-atomic-buyback-quote-port/v2"
)


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackQuotePortV2:
    """Proof-independent Tokenomics quote-phase output consumed by Spot.

    Journal and receipt roots are excluded to keep the dependency graph
    acyclic. The final route guest authenticates both child journals and checks
    that they commit this exact port root.
    """

    profile_root: str
    route_release_id: str
    command_occurrence_id: str
    global_pre_state_root: str
    producer_module_release_id: str
    consumer_module_release_id: str
    producer_quote_pre_state_root: str
    producer_quote_post_state_root: str
    producer_quote_effect_plan_root: str
    selected_pool_id: str
    quote_asset_id: str
    amount_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        for field_name in (
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "global_pre_state_root",
            "producer_module_release_id",
            "consumer_module_release_id",
            "producer_quote_pre_state_root",
            "producer_quote_post_state_root",
            "producer_quote_effect_plan_root",
            "selected_pool_id",
            "quote_asset_id",
        ):
            value = getattr(self, field_name)
            if type(value) is not str:
                raise TypeError(f"ZDEX quote port {field_name} must be exact str")
            _require_root(value, name=f"ZDEX quote port {field_name}")
        amount = _require_atoms_u128(self.amount_atoms, name="ZDEX quote port amount")
        if amount == 0 or amount > MAX_DELTA_ATOMS_V1:
            raise ValueError("ZDEX quote port amount must fit a positive signed effect")
        if self.producer_module_release_id == self.consumer_module_release_id:
            raise ValueError("ZDEX quote port module releases must differ")
        if self.producer_quote_pre_state_root == self.producer_quote_post_state_root:
            raise ValueError("ZDEX quote phase must change Tokenomics state")

    @property
    def source_principal(self) -> str:
        return FEE_BUYBACK_PRINCIPAL_V1

    @property
    def destination_principal(self) -> str:
        self.validate()
        return zdex_pool_reserve_principal_v1(
            pool_id=self.selected_pool_id,
            asset_id=self.quote_asset_id,
        )

    @property
    def port_root(self) -> str:
        return hash_global_v1("zdex-atomic-buyback-quote-port-v2", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        self.validate()
        return {
            "schema": ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2,
            "profile_root": self.profile_root,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "global_pre_state_root": self.global_pre_state_root,
            "producer_module_release_id": self.producer_module_release_id,
            "consumer_module_release_id": self.consumer_module_release_id,
            "producer_quote_pre_state_root": self.producer_quote_pre_state_root,
            "producer_quote_post_state_root": self.producer_quote_post_state_root,
            "producer_quote_effect_plan_root": self.producer_quote_effect_plan_root,
            "selected_pool_id": self.selected_pool_id,
            "quote_asset_id": self.quote_asset_id,
            "amount_atoms": self.amount_atoms,
        }


__all__ = [
    "ZDEXAtomicBuybackQuotePortV2",
    "ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2",
]
