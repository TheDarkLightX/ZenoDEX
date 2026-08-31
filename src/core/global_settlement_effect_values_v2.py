"""Economic effect row values for GlobalSettlementABI V2."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from .global_settlement_primitives_v2 import (
    LaneIdV2,
    _require_atoms_u128_v2,
    _require_delta_atoms_i128_v2,
    _require_root_v2,
    _require_token_v2,
)


class EconomicEffectKindV2(str, Enum):
    ACCOUNT_MOVEMENT = "ACCOUNT_MOVEMENT"
    ISSUE = "ISSUE"
    BURN = "BURN"
    CUSTODY = "CUSTODY"
    LIABILITY = "LIABILITY"
    RESERVE = "RESERVE"
    FEE_ALLOCATION = "FEE_ALLOCATION"
    REWARD = "REWARD"
    SLASH = "SLASH"


@dataclass(frozen=True, slots=True, order=True)
class EconomicEffectRowV2:
    kind: EconomicEffectKindV2
    principal: str
    asset: str
    custody_domain: str
    delta_atoms: int

    def __post_init__(self) -> None:
        if type(self.kind) is not EconomicEffectKindV2:
            raise TypeError("economic effect kind is not closed")
        _require_token_v2(self.principal, name="economic effect principal")
        _require_token_v2(self.asset, name="economic effect asset")
        _require_token_v2(self.custody_domain, name="economic effect custody domain")
        _require_delta_atoms_i128_v2(self.delta_atoms, name="economic effect delta")
        if self.delta_atoms == 0:
            raise ValueError("economic effect delta must be nonzero")
        if self.kind is EconomicEffectKindV2.ISSUE and self.delta_atoms < 0:
            raise ValueError("issue effect must be positive")
        if self.kind is EconomicEffectKindV2.BURN and self.delta_atoms > 0:
            raise ValueError("burn effect must be negative")

    @property
    def key(self) -> tuple[str, str, str, str]:
        return (self.kind.value, self.asset, self.principal, self.custody_domain)

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "principal": self.principal,
            "asset": self.asset,
            "custody_domain": self.custody_domain,
            "delta_atoms": self.delta_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class AssetConservationRowV2:
    asset: str
    owned_and_custodied_pre_atoms: int
    owned_and_custodied_post_atoms: int
    supply_pre_atoms: int
    supply_post_atoms: int
    authorized_issue_atoms: int
    authorized_burn_atoms: int

    def __post_init__(self) -> None:
        _require_token_v2(self.asset, name="conservation asset")
        for field_name in (
            "owned_and_custodied_pre_atoms",
            "owned_and_custodied_post_atoms",
            "supply_pre_atoms",
            "supply_post_atoms",
            "authorized_issue_atoms",
            "authorized_burn_atoms",
        ):
            _require_atoms_u128_v2(
                getattr(self, field_name),
                name=f"conservation {field_name}",
            )
        expected_owned = (
            self.owned_and_custodied_pre_atoms
            + self.authorized_issue_atoms
            - self.authorized_burn_atoms
        )
        expected_supply = (
            self.supply_pre_atoms + self.authorized_issue_atoms - self.authorized_burn_atoms
        )
        if expected_owned < 0 or self.owned_and_custodied_post_atoms != expected_owned:
            raise ValueError("owned-and-custodied conservation mismatch")
        if expected_supply < 0 or self.supply_post_atoms != expected_supply:
            raise ValueError("supply conservation mismatch")

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "owned_and_custodied_pre_atoms": self.owned_and_custodied_pre_atoms,
            "owned_and_custodied_post_atoms": self.owned_and_custodied_post_atoms,
            "supply_pre_atoms": self.supply_pre_atoms,
            "supply_post_atoms": self.supply_post_atoms,
            "authorized_issue_atoms": self.authorized_issue_atoms,
            "authorized_burn_atoms": self.authorized_burn_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class FeeConservationRowV2:
    asset: str
    fee_charged_atoms: int
    current_allocations_atoms: int
    carried_residue_atoms: int

    def __post_init__(self) -> None:
        _require_token_v2(self.asset, name="fee conservation asset")
        for field_name in (
            "fee_charged_atoms",
            "current_allocations_atoms",
            "carried_residue_atoms",
        ):
            _require_atoms_u128_v2(
                getattr(self, field_name),
                name=f"fee conservation {field_name}",
            )
        if self.fee_charged_atoms != (self.current_allocations_atoms + self.carried_residue_atoms):
            raise ValueError("fee allocation and carried residue do not reconcile")

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "fee_charged_atoms": self.fee_charged_atoms,
            "current_allocations_atoms": self.current_allocations_atoms,
            "carried_residue_atoms": self.carried_residue_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class LaneWriteV2:
    lane_id: LaneIdV2
    pre_root: str
    post_root: str

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV2:
            raise TypeError("lane write lane is not closed")
        _require_root_v2(self.pre_root, name="lane write pre-root", allow_zero=True)
        _require_root_v2(self.post_root, name="lane write post-root", allow_zero=True)

    def to_canonical(self) -> dict[str, object]:
        return {
            "lane_id": self.lane_id,
            "pre_root": self.pre_root,
            "post_root": self.post_root,
        }


@dataclass(frozen=True, slots=True, order=True)
class ExternalOutboxEnqueueV2:
    effect_id: str
    destination_id: str
    payload_hash: str
    adapter_profile_root: str

    def __post_init__(self) -> None:
        _require_root_v2(self.effect_id, name="external outbox effect id")
        _require_token_v2(self.destination_id, name="external outbox destination")
        if self.destination_id.startswith("zenoledger:"):
            raise ValueError("same-ledger movement must not enter the external outbox")
        _require_root_v2(self.payload_hash, name="external outbox payload hash")
        _require_root_v2(
            self.adapter_profile_root,
            name="external outbox adapter profile root",
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "effect_id": self.effect_id,
            "destination_id": self.destination_id,
            "payload_hash": self.payload_hash,
            "adapter_profile_root": self.adapter_profile_root,
        }


__all__ = [
    "EconomicEffectKindV2",
    "EconomicEffectRowV2",
    "AssetConservationRowV2",
    "FeeConservationRowV2",
    "LaneWriteV2",
    "ExternalOutboxEnqueueV2",
]
