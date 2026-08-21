"""Immutable contract types for governed ZDEX protocol-fee allocation.

The core moves one already-charged fee occurrence from a committed ingress
bucket into closed destination buckets and a named residue reserve. It has no
IO, verifier, writer capability, route selection, or production authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_DELTA_ATOMS_V1,
    GlobalEconomicEffectPlanV1,
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

BASIS_POINTS_DENOMINATOR_V1: Final = 10_000
PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1: Final = "protocol_fee_allocation"
ZDEX_FEE_ALLOCATION_POLICY_KIND_V1: Final = "zdex_fee_allocation"
FEE_ALLOCATION_OUTPUT_ROLE_V1: Final = "FEE_ALLOCATION_OUTPUT"
FEE_ALLOCATION_OUTPUT_PORT_V1: Final = "ZDEX_FEE_ALLOCATION_OUTPUT_V1"
FEE_INGRESS_PRINCIPAL_V1: Final = "protocol:fee-ingress"
FEE_RESIDUE_PRINCIPAL_V1: Final = "protocol:fee-unallocated-reserve"
FEE_BUYBACK_PRINCIPAL_V1: Final = "protocol-fee-buyback-reserve"
FEE_INGRESS_CONTROL_DOMAIN_V1: Final = "zenoledger:protocol-fee-ingress"
FEE_RESIDUE_CONTROL_DOMAIN_V1: Final = "zenoledger:protocol-fee-residue"


def zdex_fee_allocation_port_schema_root_v1() -> str:
    return hash_global_v1(
        "zdex-fee-allocation-port-schema-v1",
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "port": FEE_ALLOCATION_OUTPUT_PORT_V1,
        },
    )


class ZDEXFeeDestinationV1(str, Enum):
    BUYBACK = "BUYBACK"
    QUALIFIED_HOST_POOL = "QUALIFIED_HOST_POOL"
    TREASURY = "TREASURY"
    PROOF_REWARDS = "PROOF_REWARDS"
    COVER_RESERVE = "COVER_RESERVE"
    LP_REBATES = "LP_REBATES"


ZDEX_FEE_DESTINATIONS_V1: Final = tuple(ZDEXFeeDestinationV1)

_DESTINATION_PRINCIPALS_V1: Final = {
    ZDEXFeeDestinationV1.BUYBACK: FEE_BUYBACK_PRINCIPAL_V1,
    ZDEXFeeDestinationV1.QUALIFIED_HOST_POOL: "protocol:fee-qualified-host-pool",
    ZDEXFeeDestinationV1.TREASURY: "protocol:fee-treasury",
    ZDEXFeeDestinationV1.PROOF_REWARDS: "protocol:fee-proof-rewards",
    ZDEXFeeDestinationV1.COVER_RESERVE: "protocol:fee-cover-reserve",
    ZDEXFeeDestinationV1.LP_REBATES: "protocol:fee-lp-rebates",
}

_DESTINATION_CONTROL_DOMAINS_V1: Final = {
    ZDEXFeeDestinationV1.BUYBACK: "zenoledger:protocol-buyback",
    ZDEXFeeDestinationV1.QUALIFIED_HOST_POOL: "zenoledger:qualified-host-pool",
    ZDEXFeeDestinationV1.TREASURY: "zenoledger:protocol-treasury",
    ZDEXFeeDestinationV1.PROOF_REWARDS: "zenoledger:proof-rewards",
    ZDEXFeeDestinationV1.COVER_RESERVE: "zenoledger:cover-reserve",
    ZDEXFeeDestinationV1.LP_REBATES: "zenoledger:lp-rebates",
}


def fee_destination_principal_v1(destination: ZDEXFeeDestinationV1) -> str:
    if type(destination) is not ZDEXFeeDestinationV1:
        raise TypeError("ZDEX fee destination is not closed")
    return _DESTINATION_PRINCIPALS_V1[destination]


def fee_destination_control_domain_v1(destination: ZDEXFeeDestinationV1) -> str:
    if type(destination) is not ZDEXFeeDestinationV1:
        raise TypeError("ZDEX fee destination is not closed")
    return _DESTINATION_CONTROL_DOMAINS_V1[destination]


def _require_basis_points(value: object, *, name: str) -> int:
    result = _require_nonnegative_int(value, name=name)
    if result > BASIS_POINTS_DENOMINATOR_V1:
        raise ValueError(f"{name} must not exceed {BASIS_POINTS_DENOMINATOR_V1}")
    return result


@dataclass(frozen=True, slots=True)
class ZDEXFeeShareV1:
    destination: ZDEXFeeDestinationV1
    share_bps: int

    def __post_init__(self) -> None:
        if type(self.destination) is not ZDEXFeeDestinationV1:
            raise TypeError("ZDEX fee destination is not closed")
        _require_basis_points(self.share_bps, name="ZDEX fee share")

    def to_canonical(self) -> dict[str, object]:
        return {"destination": self.destination, "share_bps": self.share_bps}


@dataclass(frozen=True, slots=True)
class ZDEXFeeAllocationPolicyV1:
    shares: tuple[ZDEXFeeShareV1, ...]

    def __post_init__(self) -> None:
        if type(self.shares) is not tuple or any(
            type(share) is not ZDEXFeeShareV1 for share in self.shares
        ):
            raise TypeError("ZDEX fee shares must be exact typed tuple data")
        destinations = tuple(share.destination for share in self.shares)
        if destinations != ZDEX_FEE_DESTINATIONS_V1:
            raise ValueError("ZDEX fee shares must use the closed canonical destination order")
        if self.assigned_basis_points > BASIS_POINTS_DENOMINATOR_V1:
            raise ValueError("ZDEX assigned fee shares exceed 10000 basis points")

    @property
    def assigned_basis_points(self) -> int:
        return sum(share.share_bps for share in self.shares)

    @property
    def unassigned_basis_points(self) -> int:
        return BASIS_POINTS_DENOMINATOR_V1 - self.assigned_basis_points

    @property
    def policy_root(self) -> str:
        return hash_global_v1("zdex-fee-allocation-policy-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {"shares": self.shares}


def candidate_zdex_fee_allocation_policy_v1() -> ZDEXFeeAllocationPolicyV1:
    """Return the existing research candidate with 2,500 bps unassigned."""

    shares = (2_000, 0, 3_000, 1_000, 1_000, 500)
    return ZDEXFeeAllocationPolicyV1(
        tuple(
            ZDEXFeeShareV1(destination, share)
            for destination, share in zip(
                ZDEX_FEE_DESTINATIONS_V1,
                shares,
                strict=True,
            )
        )
    )


@dataclass(frozen=True, slots=True)
class ZDEXFeeDestinationAmountV1:
    destination: ZDEXFeeDestinationV1
    allocation_atoms: int

    def __post_init__(self) -> None:
        if type(self.destination) is not ZDEXFeeDestinationV1:
            raise TypeError("ZDEX fee destination amount is not closed")
        _require_atoms_u128(self.allocation_atoms, name="ZDEX fee destination amount")

    def to_canonical(self) -> dict[str, object]:
        return {
            "destination": self.destination,
            "allocation_atoms": self.allocation_atoms,
        }


def _validate_destination_amounts(
    values: object,
    *,
    name: str,
) -> tuple[ZDEXFeeDestinationAmountV1, ...]:
    if type(values) is not tuple or any(
        type(value) is not ZDEXFeeDestinationAmountV1 for value in values
    ):
        raise TypeError(f"{name} must be exact typed tuple data")
    typed_values = values
    if tuple(value.destination for value in typed_values) != ZDEX_FEE_DESTINATIONS_V1:
        raise ValueError(f"{name} must use the closed canonical destination order")
    return typed_values


@dataclass(frozen=True, slots=True)
class ZDEXFeeStateV1:
    fee_asset_id: str
    policy_root: str
    fee_ingress_atoms: int
    unallocated_reserve_atoms: int
    destination_balances: tuple[ZDEXFeeDestinationAmountV1, ...]
    owned_and_custodied_atoms: int
    supply_atoms: int

    def __post_init__(self) -> None:
        _require_root(self.fee_asset_id, name="ZDEX fee asset id")
        _require_root(self.policy_root, name="ZDEX fee state policy root")
        _require_atoms_u128(self.fee_ingress_atoms, name="ZDEX fee ingress")
        _require_atoms_u128(
            self.unallocated_reserve_atoms,
            name="ZDEX unallocated fee reserve",
        )
        _validate_destination_amounts(
            self.destination_balances,
            name="ZDEX fee destination balances",
        )
        _require_atoms_u128(
            self.owned_and_custodied_atoms,
            name="ZDEX fee asset owned and custodied amount",
        )
        _require_atoms_u128(self.supply_atoms, name="ZDEX fee asset supply")
        if self.selected_balance_atoms > self.owned_and_custodied_atoms:
            raise ValueError("ZDEX selected fee balances exceed owned amount")

    @property
    def selected_balance_atoms(self) -> int:
        return (
            self.fee_ingress_atoms
            + self.unallocated_reserve_atoms
            + sum(value.allocation_atoms for value in self.destination_balances)
        )

    @property
    def state_root(self) -> str:
        return hash_global_v1("zdex-fee-allocation-state-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "fee_asset_id": self.fee_asset_id,
            "policy_root": self.policy_root,
            "fee_ingress_atoms": self.fee_ingress_atoms,
            "unallocated_reserve_atoms": self.unallocated_reserve_atoms,
            "destination_balances": self.destination_balances,
            "owned_and_custodied_atoms": self.owned_and_custodied_atoms,
            "supply_atoms": self.supply_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXFeeAllocationContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    allocation_route_release_id: str
    authorized_buyback_route_release_id: str
    tokenomics_module_release_id: str
    command_occurrence_id: str
    policy_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="ZDEX fee allocation chain id")
        _require_nonnegative_int(self.writer_epoch, name="ZDEX fee writer epoch")
        for name in (
            "deployment_root",
            "profile_root",
            "allocation_route_release_id",
            "authorized_buyback_route_release_id",
            "tokenomics_module_release_id",
            "command_occurrence_id",
            "policy_root",
        ):
            _require_root(getattr(self, name), name=f"ZDEX fee {name}")

    def to_canonical(self) -> dict[str, object]:
        return {
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "allocation_route_release_id": self.allocation_route_release_id,
            "authorized_buyback_route_release_id": self.authorized_buyback_route_release_id,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "policy_root": self.policy_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXFeeAllocationCommandV1:
    fee_charged_atoms: int

    def __post_init__(self) -> None:
        _require_atoms_u128(self.fee_charged_atoms, name="ZDEX charged fee")


@dataclass(frozen=True, slots=True)
class ZDEXFeeAllocationOccurrenceV1:
    schema: str
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    allocation_route_release_id: str
    authorized_buyback_route_release_id: str
    tokenomics_module_release_id: str
    command_occurrence_id: str
    policy_root: str
    fee_asset_id: str
    fee_charged_atoms: int
    allocations: tuple[ZDEXFeeDestinationAmountV1, ...]
    carried_residue_atoms: int
    pre_lane_root: str
    post_lane_root: str
    effect_plan_root: str

    def __post_init__(self) -> None:
        if self.schema != GLOBAL_SETTLEMENT_ABI_V1:
            raise ValueError("ZDEX fee occurrence schema mismatch")
        _require_token(self.chain_id, name="ZDEX fee occurrence chain id")
        _require_nonnegative_int(self.writer_epoch, name="ZDEX fee occurrence writer epoch")
        for name in (
            "deployment_root",
            "profile_root",
            "allocation_route_release_id",
            "authorized_buyback_route_release_id",
            "tokenomics_module_release_id",
            "command_occurrence_id",
            "policy_root",
            "fee_asset_id",
            "pre_lane_root",
            "post_lane_root",
            "effect_plan_root",
        ):
            _require_root(getattr(self, name), name=f"ZDEX fee occurrence {name}")
        _require_atoms_u128(self.fee_charged_atoms, name="ZDEX occurrence charged fee")
        if self.fee_charged_atoms == 0 or self.fee_charged_atoms > MAX_DELTA_ATOMS_V1:
            raise ValueError("ZDEX occurrence charged fee must fit a positive signed effect")
        _validate_destination_amounts(self.allocations, name="ZDEX fee allocations")
        _require_atoms_u128(
            self.carried_residue_atoms,
            name="ZDEX occurrence carried residue",
        )
        if self.fee_charged_atoms != (
            sum(value.allocation_atoms for value in self.allocations)
            + self.carried_residue_atoms
        ):
            raise ValueError("ZDEX fee occurrence does not conserve charged fee")

    @property
    def buyback_quote_atoms(self) -> int:
        return self.allocations[0].allocation_atoms

    @property
    def occurrence_root(self) -> str:
        return hash_global_v1("zdex-fee-allocation-occurrence-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "allocation_route_release_id": self.allocation_route_release_id,
            "authorized_buyback_route_release_id": self.authorized_buyback_route_release_id,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "policy_root": self.policy_root,
            "fee_asset_id": self.fee_asset_id,
            "fee_charged_atoms": self.fee_charged_atoms,
            "allocations": self.allocations,
            "carried_residue_atoms": self.carried_residue_atoms,
            "pre_lane_root": self.pre_lane_root,
            "post_lane_root": self.post_lane_root,
            "effect_plan_root": self.effect_plan_root,
        }


class ZDEXFeeAllocationRejectCodeV1(str, Enum):
    ZERO_FEE = "ZERO_FEE"
    POLICY_MISMATCH = "POLICY_MISMATCH"
    INSUFFICIENT_FEE_INGRESS = "INSUFFICIENT_FEE_INGRESS"
    EFFECT_WIDTH_EXCEEDED = "EFFECT_WIDTH_EXCEEDED"
    STATE_OVERFLOW = "STATE_OVERFLOW"


@dataclass(frozen=True, slots=True)
class ZDEXFeeAllocationAcceptedV1:
    pre_state: ZDEXFeeStateV1
    post_state: ZDEXFeeStateV1
    effects: GlobalEconomicEffectPlanV1
    occurrence: ZDEXFeeAllocationOccurrenceV1

    def __post_init__(self) -> None:
        if any(
            (
                type(self.pre_state) is not ZDEXFeeStateV1,
                type(self.post_state) is not ZDEXFeeStateV1,
                type(self.effects) is not GlobalEconomicEffectPlanV1,
                type(self.occurrence) is not ZDEXFeeAllocationOccurrenceV1,
            )
        ):
            raise TypeError("ZDEX fee acceptance requires exact typed data")
        if self.effects.is_empty:
            raise ValueError("ZDEX fee acceptance requires effects")
        if (
            self.pre_state.state_root != self.occurrence.pre_lane_root
            or self.post_state.state_root != self.occurrence.post_lane_root
            or self.effects.effect_plan_root != self.occurrence.effect_plan_root
        ):
            raise ValueError("ZDEX fee acceptance commitments are disconnected")


@dataclass(frozen=True, slots=True)
class ZDEXFeeAllocationRejectedV1:
    code: ZDEXFeeAllocationRejectCodeV1
    pre_state: ZDEXFeeStateV1
    post_state: ZDEXFeeStateV1
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXFeeAllocationRejectCodeV1:
            raise TypeError("ZDEX fee reject code is not closed")
        if type(self.pre_state) is not ZDEXFeeStateV1 or self.post_state is not self.pre_state:
            raise ValueError("ZDEX fee rejection must preserve the exact pre-state")
        if type(self.effects) is not GlobalEconomicEffectPlanV1 or not self.effects.is_empty:
            raise ValueError("ZDEX fee rejection must carry no effects")


ZDEXFeeAllocationResultV1 = ZDEXFeeAllocationAcceptedV1 | ZDEXFeeAllocationRejectedV1


__all__ = [
    "BASIS_POINTS_DENOMINATOR_V1",
    "FEE_ALLOCATION_OUTPUT_PORT_V1",
    "FEE_ALLOCATION_OUTPUT_ROLE_V1",
    "FEE_INGRESS_CONTROL_DOMAIN_V1",
    "FEE_INGRESS_PRINCIPAL_V1",
    "FEE_BUYBACK_PRINCIPAL_V1",
    "FEE_RESIDUE_CONTROL_DOMAIN_V1",
    "FEE_RESIDUE_PRINCIPAL_V1",
    "PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1",
    "ZDEX_FEE_ALLOCATION_POLICY_KIND_V1",
    "ZDEX_FEE_DESTINATIONS_V1",
    "ZDEXFeeAllocationAcceptedV1",
    "ZDEXFeeAllocationCommandV1",
    "ZDEXFeeAllocationContextV1",
    "ZDEXFeeAllocationOccurrenceV1",
    "ZDEXFeeAllocationPolicyV1",
    "ZDEXFeeAllocationRejectCodeV1",
    "ZDEXFeeAllocationRejectedV1",
    "ZDEXFeeAllocationResultV1",
    "ZDEXFeeDestinationAmountV1",
    "ZDEXFeeDestinationV1",
    "ZDEXFeeShareV1",
    "ZDEXFeeStateV1",
    "candidate_zdex_fee_allocation_policy_v1",
    "fee_destination_control_domain_v1",
    "fee_destination_principal_v1",
    "zdex_fee_allocation_port_schema_root_v1",
]
