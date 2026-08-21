"""Closed values for the experimental ZDEX AMM-purchase-to-burn route."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1: Final = "protocol_buy_and_burn"
AMM_PURCHASE_OUTPUT_ROLE_V1: Final = "AMM_PURCHASE_OUTPUT"
ZDEX_BURN_INPUT_ROLE_V1: Final = "ZDEX_BURN_INPUT"

AMM_POOL_CUSTODY_DOMAIN_V1: Final = "zenoledger:amm-pool"
PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1: Final = "zenoledger:protocol-buyback"
PROTOCOL_BURN_CUSTODY_DOMAIN_V1: Final = "zenoledger:protocol-burn"
PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1: Final = "zenoledger:protocol-supply"
ZDEX_SUPPLY_PRINCIPAL_V1: Final = "protocol:zdex-supply"


class ZDEXPurchaseBurnRouteRejectCodeV1(str, Enum):
    ROUTE_BINDING_MISMATCH = "ROUTE_BINDING_MISMATCH"
    OCCURRENCE_MISMATCH = "OCCURRENCE_MISMATCH"
    PROFILE_OR_EPOCH_MISMATCH = "PROFILE_OR_EPOCH_MISMATCH"
    PURCHASE_WITNESS_MISMATCH = "PURCHASE_WITNESS_MISMATCH"
    BURN_WITNESS_MISMATCH = "BURN_WITNESS_MISMATCH"
    ASSET_MISMATCH = "ASSET_MISMATCH"
    PURCHASE_OCCURRENCE_MISMATCH = "PURCHASE_OCCURRENCE_MISMATCH"
    AMOUNT_MISMATCH = "AMOUNT_MISMATCH"
    BURN_BUCKET_MISMATCH = "BURN_BUCKET_MISMATCH"
    BUYBACK_BUDGET_MISMATCH = "BUYBACK_BUDGET_MISMATCH"
    CONSERVATION_HISTORY_DISCONNECTED = "CONSERVATION_HISTORY_DISCONNECTED"


def _port_schema_root(port_name: str) -> str:
    return hash_global_v1(
        "zdex-purchase-burn-port-schema-v1",
        {"schema": GLOBAL_SETTLEMENT_ABI_V1, "port_name": port_name},
    )


def zdex_amm_purchase_port_schema_root_v1() -> str:
    return _port_schema_root("ZDEX_AMM_PURCHASE_OUTPUT_V1")


def zdex_burn_port_schema_root_v1() -> str:
    return _port_schema_root("ZDEX_AUTHORIZED_BURN_INPUT_V1")


@dataclass(frozen=True, slots=True)
class ZDEXAMMPurchaseJournalV1:
    """Public output of a checked exact-in AMM purchase of ZDEX."""

    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    route_release_id: str
    command_occurrence_id: str
    spot_module_release_id: str
    issue_burn_policy_root: str
    buyback_budget_occurrence_root: str
    quote_asset_id: str
    zdex_asset_id: str
    quote_source_bucket_id: str
    quote_pool_bucket_id: str
    zdex_pool_bucket_id: str
    burn_bucket_id: str
    quote_amount_in_atoms: int
    purchased_zdex_atoms: int
    quote_source_pre_atoms: int
    quote_source_post_atoms: int
    quote_pool_pre_atoms: int
    quote_pool_post_atoms: int
    zdex_pool_pre_atoms: int
    zdex_pool_post_atoms: int
    burn_bucket_pre_atoms: int
    burn_bucket_post_atoms: int
    quote_owned_atoms: int
    quote_supply_atoms: int
    zdex_owned_atoms: int
    zdex_supply_atoms: int
    pre_spot_lane_root: str
    post_spot_lane_root: str
    effect_plan_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="ZDEX purchase chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "spot_module_release_id",
            "issue_burn_policy_root",
            "buyback_budget_occurrence_root",
            "quote_asset_id",
            "zdex_asset_id",
            "pre_spot_lane_root",
            "post_spot_lane_root",
            "effect_plan_root",
        ):
            _require_root(getattr(self, field_name), name=f"ZDEX purchase {field_name}")
        _require_nonnegative_int(self.writer_epoch, name="ZDEX purchase writer epoch")
        for field_name in (
            "quote_source_bucket_id",
            "quote_pool_bucket_id",
            "zdex_pool_bucket_id",
            "burn_bucket_id",
        ):
            _require_token(getattr(self, field_name), name=f"ZDEX purchase {field_name}")
        if self.quote_asset_id == self.zdex_asset_id:
            raise ValueError("ZDEX purchase quote and output assets must differ")
        if self.quote_source_bucket_id == self.quote_pool_bucket_id:
            raise ValueError("ZDEX purchase quote source and pool buckets must differ")
        if self.zdex_pool_bucket_id == self.burn_bucket_id:
            raise ValueError("ZDEX purchase pool and burn buckets must differ")
        for field_name in (
            "quote_amount_in_atoms",
            "purchased_zdex_atoms",
            "quote_source_pre_atoms",
            "quote_source_post_atoms",
            "quote_pool_pre_atoms",
            "quote_pool_post_atoms",
            "zdex_pool_pre_atoms",
            "zdex_pool_post_atoms",
            "burn_bucket_pre_atoms",
            "burn_bucket_post_atoms",
            "quote_owned_atoms",
            "quote_supply_atoms",
            "zdex_owned_atoms",
            "zdex_supply_atoms",
        ):
            _require_atoms_u128(getattr(self, field_name), name=f"ZDEX purchase {field_name}")
        if self.quote_amount_in_atoms == 0 or self.purchased_zdex_atoms == 0:
            raise ValueError("ZDEX purchase amounts must be positive")
        if (
            self.quote_amount_in_atoms > MAX_DELTA_ATOMS_V1
            or self.purchased_zdex_atoms > MAX_DELTA_ATOMS_V1
        ):
            raise ValueError("ZDEX purchase amounts must fit signed effect atoms")
        if self.quote_source_post_atoms + self.quote_amount_in_atoms != self.quote_source_pre_atoms:
            raise ValueError("ZDEX purchase quote source projection is inconsistent")
        if self.quote_pool_pre_atoms + self.quote_amount_in_atoms != self.quote_pool_post_atoms:
            raise ValueError("ZDEX purchase quote pool projection is inconsistent")
        if self.zdex_pool_post_atoms + self.purchased_zdex_atoms != self.zdex_pool_pre_atoms:
            raise ValueError("ZDEX purchase output pool projection is inconsistent")
        if self.burn_bucket_pre_atoms != 0 or self.burn_bucket_post_atoms != self.purchased_zdex_atoms:
            raise ValueError("ZDEX purchase transient burn bucket projection is inconsistent")
        if self.quote_source_pre_atoms + self.quote_pool_pre_atoms > self.quote_owned_atoms:
            raise ValueError("ZDEX purchase quote buckets exceed owned amount")
        if self.zdex_pool_pre_atoms + self.burn_bucket_pre_atoms > self.zdex_owned_atoms:
            raise ValueError("ZDEX purchase output buckets exceed owned amount")

    @property
    def journal_root(self) -> str:
        return hash_global_v1("zdex-amm-purchase-journal-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "spot_module_release_id": self.spot_module_release_id,
            "issue_burn_policy_root": self.issue_burn_policy_root,
            "buyback_budget_occurrence_root": self.buyback_budget_occurrence_root,
            "quote_asset_id": self.quote_asset_id,
            "zdex_asset_id": self.zdex_asset_id,
            "quote_source_bucket_id": self.quote_source_bucket_id,
            "quote_pool_bucket_id": self.quote_pool_bucket_id,
            "zdex_pool_bucket_id": self.zdex_pool_bucket_id,
            "burn_bucket_id": self.burn_bucket_id,
            "quote_amount_in_atoms": self.quote_amount_in_atoms,
            "purchased_zdex_atoms": self.purchased_zdex_atoms,
            "quote_source_pre_atoms": self.quote_source_pre_atoms,
            "quote_source_post_atoms": self.quote_source_post_atoms,
            "quote_pool_pre_atoms": self.quote_pool_pre_atoms,
            "quote_pool_post_atoms": self.quote_pool_post_atoms,
            "zdex_pool_pre_atoms": self.zdex_pool_pre_atoms,
            "zdex_pool_post_atoms": self.zdex_pool_post_atoms,
            "burn_bucket_pre_atoms": self.burn_bucket_pre_atoms,
            "burn_bucket_post_atoms": self.burn_bucket_post_atoms,
            "quote_owned_atoms": self.quote_owned_atoms,
            "quote_supply_atoms": self.quote_supply_atoms,
            "zdex_owned_atoms": self.zdex_owned_atoms,
            "zdex_supply_atoms": self.zdex_supply_atoms,
            "pre_spot_lane_root": self.pre_spot_lane_root,
            "post_spot_lane_root": self.post_spot_lane_root,
            "effect_plan_root": self.effect_plan_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXBurnJournalV1:
    """Public output of a checked route-bound ZDEX supply burn."""

    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    route_release_id: str
    command_occurrence_id: str
    tokenomics_module_release_id: str
    issue_burn_policy_root: str
    buyback_budget_occurrence_root: str
    authorized_quote_input_atoms: int
    purchase_occurrence_root: str
    zdex_asset_id: str
    burn_bucket_id: str
    burned_zdex_atoms: int
    burn_bucket_pre_atoms: int
    burn_bucket_post_atoms: int
    zdex_owned_pre_atoms: int
    zdex_owned_post_atoms: int
    zdex_supply_pre_atoms: int
    zdex_supply_post_atoms: int
    pre_tokenomics_lane_root: str
    post_tokenomics_lane_root: str
    effect_plan_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="ZDEX burn chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "tokenomics_module_release_id",
            "issue_burn_policy_root",
            "buyback_budget_occurrence_root",
            "purchase_occurrence_root",
            "zdex_asset_id",
            "pre_tokenomics_lane_root",
            "post_tokenomics_lane_root",
            "effect_plan_root",
        ):
            _require_root(getattr(self, field_name), name=f"ZDEX burn {field_name}")
        _require_nonnegative_int(self.writer_epoch, name="ZDEX burn writer epoch")
        _require_token(self.burn_bucket_id, name="ZDEX burn bucket id")
        for field_name in (
            "burned_zdex_atoms",
            "burn_bucket_pre_atoms",
            "burn_bucket_post_atoms",
            "authorized_quote_input_atoms",
            "zdex_owned_pre_atoms",
            "zdex_owned_post_atoms",
            "zdex_supply_pre_atoms",
            "zdex_supply_post_atoms",
        ):
            _require_atoms_u128(getattr(self, field_name), name=f"ZDEX burn {field_name}")
        if self.burned_zdex_atoms == 0:
            raise ValueError("ZDEX burn amount must be positive")
        if self.authorized_quote_input_atoms == 0:
            raise ValueError("ZDEX authorized quote input must be positive")
        if (
            self.authorized_quote_input_atoms > MAX_DELTA_ATOMS_V1
            or self.burned_zdex_atoms > MAX_DELTA_ATOMS_V1
        ):
            raise ValueError("ZDEX burn route amounts must fit signed effect atoms")
        if self.zdex_owned_post_atoms + self.burned_zdex_atoms != self.zdex_owned_pre_atoms:
            raise ValueError("ZDEX burn owned amount projection is inconsistent")
        if self.zdex_supply_post_atoms + self.burned_zdex_atoms != self.zdex_supply_pre_atoms:
            raise ValueError("ZDEX burn supply projection is inconsistent")
        if self.burn_bucket_pre_atoms != self.burned_zdex_atoms or self.burn_bucket_post_atoms != 0:
            raise ValueError("ZDEX burn transient bucket projection is inconsistent")

    @property
    def journal_root(self) -> str:
        return hash_global_v1("zdex-authorized-burn-journal-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "issue_burn_policy_root": self.issue_burn_policy_root,
            "buyback_budget_occurrence_root": self.buyback_budget_occurrence_root,
            "authorized_quote_input_atoms": self.authorized_quote_input_atoms,
            "purchase_occurrence_root": self.purchase_occurrence_root,
            "zdex_asset_id": self.zdex_asset_id,
            "burn_bucket_id": self.burn_bucket_id,
            "burned_zdex_atoms": self.burned_zdex_atoms,
            "burn_bucket_pre_atoms": self.burn_bucket_pre_atoms,
            "burn_bucket_post_atoms": self.burn_bucket_post_atoms,
            "zdex_owned_pre_atoms": self.zdex_owned_pre_atoms,
            "zdex_owned_post_atoms": self.zdex_owned_post_atoms,
            "zdex_supply_pre_atoms": self.zdex_supply_pre_atoms,
            "zdex_supply_post_atoms": self.zdex_supply_post_atoms,
            "pre_tokenomics_lane_root": self.pre_tokenomics_lane_root,
            "post_tokenomics_lane_root": self.post_tokenomics_lane_root,
            "effect_plan_root": self.effect_plan_root,
        }


__all__ = [
    "AMM_POOL_CUSTODY_DOMAIN_V1",
    "AMM_PURCHASE_OUTPUT_ROLE_V1",
    "PROTOCOL_BURN_CUSTODY_DOMAIN_V1",
    "PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1",
    "PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1",
    "PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1",
    "ZDEXAMMPurchaseJournalV1",
    "ZDEXBurnJournalV1",
    "ZDEXPurchaseBurnRouteRejectCodeV1",
    "ZDEX_BURN_INPUT_ROLE_V1",
    "ZDEX_SUPPLY_PRINCIPAL_V1",
    "ZERO_ROOT_V1",
    "zdex_amm_purchase_port_schema_root_v1",
    "zdex_burn_port_schema_root_v1",
]
