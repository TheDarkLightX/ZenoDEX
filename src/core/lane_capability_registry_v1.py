"""Closed capability vocabulary for all GlobalSettlementABI V1 lanes.

This immutable registry gives each of the 103 normative M6 capabilities one
and only one stable lane owner.  It is the fail-closed vocabulary used to
measure lane transition coverage.  It does not implement a capability or
select unresolved economic policy.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    LaneIdV1,
    _require_token,
    hash_global_v1,
)

LANE_CAPABILITY_REGISTRY_SCHEMA_V1: Final = "zenodex/lane-capability-registry/v1"

PERPS_MARGIN_REGISTERED_COMMAND_CAPABILITIES_V1: Final = (
    ("perps_margin_deposit", "margin_deposit"),
    ("perps_margin_withdraw", "margin_withdraw"),
)


class LaneCapabilityDispositionV1(str, Enum):
    REQUIRED_UNRESOLVED = "REQUIRED_UNRESOLVED"
    DISABLED_PENDING_COMPLETE_PROFILE = "DISABLED_PENDING_COMPLETE_PROFILE"


@dataclass(frozen=True, slots=True)
class LaneCapabilitySetV1:
    lane_id: LaneIdV1
    disposition: LaneCapabilityDispositionV1
    capability_ids: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("lane capability lane id must be exact")
        if type(self.disposition) is not LaneCapabilityDispositionV1:
            raise TypeError("lane capability disposition must be exact")
        if type(self.capability_ids) is not tuple or not self.capability_ids:
            raise ValueError("lane capability ids must be a nonempty exact tuple")
        for capability_id in self.capability_ids:
            if type(capability_id) is not str:
                raise TypeError("lane capability id must be exact text")
            _require_token(capability_id, name="lane capability id")
        if len(self.capability_ids) != len(set(self.capability_ids)):
            raise ValueError("lane capability ids must be unique within a lane")

    def to_canonical(self) -> dict[str, object]:
        return {
            "capability_ids": self.capability_ids,
            "disposition": self.disposition,
            "lane_id": self.lane_id,
        }


@dataclass(frozen=True, slots=True)
class LaneCapabilityResolutionV1:
    lane: LaneCapabilitySetV1
    capability_id: str

    def __post_init__(self) -> None:
        if type(self.lane) is not LaneCapabilitySetV1:
            raise TypeError("lane capability resolution lane must be exact")
        if type(self.capability_id) is not str:
            raise TypeError("lane capability resolution id must be exact text")
        if self.capability_id not in self.lane.capability_ids:
            raise ValueError("lane capability resolution is outside its lane")


def _row(
    lane_id: LaneIdV1,
    capability_ids: tuple[str, ...],
    disposition: LaneCapabilityDispositionV1 = LaneCapabilityDispositionV1.REQUIRED_UNRESOLVED,
) -> LaneCapabilitySetV1:
    return LaneCapabilitySetV1(lane_id, disposition, capability_ids)


LANE_CAPABILITY_REGISTRY_V1: Final = (
    _row(
        LaneIdV1.ASSET_TRANSFER,
        (
            "account_lifecycle",
            "native_asset_accounting",
            "generic_transfer",
            "managed_issue",
            "managed_burn",
            "transaction_fee",
            "tau_originated_asset_registration",
        ),
    ),
    _row(
        LaneIdV1.SPOT_LIQUIDITY,
        (
            "pool_create",
            "exact_in_swap",
            "exact_out_swap",
            "governed_route",
            "atomic_batch",
            "lp_issue",
            "lp_burn",
            "pool_close",
            "fee_allocation",
            "residue_terminal_disposition",
        ),
    ),
    _row(
        LaneIdV1.FARM_INCENTIVES,
        (
            "lp_stake",
            "stake_activation",
            "emission_accrual",
            "emission_claim",
            "farm_cancellation",
            "farm_terminal_drain",
        ),
    ),
    _row(
        LaneIdV1.ZDEX_TOKENOMICS,
        (
            "fee_routing",
            "staking_claim",
            "host_compensation_claim",
            "treasury_claim",
            "reserve_lifecycle",
            "atomic_purchase_and_burn",
            "retained_supply_hyperdeflation",
        ),
    ),
    _row(
        LaneIdV1.ZUSD_MONETARY,
        (
            "vault_open",
            "collateral_deposit",
            "collateral_withdraw",
            "zusd_mint",
            "zusd_repay",
            "vault_owner_close",
            "multi_vault_redemption",
            "stability_pool_deposit",
            "stability_pool_withdraw",
            "stability_pool_claim",
            "liquidation",
            "recovery_mode",
            "all_claims_terminal_drain",
        ),
    ),
    _row(
        LaneIdV1.PERPS_MARKET,
        (
            "margin_deposit",
            "margin_withdraw",
            "position_open",
            "position_adjust",
            "funding_accrual",
            "fee_allocation",
            "liquidation",
            "insurance_reserve",
            "auto_deleveraging",
            "bankruptcy_resolution",
            "terminal_closeout",
        ),
    ),
    _row(
        LaneIdV1.ORACLE_MARKET,
        (
            "query_create",
            "tip_escrow",
            "reporter_bond",
            "report_submit",
            "report_finality",
            "reporter_reward",
            "report_dispute",
            "reward_clawback",
            "reporter_slash",
            "oracle_terminal_drain",
        ),
    ),
    _row(
        LaneIdV1.SEALED_AUCTION,
        (
            "bid_commitment",
            "bond_accounting_location",
            "bid_reveal",
            "deterministic_clearing",
            "payment_settlement",
            "inventory_settlement",
            "refund",
            "slash",
            "auction_cancel",
            "auction_expiry",
        ),
    ),
    _row(
        LaneIdV1.STRATEGY_ESCROW,
        (
            "value_reservation",
            "strategy_activation",
            "strategy_trigger",
            "strategy_replace",
            "strategy_cancel",
            "strategy_expiry",
            "strategy_recovery",
        ),
    ),
    _row(
        LaneIdV1.PROOF_REWARDS,
        (
            "reward_reserve",
            "verified_result_binding",
            "claimant_binding",
            "claim_nullifier",
            "reward_payout",
            "task_terminal_state",
        ),
    ),
    _row(
        LaneIdV1.EXTERNAL_CUSTODY,
        (
            "registered_external_lock",
            "registered_external_burn",
            "registered_external_release",
            "registered_external_mint",
            "external_finality",
            "external_timeout",
            "external_refund",
            "outbox_acknowledgment",
            "destination_idempotency",
        ),
        LaneCapabilityDispositionV1.DISABLED_PENDING_COMPLETE_PROFILE,
    ),
    _row(
        LaneIdV1.GOVERNANCE_MIGRATION,
        (
            "asset_registry_change",
            "parameter_change",
            "release_activation",
            "treasury_action",
            "schema_migration",
            "writer_epoch_rotation",
            "autonomous_governance_command_submission",
        ),
    ),
)


def _validate_registry_v1() -> None:
    if tuple(row.lane_id for row in LANE_CAPABILITY_REGISTRY_V1) != ALL_LANE_IDS_V1:
        raise ValueError("lane capability registry must cover the canonical lanes exactly")
    if sum(len(row.capability_ids) for row in LANE_CAPABILITY_REGISTRY_V1) != 103:
        raise ValueError("lane capability registry must contain exactly 103 capabilities")
    disabled = tuple(
        row.lane_id
        for row in LANE_CAPABILITY_REGISTRY_V1
        if row.disposition
        is LaneCapabilityDispositionV1.DISABLED_PENDING_COMPLETE_PROFILE
    )
    if disabled != (LaneIdV1.EXTERNAL_CUSTODY,):
        raise ValueError("only the external lane may use the current disabled disposition")
    perps_commands = tuple(
        command_kind
        for command_kind, _capability_id in PERPS_MARGIN_REGISTERED_COMMAND_CAPABILITIES_V1
    )
    perps_capabilities = tuple(
        capability_id
        for _command_kind, capability_id in PERPS_MARGIN_REGISTERED_COMMAND_CAPABILITIES_V1
    )
    perps_lane = LANE_CAPABILITY_REGISTRY_V1[
        ALL_LANE_IDS_V1.index(LaneIdV1.PERPS_MARKET)
    ]
    if (
        len(perps_commands) != len(set(perps_commands))
        or len(perps_capabilities) != len(set(perps_capabilities))
        or any(
            capability_id not in perps_lane.capability_ids
            for capability_id in perps_capabilities
        )
    ):
        raise ValueError("perps margin command capability bindings must be exact")


def resolve_lane_capability_v1(
    lane_id: LaneIdV1,
    capability_id: str,
) -> LaneCapabilityResolutionV1:
    if type(lane_id) is not LaneIdV1:
        raise TypeError("lane capability lane id must be exact")
    if type(capability_id) is not str:
        raise TypeError("lane capability id must be exact text")
    _require_token(capability_id, name="lane capability id")
    _validate_registry_v1()
    lane = LANE_CAPABILITY_REGISTRY_V1[ALL_LANE_IDS_V1.index(lane_id)]
    if capability_id not in lane.capability_ids:
        raise ValueError("unknown lane capability")
    return LaneCapabilityResolutionV1(lane, capability_id)


def resolve_perps_margin_command_capability_v1(
    command_kind: str,
) -> LaneCapabilityResolutionV1:
    """Resolve only exact perps commands whose M6 capability meaning is fixed."""

    if type(command_kind) is not str:
        raise TypeError("perps margin command kind must be exact text")
    _require_token(command_kind, name="perps margin command kind")
    capability_id = dict(PERPS_MARGIN_REGISTERED_COMMAND_CAPABILITIES_V1).get(
        command_kind
    )
    if capability_id is None:
        raise ValueError("perps margin command lacks an exact capability binding")
    return resolve_lane_capability_v1(LaneIdV1.PERPS_MARKET, capability_id)


def lane_capability_registry_root_v1() -> str:
    _validate_registry_v1()
    return hash_global_v1(
        "lane-capability-registry-v1",
        {
            "schema": LANE_CAPABILITY_REGISTRY_SCHEMA_V1,
            "lanes": LANE_CAPABILITY_REGISTRY_V1,
        },
    )


_validate_registry_v1()


__all__ = [
    "LANE_CAPABILITY_REGISTRY_SCHEMA_V1",
    "LANE_CAPABILITY_REGISTRY_V1",
    "PERPS_MARGIN_REGISTERED_COMMAND_CAPABILITIES_V1",
    "LaneCapabilityDispositionV1",
    "LaneCapabilityResolutionV1",
    "LaneCapabilitySetV1",
    "lane_capability_registry_root_v1",
    "resolve_lane_capability_v1",
    "resolve_perps_margin_command_capability_v1",
]
