"""Closed tokenomics-lane values for the unmounted ZDEX burn coordinator.

These values define an exact component envelope and private port. They
authenticate no receipt and grant no settlement or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_economic_proof_v1 import (
    LaneCompositionJournalV1,
    LaneModuleTransitionJournalV1,
)
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    ZERO_ROOT_V1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .zdex_fee_allocation_types_v1 import ZDEXFeeStateV1
from .zdex_hyperdeflation_types_v1 import ZDEXSupplyStateV1
from .zdex_purchase_burn_effects_v1 import burn_effects_v1
from .zdex_purchase_burn_route_types_v1 import ZDEXBurnJournalV1

ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-lane-state/v1"
)
ZDEX_TOKENOMICS_BURN_PRIVATE_PORT_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-burn-private-port/v1"
)
ZDEX_TOKENOMICS_BURN_COORDINATOR_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-burn-coordinator/v1"
)
MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1: Final = 64


def zdex_tokenomics_complete_lane_obligation_root_v1() -> str:
    return hash_global_v1(
        "zdex-tokenomics-coordinator-obligation-v1",
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "lane_id": LaneIdV1.ZDEX_TOKENOMICS,
            "requirement": "VERIFIED_COMPLETE_LANE_ROOT",
        },
    )


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsLaneStateV1:
    """Exact closed component envelope for the current tokenomics lane."""

    supply_state: ZDEXSupplyStateV1
    fee_allocation_states: tuple[ZDEXFeeStateV1, ...]
    staking_state_root: str
    host_claims_state_root: str
    treasury_claims_state_root: str
    proof_rewards_state_root: str
    cover_reserve_state_root: str
    lp_rebates_state_root: str

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.supply_state) is not ZDEXSupplyStateV1:
            raise TypeError("ZDEX tokenomics supply state must be exact typed data")
        self.supply_state.validate()
        if type(self.fee_allocation_states) is not tuple:
            raise TypeError("ZDEX tokenomics fee states must be an exact tuple")
        if not 1 <= len(self.fee_allocation_states) <= MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1:
            raise ValueError("ZDEX tokenomics fee-state registry width is unsupported")
        if any(type(state) is not ZDEXFeeStateV1 for state in self.fee_allocation_states):
            raise TypeError("ZDEX tokenomics fee states must be exact typed data")
        for state in self.fee_allocation_states:
            state.validate()
        fee_asset_ids = tuple(state.fee_asset_id for state in self.fee_allocation_states)
        if fee_asset_ids != tuple(sorted(fee_asset_ids)) or len(set(fee_asset_ids)) != len(
            fee_asset_ids
        ):
            raise ValueError("ZDEX tokenomics fee states must be uniquely asset-ordered")
        for field_name in (
            "staking_state_root",
            "host_claims_state_root",
            "treasury_claims_state_root",
            "proof_rewards_state_root",
            "cover_reserve_state_root",
            "lp_rebates_state_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"ZDEX tokenomics {field_name}",
            )
        if self.supply_state.asset_id in fee_asset_ids:
            raise ValueError("ZDEX supply asset cannot also be a fee asset")

    @property
    def state_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-tokenomics-lane-state-v1", self.to_canonical())

    def unrelated_to_burn_matches(self, other: ZDEXTokenomicsLaneStateV1) -> bool:
        return (
            type(other) is ZDEXTokenomicsLaneStateV1
            and self.fee_allocation_states == other.fee_allocation_states
            and self.staking_state_root == other.staking_state_root
            and self.host_claims_state_root == other.host_claims_state_root
            and self.treasury_claims_state_root == other.treasury_claims_state_root
            and self.proof_rewards_state_root == other.proof_rewards_state_root
            and self.cover_reserve_state_root == other.cover_reserve_state_root
            and self.lp_rebates_state_root == other.lp_rebates_state_root
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1,
            "supply_state": self.supply_state,
            "fee_allocation_states": self.fee_allocation_states,
            "staking_state_root": self.staking_state_root,
            "host_claims_state_root": self.host_claims_state_root,
            "treasury_claims_state_root": self.treasury_claims_state_root,
            "proof_rewards_state_root": self.proof_rewards_state_root,
            "cover_reserve_state_root": self.cover_reserve_state_root,
            "lp_rebates_state_root": self.lp_rebates_state_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBurnPrivatePortV1:
    module_release_id: str
    command_occurrence_id: str
    burn_journal_root: str
    pre_burn_substate_root: str
    post_burn_substate_root: str
    module_effect_plan_root: str
    terminal_obligations_root: str

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        for field_name in (
            "module_release_id",
            "command_occurrence_id",
            "burn_journal_root",
            "pre_burn_substate_root",
            "post_burn_substate_root",
            "module_effect_plan_root",
            "terminal_obligations_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"ZDEX tokenomics burn port {field_name}",
            )
        if (
            self.terminal_obligations_root
            != zdex_tokenomics_complete_lane_obligation_root_v1()
        ):
            raise ValueError("ZDEX tokenomics burn port obligation is unsupported")

    @property
    def port_root(self) -> str:
        self.validate()
        return hash_global_v1(
            "zdex-tokenomics-burn-private-port-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_TOKENOMICS_BURN_PRIVATE_PORT_SCHEMA_V1,
            "module_release_id": self.module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "burn_journal_root": self.burn_journal_root,
            "pre_burn_substate_root": self.pre_burn_substate_root,
            "post_burn_substate_root": self.post_burn_substate_root,
            "module_effect_plan_root": self.module_effect_plan_root,
            "terminal_obligations_root": self.terminal_obligations_root,
        }


def build_zdex_tokenomics_burn_private_port_v1(
    journal: ZDEXBurnJournalV1,
    effects: GlobalEconomicEffectPlanV1,
) -> ZDEXTokenomicsBurnPrivatePortV1:
    if type(journal) is not ZDEXBurnJournalV1:
        raise TypeError("ZDEX tokenomics burn port requires an exact burn journal")
    if type(effects) is not GlobalEconomicEffectPlanV1:
        raise TypeError("ZDEX tokenomics burn port requires an exact effect plan")
    journal.validate()
    if effects != burn_effects_v1(journal):
        raise ValueError("ZDEX tokenomics burn port effects do not match the journal")
    return ZDEXTokenomicsBurnPrivatePortV1(
        module_release_id=journal.tokenomics_module_release_id,
        command_occurrence_id=journal.command_occurrence_id,
        burn_journal_root=journal.journal_root,
        pre_burn_substate_root=journal.pre_tokenomics_burn_substate_root,
        post_burn_substate_root=journal.post_tokenomics_burn_substate_root,
        module_effect_plan_root=effects.effect_plan_root,
        terminal_obligations_root=(
            zdex_tokenomics_complete_lane_obligation_root_v1()
        ),
    )


def _zdex_tokenomics_burn_module_receipt_root_v1(
    journal: ZDEXBurnJournalV1,
    effects: GlobalEconomicEffectPlanV1,
    private_port: ZDEXTokenomicsBurnPrivatePortV1,
) -> str:
    return hash_global_v1(
        "zdex-tokenomics-burn-lane-module-receipt-v1",
        {
            "burn_journal_root": journal.journal_root,
            "pre_burn_substate_root": journal.pre_tokenomics_burn_substate_root,
            "post_burn_substate_root": journal.post_tokenomics_burn_substate_root,
            "effect_plan_root": effects.effect_plan_root,
            "private_port_root": private_port.port_root,
            "terminal_obligations_root": private_port.terminal_obligations_root,
        },
    )


def build_zdex_tokenomics_burn_module_journal_v1(
    journal: ZDEXBurnJournalV1,
    effects: GlobalEconomicEffectPlanV1,
    private_port: ZDEXTokenomicsBurnPrivatePortV1,
) -> LaneModuleTransitionJournalV1:
    """Build the canonical module journal consumed by the lane coordinator."""

    if type(journal) is not ZDEXBurnJournalV1:
        raise TypeError("ZDEX burn module journal requires an exact burn journal")
    if type(effects) is not GlobalEconomicEffectPlanV1:
        raise TypeError("ZDEX burn module journal requires an exact effect plan")
    if type(private_port) is not ZDEXTokenomicsBurnPrivatePortV1:
        raise TypeError("ZDEX burn module journal requires an exact private port")
    journal.validate()
    effects.validate()
    private_port.validate()
    if effects != burn_effects_v1(journal):
        raise ValueError("ZDEX burn module journal effects do not match the burn")
    if private_port != build_zdex_tokenomics_burn_private_port_v1(journal, effects):
        raise ValueError("ZDEX burn module journal private port does not match the burn")
    return LaneModuleTransitionJournalV1(
        chain_id=journal.chain_id,
        deployment_root=journal.deployment_root,
        profile_root=journal.profile_root,
        writer_epoch=journal.writer_epoch,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        module_release_id=journal.tokenomics_module_release_id,
        command_occurrence_id=journal.command_occurrence_id,
        pre_lane_root=ZERO_ROOT_V1,
        post_lane_root=ZERO_ROOT_V1,
        effect_plan_root=effects.effect_plan_root,
        private_port_root=private_port.port_root,
        receipt_root=_zdex_tokenomics_burn_module_receipt_root_v1(
            journal,
            effects,
            private_port,
        ),
        terminal_obligations_root=private_port.terminal_obligations_root,
    )


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBurnCoordinatorContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    coordinator_release_id: str
    route_release_id: str
    tokenomics_module_release_id: str
    command_occurrence_id: str
    issue_burn_policy_root: str

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_token(self.chain_id, name="ZDEX tokenomics coordinator chain id")
        _require_nonnegative_int(
            self.writer_epoch,
            name="ZDEX tokenomics coordinator writer epoch",
        )
        for field_name in (
            "deployment_root",
            "profile_root",
            "coordinator_release_id",
            "route_release_id",
            "tokenomics_module_release_id",
            "command_occurrence_id",
            "issue_burn_policy_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"ZDEX tokenomics coordinator {field_name}",
            )


class ZDEXTokenomicsLaneCoordinatorRejectCodeV1(str, Enum):
    CHAIN_MISMATCH = "CHAIN_MISMATCH"
    DEPLOYMENT_MISMATCH = "DEPLOYMENT_MISMATCH"
    PROFILE_MISMATCH = "PROFILE_MISMATCH"
    WRITER_EPOCH_MISMATCH = "WRITER_EPOCH_MISMATCH"
    WRONG_LANE = "WRONG_LANE"
    MODULE_RELEASE_MISMATCH = "MODULE_RELEASE_MISMATCH"
    ROUTE_RELEASE_MISMATCH = "ROUTE_RELEASE_MISMATCH"
    OCCURRENCE_MISMATCH = "OCCURRENCE_MISMATCH"
    PARTIAL_LANE_ROOT_CLAIM = "PARTIAL_LANE_ROOT_CLAIM"
    PRIVATE_PORT_MISMATCH = "PRIVATE_PORT_MISMATCH"
    MODULE_RECEIPT_MISMATCH = "MODULE_RECEIPT_MISMATCH"
    TERMINAL_OBLIGATION_MISMATCH = "TERMINAL_OBLIGATION_MISMATCH"
    BURN_JOURNAL_MISMATCH = "BURN_JOURNAL_MISMATCH"
    EFFECT_PLAN_MISMATCH = "EFFECT_PLAN_MISMATCH"
    PRE_SUBSTATE_MISMATCH = "PRE_SUBSTATE_MISMATCH"
    POST_SUBSTATE_MISMATCH = "POST_SUBSTATE_MISMATCH"
    UNRELATED_STATE_MUTATION = "UNRELATED_STATE_MUTATION"
    STATE_EFFECT_MISMATCH = "STATE_EFFECT_MISMATCH"


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsLaneCompositionAcceptedV1:
    post_state: ZDEXTokenomicsLaneStateV1
    effects: GlobalEconomicEffectPlanV1
    lane_journal: LaneCompositionJournalV1

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.post_state) is not ZDEXTokenomicsLaneStateV1:
            raise TypeError("ZDEX tokenomics accepted post-state must be exact")
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("ZDEX tokenomics accepted effects must be exact")
        if type(self.lane_journal) is not LaneCompositionJournalV1:
            raise TypeError("ZDEX tokenomics accepted lane journal must be exact")
        self.post_state.validate()
        self.effects.validate()
        self.lane_journal.validate()
        _require_root(
            self.lane_journal.pre_lane_root,
            name="ZDEX tokenomics accepted pre-lane root",
        )
        _require_root(
            self.lane_journal.post_lane_root,
            name="ZDEX tokenomics accepted post-lane root",
        )
        if (
            self.lane_journal.lane_id is not LaneIdV1.ZDEX_TOKENOMICS
            or self.lane_journal.post_lane_root != self.post_state.state_root
            or self.lane_journal.effect_plan_root != self.effects.effect_plan_root
            or self.lane_journal.terminal_obligations_root != ZERO_ROOT_V1
            or self.effects.lane_writes != (self.expected_lane_write,)
        ):
            raise ValueError("ZDEX tokenomics lane acceptance is inconsistent")

    @property
    def expected_lane_write(self) -> LaneWriteV1:
        return LaneWriteV1(
            LaneIdV1.ZDEX_TOKENOMICS,
            self.lane_journal.pre_lane_root,
            self.lane_journal.post_lane_root,
        )


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsLaneCompositionRejectedV1:
    code: ZDEXTokenomicsLaneCoordinatorRejectCodeV1
    pre_lane_root: str
    post_lane_root: str
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.code) is not ZDEXTokenomicsLaneCoordinatorRejectCodeV1:
            raise TypeError("ZDEX tokenomics coordinator reject code is not closed")
        _require_root(self.pre_lane_root, name="ZDEX tokenomics rejected pre-root")
        _require_root(self.post_lane_root, name="ZDEX tokenomics rejected post-root")
        self.effects.validate()
        if self.pre_lane_root != self.post_lane_root or not self.effects.is_empty:
            raise ValueError("ZDEX tokenomics rejection must be an exact no-op")


ZDEXTokenomicsLaneCompositionResultV1 = (
    ZDEXTokenomicsLaneCompositionAcceptedV1
    | ZDEXTokenomicsLaneCompositionRejectedV1
)

__all__ = [
    "MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1",
    "ZDEXTokenomicsBurnCoordinatorContextV1",
    "ZDEXTokenomicsBurnPrivatePortV1",
    "ZDEXTokenomicsLaneCompositionAcceptedV1",
    "ZDEXTokenomicsLaneCompositionRejectedV1",
    "ZDEXTokenomicsLaneCompositionResultV1",
    "ZDEXTokenomicsLaneCoordinatorRejectCodeV1",
    "ZDEXTokenomicsLaneStateV1",
    "build_zdex_tokenomics_burn_module_journal_v1",
    "build_zdex_tokenomics_burn_private_port_v1",
    "zdex_tokenomics_complete_lane_obligation_root_v1",
]
