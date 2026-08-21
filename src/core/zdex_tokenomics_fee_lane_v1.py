"""Closed private port for embedding fee allocation in the tokenomics lane.

The legacy V1 occurrence field names ``pre_lane_root`` and ``post_lane_root``
commit one fee-asset substate. This module preserves those canonical bytes and
prevents the substate roots from being presented as complete lane roots.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    LaneIdV1,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .zdex_fee_allocation_types_v1 import (
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationPolicyV1,
)
from .zdex_fee_allocation_v1 import (
    fee_allocation_effects_v1,
    transition_zdex_fee_allocation_v1,
)
from .zdex_tokenomics_lane_v1 import (
    zdex_tokenomics_complete_lane_obligation_root_v1,
)

ZDEX_TOKENOMICS_FEE_ALLOCATION_PRIVATE_PORT_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-fee-allocation-private-port/v1"
)
ZDEX_TOKENOMICS_FEE_ALLOCATION_COORDINATOR_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-fee-allocation-coordinator/v1"
)


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsFeeAllocationPrivatePortV1:
    module_release_id: str
    command_occurrence_id: str
    allocation_occurrence_root: str
    pre_fee_substate_root: str
    post_fee_substate_root: str
    module_effect_plan_root: str
    terminal_obligations_root: str

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        for field_name in (
            "module_release_id",
            "command_occurrence_id",
            "allocation_occurrence_root",
            "pre_fee_substate_root",
            "post_fee_substate_root",
            "module_effect_plan_root",
            "terminal_obligations_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"ZDEX tokenomics fee port {field_name}",
            )
        if (
            self.terminal_obligations_root
            != zdex_tokenomics_complete_lane_obligation_root_v1()
        ):
            raise ValueError("ZDEX tokenomics fee port obligation is unsupported")

    @property
    def port_root(self) -> str:
        self.validate()
        return hash_global_v1(
            "zdex-tokenomics-fee-allocation-private-port-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_TOKENOMICS_FEE_ALLOCATION_PRIVATE_PORT_SCHEMA_V1,
            "module_release_id": self.module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "allocation_occurrence_root": self.allocation_occurrence_root,
            "pre_fee_substate_root": self.pre_fee_substate_root,
            "post_fee_substate_root": self.post_fee_substate_root,
            "module_effect_plan_root": self.module_effect_plan_root,
            "terminal_obligations_root": self.terminal_obligations_root,
        }


def _require_exact_allocation(
    allocation: object,
    policy: object,
) -> ZDEXFeeAllocationAcceptedV1:
    if type(allocation) is not ZDEXFeeAllocationAcceptedV1:
        raise TypeError("ZDEX tokenomics fee port requires an accepted allocation")
    typed = allocation
    if type(policy) is not ZDEXFeeAllocationPolicyV1:
        raise TypeError("ZDEX tokenomics fee port requires an exact policy")
    typed_policy = policy
    typed.pre_state.validate()
    typed.post_state.validate()
    typed.effects.validate()
    typed.occurrence.validate()
    typed_policy.validate()
    expected = fee_allocation_effects_v1(
        typed.occurrence,
        typed.pre_state,
        typed.post_state,
        typed_policy,
    )
    if typed.effects != expected:
        raise ValueError("ZDEX tokenomics fee allocation effects are not canonical")
    occurrence = typed.occurrence
    recomputed = transition_zdex_fee_allocation_v1(
        ZDEXFeeAllocationContextV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            writer_epoch=occurrence.writer_epoch,
            allocation_route_release_id=occurrence.allocation_route_release_id,
            authorized_buyback_route_release_id=(
                occurrence.authorized_buyback_route_release_id
            ),
            tokenomics_module_release_id=occurrence.tokenomics_module_release_id,
            command_occurrence_id=occurrence.command_occurrence_id,
            policy_root=occurrence.policy_root,
        ),
        typed.pre_state,
        typed_policy,
        ZDEXFeeAllocationCommandV1(occurrence.fee_charged_atoms),
    )
    if recomputed != typed:
        raise ValueError("ZDEX tokenomics fee allocation does not refine the policy")
    return typed


def build_zdex_tokenomics_fee_allocation_private_port_v1(
    allocation: ZDEXFeeAllocationAcceptedV1,
    policy: ZDEXFeeAllocationPolicyV1,
) -> ZDEXTokenomicsFeeAllocationPrivatePortV1:
    typed = _require_exact_allocation(allocation, policy)
    occurrence = typed.occurrence
    return ZDEXTokenomicsFeeAllocationPrivatePortV1(
        module_release_id=occurrence.tokenomics_module_release_id,
        command_occurrence_id=occurrence.command_occurrence_id,
        allocation_occurrence_root=occurrence.occurrence_root,
        pre_fee_substate_root=occurrence.pre_lane_root,
        post_fee_substate_root=occurrence.post_lane_root,
        module_effect_plan_root=typed.effects.effect_plan_root,
        terminal_obligations_root=(
            zdex_tokenomics_complete_lane_obligation_root_v1()
        ),
    )


def _module_receipt_root_v1(
    allocation: ZDEXFeeAllocationAcceptedV1,
    private_port: ZDEXTokenomicsFeeAllocationPrivatePortV1,
) -> str:
    occurrence = allocation.occurrence
    return hash_global_v1(
        "zdex-tokenomics-fee-allocation-lane-module-receipt-v1",
        {
            "allocation_occurrence_root": occurrence.occurrence_root,
            "pre_fee_substate_root": occurrence.pre_lane_root,
            "post_fee_substate_root": occurrence.post_lane_root,
            "effect_plan_root": allocation.effects.effect_plan_root,
            "private_port_root": private_port.port_root,
            "terminal_obligations_root": private_port.terminal_obligations_root,
        },
    )


def build_zdex_tokenomics_fee_allocation_module_journal_v1(
    allocation: ZDEXFeeAllocationAcceptedV1,
    policy: ZDEXFeeAllocationPolicyV1,
    private_port: ZDEXTokenomicsFeeAllocationPrivatePortV1,
) -> LaneModuleTransitionJournalV1:
    typed = _require_exact_allocation(allocation, policy)
    if type(private_port) is not ZDEXTokenomicsFeeAllocationPrivatePortV1:
        raise TypeError("ZDEX fee module journal requires an exact private port")
    if private_port != build_zdex_tokenomics_fee_allocation_private_port_v1(
        typed,
        policy,
    ):
        raise ValueError("ZDEX fee module journal private port does not match")
    occurrence = typed.occurrence
    return LaneModuleTransitionJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=occurrence.writer_epoch,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        module_release_id=occurrence.tokenomics_module_release_id,
        command_occurrence_id=occurrence.command_occurrence_id,
        pre_lane_root=ZERO_ROOT_V1,
        post_lane_root=ZERO_ROOT_V1,
        effect_plan_root=typed.effects.effect_plan_root,
        private_port_root=private_port.port_root,
        receipt_root=_module_receipt_root_v1(typed, private_port),
        terminal_obligations_root=private_port.terminal_obligations_root,
    )


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsFeeAllocationCoordinatorContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    coordinator_release_id: str
    allocation_route_release_id: str
    authorized_buyback_route_release_id: str
    tokenomics_module_release_id: str
    command_occurrence_id: str
    policy_root: str

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_token(self.chain_id, name="ZDEX tokenomics fee coordinator chain id")
        _require_nonnegative_int(
            self.writer_epoch,
            name="ZDEX tokenomics fee coordinator writer epoch",
        )
        for field_name in (
            "deployment_root",
            "profile_root",
            "coordinator_release_id",
            "allocation_route_release_id",
            "authorized_buyback_route_release_id",
            "tokenomics_module_release_id",
            "command_occurrence_id",
            "policy_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"ZDEX tokenomics fee coordinator {field_name}",
            )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_TOKENOMICS_FEE_ALLOCATION_COORDINATOR_SCHEMA_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "coordinator_release_id": self.coordinator_release_id,
            "allocation_route_release_id": self.allocation_route_release_id,
            "authorized_buyback_route_release_id": (
                self.authorized_buyback_route_release_id
            ),
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "policy_root": self.policy_root,
        }


__all__ = [
    "ZDEXTokenomicsFeeAllocationCoordinatorContextV1",
    "ZDEXTokenomicsFeeAllocationPrivatePortV1",
    "build_zdex_tokenomics_fee_allocation_module_journal_v1",
    "build_zdex_tokenomics_fee_allocation_private_port_v1",
]
