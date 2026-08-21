"""Embed one verified fee-allocation substate in the complete tokenomics lane."""

from __future__ import annotations

from dataclasses import dataclass

from .global_economic_proof_v1 import (
    LaneCompositionJournalV1,
    LaneModuleTransitionJournalV1,
)
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
)
from .zdex_fee_allocation_types_v1 import (
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationPolicyV1,
)
from .zdex_fee_allocation_v1 import fee_allocation_effects_v1
from .zdex_tokenomics_fee_lane_v1 import (
    ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    ZDEXTokenomicsFeeAllocationPrivatePortV1,
    build_zdex_tokenomics_fee_allocation_module_journal_v1,
)
from .zdex_tokenomics_lane_v1 import (
    ZDEXTokenomicsLaneCompositionAcceptedV1,
    ZDEXTokenomicsLaneCompositionRejectedV1,
    ZDEXTokenomicsLaneCompositionResultV1,
    ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    ZDEXTokenomicsLaneStateV1,
    zdex_tokenomics_complete_lane_obligation_root_v1,
)


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsFeeAllocationLaneCandidateV1:
    context: ZDEXTokenomicsFeeAllocationCoordinatorContextV1
    module_journal: LaneModuleTransitionJournalV1
    private_port: ZDEXTokenomicsFeeAllocationPrivatePortV1
    pre_state: ZDEXTokenomicsLaneStateV1
    post_state: ZDEXTokenomicsLaneStateV1
    allocation: ZDEXFeeAllocationAcceptedV1
    policy: ZDEXFeeAllocationPolicyV1

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        expected = (
            (self.context, ZDEXTokenomicsFeeAllocationCoordinatorContextV1, "context"),
            (self.module_journal, LaneModuleTransitionJournalV1, "module journal"),
            (self.private_port, ZDEXTokenomicsFeeAllocationPrivatePortV1, "private port"),
            (self.pre_state, ZDEXTokenomicsLaneStateV1, "pre-state"),
            (self.post_state, ZDEXTokenomicsLaneStateV1, "post-state"),
            (self.allocation, ZDEXFeeAllocationAcceptedV1, "allocation"),
            (self.policy, ZDEXFeeAllocationPolicyV1, "policy"),
        )
        for value, expected_type, name in expected:
            if type(value) is not expected_type:
                raise TypeError(
                    f"ZDEX tokenomics fee coordinator {name} must be exact typed data"
                )
        self.context.validate()
        self.module_journal.validate()
        self.private_port.validate()
        self.pre_state.validate()
        self.post_state.validate()
        self.allocation.validate()
        self.policy.validate()


def _reject(
    code: ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    pre_state: ZDEXTokenomicsLaneStateV1,
) -> ZDEXTokenomicsLaneCompositionRejectedV1:
    root = pre_state.state_root
    return ZDEXTokenomicsLaneCompositionRejectedV1(
        code,
        root,
        root,
        GlobalEconomicEffectPlanV1.empty(),
    )


def _context_reject(
    candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1,
) -> ZDEXTokenomicsLaneCoordinatorRejectCodeV1 | None:
    context = candidate.context
    module = candidate.module_journal
    occurrence = candidate.allocation.occurrence
    checks = (
        (module.chain_id != context.chain_id, "CHAIN_MISMATCH"),
        (module.deployment_root != context.deployment_root, "DEPLOYMENT_MISMATCH"),
        (module.profile_root != context.profile_root, "PROFILE_MISMATCH"),
        (module.writer_epoch != context.writer_epoch, "WRITER_EPOCH_MISMATCH"),
        (module.lane_id is not LaneIdV1.ZDEX_TOKENOMICS, "WRONG_LANE"),
        (
            module.module_release_id != context.tokenomics_module_release_id,
            "MODULE_RELEASE_MISMATCH",
        ),
        (
            module.command_occurrence_id != context.command_occurrence_id,
            "OCCURRENCE_MISMATCH",
        ),
        (
            module.pre_lane_root != ZERO_ROOT_V1
            or module.post_lane_root != ZERO_ROOT_V1,
            "PARTIAL_LANE_ROOT_CLAIM",
        ),
        (
            occurrence.allocation_route_release_id
            != context.allocation_route_release_id,
            "ROUTE_RELEASE_MISMATCH",
        ),
        (
            occurrence.authorized_buyback_route_release_id
            != context.authorized_buyback_route_release_id,
            "ROUTE_RELEASE_MISMATCH",
        ),
    )
    for failed, code in checks:
        if failed:
            return ZDEXTokenomicsLaneCoordinatorRejectCodeV1(code)
    return None


def _port_reject(
    candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1,
) -> ZDEXTokenomicsLaneCoordinatorRejectCodeV1 | None:
    module = candidate.module_journal
    port = candidate.private_port
    if (
        module.private_port_root != port.port_root
        or port.module_release_id != module.module_release_id
        or port.command_occurrence_id != module.command_occurrence_id
    ):
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PRIVATE_PORT_MISMATCH
    obligation = zdex_tokenomics_complete_lane_obligation_root_v1()
    if (
        module.terminal_obligations_root != obligation
        or port.terminal_obligations_root != obligation
    ):
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.TERMINAL_OBLIGATION_MISMATCH
    if not _occurrence_matches_context(candidate):
        return (
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1.FEE_ALLOCATION_OCCURRENCE_MISMATCH
        )
    return _effect_reject(candidate)


def _occurrence_matches_context(
    candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1,
) -> bool:
    context = candidate.context
    port = candidate.private_port
    occurrence = candidate.allocation.occurrence
    occurrence_bindings = (
        occurrence.chain_id == context.chain_id,
        occurrence.deployment_root == context.deployment_root,
        occurrence.profile_root == context.profile_root,
        occurrence.writer_epoch == context.writer_epoch,
        occurrence.tokenomics_module_release_id == context.tokenomics_module_release_id,
        occurrence.command_occurrence_id == context.command_occurrence_id,
        occurrence.policy_root == context.policy_root,
        port.allocation_occurrence_root == occurrence.occurrence_root,
        port.pre_fee_substate_root == occurrence.pre_lane_root,
        port.post_fee_substate_root == occurrence.post_lane_root,
    )
    return all(occurrence_bindings)


def _effect_reject(
    candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1,
) -> ZDEXTokenomicsLaneCoordinatorRejectCodeV1 | None:
    module = candidate.module_journal
    port = candidate.private_port
    allocation = candidate.allocation
    occurrence = allocation.occurrence
    try:
        expected_effects = fee_allocation_effects_v1(
            occurrence,
            allocation.pre_state,
            allocation.post_state,
            candidate.policy,
        )
    except (TypeError, ValueError):
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.EFFECT_PLAN_MISMATCH
    if (
        allocation.effects != expected_effects
        or module.effect_plan_root != expected_effects.effect_plan_root
        or port.module_effect_plan_root != expected_effects.effect_plan_root
    ):
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.EFFECT_PLAN_MISMATCH
    expected_module = build_zdex_tokenomics_fee_allocation_module_journal_v1(
        allocation,
        candidate.policy,
        port,
    )
    if module.receipt_root != expected_module.receipt_root:
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.MODULE_RECEIPT_MISMATCH
    return None


def _state_reject(
    candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1,
) -> ZDEXTokenomicsLaneCoordinatorRejectCodeV1 | None:
    allocation = candidate.allocation
    asset = allocation.occurrence.fee_asset_id
    pre_target = next(
        (state for state in candidate.pre_state.fee_allocation_states if state.fee_asset_id == asset),
        None,
    )
    post_target = next(
        (state for state in candidate.post_state.fee_allocation_states if state.fee_asset_id == asset),
        None,
    )
    if pre_target != allocation.pre_state:
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PRE_SUBSTATE_MISMATCH
    if post_target != allocation.post_state:
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.POST_SUBSTATE_MISMATCH
    pre_other = tuple(
        state for state in candidate.pre_state.fee_allocation_states if state.fee_asset_id != asset
    )
    post_other = tuple(
        state for state in candidate.post_state.fee_allocation_states if state.fee_asset_id != asset
    )
    if (
        pre_other != post_other
        or candidate.pre_state.supply_state != candidate.post_state.supply_state
        or candidate.pre_state.staking_state_root != candidate.post_state.staking_state_root
        or candidate.pre_state.host_claims_state_root
        != candidate.post_state.host_claims_state_root
        or candidate.pre_state.treasury_claims_state_root
        != candidate.post_state.treasury_claims_state_root
        or candidate.pre_state.proof_rewards_state_root
        != candidate.post_state.proof_rewards_state_root
        or candidate.pre_state.cover_reserve_state_root
        != candidate.post_state.cover_reserve_state_root
        or candidate.pre_state.lp_rebates_state_root
        != candidate.post_state.lp_rebates_state_root
    ):
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.UNRELATED_STATE_MUTATION
    return None


def _normalize_effects(
    candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1,
) -> GlobalEconomicEffectPlanV1:
    effects = candidate.allocation.effects
    return GlobalEconomicEffectPlanV1(
        effects.rows,
        effects.asset_conservation,
        effects.fee_conservation,
        (
            LaneWriteV1(
                LaneIdV1.ZDEX_TOKENOMICS,
                candidate.pre_state.state_root,
                candidate.post_state.state_root,
            ),
        ),
        effects.occurrence_consumptions,
        effects.external_outbox_enqueue,
    )


def compose_zdex_tokenomics_fee_allocation_lane_v1(
    candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1,
) -> ZDEXTokenomicsLaneCompositionResultV1:
    if type(candidate) is not ZDEXTokenomicsFeeAllocationLaneCandidateV1:
        raise TypeError("ZDEX tokenomics fee candidate must be exact typed data")
    candidate.validate()
    if code := _context_reject(candidate):
        return _reject(code, candidate.pre_state)
    if code := _port_reject(candidate):
        return _reject(code, candidate.pre_state)
    if code := _state_reject(candidate):
        return _reject(code, candidate.pre_state)
    normalized = _normalize_effects(candidate)
    context = candidate.context
    lane_journal = LaneCompositionJournalV1(
        chain_id=context.chain_id,
        deployment_root=context.deployment_root,
        profile_root=context.profile_root,
        writer_epoch=context.writer_epoch,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        coordinator_release_id=context.coordinator_release_id,
        command_occurrence_id=context.command_occurrence_id,
        ordered_module_journal_roots=(candidate.module_journal.journal_root,),
        pre_lane_root=candidate.pre_state.state_root,
        post_lane_root=candidate.post_state.state_root,
        effect_plan_root=normalized.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
    )
    return ZDEXTokenomicsLaneCompositionAcceptedV1(
        candidate.post_state,
        normalized,
        lane_journal,
    )


__all__ = [
    "ZDEXTokenomicsFeeAllocationLaneCandidateV1",
    "compose_zdex_tokenomics_fee_allocation_lane_v1",
]
