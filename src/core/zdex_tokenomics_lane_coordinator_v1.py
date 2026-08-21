"""Pure burn-to-tokenomics-lane composition with typed no-effect rejection."""

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
from .zdex_purchase_burn_effects_v1 import burn_effects_v1
from .zdex_purchase_burn_route_types_v1 import ZDEXBurnJournalV1
from .zdex_tokenomics_lane_v1 import (
    ZDEXTokenomicsBurnCoordinatorContextV1,
    ZDEXTokenomicsBurnPrivatePortV1,
    ZDEXTokenomicsLaneCompositionAcceptedV1,
    ZDEXTokenomicsLaneCompositionRejectedV1,
    ZDEXTokenomicsLaneCompositionResultV1,
    ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    ZDEXTokenomicsLaneStateV1,
    zdex_tokenomics_complete_lane_obligation_root_v1,
)


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBurnLaneCandidateV1:
    context: ZDEXTokenomicsBurnCoordinatorContextV1
    module_journal: LaneModuleTransitionJournalV1
    private_port: ZDEXTokenomicsBurnPrivatePortV1
    pre_state: ZDEXTokenomicsLaneStateV1
    post_state: ZDEXTokenomicsLaneStateV1
    burn_journal: ZDEXBurnJournalV1
    module_effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        expected_types = (
            (
                self.context,
                ZDEXTokenomicsBurnCoordinatorContextV1,
                "context",
            ),
            (self.module_journal, LaneModuleTransitionJournalV1, "module journal"),
            (self.private_port, ZDEXTokenomicsBurnPrivatePortV1, "private port"),
            (self.pre_state, ZDEXTokenomicsLaneStateV1, "pre-state"),
            (self.post_state, ZDEXTokenomicsLaneStateV1, "post-state"),
            (self.burn_journal, ZDEXBurnJournalV1, "burn journal"),
            (self.module_effects, GlobalEconomicEffectPlanV1, "effects"),
        )
        for value, expected_type, name in expected_types:
            if type(value) is not expected_type:
                raise TypeError(
                    f"ZDEX tokenomics coordinator {name} must be exact typed data"
                )
        self.context.validate()
        self.module_journal.validate()
        self.private_port.validate()
        self.pre_state.validate()
        self.post_state.validate()
        self.burn_journal.validate()
        self.module_effects.validate()


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
    candidate: ZDEXTokenomicsBurnLaneCandidateV1,
) -> ZDEXTokenomicsLaneCoordinatorRejectCodeV1 | None:
    context = candidate.context
    module = candidate.module_journal
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
    )
    for failed, code in checks:
        if failed:
            return ZDEXTokenomicsLaneCoordinatorRejectCodeV1(code)
    return None


def _port_reject(
    candidate: ZDEXTokenomicsBurnLaneCandidateV1,
) -> ZDEXTokenomicsLaneCoordinatorRejectCodeV1 | None:
    context = candidate.context
    module = candidate.module_journal
    port = candidate.private_port
    burn = candidate.burn_journal
    effects = candidate.module_effects
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
    if burn.route_release_id != context.route_release_id:
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.ROUTE_RELEASE_MISMATCH
    burn_bindings = (
        burn.chain_id == context.chain_id,
        burn.deployment_root == context.deployment_root,
        burn.profile_root == context.profile_root,
        burn.writer_epoch == context.writer_epoch,
        burn.tokenomics_module_release_id == context.tokenomics_module_release_id,
        burn.command_occurrence_id == context.command_occurrence_id,
        burn.issue_burn_policy_root == context.issue_burn_policy_root,
        port.burn_journal_root == burn.journal_root,
        port.pre_burn_substate_root == burn.pre_tokenomics_burn_substate_root,
        port.post_burn_substate_root == burn.post_tokenomics_burn_substate_root,
    )
    if not all(burn_bindings):
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.BURN_JOURNAL_MISMATCH
    if (
        effects != burn_effects_v1(burn)
        or module.effect_plan_root != effects.effect_plan_root
        or port.module_effect_plan_root != effects.effect_plan_root
        or burn.effect_plan_root != effects.effect_plan_root
    ):
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.EFFECT_PLAN_MISMATCH
    return None


def _state_reject(
    candidate: ZDEXTokenomicsBurnLaneCandidateV1,
) -> ZDEXTokenomicsLaneCoordinatorRejectCodeV1 | None:
    context = candidate.context
    pre_state = candidate.pre_state
    post_state = candidate.post_state
    burn = candidate.burn_journal
    if pre_state.supply_state.state_root != burn.pre_tokenomics_burn_substate_root:
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PRE_SUBSTATE_MISMATCH
    if post_state.supply_state.state_root != burn.post_tokenomics_burn_substate_root:
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.POST_SUBSTATE_MISMATCH
    if not pre_state.unrelated_to_burn_matches(post_state):
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.UNRELATED_STATE_MUTATION
    pre_bucket = pre_state.supply_state.bucket_atoms(burn.burn_bucket_id)
    post_bucket = post_state.supply_state.bucket_atoms(burn.burn_bucket_id)
    state_effect_matches = (
        pre_state.supply_state.policy_root == context.issue_burn_policy_root
        and post_state.supply_state.policy_root == context.issue_burn_policy_root
        and pre_state.supply_state.asset_id == burn.zdex_asset_id
        and post_state.supply_state.asset_id == burn.zdex_asset_id
        and pre_state.supply_state.live_supply_atoms == burn.zdex_supply_pre_atoms
        and post_state.supply_state.live_supply_atoms == burn.zdex_supply_post_atoms
        and burn.zdex_owned_pre_atoms == burn.zdex_supply_pre_atoms
        and burn.zdex_owned_post_atoms == burn.zdex_supply_post_atoms
        and pre_bucket == burn.burn_bucket_pre_atoms
        and post_bucket is None
        and burn.burn_bucket_post_atoms == 0
    )
    if not state_effect_matches:
        return ZDEXTokenomicsLaneCoordinatorRejectCodeV1.STATE_EFFECT_MISMATCH
    return None


def _normalize_effects(
    candidate: ZDEXTokenomicsBurnLaneCandidateV1,
) -> GlobalEconomicEffectPlanV1:
    effects = candidate.module_effects
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


def compose_zdex_tokenomics_burn_lane_v1(
    candidate: ZDEXTokenomicsBurnLaneCandidateV1,
) -> ZDEXTokenomicsLaneCompositionResultV1:
    """Embed one checked burn transition while preserving unrelated state."""

    if type(candidate) is not ZDEXTokenomicsBurnLaneCandidateV1:
        raise TypeError("ZDEX tokenomics composition candidate must be exact typed data")
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
    "ZDEXTokenomicsBurnLaneCandidateV1",
    "compose_zdex_tokenomics_burn_lane_v1",
]
