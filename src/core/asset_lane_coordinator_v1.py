"""Fail-closed single-module coordinator for the `ASSET_TRANSFER` lane."""

from __future__ import annotations

from .asset_lane_projection_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    AssetLaneCompositionAcceptedV1,
    AssetLaneCompositionRejectedV1,
    AssetLaneCompositionResultV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneCoordinatorRejectCodeV1,
    AssetLanePrivatePortV1,
    AssetLaneStateProjectionV1,
)
from .global_economic_proof_v1 import (
    LaneCompositionJournalV1,
    LaneModuleTransitionJournalV1,
)
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicEffectKindV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
)


def _reject(
    code: AssetLaneCoordinatorRejectCodeV1,
    pre_state: AssetLaneStateProjectionV1,
) -> AssetLaneCompositionRejectedV1:
    return AssetLaneCompositionRejectedV1(
        code,
        pre_state.state_root,
        pre_state.state_root,
        GlobalEconomicEffectPlanV1.empty(),
    )


def _changed_assets(
    pre_state: AssetLaneStateProjectionV1,
    post_state: AssetLaneStateProjectionV1,
) -> set[str]:
    pre_holdings = {row.key: row.amount_atoms for row in (*pre_state.balances, *pre_state.custody)}
    post_holdings = {
        row.key: row.amount_atoms for row in (*post_state.balances, *post_state.custody)
    }
    changed = {
        key[0]
        for key in pre_holdings.keys() | post_holdings.keys()
        if pre_holdings.get(key, 0) != post_holdings.get(key, 0)
    }
    pre_supply = {row.asset: row.amount_atoms for row in pre_state.supplies}
    post_supply = {row.asset: row.amount_atoms for row in post_state.supplies}
    changed.update(
        asset
        for asset in pre_supply.keys() | post_supply.keys()
        if pre_supply.get(asset) != post_supply.get(asset)
    )
    return changed


def _movement_deltas(
    state: AssetLaneStateProjectionV1,
) -> dict[tuple[str, str, str], int]:
    return {
        (row.asset, row.owner, row.custody_domain): row.amount_atoms
        for row in (*state.balances, *state.custody)
    }


def _effect_deltas(
    effects: GlobalEconomicEffectPlanV1,
) -> dict[tuple[str, str, str], int] | None:
    deltas: dict[tuple[str, str, str], int] = {}
    for row in effects.rows:
        if row.kind not in {
            EconomicEffectKindV1.ACCOUNT_MOVEMENT,
            EconomicEffectKindV1.CUSTODY,
        }:
            continue
        if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT:
            if row.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1:
                return None
        elif row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V1:
            return None
        key = (row.asset, row.principal, row.custody_domain)
        deltas[key] = deltas.get(key, 0) + row.delta_atoms
    return {key: value for key, value in deltas.items() if value != 0}


def _state_effects_match(
    pre_state: AssetLaneStateProjectionV1,
    post_state: AssetLaneStateProjectionV1,
    effects: GlobalEconomicEffectPlanV1,
) -> bool:
    pre = _movement_deltas(pre_state)
    post = _movement_deltas(post_state)
    expected = {
        key: post.get(key, 0) - pre.get(key, 0)
        for key in pre.keys() | post.keys()
        if post.get(key, 0) != pre.get(key, 0)
    }
    return _effect_deltas(effects) == expected


def _conservation_reject(
    pre_state: AssetLaneStateProjectionV1,
    post_state: AssetLaneStateProjectionV1,
    effects: GlobalEconomicEffectPlanV1,
) -> AssetLaneCoordinatorRejectCodeV1 | None:
    changed_assets = _changed_assets(pre_state, post_state)
    if {row.asset for row in effects.asset_conservation} != changed_assets:
        return AssetLaneCoordinatorRejectCodeV1.CONSERVATION_COVERAGE_MISMATCH
    pre_supply = {row.asset: row.amount_atoms for row in pre_state.supplies}
    post_supply = {row.asset: row.amount_atoms for row in post_state.supplies}
    for row in effects.asset_conservation:
        if (
            row.owned_and_custodied_pre_atoms
            != pre_state.owned_and_custodied_atoms(row.asset)
            or row.owned_and_custodied_post_atoms
            != post_state.owned_and_custodied_atoms(row.asset)
            or row.supply_pre_atoms != pre_supply.get(row.asset)
            or row.supply_post_atoms != post_supply.get(row.asset)
        ):
            return AssetLaneCoordinatorRejectCodeV1.CONSERVATION_STATE_MISMATCH
    if not _state_effects_match(pre_state, post_state, effects):
        return AssetLaneCoordinatorRejectCodeV1.STATE_EFFECT_MISMATCH
    return None


def _context_binding_reject(
    context: AssetLaneCoordinatorContextV1,
    module_journal: LaneModuleTransitionJournalV1,
) -> AssetLaneCoordinatorRejectCodeV1 | None:
    if module_journal.chain_id != context.chain_id:
        return AssetLaneCoordinatorRejectCodeV1.CHAIN_MISMATCH
    if module_journal.deployment_root != context.deployment_root:
        return AssetLaneCoordinatorRejectCodeV1.DEPLOYMENT_MISMATCH
    if module_journal.profile_root != context.profile_root:
        return AssetLaneCoordinatorRejectCodeV1.PROFILE_MISMATCH
    if module_journal.writer_epoch != context.writer_epoch:
        return AssetLaneCoordinatorRejectCodeV1.WRITER_EPOCH_MISMATCH
    if module_journal.lane_id is not LaneIdV1.ASSET_TRANSFER:
        return AssetLaneCoordinatorRejectCodeV1.WRONG_LANE
    return None


def _module_binding_reject(
    context: AssetLaneCoordinatorContextV1,
    module_journal: LaneModuleTransitionJournalV1,
    private_port: AssetLanePrivatePortV1,
    module_effects: GlobalEconomicEffectPlanV1,
) -> AssetLaneCoordinatorRejectCodeV1 | None:
    compatibility = next(
        (
            item
            for item in context.compatible_modules
            if item.module_release_id == module_journal.module_release_id
        ),
        None,
    )
    if compatibility is None:
        return AssetLaneCoordinatorRejectCodeV1.MODULE_NOT_REGISTERED
    if private_port.producer_module_schema != compatibility.module_schema:
        return AssetLaneCoordinatorRejectCodeV1.MODULE_SCHEMA_MISMATCH
    if private_port.module_release_id != module_journal.module_release_id:
        return AssetLaneCoordinatorRejectCodeV1.MODULE_RELEASE_MISMATCH
    if (
        module_journal.command_occurrence_id != context.command_occurrence_id
        or private_port.command_occurrence_id != context.command_occurrence_id
    ):
        return AssetLaneCoordinatorRejectCodeV1.OCCURRENCE_MISMATCH
    if module_journal.private_port_root == ZERO_ROOT_V1:
        return AssetLaneCoordinatorRejectCodeV1.PRIVATE_PORT_UNBOUND
    if module_journal.private_port_root != private_port.port_root:
        return AssetLaneCoordinatorRejectCodeV1.PRIVATE_PORT_ROOT_MISMATCH
    if (
        module_journal.effect_plan_root != module_effects.effect_plan_root
        or private_port.module_effect_plan_root != module_effects.effect_plan_root
    ):
        return AssetLaneCoordinatorRejectCodeV1.EFFECT_PLAN_MISMATCH
    if module_journal.terminal_obligations_root != private_port.terminal_obligations_root:
        return AssetLaneCoordinatorRejectCodeV1.TERMINAL_OBLIGATION_MISMATCH
    if any(
        state.asset_policy_registry_root != context.asset_policy_registry_root
        or state.fee_policy_registry_root != context.fee_policy_registry_root
        for state in (private_port.pre_state, private_port.post_state)
    ):
        return AssetLaneCoordinatorRejectCodeV1.POLICY_ROOT_MISMATCH
    return None


def _effect_binding_reject(
    context: AssetLaneCoordinatorContextV1,
    module_journal: LaneModuleTransitionJournalV1,
    module_effects: GlobalEconomicEffectPlanV1,
) -> AssetLaneCoordinatorRejectCodeV1 | None:
    if module_effects.occurrence_consumptions != (context.command_occurrence_id,):
        return AssetLaneCoordinatorRejectCodeV1.OCCURRENCE_EFFECT_MISMATCH
    expected_module_write = (
        LaneWriteV1(
            LaneIdV1.ASSET_TRANSFER,
            module_journal.pre_lane_root,
            module_journal.post_lane_root,
        ),
    )
    if module_effects.lane_writes != expected_module_write:
        return AssetLaneCoordinatorRejectCodeV1.LANE_WRITE_SHAPE_MISMATCH
    if module_effects.external_outbox_enqueue:
        return AssetLaneCoordinatorRejectCodeV1.EXTERNAL_OUTBOX_FORBIDDEN
    allowed_kinds = {
        EconomicEffectKindV1.ACCOUNT_MOVEMENT,
        EconomicEffectKindV1.ISSUE,
        EconomicEffectKindV1.BURN,
        EconomicEffectKindV1.CUSTODY,
        EconomicEffectKindV1.FEE_ALLOCATION,
    }
    if any(row.kind not in allowed_kinds for row in module_effects.rows):
        return AssetLaneCoordinatorRejectCodeV1.EFFECT_KIND_FORBIDDEN
    return None


def _normalized_effects(
    private_port: AssetLanePrivatePortV1,
    module_effects: GlobalEconomicEffectPlanV1,
) -> GlobalEconomicEffectPlanV1:
    return GlobalEconomicEffectPlanV1(
        rows=module_effects.rows,
        asset_conservation=module_effects.asset_conservation,
        fee_conservation=module_effects.fee_conservation,
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.ASSET_TRANSFER,
                private_port.pre_state.state_root,
                private_port.post_state.state_root,
            ),
        ),
        occurrence_consumptions=module_effects.occurrence_consumptions,
        external_outbox_enqueue=(),
    )


def compose_asset_lane_single_v1(
    context: AssetLaneCoordinatorContextV1,
    module_journal: LaneModuleTransitionJournalV1,
    private_port: AssetLanePrivatePortV1,
    module_effects: GlobalEconomicEffectPlanV1,
) -> AssetLaneCompositionResultV1:
    """Compose one structurally bound module journal into the shared lane state.

    Receipt validity and release selection are obligations of the caller's
    proof verifier. This function checks exact typed bindings and economics.
    """

    if not isinstance(context, AssetLaneCoordinatorContextV1):
        raise TypeError("asset lane coordinator context must be typed")
    if not isinstance(module_journal, LaneModuleTransitionJournalV1):
        raise TypeError("asset lane module journal must be typed")
    if not isinstance(private_port, AssetLanePrivatePortV1):
        raise TypeError("asset lane private port must be typed")
    if not isinstance(module_effects, GlobalEconomicEffectPlanV1):
        raise TypeError("asset lane module effects must be typed")

    pre_state = private_port.pre_state
    for binding_reject in (
        _context_binding_reject(context, module_journal),
        _module_binding_reject(context, module_journal, private_port, module_effects),
        _effect_binding_reject(context, module_journal, module_effects),
    ):
        if binding_reject is not None:
            return _reject(binding_reject, pre_state)
    economic_reject = _conservation_reject(
        private_port.pre_state,
        private_port.post_state,
        module_effects,
    )
    if economic_reject is not None:
        return _reject(economic_reject, pre_state)

    normalized_effects = _normalized_effects(private_port, module_effects)
    lane_journal = LaneCompositionJournalV1(
        chain_id=context.chain_id,
        deployment_root=context.deployment_root,
        profile_root=context.profile_root,
        writer_epoch=context.writer_epoch,
        lane_id=LaneIdV1.ASSET_TRANSFER,
        coordinator_release_id=context.coordinator_release_id,
        command_occurrence_id=context.command_occurrence_id,
        ordered_module_journal_roots=(module_journal.journal_root,),
        pre_lane_root=private_port.pre_state.state_root,
        post_lane_root=private_port.post_state.state_root,
        effect_plan_root=normalized_effects.effect_plan_root,
        terminal_obligations_root=private_port.terminal_obligations_root,
    )
    return AssetLaneCompositionAcceptedV1(
        private_port.post_state,
        normalized_effects,
        lane_journal,
    )


__all__ = ["compose_asset_lane_single_v1"]
