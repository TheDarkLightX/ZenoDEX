"""Deterministic refinement from checked ZDEX burn state to route leaf output.

This module authenticates no receipt and grants no settlement authority. It
removes fixture freedom by deriving the burn journal and global effects from an
accepted hyperdeflation transition and the exact purchase journal it names.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from .global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    _require_root,
)
from .zdex_hyperdeflation_results_v1 import ZDEXPurchaseAndBurnAcceptedV1
from .zdex_purchase_burn_effects_v1 import (
    _burn_effects_from_values_v1,
    _ZDEXBurnEffectInputsV1,
    burn_effects_v1,
    purchase_effects_v1,
    purchase_effects_v2,
)
from .zdex_purchase_burn_route_types_v1 import (
    ZDEXAMMPurchaseJournalV1,
    ZDEXAMMPurchaseJournalV2,
    ZDEXBurnJournalV1,
)

ZDEXPurchaseJournalForBurnV1: TypeAlias = (
    ZDEXAMMPurchaseJournalV1 | ZDEXAMMPurchaseJournalV2
)


def _purchase_effects(
    purchase: ZDEXPurchaseJournalForBurnV1,
) -> GlobalEconomicEffectPlanV1:
    if type(purchase) is ZDEXAMMPurchaseJournalV1:
        return purchase_effects_v1(purchase)
    if type(purchase) is ZDEXAMMPurchaseJournalV2:
        return purchase_effects_v2(purchase)
    raise TypeError("ZDEX burn refinement requires a closed purchase journal")


@dataclass(frozen=True, slots=True)
class ZDEXBurnLeafProjectionV1:
    """Self-recomputing, non-authoritative burn-leaf projection."""

    accepted: ZDEXPurchaseAndBurnAcceptedV1
    purchase_journal: ZDEXPurchaseJournalForBurnV1
    tokenomics_module_release_id: str
    journal: ZDEXBurnJournalV1
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        _require_exact_types(self)
        _require_root(
            self.tokenomics_module_release_id,
            name="ZDEX tokenomics module release id",
        )
        _require_refinement_bindings(self.accepted, self.purchase_journal)
        recomputed_effects = burn_effects_v1(self.journal)
        if self.journal.effect_plan_root != recomputed_effects.effect_plan_root:
            raise ValueError("ZDEX burn journal effect plan root is inconsistent")
        expected_journal = _derive_burn_journal_v1(
            self.accepted,
            self.purchase_journal,
            self.tokenomics_module_release_id,
        )
        if self.journal != expected_journal:
            raise ValueError("ZDEX burn journal is not the exact checked refinement")
        if self.effects != recomputed_effects:
            raise ValueError("ZDEX burn effects are not the exact journal projection")


def _require_exact_types(projection: ZDEXBurnLeafProjectionV1) -> None:
    if type(projection.accepted) is not ZDEXPurchaseAndBurnAcceptedV1:
        raise TypeError("ZDEX burn refinement requires an exact accepted transition")
    if type(projection.purchase_journal) not in (
        ZDEXAMMPurchaseJournalV1,
        ZDEXAMMPurchaseJournalV2,
    ):
        raise TypeError("ZDEX burn refinement requires an exact purchase journal")
    if type(projection.tokenomics_module_release_id) is not str:
        raise TypeError("ZDEX burn refinement module release id must be a string")
    if type(projection.journal) is not ZDEXBurnJournalV1:
        raise TypeError("ZDEX burn refinement requires an exact burn journal")
    if type(projection.effects) is not GlobalEconomicEffectPlanV1:
        raise TypeError("ZDEX burn refinement requires an exact effect plan")


def _require_refinement_bindings(
    accepted: ZDEXPurchaseAndBurnAcceptedV1,
    purchase: ZDEXPurchaseJournalForBurnV1,
) -> None:
    accepted.validate()
    purchase.validate()
    if purchase.effect_plan_root != _purchase_effects(purchase).effect_plan_root:
        raise ValueError("ZDEX purchase effect plan was not recomputed exactly")
    route = accepted.route_context
    burn = accepted.effect.authorized_burn_atoms
    if purchase.route_release_id != route.route_release_id:
        raise ValueError("ZDEX purchase route release does not match the checked burn")
    if purchase.issue_burn_policy_root != accepted.policy.policy_root:
        raise ValueError("ZDEX purchase issue/burn policy does not match the checked burn")
    if purchase.journal_root != route.purchase_occurrence_root:
        raise ValueError("ZDEX purchase journal root does not match the checked occurrence")
    if purchase.zdex_asset_id != accepted.policy.asset_id:
        raise ValueError("ZDEX purchase asset does not match the checked burn")
    if purchase.burn_bucket_id != accepted.effect.source_bucket_id:
        raise ValueError("ZDEX purchase burn bucket does not match the checked source")
    if purchase.purchased_zdex_atoms != burn:
        raise ValueError("ZDEX purchased amount does not match the checked burn")
    if (
        purchase.zdex_owned_atoms != accepted.pre_state.live_supply_atoms
        or purchase.zdex_supply_atoms != accepted.pre_state.live_supply_atoms
    ):
        raise ValueError("ZDEX purchase totals do not match the checked burn state")
    source_pre = accepted.pre_state.bucket_atoms(accepted.effect.source_bucket_id)
    source_post = accepted.post_state.bucket_atoms(accepted.effect.source_bucket_id)
    if source_pre != burn or source_post is not None:
        raise ValueError("ZDEX checked transition did not drain the transient burn bucket")


def _derive_burn_journal_v1(
    accepted: ZDEXPurchaseAndBurnAcceptedV1,
    purchase: ZDEXPurchaseJournalForBurnV1,
    tokenomics_module_release_id: str,
) -> ZDEXBurnJournalV1:
    _require_root(
        tokenomics_module_release_id,
        name="ZDEX tokenomics module release id",
    )
    _require_refinement_bindings(accepted, purchase)
    burn = accepted.effect.authorized_burn_atoms
    pre_burn_substate_root = accepted.pre_state.state_root
    post_burn_substate_root = accepted.post_state.state_root
    effects = _burn_effects_from_values_v1(
        _ZDEXBurnEffectInputsV1(
            command_occurrence_id=purchase.command_occurrence_id,
            zdex_asset_id=accepted.policy.asset_id,
            burn_bucket_id=accepted.effect.source_bucket_id,
            burned_zdex_atoms=burn,
            zdex_owned_pre_atoms=accepted.pre_state.live_supply_atoms,
            zdex_owned_post_atoms=accepted.post_state.live_supply_atoms,
            zdex_supply_pre_atoms=accepted.pre_state.live_supply_atoms,
            zdex_supply_post_atoms=accepted.post_state.live_supply_atoms,
        )
    )
    return ZDEXBurnJournalV1(
        chain_id=purchase.chain_id,
        deployment_root=purchase.deployment_root,
        profile_root=purchase.profile_root,
        writer_epoch=purchase.writer_epoch,
        route_release_id=purchase.route_release_id,
        command_occurrence_id=purchase.command_occurrence_id,
        tokenomics_module_release_id=tokenomics_module_release_id,
        issue_burn_policy_root=accepted.policy.policy_root,
        buyback_budget_occurrence_root=purchase.buyback_budget_occurrence_root,
        authorized_quote_input_atoms=purchase.quote_amount_in_atoms,
        purchase_occurrence_root=purchase.journal_root,
        route_context_root=accepted.route_context.context_root,
        zdex_asset_id=accepted.policy.asset_id,
        burn_bucket_id=accepted.effect.source_bucket_id,
        burned_zdex_atoms=burn,
        burn_bucket_pre_atoms=burn,
        burn_bucket_post_atoms=0,
        zdex_owned_pre_atoms=accepted.pre_state.live_supply_atoms,
        zdex_owned_post_atoms=accepted.post_state.live_supply_atoms,
        zdex_supply_pre_atoms=accepted.pre_state.live_supply_atoms,
        zdex_supply_post_atoms=accepted.post_state.live_supply_atoms,
        pre_tokenomics_burn_substate_root=pre_burn_substate_root,
        post_tokenomics_burn_substate_root=post_burn_substate_root,
        effect_plan_root=effects.effect_plan_root,
    )


def refine_zdex_burn_leaf_v1(
    accepted: ZDEXPurchaseAndBurnAcceptedV1,
    purchase_journal: ZDEXPurchaseJournalForBurnV1,
    tokenomics_module_release_id: str,
) -> ZDEXBurnLeafProjectionV1:
    """Derive the exact route burn journal and effects from checked values."""

    if type(accepted) is not ZDEXPurchaseAndBurnAcceptedV1:
        raise TypeError("ZDEX burn refinement requires an exact accepted transition")
    if type(purchase_journal) not in (
        ZDEXAMMPurchaseJournalV1,
        ZDEXAMMPurchaseJournalV2,
    ):
        raise TypeError("ZDEX burn refinement requires an exact purchase journal")
    journal = _derive_burn_journal_v1(
        accepted,
        purchase_journal,
        tokenomics_module_release_id,
    )
    return ZDEXBurnLeafProjectionV1(
        accepted=accepted,
        purchase_journal=purchase_journal,
        tokenomics_module_release_id=tokenomics_module_release_id,
        journal=journal,
        effects=burn_effects_v1(journal),
    )


__all__ = ["ZDEXBurnLeafProjectionV1", "refine_zdex_burn_leaf_v1"]
