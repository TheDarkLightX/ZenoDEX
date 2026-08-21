//! Deterministic refinement from checked ZDEX burn state to route leaf output.
//!
//! This module verifies no receipt and grants no settlement authority. It
//! removes fixture freedom by deriving the burn journal and global effects from
//! an accepted hyperdeflation transition and the exact purchase journal it
//! names.

use serde::Serialize;

use crate::canonical::{AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::zdex_hyperdeflation_results::ZDEXPurchaseAndBurnAcceptedV1;
use crate::zdex_purchase_burn_effects::{
    burn_effects_from_inputs_v1, burn_effects_v1, purchase_effects_v1, ZDEXBurnEffectInputsV1,
};
use crate::zdex_purchase_burn_types::{ZDEXAMMPurchaseJournalV1, ZDEXBurnJournalV1};

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXBurnLeafProjectionV1 {
    pub(crate) accepted: ZDEXPurchaseAndBurnAcceptedV1,
    pub(crate) purchase_journal: ZDEXAMMPurchaseJournalV1,
    pub(crate) tokenomics_module_release_id: RootV1,
    pub(crate) journal: ZDEXBurnJournalV1,
    pub(crate) effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXBurnLeafProjectionV1 {
    pub fn accepted(&self) -> &ZDEXPurchaseAndBurnAcceptedV1 {
        &self.accepted
    }

    pub fn purchase_journal(&self) -> &ZDEXAMMPurchaseJournalV1 {
        &self.purchase_journal
    }

    pub fn tokenomics_module_release_id(&self) -> &RootV1 {
        &self.tokenomics_module_release_id
    }

    pub fn journal(&self) -> &ZDEXBurnJournalV1 {
        &self.journal
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.tokenomics_module_release_id
            .validate("ZDEX tokenomics module release id", false)?;
        require_refinement_bindings_v1(&self.accepted, &self.purchase_journal)?;
        let recomputed_effects = burn_effects_v1(&self.journal)?;
        if self.journal.effect_plan_root != recomputed_effects.effect_plan_root()? {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX burn journal effect plan root",
            ));
        }
        let expected_journal = derive_burn_journal_v1(
            &self.accepted,
            &self.purchase_journal,
            &self.tokenomics_module_release_id,
        )?;
        if self.journal != expected_journal || self.effects != recomputed_effects {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX burn leaf exact refinement",
            ));
        }
        Ok(())
    }
}

fn require_refinement_bindings_v1(
    accepted: &ZDEXPurchaseAndBurnAcceptedV1,
    purchase: &ZDEXAMMPurchaseJournalV1,
) -> AbiResultV1<()> {
    accepted.validate()?;
    purchase.validate()?;
    if purchase.effect_plan_root != purchase_effects_v1(purchase)?.effect_plan_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX purchase effect plan refinement",
        ));
    }
    let policy_root = accepted.policy.policy_root()?;
    let purchase_root = purchase.journal_root()?;
    if purchase.route_release_id != accepted.route_context.route_release_id
        || purchase.issue_burn_policy_root != policy_root
        || purchase_root != accepted.route_context.purchase_occurrence_root
        || purchase.zdex_asset_id != accepted.policy.asset_id
        || purchase.burn_bucket_id != accepted.effect.source_bucket_id
        || purchase.purchased_zdex_atoms != accepted.effect.authorized_burn_atoms
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX purchase to checked burn binding",
        ));
    }
    if purchase.zdex_owned_atoms != accepted.pre_state.live_supply_atoms
        || purchase.zdex_supply_atoms != accepted.pre_state.live_supply_atoms
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX purchase totals to checked burn state",
        ));
    }
    let source_bucket_id = &accepted.effect.source_bucket_id;
    let source_pre = accepted.pre_state.bucket_atoms(source_bucket_id)?;
    let source_post = accepted.post_state.bucket_atoms(source_bucket_id)?;
    if source_pre != Some(accepted.effect.authorized_burn_atoms) || source_post.is_some() {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX transient burn bucket exact drain",
        ));
    }
    Ok(())
}

fn derive_burn_journal_v1(
    accepted: &ZDEXPurchaseAndBurnAcceptedV1,
    purchase: &ZDEXAMMPurchaseJournalV1,
    tokenomics_module_release_id: &RootV1,
) -> AbiResultV1<ZDEXBurnJournalV1> {
    tokenomics_module_release_id.validate("ZDEX tokenomics module release id", false)?;
    require_refinement_bindings_v1(accepted, purchase)?;
    let burn_atoms = accepted.effect.authorized_burn_atoms;
    let pre_lane_root = accepted.pre_state.state_root()?;
    let post_lane_root = accepted.post_state.state_root()?;
    let effects = burn_effects_from_inputs_v1(&ZDEXBurnEffectInputsV1 {
        command_occurrence_id: &purchase.command_occurrence_id,
        zdex_asset_id: &accepted.policy.asset_id,
        burn_bucket_id: &accepted.effect.source_bucket_id,
        burned_zdex_atoms: burn_atoms,
        zdex_owned_pre_atoms: accepted.pre_state.live_supply_atoms,
        zdex_owned_post_atoms: accepted.post_state.live_supply_atoms,
        zdex_supply_pre_atoms: accepted.pre_state.live_supply_atoms,
        zdex_supply_post_atoms: accepted.post_state.live_supply_atoms,
        pre_tokenomics_lane_root: &pre_lane_root,
        post_tokenomics_lane_root: &post_lane_root,
    })?;
    let journal = ZDEXBurnJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: purchase.chain_id.clone(),
        deployment_root: purchase.deployment_root.clone(),
        profile_root: purchase.profile_root.clone(),
        writer_epoch: purchase.writer_epoch,
        route_release_id: purchase.route_release_id.clone(),
        command_occurrence_id: purchase.command_occurrence_id.clone(),
        tokenomics_module_release_id: tokenomics_module_release_id.clone(),
        issue_burn_policy_root: accepted.policy.policy_root()?,
        buyback_budget_occurrence_root: purchase.buyback_budget_occurrence_root.clone(),
        authorized_quote_input_atoms: purchase.quote_amount_in_atoms,
        purchase_occurrence_root: purchase.journal_root()?,
        zdex_asset_id: accepted.policy.asset_id.clone(),
        burn_bucket_id: accepted.effect.source_bucket_id.clone(),
        burned_zdex_atoms: burn_atoms,
        burn_bucket_pre_atoms: burn_atoms,
        burn_bucket_post_atoms: 0,
        zdex_owned_pre_atoms: accepted.pre_state.live_supply_atoms,
        zdex_owned_post_atoms: accepted.post_state.live_supply_atoms,
        zdex_supply_pre_atoms: accepted.pre_state.live_supply_atoms,
        zdex_supply_post_atoms: accepted.post_state.live_supply_atoms,
        pre_tokenomics_lane_root: pre_lane_root,
        post_tokenomics_lane_root: post_lane_root,
        effect_plan_root: effects.effect_plan_root()?,
    };
    journal.validate()?;
    Ok(journal)
}

pub fn refine_zdex_burn_leaf_v1(
    accepted: &ZDEXPurchaseAndBurnAcceptedV1,
    purchase_journal: &ZDEXAMMPurchaseJournalV1,
    tokenomics_module_release_id: &RootV1,
) -> AbiResultV1<ZDEXBurnLeafProjectionV1> {
    let journal = derive_burn_journal_v1(accepted, purchase_journal, tokenomics_module_release_id)?;
    let projection = ZDEXBurnLeafProjectionV1 {
        accepted: accepted.clone(),
        purchase_journal: purchase_journal.clone(),
        tokenomics_module_release_id: tokenomics_module_release_id.clone(),
        effects: burn_effects_v1(&journal)?,
        journal,
    };
    projection.validate()?;
    Ok(projection)
}
