use alloc::collections::{BTreeMap, BTreeSet};

use super::{
    GlobalAssetReconciliationV1, GlobalEconomicEffectPlanErrorV1, GlobalEconomicEffectRowV1,
    GlobalIssueBurnKindV1,
};
use crate::CommitmentV3;

use super::global_economic_effect_plan_types::GlobalEconomicEffectContentV1;

#[derive(Default)]
struct AssetTotals {
    debit: u128,
    credit: u128,
    issue: u128,
    burn: u128,
    liability_pre: u128,
    liability_post: u128,
    reserve_pre: u128,
    reserve_post: u128,
}

pub(super) fn validate_asset_reconciliations_v1(
    local_domain_id: Option<crate::DomainIdV3>,
    effects: &[GlobalEconomicEffectRowV1],
    reconciliations: &[GlobalAssetReconciliationV1],
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let mut totals = BTreeMap::<CommitmentV3, AssetTotals>::new();
    let mut value_effects = BTreeMap::<CommitmentV3, (CommitmentV3, u128)>::new();
    for effect in effects {
        accumulate_effect(effect, &mut totals, &mut value_effects)?;
    }
    validate_outboxes(local_domain_id, effects, &value_effects)?;
    reconcile_assets(reconciliations, totals)
}

fn reconcile_assets(
    reconciliations: &[GlobalAssetReconciliationV1],
    mut totals: BTreeMap<CommitmentV3, AssetTotals>,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    for reconciliation in reconciliations {
        let asset_id = reconciliation.asset_id();
        let asset_totals = totals
            .remove(&asset_id)
            .ok_or(GlobalEconomicEffectPlanErrorV1::ReconciliationWithoutEffect(asset_id))?;
        validate_reconciliation(*reconciliation, asset_totals)?;
    }
    if let Some(asset_id) = totals.into_keys().next() {
        return Err(GlobalEconomicEffectPlanErrorV1::MissingAssetReconciliation(
            asset_id,
        ));
    }
    Ok(())
}

fn accumulate_effect(
    effect: &GlobalEconomicEffectRowV1,
    totals: &mut BTreeMap<CommitmentV3, AssetTotals>,
    value_effects: &mut BTreeMap<CommitmentV3, (CommitmentV3, u128)>,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let Some(asset) = effect_asset_id(effect.content()) else {
        return Ok(());
    };
    let row = totals.entry(asset).or_default();
    match effect.content() {
        GlobalEconomicEffectContentV1::AccountMovement { amount_atoms, .. } => {
            add(&mut row.debit, *amount_atoms, "account_debit")?;
            add(&mut row.credit, *amount_atoms, "account_credit")?;
            value_effects.insert(effect.canonical_id()?, (asset, *amount_atoms));
        }
        GlobalEconomicEffectContentV1::IssueBurn {
            kind, amount_atoms, ..
        } => {
            accumulate_issue_burn(row, *kind, *amount_atoms)?;
            value_effects.insert(effect.canonical_id()?, (asset, *amount_atoms));
        }
        GlobalEconomicEffectContentV1::Liability {
            pre_atoms,
            post_atoms,
            ..
        } => {
            add(&mut row.liability_pre, *pre_atoms, "liability_pre")?;
            add(&mut row.liability_post, *post_atoms, "liability_post")?;
        }
        GlobalEconomicEffectContentV1::Reserve {
            pre_atoms,
            post_atoms,
            ..
        } => {
            add(&mut row.reserve_pre, *pre_atoms, "reserve_pre")?;
            add(&mut row.reserve_post, *post_atoms, "reserve_post")?;
        }
        GlobalEconomicEffectContentV1::RewardSlash { amount_atoms, .. } => {
            add(&mut row.debit, *amount_atoms, "reward_slash_debit")?;
            add(&mut row.credit, *amount_atoms, "reward_slash_credit")?;
            value_effects.insert(effect.canonical_id()?, (asset, *amount_atoms));
        }
        _ => {}
    }
    Ok(())
}

fn effect_asset_id(content: &GlobalEconomicEffectContentV1) -> Option<CommitmentV3> {
    match content {
        GlobalEconomicEffectContentV1::AccountMovement { asset_id, .. }
        | GlobalEconomicEffectContentV1::IssueBurn { asset_id, .. }
        | GlobalEconomicEffectContentV1::Custody { asset_id, .. }
        | GlobalEconomicEffectContentV1::Liability { asset_id, .. }
        | GlobalEconomicEffectContentV1::Reserve { asset_id, .. }
        | GlobalEconomicEffectContentV1::Fee { asset_id, .. }
        | GlobalEconomicEffectContentV1::RewardSlash { asset_id, .. }
        | GlobalEconomicEffectContentV1::ExternalOutboxEnqueue { asset_id, .. } => Some(*asset_id),
        _ => None,
    }
}

fn accumulate_issue_burn(
    totals: &mut AssetTotals,
    kind: GlobalIssueBurnKindV1,
    amount_atoms: u128,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    match kind {
        GlobalIssueBurnKindV1::Issue => {
            add(&mut totals.issue, amount_atoms, "authorized_issue")?;
            add(&mut totals.credit, amount_atoms, "issue_credit")
        }
        GlobalIssueBurnKindV1::Burn => {
            add(&mut totals.burn, amount_atoms, "authorized_burn")?;
            add(&mut totals.debit, amount_atoms, "burn_debit")
        }
    }
}

fn validate_reconciliation(
    reconciliation: GlobalAssetReconciliationV1,
    totals: AssetTotals,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let asset = reconciliation.asset_id();
    require_equation(
        [totals.debit, totals.issue],
        [totals.credit, totals.burn],
        GlobalEconomicEffectPlanErrorV1::AssetConservationViolation(asset),
    )?;
    require_equation(
        [reconciliation.owned_and_custodied_pre_atoms(), totals.issue],
        [reconciliation.owned_and_custodied_post_atoms(), totals.burn],
        GlobalEconomicEffectPlanErrorV1::OwnedConservationViolation(asset),
    )?;
    require_equation(
        [reconciliation.supply_pre_atoms(), totals.issue],
        [reconciliation.supply_post_atoms(), totals.burn],
        GlobalEconomicEffectPlanErrorV1::SupplyConservationViolation(asset),
    )?;
    require_equation(
        [
            reconciliation.liabilities_pre_atoms(),
            totals.liability_post,
        ],
        [
            reconciliation.liabilities_post_atoms(),
            totals.liability_pre,
        ],
        GlobalEconomicEffectPlanErrorV1::LiabilityReconciliationViolation(asset),
    )?;
    require_equation(
        [
            reconciliation.named_reserves_pre_atoms(),
            totals.reserve_post,
        ],
        [
            reconciliation.named_reserves_post_atoms(),
            totals.reserve_pre,
        ],
        GlobalEconomicEffectPlanErrorV1::ReserveReconciliationViolation(asset),
    )
}

fn validate_outboxes(
    local_domain_id: Option<crate::DomainIdV3>,
    effects: &[GlobalEconomicEffectRowV1],
    value_effects: &BTreeMap<CommitmentV3, (CommitmentV3, u128)>,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let mut used = BTreeSet::new();
    for effect in effects {
        let GlobalEconomicEffectContentV1::ExternalOutboxEnqueue {
            destination_domain_id,
            asset_id,
            amount_atoms,
            value_effect_id,
            ..
        } = effect.content()
        else {
            continue;
        };
        if local_domain_id == Some(*destination_domain_id) {
            return Err(GlobalEconomicEffectPlanErrorV1::InternalOutboxDestination);
        }
        if value_effects.get(value_effect_id) != Some(&(*asset_id, *amount_atoms)) {
            return Err(GlobalEconomicEffectPlanErrorV1::OutboxValueEffectMismatch);
        }
        if !used.insert(*value_effect_id) {
            return Err(GlobalEconomicEffectPlanErrorV1::DuplicateOutboxValueEffect);
        }
    }
    Ok(())
}

fn require_equation(
    left: [u128; 2],
    right: [u128; 2],
    error: GlobalEconomicEffectPlanErrorV1,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let left =
        left[0]
            .checked_add(left[1])
            .ok_or(GlobalEconomicEffectPlanErrorV1::ArithmeticOverflow(
                "reconciliation_left",
            ))?;
    let right = right[0].checked_add(right[1]).ok_or(
        GlobalEconomicEffectPlanErrorV1::ArithmeticOverflow("reconciliation_right"),
    )?;
    if left == right {
        Ok(())
    } else {
        Err(error)
    }
}

fn add(
    target: &mut u128,
    value: u128,
    field: &'static str,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    *target = target
        .checked_add(value)
        .ok_or(GlobalEconomicEffectPlanErrorV1::ArithmeticOverflow(field))?;
    Ok(())
}
