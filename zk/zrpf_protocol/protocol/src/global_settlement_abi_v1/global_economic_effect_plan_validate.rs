use alloc::collections::BTreeSet;

use super::{
    EconomicLaneIdV1, GlobalAssetReconciliationV1, GlobalEconomicEffectPlanErrorV1,
    GlobalEconomicEffectRowV1, GlobalIssueBurnKindV1, GlobalOccurrenceConsumptionKindV1,
    MAX_GLOBAL_ASSET_RECONCILIATIONS_V1, MAX_GLOBAL_ECONOMIC_EFFECT_ROWS_V1,
};
use crate::CommitmentV3;

use super::global_economic_effect_plan_reconcile::validate_asset_reconciliations_v1;
use super::global_economic_effect_plan_types::GlobalEconomicEffectContentV1;

pub(super) fn validate_effect_content_v1(
    content: &GlobalEconomicEffectContentV1,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    match content {
        GlobalEconomicEffectContentV1::AccountMovement {
            source_id,
            destination_id,
            amount_atoms,
            ..
        } => {
            require_positive(*amount_atoms, "account movement")?;
            require_distinct(*source_id, *destination_id, "account movement")?;
        }
        GlobalEconomicEffectContentV1::IssueBurn { amount_atoms, .. } => {
            require_positive(*amount_atoms, "issue/burn")?
        }
        GlobalEconomicEffectContentV1::Custody {
            custody_pre_atoms,
            custody_post_atoms,
            claimant_entitlements_pre_atoms,
            claimant_entitlements_post_atoms,
            unencumbered_reserves_pre_atoms,
            unencumbered_reserves_post_atoms,
            ..
        } => validate_custody(
            [
                *custody_pre_atoms,
                *claimant_entitlements_pre_atoms,
                *unencumbered_reserves_pre_atoms,
            ],
            [
                *custody_post_atoms,
                *claimant_entitlements_post_atoms,
                *unencumbered_reserves_post_atoms,
            ],
        )?,
        GlobalEconomicEffectContentV1::Liability {
            pre_atoms,
            post_atoms,
            ..
        } if pre_atoms == post_atoms => {
            return Err(GlobalEconomicEffectPlanErrorV1::NonChangingEffect(
                "liability",
            ));
        }
        GlobalEconomicEffectContentV1::Reserve {
            pre_atoms,
            post_atoms,
            ..
        } if pre_atoms == post_atoms => {
            return Err(GlobalEconomicEffectPlanErrorV1::NonChangingEffect(
                "reserve",
            ));
        }
        GlobalEconomicEffectContentV1::Fee {
            charged_atoms,
            allocated_atoms,
            carried_residue_atoms,
            ..
        } => {
            require_positive(*charged_atoms, "fee")?;
            require_sum(
                *allocated_atoms,
                *carried_residue_atoms,
                *charged_atoms,
                GlobalEconomicEffectPlanErrorV1::FeeAllocationMismatch,
            )?;
        }
        GlobalEconomicEffectContentV1::RewardSlash {
            source_id,
            destination_id,
            amount_atoms,
            ..
        } => {
            require_positive(*amount_atoms, "reward/slash")?;
            require_distinct(*source_id, *destination_id, "reward/slash")?;
        }
        GlobalEconomicEffectContentV1::LaneWrite {
            pre_value_hash,
            post_value_hash,
            ..
        } if pre_value_hash == post_value_hash => {
            return Err(GlobalEconomicEffectPlanErrorV1::NonChangingEffect(
                "lane write",
            ));
        }
        GlobalEconomicEffectContentV1::TerminalObligation {
            pre_status_hash,
            post_status_hash,
            ..
        } if pre_status_hash == post_status_hash => {
            return Err(GlobalEconomicEffectPlanErrorV1::NonChangingEffect(
                "terminal obligation",
            ));
        }
        GlobalEconomicEffectContentV1::ExternalOutboxEnqueue { amount_atoms, .. } => {
            require_positive(*amount_atoms, "external outbox")?
        }
        _ => {}
    }
    Ok(())
}

pub(super) fn canonicalize_body_rows_v1(
    effects: &mut [GlobalEconomicEffectRowV1],
    reconciliations: &mut [GlobalAssetReconciliationV1],
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let mut keyed = effects
        .iter()
        .map(|row| Ok((row.canonical_id()?, row.clone())))
        .collect::<Result<alloc::vec::Vec<_>, GlobalEconomicEffectPlanErrorV1>>()?;
    keyed.sort_by_key(|(id, _)| *id);
    for (target, (_, value)) in effects.iter_mut().zip(keyed) {
        *target = value;
    }
    reconciliations.sort_by_key(|row| row.asset_id());
    Ok(())
}

pub(super) fn validate_body_rows_v1(
    local_domain_id: Option<crate::DomainIdV3>,
    effects: &[GlobalEconomicEffectRowV1],
    reconciliations: &[GlobalAssetReconciliationV1],
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    require_lengths(effects, reconciliations)?;
    require_canonical_effect_order(effects)?;
    require_unique_write_targets(effects)?;
    require_canonical_reconciliation_order(reconciliations)?;
    for effect in effects {
        validate_effect_content_v1(effect.content())?;
    }
    validate_asset_reconciliations_v1(local_domain_id, effects, reconciliations)
}

fn validate_custody(
    pre: [u128; 3],
    post: [u128; 3],
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    require_sum(
        pre[1],
        pre[2],
        pre[0],
        GlobalEconomicEffectPlanErrorV1::CustodyClaimMismatch,
    )?;
    require_sum(
        post[1],
        post[2],
        post[0],
        GlobalEconomicEffectPlanErrorV1::CustodyClaimMismatch,
    )?;
    if pre == post {
        return Err(GlobalEconomicEffectPlanErrorV1::NonChangingEffect(
            "custody",
        ));
    }
    Ok(())
}

fn require_lengths(
    effects: &[GlobalEconomicEffectRowV1],
    reconciliations: &[GlobalAssetReconciliationV1],
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    if effects.is_empty() {
        return Err(GlobalEconomicEffectPlanErrorV1::EmptyEffects);
    }
    if effects.len() > MAX_GLOBAL_ECONOMIC_EFFECT_ROWS_V1 {
        return Err(GlobalEconomicEffectPlanErrorV1::TooManyEffects {
            actual: effects.len(),
            maximum: MAX_GLOBAL_ECONOMIC_EFFECT_ROWS_V1,
        });
    }
    if reconciliations.is_empty() {
        return Err(GlobalEconomicEffectPlanErrorV1::EmptyReconciliations);
    }
    if reconciliations.len() > MAX_GLOBAL_ASSET_RECONCILIATIONS_V1 {
        return Err(GlobalEconomicEffectPlanErrorV1::TooManyReconciliations {
            actual: reconciliations.len(),
            maximum: MAX_GLOBAL_ASSET_RECONCILIATIONS_V1,
        });
    }
    Ok(())
}

fn require_canonical_effect_order(
    effects: &[GlobalEconomicEffectRowV1],
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let mut prior = None;
    for effect in effects {
        let id = effect.canonical_id()?;
        if prior == Some(id) {
            return Err(GlobalEconomicEffectPlanErrorV1::DuplicateEffect);
        }
        if prior.is_some_and(|value| value > id) {
            return Err(GlobalEconomicEffectPlanErrorV1::NonCanonicalOrder(
                "effects",
            ));
        }
        prior = Some(id);
    }
    Ok(())
}

fn require_canonical_reconciliation_order(
    rows: &[GlobalAssetReconciliationV1],
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let mut prior = None;
    for row in rows {
        let asset = row.asset_id();
        if prior == Some(asset) {
            return Err(GlobalEconomicEffectPlanErrorV1::DuplicateAssetReconciliation(asset));
        }
        if prior.is_some_and(|value| value > asset) {
            return Err(GlobalEconomicEffectPlanErrorV1::NonCanonicalOrder(
                "reconciliations",
            ));
        }
        prior = Some(asset);
    }
    Ok(())
}

fn require_unique_write_targets(
    effects: &[GlobalEconomicEffectRowV1],
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let mut targets = BTreeSet::new();
    for effect in effects {
        let Some((lane_id, target_id, label)) = write_target(effect.content()) else {
            continue;
        };
        let key = (effect.kind().code(), lane_id, target_id);
        if !targets.insert(key) {
            return Err(GlobalEconomicEffectPlanErrorV1::DuplicateWriteTarget(
                label, target_id,
            ));
        }
    }
    Ok(())
}

fn write_target(
    content: &GlobalEconomicEffectContentV1,
) -> Option<(EconomicLaneIdV1, CommitmentV3, &'static str)> {
    match content {
        GlobalEconomicEffectContentV1::Custody {
            lane_id,
            custody_id,
            ..
        } => Some((*lane_id, *custody_id, "custody")),
        GlobalEconomicEffectContentV1::Liability {
            lane_id,
            liability_id,
            ..
        } => Some((*lane_id, *liability_id, "liability")),
        GlobalEconomicEffectContentV1::Reserve {
            lane_id,
            reserve_id,
            ..
        } => Some((*lane_id, *reserve_id, "reserve")),
        GlobalEconomicEffectContentV1::Fee {
            lane_id, fee_id, ..
        } => Some((*lane_id, *fee_id, "fee")),
        GlobalEconomicEffectContentV1::LaneWrite {
            lane_id, object_id, ..
        } => Some((*lane_id, *object_id, "lane")),
        GlobalEconomicEffectContentV1::TerminalObligation {
            lane_id,
            obligation_id,
            ..
        } => Some((*lane_id, *obligation_id, "terminal-obligation")),
        GlobalEconomicEffectContentV1::ExternalOutboxEnqueue {
            lane_id, outbox_id, ..
        } => Some((*lane_id, *outbox_id, "outbox")),
        _ => None,
    }
}

fn require_positive(
    value: u128,
    kind: &'static str,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    if value == 0 {
        Err(GlobalEconomicEffectPlanErrorV1::ZeroAmount(kind))
    } else {
        Ok(())
    }
}

fn require_distinct(
    left: CommitmentV3,
    right: CommitmentV3,
    kind: &'static str,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    if left == right {
        Err(GlobalEconomicEffectPlanErrorV1::SelfTransfer(kind))
    } else {
        Ok(())
    }
}

fn require_sum(
    left: u128,
    right: u128,
    expected: u128,
    error: GlobalEconomicEffectPlanErrorV1,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let actual =
        left.checked_add(right)
            .ok_or(GlobalEconomicEffectPlanErrorV1::ArithmeticOverflow(
                "effect_sum",
            ))?;
    if actual == expected {
        Ok(())
    } else {
        Err(error)
    }
}

pub(super) fn consumption_rows_v1(
    effects: &[GlobalEconomicEffectRowV1],
    kind: GlobalOccurrenceConsumptionKindV1,
) -> alloc::vec::Vec<CommitmentV3> {
    let mut values = effects
        .iter()
        .filter_map(|effect| match effect.content() {
            GlobalEconomicEffectContentV1::OccurrenceConsumption {
                kind: actual,
                consumption_id,
            } if *actual == kind => Some(*consumption_id),
            _ => None,
        })
        .collect::<alloc::vec::Vec<_>>();
    values.sort_unstable();
    values
}

pub(super) fn authority_rows_match_v1(
    effects: &[GlobalEconomicEffectRowV1],
    scope: crate::AuthorizationScopeIdV1,
    binding: crate::ActionAuthorizationBindingIdV1,
) -> bool {
    effects.iter().all(|effect| match effect.content() {
        GlobalEconomicEffectContentV1::IssueBurn {
            authority_scope_id,
            action_authorization_binding,
            ..
        }
        | GlobalEconomicEffectContentV1::RewardSlash {
            authority_scope_id,
            action_authorization_binding,
            ..
        } => *authority_scope_id == scope && *action_authorization_binding == binding,
        _ => true,
    })
}

pub(super) fn issue_burn_policy_matches_v1(
    effects: &[GlobalEconomicEffectRowV1],
    policy: super::RouteIssueBurnPolicyV1,
) -> bool {
    effects.iter().all(|effect| match effect.content() {
        GlobalEconomicEffectContentV1::IssueBurn {
            kind: GlobalIssueBurnKindV1::Issue,
            ..
        } => matches!(
            policy,
            super::RouteIssueBurnPolicyV1::IssueOnly { .. }
                | super::RouteIssueBurnPolicyV1::IssueAndBurn { .. }
        ),
        GlobalEconomicEffectContentV1::IssueBurn {
            kind: GlobalIssueBurnKindV1::Burn,
            ..
        } => matches!(
            policy,
            super::RouteIssueBurnPolicyV1::BurnOnly { .. }
                | super::RouteIssueBurnPolicyV1::IssueAndBurn { .. }
        ),
        _ => true,
    })
}
