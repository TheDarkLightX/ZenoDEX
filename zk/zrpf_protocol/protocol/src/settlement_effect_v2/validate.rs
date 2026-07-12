use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use super::{
    AssetEffectKindV2, AssetEffectV2, CarryEffectKindV2, LedgerCellWriteV2, MessageEffectKindV2,
    MessageEffectV2, SettlementEffectErrorV2, SettlementEffectPlanInputV2, SettlementEffectPlanV2,
    MAX_SETTLEMENT_EFFECT_ROWS_V2,
};
use crate::{AuthorizedEconomicActionV1, CommitmentV3, EconomicActionIdV1};

pub(super) fn canonicalize_plan_rows(
    input: &mut SettlementEffectPlanInputV2,
) -> Result<(), SettlementEffectErrorV2> {
    require_rows(&input.ledger_cell_writes, "ledger_cell_writes", false)?;
    require_rows(&input.asset_effects, "asset_effects", false)?;
    require_rows(&input.message_effects, "message_effects", true)?;
    require_rows(&input.carry_effects, "carry_effects", true)?;
    require_rows(&input.reward_effects, "reward_effects", true)?;
    input
        .ledger_cell_writes
        .sort_by_key(LedgerCellWriteV2::cell_key);
    input.asset_effects = sort_by_derived_id(core::mem::take(&mut input.asset_effects), |row| {
        row.canonical_id()
    })?;
    input.message_effects =
        sort_by_derived_id(core::mem::take(&mut input.message_effects), |row| {
            row.canonical_id()
        })?;
    input.carry_effects = sort_by_derived_id(core::mem::take(&mut input.carry_effects), |row| {
        row.canonical_id()
    })?;
    input.reward_effects = sort_by_derived_id(core::mem::take(&mut input.reward_effects), |row| {
        row.canonical_id()
    })?;
    Ok(())
}

pub(super) fn validate_plan_v2(
    plan: &SettlementEffectPlanV2,
) -> Result<(), SettlementEffectErrorV2> {
    plan.economic_action_batch().validate_self_consistency()?;
    if plan.post_state_root() == plan.economic_action_batch().pre_state_root() {
        return Err(SettlementEffectErrorV2::NonChangingState);
    }
    require_rows(plan.ledger_cell_writes(), "ledger_cell_writes", false)?;
    require_rows(plan.asset_effects(), "asset_effects", false)?;
    require_rows(plan.message_effects(), "message_effects", true)?;
    require_rows(plan.carry_effects(), "carry_effects", true)?;
    require_rows(plan.reward_effects(), "reward_effects", true)?;
    require_canonical_rows(plan)?;
    let actions = action_map(plan.economic_action_batch().actions())?;
    validate_action_coverage(plan, &actions)?;
    validate_authorized_effects(plan.asset_effects(), &actions)?;
    validate_conservation(plan.asset_effects())?;
    validate_messages(plan, &actions)?;
    validate_rewards(plan, &actions)?;
    Ok(())
}

fn action_map(
    actions: &[AuthorizedEconomicActionV1],
) -> Result<BTreeMap<EconomicActionIdV1, &AuthorizedEconomicActionV1>, SettlementEffectErrorV2> {
    let mut result = BTreeMap::new();
    for action in actions {
        if result.insert(action.action_id()?, action).is_some() {
            return Err(SettlementEffectErrorV2::DuplicateAction);
        }
    }
    Ok(result)
}

fn validate_action_coverage(
    plan: &SettlementEffectPlanV2,
    actions: &BTreeMap<EconomicActionIdV1, &AuthorizedEconomicActionV1>,
) -> Result<(), SettlementEffectErrorV2> {
    let mut writes = BTreeSet::new();
    let mut effects = BTreeSet::new();
    for row in plan.ledger_cell_writes() {
        require_known_action(actions, row.economic_action_id())?;
        writes.insert(row.economic_action_id());
    }
    for row in plan.asset_effects() {
        require_known_action(actions, row.economic_action_id())?;
        effects.insert(row.economic_action_id());
    }
    for action_id in actions.keys() {
        if !writes.contains(action_id) {
            return Err(SettlementEffectErrorV2::ActionWithoutCellWrite);
        }
        if !effects.contains(action_id) {
            return Err(SettlementEffectErrorV2::ActionWithoutAssetEffect);
        }
    }
    Ok(())
}

fn validate_authorized_effects(
    effects: &[AssetEffectV2],
    actions: &BTreeMap<EconomicActionIdV1, &AuthorizedEconomicActionV1>,
) -> Result<(), SettlementEffectErrorV2> {
    let mut consumed = BTreeSet::new();
    for effect in effects
        .iter()
        .filter(|effect| effect.requires_authorization())
    {
        let action = require_known_action(actions, effect.economic_action_id())?;
        let expected_binding = action.action_authorization_binding()?;
        let expected_scope = action.record().authorization_scope_id();
        if effect.action_authorization_binding() != Some(expected_binding)
            || effect.authority_scope_id() != Some(expected_scope)
        {
            return Err(SettlementEffectErrorV2::AuthorizationMismatch);
        }
        if !consumed.insert(expected_binding) {
            return Err(SettlementEffectErrorV2::AuthorizationReused);
        }
    }
    Ok(())
}

fn validate_conservation(effects: &[AssetEffectV2]) -> Result<(), SettlementEffectErrorV2> {
    let mut totals = BTreeMap::<CommitmentV3, [u128; 4]>::new();
    for effect in effects {
        let row = totals.entry(effect.asset_id()).or_insert([0; 4]);
        for (total, value) in row.iter_mut().zip([
            effect.debit_atoms(),
            effect.credit_atoms(),
            effect.authorized_mint_atoms(),
            effect.authorized_burn_atoms(),
        ]) {
            *total = total
                .checked_add(value)
                .ok_or(SettlementEffectErrorV2::ArithmeticOverflow("asset_total"))?;
        }
    }
    for [debit, credit, mint, burn] in totals.into_values() {
        let left = debit
            .checked_add(mint)
            .ok_or(SettlementEffectErrorV2::ArithmeticOverflow(
                "debit_plus_mint",
            ))?;
        let right = credit
            .checked_add(burn)
            .ok_or(SettlementEffectErrorV2::ArithmeticOverflow(
                "credit_plus_burn",
            ))?;
        if left != right {
            return Err(SettlementEffectErrorV2::AssetConservationViolation);
        }
    }
    Ok(())
}

fn validate_messages(
    plan: &SettlementEffectPlanV2,
    actions: &BTreeMap<EconomicActionIdV1, &AuthorizedEconomicActionV1>,
) -> Result<(), SettlementEffectErrorV2> {
    let effect_map = asset_effect_map(plan.asset_effects())?;
    let mut carry_map = BTreeMap::new();
    for carry in plan.carry_effects() {
        require_known_action(actions, carry.economic_action_id())?;
        if carry_map.insert(carry.message_id(), carry).is_some() {
            return Err(SettlementEffectErrorV2::MessageCarryMismatch);
        }
    }
    if carry_map.len() != plan.message_effects().len() {
        return Err(SettlementEffectErrorV2::MessageCarryMismatch);
    }
    let mut used_effects = BTreeSet::new();
    for message in plan.message_effects() {
        require_known_action(actions, message.economic_action_id())?;
        let effect = effect_map
            .get(&message.asset_effect_id())
            .ok_or(SettlementEffectErrorV2::MessageCarryMismatch)?;
        let carry = carry_map
            .get(&message.canonical_id()?)
            .ok_or(SettlementEffectErrorV2::MessageCarryMismatch)?;
        let local_domain = plan.economic_action_batch().chain_or_domain_id();
        // Lock/release carry continuity models an ordinary asset transfer.
        // Supply-changing bridge modes require a separate typed protocol so a
        // burn or mint cannot also be interpreted as a carry lock or release.
        let uses_supported_effect = effect.kind() == AssetEffectKindV2::OrdinaryTransfer;
        let amount_matches_complete_effect = effect.debit_atoms() == message.amount_atoms()
            && effect.credit_atoms() == message.amount_atoms();
        let direction_matches = match message.kind() {
            MessageEffectKindV2::OutboxEnqueue => {
                message.source_domain_id() == local_domain
                    && carry.kind() == CarryEffectKindV2::Lock
            }
            MessageEffectKindV2::InboxConsume => {
                message.destination_domain_id() == local_domain
                    && carry.kind() == CarryEffectKindV2::Release
            }
        };
        if !used_effects.insert(message.asset_effect_id())
            || !uses_supported_effect
            || !amount_matches_complete_effect
            || !direction_matches
            || effect.economic_action_id() != message.economic_action_id()
            || effect.asset_id() != message.asset_id()
            || carry.economic_action_id() != message.economic_action_id()
            || carry.asset_id() != message.asset_id()
            || carry.amount_atoms() != message.amount_atoms()
        {
            return Err(SettlementEffectErrorV2::MessageCarryMismatch);
        }
    }
    Ok(())
}

fn validate_rewards(
    plan: &SettlementEffectPlanV2,
    actions: &BTreeMap<EconomicActionIdV1, &AuthorizedEconomicActionV1>,
) -> Result<(), SettlementEffectErrorV2> {
    let effects = asset_effect_map(plan.asset_effects())?;
    let writes = plan
        .ledger_cell_writes()
        .iter()
        .map(|row| (row.cell_key(), row))
        .collect::<BTreeMap<_, _>>();
    let mut used_effects = plan
        .message_effects()
        .iter()
        .map(MessageEffectV2::asset_effect_id)
        .collect::<BTreeSet<_>>();
    let mut submitted_reward_effects = BTreeSet::new();
    for reward in plan.reward_effects() {
        let action = require_known_action(actions, reward.economic_action_id())?;
        let effect = effects
            .get(&reward.asset_effect_id())
            .ok_or(SettlementEffectErrorV2::RewardMismatch)?;
        let write = writes
            .get(&reward.recipient_cell_key())
            .ok_or(SettlementEffectErrorV2::RewardMismatch)?;
        if !used_effects.insert(reward.asset_effect_id())
            || effect.kind() != AssetEffectKindV2::AuthorizedReward
            || effect.economic_action_id() != reward.economic_action_id()
            || effect.asset_id() != reward.asset_id()
            || effect.credit_atoms() != reward.amount_atoms()
            || effect.authority_scope_id() != Some(reward.authority_scope_id())
            || effect.action_authorization_binding() != Some(reward.action_authorization_binding())
            || write.economic_action_id() != reward.economic_action_id()
            || action.action_authorization_binding()? != reward.action_authorization_binding()
        {
            return Err(SettlementEffectErrorV2::RewardMismatch);
        }
        submitted_reward_effects.insert(reward.asset_effect_id());
    }
    let expected_reward_effects = plan
        .asset_effects()
        .iter()
        .filter(|effect| effect.kind() == AssetEffectKindV2::AuthorizedReward)
        .map(AssetEffectV2::canonical_id)
        .collect::<Result<BTreeSet<_>, _>>()?;
    if submitted_reward_effects != expected_reward_effects {
        return Err(SettlementEffectErrorV2::RewardMismatch);
    }
    Ok(())
}

fn require_canonical_rows(plan: &SettlementEffectPlanV2) -> Result<(), SettlementEffectErrorV2> {
    require_strict_order(
        plan.ledger_cell_writes()
            .iter()
            .map(LedgerCellWriteV2::cell_key),
        "ledger_cell_writes",
        SettlementEffectErrorV2::DuplicateCellWrite,
    )?;
    require_derived_order(
        plan.asset_effects(),
        |row| row.canonical_id(),
        "asset_effects",
        SettlementEffectErrorV2::DuplicateAssetEffect,
    )?;
    require_derived_order(
        plan.message_effects(),
        |row| row.canonical_id(),
        "message_effects",
        SettlementEffectErrorV2::DuplicateMessage,
    )?;
    require_derived_order(
        plan.carry_effects(),
        |row| row.canonical_id(),
        "carry_effects",
        SettlementEffectErrorV2::DuplicateCarry,
    )?;
    require_derived_order(
        plan.reward_effects(),
        |row| row.canonical_id(),
        "reward_effects",
        SettlementEffectErrorV2::DuplicateReward,
    )?;
    Ok(())
}

fn asset_effect_map(
    rows: &[AssetEffectV2],
) -> Result<BTreeMap<CommitmentV3, &AssetEffectV2>, SettlementEffectErrorV2> {
    rows.iter()
        .map(|row| Ok((row.canonical_id()?, row)))
        .collect()
}

fn require_known_action<'a>(
    actions: &'a BTreeMap<EconomicActionIdV1, &'a AuthorizedEconomicActionV1>,
    action_id: EconomicActionIdV1,
) -> Result<&'a AuthorizedEconomicActionV1, SettlementEffectErrorV2> {
    actions
        .get(&action_id)
        .copied()
        .ok_or(SettlementEffectErrorV2::UnknownAction)
}

fn require_rows<T>(
    rows: &[T],
    field: &'static str,
    allow_empty: bool,
) -> Result<(), SettlementEffectErrorV2> {
    if !allow_empty && rows.is_empty() {
        return Err(SettlementEffectErrorV2::EmptyCollection(field));
    }
    if rows.len() > MAX_SETTLEMENT_EFFECT_ROWS_V2 {
        return Err(SettlementEffectErrorV2::CollectionTooLarge {
            field,
            actual: rows.len(),
            maximum: MAX_SETTLEMENT_EFFECT_ROWS_V2,
        });
    }
    Ok(())
}

fn sort_by_derived_id<T>(
    rows: Vec<T>,
    derive: impl Fn(&T) -> Result<CommitmentV3, SettlementEffectErrorV2>,
) -> Result<Vec<T>, SettlementEffectErrorV2> {
    let mut keyed = rows
        .into_iter()
        .map(|row| Ok((derive(&row)?, row)))
        .collect::<Result<Vec<_>, SettlementEffectErrorV2>>()?;
    keyed.sort_by_key(|(id, _)| *id);
    Ok(keyed.into_iter().map(|(_, row)| row).collect())
}

fn require_derived_order<T>(
    rows: &[T],
    derive: impl Fn(&T) -> Result<CommitmentV3, SettlementEffectErrorV2>,
    field: &'static str,
    duplicate_error: SettlementEffectErrorV2,
) -> Result<(), SettlementEffectErrorV2> {
    let values = rows.iter().map(derive).collect::<Result<Vec<_>, _>>()?;
    require_strict_order(values.into_iter(), field, duplicate_error)
}

fn require_strict_order<T: Ord + Copy>(
    values: impl Iterator<Item = T>,
    field: &'static str,
    duplicate_error: SettlementEffectErrorV2,
) -> Result<(), SettlementEffectErrorV2> {
    let mut prior = None;
    for value in values {
        if prior == Some(value) {
            return Err(duplicate_error);
        }
        if prior.is_some_and(|previous| previous > value) {
            return Err(SettlementEffectErrorV2::NonCanonicalOrder(field));
        }
        prior = Some(value);
    }
    Ok(())
}
