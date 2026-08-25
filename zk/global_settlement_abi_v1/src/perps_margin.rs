//! Deterministic SHADOW core for subject-bound perps margin accounting.
//!
//! Accepted outputs remain route-incomplete candidate effects. This module has
//! no authentication witness, verifier, mount, durable writer, or publication
//! authority.

use serde::Serialize;

use crate::asset_transfer_types::ACCOUNT_CUSTODY_DOMAIN_V1;
use crate::canonical::{hash_global_v1, AbiResultV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1, LaneWriteV1,
};
use crate::perps_margin_types::*;
use crate::proof::LaneModuleTransitionJournalV1;
use crate::release::LaneIdV1;

fn empty_effects() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: Vec::new(),
        asset_conservation: Vec::new(),
        fee_conservation: Vec::new(),
        lane_writes: Vec::new(),
        occurrence_consumptions: Vec::new(),
        external_outbox_enqueue: Vec::new(),
    }
}

fn reject(
    code: PerpsMarginRejectCodeV1,
    pre_state: &PerpsMarginStateV1,
) -> AbiResultV1<PerpsMarginResultV1> {
    let root = pre_state.state_root()?;
    let rejected = PerpsMarginRejectedV1 {
        code,
        pre_state_root: root.clone(),
        post_state_root: root,
        effects: empty_effects(),
    };
    rejected.validate()?;
    Ok(PerpsMarginResultV1::Rejected(Box::new(rejected)))
}

fn common_policy_reject(
    context: &PerpsMarginContextV1,
    state: &PerpsMarginStateV1,
    command: &PerpsMarginCommandV1,
) -> Option<PerpsMarginRejectCodeV1> {
    if context.module_release_id != state.module_release_id {
        return Some(PerpsMarginRejectCodeV1::RELEASE_MISMATCH);
    }
    if !matches!(
        command.command_kind.as_str(),
        PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1
            | PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1
            | PERPS_MARGIN_CLOSE_COMMAND_KIND_V1
    ) {
        return Some(PerpsMarginRejectCodeV1::UNKNOWN_COMMAND);
    }
    if state.market_status == PerpsMarginMarketStatusV1::HALTED {
        return Some(PerpsMarginRejectCodeV1::HALTED_MARKET);
    }
    if state.market_status == PerpsMarginMarketStatusV1::DRAIN_ONLY
        && command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1
    {
        return Some(PerpsMarginRejectCodeV1::MARKET_DRAIN_ONLY);
    }
    if command.market_id != state.market_id {
        return Some(PerpsMarginRejectCodeV1::MARKET_MISMATCH);
    }
    if command.asset != state.collateral_asset {
        return Some(PerpsMarginRejectCodeV1::ASSET_MISMATCH);
    }
    if command.owner != context.subject_id {
        return Some(PerpsMarginRejectCodeV1::UNAUTHORIZED_SUBJECT);
    }
    if command.command_kind != PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1
        && context.has_oracle_authority()
    {
        return Some(PerpsMarginRejectCodeV1::UNEXPECTED_ORACLE_AUTHORITY);
    }
    None
}

fn oracle_policy_reject(
    context: &PerpsMarginContextV1,
    state: &PerpsMarginStateV1,
    command: &PerpsMarginCommandV1,
    account: &PerpsMarginAccountV1,
) -> Option<PerpsMarginRejectCodeV1> {
    if command.command_kind != PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1 {
        return None;
    }
    if account.position_base == 0 {
        return context
            .has_oracle_authority()
            .then_some(PerpsMarginRejectCodeV1::UNEXPECTED_ORACLE_AUTHORITY);
    }
    if !context.has_oracle_authority() {
        return Some(PerpsMarginRejectCodeV1::ORACLE_AUTHORITY_MISSING);
    }
    if context.oracle_price_e8 != state.index_price_e8 {
        return Some(PerpsMarginRejectCodeV1::ORACLE_PRICE_MISMATCH);
    }
    None
}

fn prepared_account(
    state: &PerpsMarginStateV1,
    command: &PerpsMarginCommandV1,
) -> Result<PerpsMarginAccountV1, PerpsMarginRejectCodeV1> {
    let existing = state.account(&command.account_id);
    if existing.is_none() && command.command_kind != PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 {
        return Err(PerpsMarginRejectCodeV1::ACCOUNT_MISSING);
    }
    if existing.is_none() && state.accounts.len() >= MAX_PERPS_MARGIN_ACCOUNTS_V1 {
        return Err(PerpsMarginRejectCodeV1::ACCOUNT_LIMIT);
    }
    if existing.is_some_and(|account| account.owner != command.owner) {
        return Err(PerpsMarginRejectCodeV1::ACCOUNT_OWNER_MISMATCH);
    }
    if existing.is_some_and(|account| account.status == PerpsMarginAccountStatusV1::CLOSED) {
        return Err(PerpsMarginRejectCodeV1::ACCOUNT_CLOSED);
    }
    let current_nonce = existing.map(|account| account.nonce).unwrap_or(0);
    let expected_nonce = current_nonce
        .checked_add(1)
        .ok_or(PerpsMarginRejectCodeV1::NONCE_OVERFLOW)?;
    if command.nonce != expected_nonce {
        return Err(PerpsMarginRejectCodeV1::NONCE_MISMATCH);
    }
    Ok(existing.cloned().unwrap_or_else(|| PerpsMarginAccountV1 {
        account_id: command.account_id.clone(),
        owner: command.owner.clone(),
        position_base: 0,
        entry_price_e8: 0,
        collateral_atoms: 0,
        nonce: 0,
        status: PerpsMarginAccountStatusV1::OPEN,
    }))
}

fn maintenance_requirement(
    state: &PerpsMarginStateV1,
    position_base: i128,
) -> Result<u128, PerpsMarginRejectCodeV1> {
    let risk_bps = u128::from(
        state
            .maintenance_margin_bps
            .checked_add(state.depeg_buffer_bps)
            .ok_or(PerpsMarginRejectCodeV1::ARITHMETIC_OVERFLOW)?,
    );
    let numerator = position_base
        .unsigned_abs()
        .checked_mul(state.index_price_e8)
        .and_then(|value| value.checked_mul(risk_bps))
        .ok_or(PerpsMarginRejectCodeV1::ARITHMETIC_OVERFLOW)?;
    let quotient = numerator / BPS_SCALE_V1;
    quotient
        .checked_add(u128::from(numerator % BPS_SCALE_V1 != 0))
        .ok_or(PerpsMarginRejectCodeV1::ARITHMETIC_OVERFLOW)
}

fn post_account(
    state: &PerpsMarginStateV1,
    command: &PerpsMarginCommandV1,
    mut account: PerpsMarginAccountV1,
) -> Result<PerpsMarginAccountV1, PerpsMarginRejectCodeV1> {
    if command.command_kind == PERPS_MARGIN_CLOSE_COMMAND_KIND_V1 {
        if command.amount_atoms != 0 {
            return Err(PerpsMarginRejectCodeV1::INVALID_CLOSE_AMOUNT);
        }
        if account.position_base != 0 {
            return Err(PerpsMarginRejectCodeV1::POSITION_OPEN);
        }
        if account.collateral_atoms != 0 {
            return Err(PerpsMarginRejectCodeV1::COLLATERAL_REMAINS);
        }
        account.nonce = command.nonce;
        account.status = PerpsMarginAccountStatusV1::CLOSED;
        return Ok(account);
    }
    if command.amount_atoms == 0 {
        return Err(PerpsMarginRejectCodeV1::ZERO_AMOUNT);
    }
    let _delta = i128::try_from(command.amount_atoms)
        .map_err(|_| PerpsMarginRejectCodeV1::EFFECT_DELTA_OVERFLOW)?;
    if command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 {
        account.collateral_atoms = account
            .collateral_atoms
            .checked_add(command.amount_atoms)
            .ok_or(PerpsMarginRejectCodeV1::BALANCE_OVERFLOW)?;
        account.nonce = command.nonce;
        return Ok(account);
    }
    let remaining = account
        .collateral_atoms
        .checked_sub(command.amount_atoms)
        .ok_or(PerpsMarginRejectCodeV1::INSUFFICIENT_COLLATERAL)?;
    let maintenance = maintenance_requirement(state, account.position_base)?;
    if account.position_base != 0 && remaining < maintenance {
        return Err(PerpsMarginRejectCodeV1::MAINTENANCE_BREACH);
    }
    account.collateral_atoms = remaining;
    account.nonce = command.nonce;
    Ok(account)
}

fn post_state(
    state: &PerpsMarginStateV1,
    account: PerpsMarginAccountV1,
) -> AbiResultV1<PerpsMarginStateV1> {
    let mut accounts = state
        .accounts
        .iter()
        .cloned()
        .map(|value| (value.account_id.clone(), value))
        .collect::<std::collections::BTreeMap<_, _>>();
    accounts.insert(account.account_id.clone(), account);
    let candidate = PerpsMarginStateV1 {
        schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: state.module_release_id.clone(),
        market_id: state.market_id.clone(),
        collateral_asset: state.collateral_asset.clone(),
        index_price_e8: state.index_price_e8,
        maintenance_margin_bps: state.maintenance_margin_bps,
        depeg_buffer_bps: state.depeg_buffer_bps,
        max_position_abs: state.max_position_abs,
        market_status: state.market_status,
        accounts: accounts.into_values().collect(),
    };
    candidate.validate()?;
    Ok(candidate)
}

fn effect_rows(
    command: &PerpsMarginCommandV1,
) -> Result<Vec<EconomicEffectRowV1>, PerpsMarginRejectCodeV1> {
    if command.command_kind == PERPS_MARGIN_CLOSE_COMMAND_KIND_V1 {
        return Ok(Vec::new());
    }
    let amount = i128::try_from(command.amount_atoms)
        .map_err(|_| PerpsMarginRejectCodeV1::EFFECT_DELTA_OVERFLOW)?;
    let direction = if command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 {
        1_i128
    } else {
        -1_i128
    };
    Ok(vec![
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::ACCOUNT_MOVEMENT,
            principal: command.owner.clone(),
            asset: command.asset.clone(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: -direction * amount,
        },
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::CUSTODY,
            principal: command.account_id.clone(),
            asset: command.asset.clone(),
            custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: direction * amount,
        },
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::LIABILITY,
            principal: command.owner.clone(),
            asset: command.asset.clone(),
            custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: direction * amount,
        },
    ])
}

fn effect_plan(
    context: &PerpsMarginContextV1,
    pre_state: &PerpsMarginStateV1,
    post_state: &PerpsMarginStateV1,
    command: &PerpsMarginCommandV1,
) -> Result<GlobalEconomicEffectPlanV1, PerpsMarginRejectCodeV1> {
    Ok(GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: effect_rows(command)?,
        asset_conservation: Vec::new(),
        fee_conservation: Vec::new(),
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::PERPS_MARKET,
            pre_root: pre_state
                .state_root()
                .map_err(|_| PerpsMarginRejectCodeV1::ARITHMETIC_OVERFLOW)?,
            post_root: post_state
                .state_root()
                .map_err(|_| PerpsMarginRejectCodeV1::ARITHMETIC_OVERFLOW)?,
        }],
        occurrence_consumptions: vec![context.command_occurrence_id.clone()],
        external_outbox_enqueue: Vec::new(),
    })
}

#[derive(Serialize)]
struct PerpsMarginStatementBodyV1<'a> {
    schema: &'static str,
    context: &'a PerpsMarginContextV1,
    pre_state: &'a PerpsMarginStateV1,
    command: &'a PerpsMarginCommandV1,
}

fn accept(
    context: &PerpsMarginContextV1,
    pre_state: &PerpsMarginStateV1,
    post_state: PerpsMarginStateV1,
    command: &PerpsMarginCommandV1,
) -> AbiResultV1<PerpsMarginResultV1> {
    let effects = match effect_plan(context, pre_state, &post_state, command) {
        Ok(value) => value,
        Err(code) => return reject(code, pre_state),
    };
    let pre_root = pre_state.state_root()?;
    let post_root = post_state.state_root()?;
    let effect_root = effects.effect_plan_root()?;
    let terminal_obligations = post_state.terminal_obligations()?;
    let terminal_obligations_root = post_state.terminal_obligations_root()?;
    let statement_root = hash_global_v1(
        "perps-margin-statement-v1",
        &PerpsMarginStatementBodyV1 {
            schema: PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1,
            context,
            pre_state,
            command,
        },
    )?;
    let private_port = PerpsMarginPrivatePortV1 {
        schema: PERPS_MARGIN_PRIVATE_PORT_SCHEMA_V1.to_owned(),
        producer_module_schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: context.module_release_id.clone(),
        command_occurrence_id: context.command_occurrence_id.clone(),
        command_body_hash: command.command_body_hash()?,
        market_id: command.market_id.clone(),
        account_id: command.account_id.clone(),
        module_effect_plan_root: effect_root.clone(),
        terminal_obligations_root: terminal_obligations_root.clone(),
        oracle_authority_root: context.oracle_authority_root.clone(),
        oracle_occurrence_root: context.oracle_occurrence_root.clone(),
        oracle_price_e8: context.oracle_price_e8,
    };
    let private_port_root = private_port.port_root()?;
    let receipt_root = perps_margin_receipt_root_v1(
        &statement_root,
        &pre_root,
        &post_root,
        &effects,
        &private_port,
    )?;
    let module_journal = LaneModuleTransitionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: context.chain_id.clone(),
        deployment_root: context.deployment_root.clone(),
        profile_root: context.profile_root.clone(),
        writer_epoch: context.writer_epoch,
        lane_id: LaneIdV1::PERPS_MARKET,
        module_release_id: context.module_release_id.clone(),
        command_occurrence_id: context.command_occurrence_id.clone(),
        pre_lane_root: pre_root,
        post_lane_root: post_root,
        effect_plan_root: effect_root,
        private_port_root,
        receipt_root,
        terminal_obligations_root,
    };
    let accepted = PerpsMarginAcceptedV1 {
        statement_root,
        post_state,
        effects,
        module_journal,
        private_port,
        terminal_obligations,
    };
    accepted.validate()?;
    Ok(PerpsMarginResultV1::Accepted(Box::new(accepted)))
}

#[must_use = "the result owns the only candidate effects and terminal obligations"]
pub fn transition_perps_margin_v1(
    context: &PerpsMarginContextV1,
    pre_state: &PerpsMarginStateV1,
    command: &PerpsMarginCommandV1,
) -> AbiResultV1<PerpsMarginResultV1> {
    context.validate()?;
    pre_state.validate()?;
    command.validate()?;
    if let Some(code) = common_policy_reject(context, pre_state, command) {
        return reject(code, pre_state);
    }
    let account = match prepared_account(pre_state, command) {
        Ok(value) => value,
        Err(code) => return reject(code, pre_state),
    };
    if let Some(code) = oracle_policy_reject(context, pre_state, command, &account) {
        return reject(code, pre_state);
    }
    let account = match post_account(pre_state, command, account) {
        Ok(value) => value,
        Err(code) => return reject(code, pre_state),
    };
    let post_state = post_state(pre_state, account)?;
    accept(context, pre_state, post_state, command)
}
