use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{CommitmentV3, MAX_VALUE_TRANSFER_ACTION_INDEX_V2};

use crate::row::ZusdValueFlowRowInputV1;
use crate::{
    ZusdValueEffectKindV1, ZusdValueFlowContextV1, ZusdValueFlowErrorV1, ZusdValueFlowRowV1,
    ZusdValueOperationInputV1, ZusdValueOperationV1, MAX_ZUSD_AMOUNT_ATOMS_V1, ZUSD_BPS_SCALE_V1,
};

const E8_V1: u128 = 100_000_000;

pub(crate) fn expected_rows_v1(
    context: ZusdValueFlowContextV1,
    operations: &[ZusdValueOperationV1],
) -> Result<Vec<ZusdValueFlowRowV1>, ZusdValueFlowErrorV1> {
    let capacity = operations
        .len()
        .checked_mul(4)
        .ok_or(ZusdValueFlowErrorV1::ConservationOverflow)?;
    let mut rows = Vec::with_capacity(capacity);
    for operation in operations {
        operation.validate_self_consistency()?;
        validate_operation_context(context, operation)?;
        append_operation_rows(context, operation, &mut rows)?;
    }
    rows.sort_by_key(|row| (row.action_index(), row.leg_index()));
    require_conservation_v1(&rows)?;
    Ok(rows)
}

pub(crate) fn require_conservation_v1(
    rows: &[ZusdValueFlowRowV1],
) -> Result<(), ZusdValueFlowErrorV1> {
    let mut totals = BTreeMap::<CommitmentV3, [u128; 4]>::new();
    for row in rows {
        row.validate_self_consistency()?;
        let total = totals.entry(row.asset_id()).or_insert([0; 4]);
        for (slot, value) in total.iter_mut().zip([
            row.debit_atoms(),
            row.credit_atoms(),
            row.authorized_mint_atoms(),
            row.authorized_burn_atoms(),
        ]) {
            *slot = slot
                .checked_add(value)
                .ok_or(ZusdValueFlowErrorV1::ConservationOverflow)?;
        }
    }
    for [debit, credit, mint, burn] in totals.into_values() {
        let left = debit
            .checked_add(mint)
            .ok_or(ZusdValueFlowErrorV1::ConservationOverflow)?;
        let right = credit
            .checked_add(burn)
            .ok_or(ZusdValueFlowErrorV1::ConservationOverflow)?;
        if left != right {
            return Err(ZusdValueFlowErrorV1::ConservationMismatch);
        }
    }
    Ok(())
}

fn append_operation_rows(
    context: ZusdValueFlowContextV1,
    operation: &ZusdValueOperationV1,
    rows: &mut Vec<ZusdValueFlowRowV1>,
) -> Result<(), ZusdValueFlowErrorV1> {
    let operation_id = operation.canonical_id()?;
    match operation.input() {
        ZusdValueOperationInputV1::DepositCollateral {
            depositor_scope_id,
            vault_scope_id,
            collateral_atoms,
            ..
        } => append_pair(
            rows,
            operation,
            operation_id,
            context.collateral_asset_id(),
            *depositor_scope_id,
            *vault_scope_id,
            *collateral_atoms,
        ),
        ZusdValueOperationInputV1::WithdrawCollateral {
            recipient_scope_id,
            vault_scope_id,
            collateral_atoms,
            ..
        } => append_pair(
            rows,
            operation,
            operation_id,
            context.collateral_asset_id(),
            *vault_scope_id,
            *recipient_scope_id,
            *collateral_atoms,
        ),
        ZusdValueOperationInputV1::MintZusd {
            recipient_scope_id,
            principal_atoms,
            fee_bps,
            ..
        } => append_mint_rows(
            context,
            operation,
            operation_id,
            *recipient_scope_id,
            *principal_atoms,
            *fee_bps,
            rows,
        ),
        ZusdValueOperationInputV1::RepayBurn {
            payer_scope_id,
            zusd_atoms,
            ..
        } => push_row(
            rows,
            operation,
            operation_id,
            0,
            ZusdValueEffectKindV1::AuthorizedBurnDebit,
            context.zusd_asset_id(),
            *payer_scope_id,
            *zusd_atoms,
            Some(context.burn_authority_scope_id()),
        ),
        ZusdValueOperationInputV1::StabilityPoolDeposit {
            depositor_scope_id,
            zusd_atoms,
            ..
        } => append_pair(
            rows,
            operation,
            operation_id,
            context.zusd_asset_id(),
            *depositor_scope_id,
            context.stability_pool_scope_id(),
            *zusd_atoms,
        ),
        ZusdValueOperationInputV1::StabilityPoolWithdraw {
            recipient_scope_id,
            zusd_atoms,
            ..
        } => append_pair(
            rows,
            operation,
            operation_id,
            context.zusd_asset_id(),
            context.stability_pool_scope_id(),
            *recipient_scope_id,
            *zusd_atoms,
        ),
        ZusdValueOperationInputV1::RedeemZusd {
            redeemer_scope_id,
            vault_scope_id,
            zusd_atoms,
            oracle_price_e8,
            redemption_fee_bps,
            ..
        } => append_redeem_rows(
            context,
            operation,
            operation_id,
            *redeemer_scope_id,
            *vault_scope_id,
            *zusd_atoms,
            *oracle_price_e8,
            *redemption_fee_bps,
            rows,
        ),
        ZusdValueOperationInputV1::Liquidate {
            vault_scope_id,
            liquidator_scope_id,
            debt_zusd_atoms,
            collateral_atoms,
            gas_comp_fixed_collateral_atoms,
            gas_comp_bps,
            ..
        } => append_liquidation_rows(
            context,
            operation,
            operation_id,
            *vault_scope_id,
            *liquidator_scope_id,
            *debt_zusd_atoms,
            *collateral_atoms,
            *gas_comp_fixed_collateral_atoms,
            *gas_comp_bps,
            rows,
        ),
    }
}

fn append_pair(
    rows: &mut Vec<ZusdValueFlowRowV1>,
    operation: &ZusdValueOperationV1,
    operation_id: CommitmentV3,
    asset_id: CommitmentV3,
    debit_scope_id: CommitmentV3,
    credit_scope_id: CommitmentV3,
    amount: u128,
) -> Result<(), ZusdValueFlowErrorV1> {
    push_row(
        rows,
        operation,
        operation_id,
        0,
        ZusdValueEffectKindV1::OrdinaryDebit,
        asset_id,
        debit_scope_id,
        amount,
        None,
    )?;
    push_row(
        rows,
        operation,
        operation_id,
        1,
        ZusdValueEffectKindV1::OrdinaryCredit,
        asset_id,
        credit_scope_id,
        amount,
        None,
    )
}

fn append_mint_rows(
    context: ZusdValueFlowContextV1,
    operation: &ZusdValueOperationV1,
    operation_id: CommitmentV3,
    recipient_scope_id: CommitmentV3,
    principal_atoms: u128,
    fee_bps: u16,
    rows: &mut Vec<ZusdValueFlowRowV1>,
) -> Result<(), ZusdValueFlowErrorV1> {
    let action_index = operation.action_index();
    let fee_atoms = mul_div_up(action_index, principal_atoms, fee_bps, "mint_fee")?;
    let total =
        principal_atoms
            .checked_add(fee_atoms)
            .ok_or(ZusdValueFlowErrorV1::ArithmeticOverflow {
                action_index,
                field: "mint_total",
            })?;
    require_derived_bound(action_index, "mint_total", total)?;
    push_row(
        rows,
        operation,
        operation_id,
        0,
        ZusdValueEffectKindV1::AuthorizedMintCredit,
        context.zusd_asset_id(),
        recipient_scope_id,
        principal_atoms,
        Some(context.mint_authority_scope_id()),
    )?;
    if fee_atoms == 0 {
        return Ok(());
    }
    push_row(
        rows,
        operation,
        operation_id,
        1,
        ZusdValueEffectKindV1::AuthorizedMintCredit,
        context.zusd_asset_id(),
        context.protocol_scope_id(),
        fee_atoms,
        Some(context.mint_authority_scope_id()),
    )
}

#[allow(clippy::too_many_arguments)]
fn append_redeem_rows(
    context: ZusdValueFlowContextV1,
    operation: &ZusdValueOperationV1,
    operation_id: CommitmentV3,
    redeemer_scope_id: CommitmentV3,
    vault_scope_id: CommitmentV3,
    zusd_atoms: u128,
    oracle_price_e8: u128,
    redemption_fee_bps: u16,
    rows: &mut Vec<ZusdValueFlowRowV1>,
) -> Result<(), ZusdValueFlowErrorV1> {
    let action_index = operation.action_index();
    let gross = zusd_atoms
        .checked_mul(E8_V1)
        .ok_or(ZusdValueFlowErrorV1::ArithmeticOverflow {
            action_index,
            field: "redemption_gross_product",
        })?
        / oracle_price_e8;
    if gross == 0 {
        return Err(ZusdValueFlowErrorV1::GrossCollateralZero { action_index });
    }
    require_derived_bound(action_index, "redemption_gross", gross)?;
    let fee = mul_div_up(action_index, gross, redemption_fee_bps, "redemption_fee")?;
    if fee >= gross {
        return Err(ZusdValueFlowErrorV1::FeeConsumesCollateral { action_index });
    }
    let collateral_out = gross - fee;
    push_row(
        rows,
        operation,
        operation_id,
        0,
        ZusdValueEffectKindV1::AuthorizedBurnDebit,
        context.zusd_asset_id(),
        redeemer_scope_id,
        zusd_atoms,
        Some(context.burn_authority_scope_id()),
    )?;
    push_row(
        rows,
        operation,
        operation_id,
        1,
        ZusdValueEffectKindV1::OrdinaryDebit,
        context.collateral_asset_id(),
        vault_scope_id,
        gross,
        None,
    )?;
    push_row(
        rows,
        operation,
        operation_id,
        2,
        ZusdValueEffectKindV1::OrdinaryCredit,
        context.collateral_asset_id(),
        redeemer_scope_id,
        collateral_out,
        None,
    )?;
    if fee == 0 {
        return Ok(());
    }
    push_row(
        rows,
        operation,
        operation_id,
        3,
        ZusdValueEffectKindV1::OrdinaryCredit,
        context.collateral_asset_id(),
        context.protocol_scope_id(),
        fee,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn append_liquidation_rows(
    context: ZusdValueFlowContextV1,
    operation: &ZusdValueOperationV1,
    operation_id: CommitmentV3,
    vault_scope_id: CommitmentV3,
    liquidator_scope_id: CommitmentV3,
    debt_zusd_atoms: u128,
    collateral_atoms: u128,
    fixed_compensation: u128,
    compensation_bps: u16,
    rows: &mut Vec<ZusdValueFlowRowV1>,
) -> Result<(), ZusdValueFlowErrorV1> {
    let action_index = operation.action_index();
    let variable = mul_div_up(
        action_index,
        collateral_atoms,
        compensation_bps,
        "liquidation_variable_compensation",
    )?;
    let requested = fixed_compensation.checked_add(variable).ok_or(
        ZusdValueFlowErrorV1::ArithmeticOverflow {
            action_index,
            field: "liquidation_requested_compensation",
        },
    )?;
    let liquidator_compensation = collateral_atoms.min(requested);
    let stability_pool_gain = collateral_atoms - liquidator_compensation;
    push_row(
        rows,
        operation,
        operation_id,
        0,
        ZusdValueEffectKindV1::AuthorizedBurnDebit,
        context.zusd_asset_id(),
        context.stability_pool_scope_id(),
        debt_zusd_atoms,
        Some(context.burn_authority_scope_id()),
    )?;
    push_row(
        rows,
        operation,
        operation_id,
        1,
        ZusdValueEffectKindV1::OrdinaryDebit,
        context.collateral_asset_id(),
        vault_scope_id,
        collateral_atoms,
        None,
    )?;
    if stability_pool_gain > 0 {
        push_row(
            rows,
            operation,
            operation_id,
            2,
            ZusdValueEffectKindV1::OrdinaryCredit,
            context.collateral_asset_id(),
            context.stability_pool_scope_id(),
            stability_pool_gain,
            None,
        )?;
    }
    if liquidator_compensation == 0 {
        return Ok(());
    }
    push_row(
        rows,
        operation,
        operation_id,
        3,
        ZusdValueEffectKindV1::OrdinaryCredit,
        context.collateral_asset_id(),
        liquidator_scope_id,
        liquidator_compensation,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn push_row(
    rows: &mut Vec<ZusdValueFlowRowV1>,
    operation: &ZusdValueOperationV1,
    operation_id: CommitmentV3,
    leg_index: u8,
    effect_kind: ZusdValueEffectKindV1,
    asset_id: CommitmentV3,
    account_scope_id: CommitmentV3,
    amount_atoms: u128,
    authority_scope_id: Option<CommitmentV3>,
) -> Result<(), ZusdValueFlowErrorV1> {
    rows.push(ZusdValueFlowRowV1::new(ZusdValueFlowRowInputV1 {
        operation_id,
        action_index: operation.action_index(),
        leg_index,
        operation_kind: operation.kind(),
        effect_kind,
        asset_id,
        account_scope_id,
        amount_atoms,
        authority_scope_id,
    })?);
    Ok(())
}

fn mul_div_up(
    action_index: u32,
    amount: u128,
    bps: u16,
    field: &'static str,
) -> Result<u128, ZusdValueFlowErrorV1> {
    if bps == 0 {
        return Ok(0);
    }
    let product =
        amount
            .checked_mul(u128::from(bps))
            .ok_or(ZusdValueFlowErrorV1::ArithmeticOverflow {
                action_index,
                field,
            })?;
    let rounded = product
        .checked_add(u128::from(ZUSD_BPS_SCALE_V1) - 1)
        .ok_or(ZusdValueFlowErrorV1::ArithmeticOverflow {
            action_index,
            field,
        })?
        / u128::from(ZUSD_BPS_SCALE_V1);
    require_derived_bound(action_index, field, rounded)?;
    Ok(rounded)
}

fn require_derived_bound(
    action_index: u32,
    field: &'static str,
    value: u128,
) -> Result<(), ZusdValueFlowErrorV1> {
    if value > MAX_ZUSD_AMOUNT_ATOMS_V1 {
        return Err(ZusdValueFlowErrorV1::AmountOutOfRange {
            action_index,
            field,
        });
    }
    Ok(())
}

pub(crate) fn validate_operation_context(
    context: ZusdValueFlowContextV1,
    operation: &ZusdValueOperationV1,
) -> Result<(), ZusdValueFlowErrorV1> {
    let action_index = operation.action_index();
    if action_index > MAX_VALUE_TRANSFER_ACTION_INDEX_V2 {
        return Err(ZusdValueFlowErrorV1::ActionIndexOutOfRange {
            actual: action_index,
            maximum: MAX_VALUE_TRANSFER_ACTION_INDEX_V2,
        });
    }
    for scope in external_scopes(operation).into_iter().flatten() {
        if scope == context.stability_pool_scope_id() || scope == context.protocol_scope_id() {
            return Err(ZusdValueFlowErrorV1::ScopeAlias { action_index });
        }
    }
    Ok(())
}

fn external_scopes(operation: &ZusdValueOperationV1) -> [Option<CommitmentV3>; 2] {
    match operation.input() {
        ZusdValueOperationInputV1::DepositCollateral {
            depositor_scope_id,
            vault_scope_id,
            ..
        } => [Some(*depositor_scope_id), Some(*vault_scope_id)],
        ZusdValueOperationInputV1::WithdrawCollateral {
            recipient_scope_id,
            vault_scope_id,
            ..
        } => [Some(*recipient_scope_id), Some(*vault_scope_id)],
        ZusdValueOperationInputV1::MintZusd {
            recipient_scope_id,
            vault_scope_id,
            ..
        } => [Some(*recipient_scope_id), Some(*vault_scope_id)],
        ZusdValueOperationInputV1::RepayBurn {
            payer_scope_id,
            vault_scope_id,
            ..
        } => [Some(*payer_scope_id), Some(*vault_scope_id)],
        ZusdValueOperationInputV1::StabilityPoolDeposit {
            depositor_scope_id, ..
        } => [Some(*depositor_scope_id), None],
        ZusdValueOperationInputV1::StabilityPoolWithdraw {
            recipient_scope_id, ..
        } => [Some(*recipient_scope_id), None],
        ZusdValueOperationInputV1::RedeemZusd {
            redeemer_scope_id,
            vault_scope_id,
            ..
        } => [Some(*redeemer_scope_id), Some(*vault_scope_id)],
        ZusdValueOperationInputV1::Liquidate {
            vault_scope_id,
            liquidator_scope_id,
            ..
        } => [Some(*vault_scope_id), Some(*liquidator_scope_id)],
    }
}
