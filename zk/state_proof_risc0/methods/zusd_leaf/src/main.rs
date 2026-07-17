#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use tau_state_proof_risc0_shared::{
    compose_zusd_recursive_leaf_summary_v1, ZusdOperationV1, ZusdRecursiveLeafInputV1,
    ZusdTransitionInputV1, RECURSIVE_ZUSD_LEAF_MAX_INPUT_BYTES,
};

const ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS: u32 = 11_000;

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > RECURSIVE_ZUSD_LEAF_MAX_INPUT_BYTES {
        abort("recursive zUSD leaf input length unsupported");
    }
    let mut input_bytes = vec![0u8; input_len as usize];
    env::read_slice(&mut input_bytes);
    let input: ZusdRecursiveLeafInputV1 = match postcard::from_bytes(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("failed to decode recursive zUSD leaf input"),
    };
    if let Err(error) = validate_zusd_recursive_baseline_input_v1(&input) {
        abort(error);
    }
    let summary = match compose_zusd_recursive_leaf_summary_v1(input) {
        Ok(value) => value,
        Err(_) => abort("recursive zUSD leaf transition rejected"),
    };
    let journal_bytes = match postcard::to_allocvec(&summary) {
        Ok(value) => value,
        Err(_) => abort("failed to encode recursive zUSD leaf journal"),
    };
    env::commit_slice(&journal_bytes);
}

fn validate_zusd_recursive_baseline_input_v1(
    input: &ZusdRecursiveLeafInputV1,
) -> Result<(), &'static str> {
    validate_zusd_scoped_snapshot_conservation_v1(&input.zusd_input)?;
    if !input.zusd_input.pre_app_hash_present {
        return Err("zUSD recursive leaf requires pre_app_hash");
    }
    let mcr_bps = match &input.zusd_input.operation {
        ZusdOperationV1::DepositMint { mcr_bps, .. } => *mcr_bps,
    };
    if mcr_bps != ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS {
        return Err("zUSD recursive leaf requires baseline MCR 11000");
    }
    Ok(())
}

fn validate_zusd_scoped_snapshot_conservation_v1(
    input: &ZusdTransitionInputV1,
) -> Result<(), &'static str> {
    if input.pre_state.version != 1 {
        return Err("unsupported zusd snapshot version");
    }

    let vault_debt = input.pre_state.vaults.iter().try_fold(0u128, |total, vault| {
        total.checked_add(vault.debt_zusd_e8).ok_or("debt overflow")
    })?;
    if vault_debt != input.pre_state.total_debt_zusd_e8 {
        return Err("zusd total debt mismatch");
    }

    let balance_supply = input
        .pre_state
        .balances
        .iter()
        .try_fold(0u128, |total, balance| {
            total
                .checked_add(balance.amount_e8)
                .ok_or("zusd balance supply overflow")
        })?;
    if balance_supply != input.pre_state.total_debt_zusd_e8 {
        return Err("zusd balance supply mismatch");
    }

    Ok(())
}
