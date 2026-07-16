extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{TransitionError, PROOF_TYPE_ZUSD};

pub const PROOF_TYPE_ZUSD_RUNTIME_MINT_PROJECTION_V1: &str =
    "risc0.zenodex_zusd_runtime_mint_projection.v1";
pub const ZUSD_RUNTIME_MINT_PROJECTION_VERSION_V1: u32 = 1;

const E8: u128 = 100_000_000;
const BPS_SCALE: u128 = 10_000;
const FEE_ACC_SCALE: u128 = 1_000_000;
const MAX_AMOUNT_E8: u128 = 1_000_000_000_000_000_000_000_000_000_000;
const MAX_FEE_ACCOUNTS: usize = 4_096;
const LIQUITY_V1_MCR_BPS: u32 = 11_000;
const LIQUITY_V1_CCR_BPS: u32 = 15_000;
const LIQUITY_V1_MIN_DEBT_OPEN_E8: u128 = 1_800 * E8;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ZusdRuntimeRedemptionProfileProjectionV1 {
    #[serde(rename = "zenodex/zusd-liquity-v1-minimum")]
    LiquityV1Minimum,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ZusdRuntimeShutdownExtensionProfileProjectionV1 {
    #[serde(rename = "zenodex/zusd-terminal-freeze-v1")]
    TerminalFreezeV1,
}

/// Optional shutdown state is a separate sum from the baseline core.
///
/// The open variant cannot carry a stale frozen snapshot. The frozen variant
/// is representable for cross-layer decoding, while mint validation rejects it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "phase", deny_unknown_fields)]
pub enum ZusdRuntimeShutdownExtensionProjectionV1 {
    #[serde(rename = "OPEN")]
    Open {
        profile: ZusdRuntimeShutdownExtensionProfileProjectionV1,
    },
    #[serde(rename = "FROZEN")]
    Frozen {
        profile: ZusdRuntimeShutdownExtensionProfileProjectionV1,
        epoch: u128,
        oracle_observed_epoch: u128,
        price_e8: u128,
        collateral_e8: u128,
        debt_e8: u128,
        source_state_root: [u8; 32],
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeMintAuthorityProjectionV1 {
    pub protocol_fee_recipient_pubkey: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeMintPolicyProjectionV1 {
    pub redemption_profile: ZusdRuntimeRedemptionProfileProjectionV1,
    pub shutdown_extension_profile: Option<ZusdRuntimeShutdownExtensionProfileProjectionV1>,
    pub mcr_bps: u32,
    pub ccr_bps: u32,
    pub min_debt_open_e8: u128,
    pub max_debt_e8: u128,
    pub max_debt_supply_e8: u128,
    pub max_oracle_staleness_epochs: u128,
    pub base_rate_decay_per_epoch_bps: u32,
    pub base_rate_borrow_bump_bps: u32,
    pub borrow_fee_floor_bps: u32,
    pub borrow_fee_max_bps: u32,
    pub host_protocol_fee_share_bps: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeMintCoreProjectionV1 {
    pub now_epoch: u128,
    pub oracle_seen: bool,
    pub oracle_last_update_epoch: u128,
    pub oracle_pending_update_epoch: u128,
    pub price_e8: u128,
    pub price_pending_e8: u128,
    pub max_oracle_staleness_epochs: u128,
    pub collateral_e8: u128,
    pub debt_e8: u128,
    pub free_debt_e8: u128,
    pub sp_debt_e8: u128,
    pub sp_coll_e8: u128,
    pub protocol_collateral_e8: u128,
    pub protocol_revenue_zusd_cum_e8: u128,
    pub liquidator_compensation_collateral_cum_e8: u128,
    pub epoch_redemption_used_e8: u128,
    pub mcr_bps: u32,
    pub ccr_bps: u32,
    pub min_debt_open_e8: u128,
    pub max_debt_e8: u128,
    pub max_debt_supply_e8: u128,
    pub base_rate_bps: u32,
    pub base_rate_last_epoch: u128,
    pub base_rate_decay_per_epoch_bps: u32,
    pub base_rate_borrow_bump_bps: u32,
    pub borrow_fee_floor_bps: u32,
    pub borrow_fee_max_bps: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeFeeStakeEntryV1 {
    pub pubkey: String,
    pub active_shares: u128,
    pub reward_debt_e8: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeHostFeeEntryV1 {
    pub pubkey: String,
    pub amount_e8: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeMintFeeProjectionV1 {
    pub protocol_zusd_fee_reserve_e8: u128,
    pub staking_zusd_fee_pool_e8: u128,
    pub staking_zusd_fee_acc_per_share_e8: u128,
    pub host_zusd_fee_pool_e8: u128,
    pub host_zusd_fee_cum_e8: u128,
    pub host_fee_claims: Vec<ZusdRuntimeHostFeeEntryV1>,
    pub active_fee_stakes: Vec<ZusdRuntimeFeeStakeEntryV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeMintLiabilityProjectionV1 {
    pub actor_external_balance_units: u128,
    pub stability_pool_escrow_balance_units: u128,
    pub external_free_liability_e8: u128,
    pub perps_zusd_liability_e8: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeMintStateProjectionV1 {
    pub vault_owner_pubkey: String,
    pub actor_monetary_nonce: u32,
    pub shutdown_extension: Option<ZusdRuntimeShutdownExtensionProjectionV1>,
    pub core: ZusdRuntimeMintCoreProjectionV1,
    pub fees: ZusdRuntimeMintFeeProjectionV1,
    pub liabilities: ZusdRuntimeMintLiabilityProjectionV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeMintOperationProjectionV1 {
    pub module: String,
    pub operation_version: String,
    pub action: String,
    pub actor_pubkey: String,
    pub principal_e8: u128,
    pub nonce_before: u32,
    pub nonce_after: u32,
    pub deadline: u32,
    pub block_timestamp: u32,
    pub host_pubkey: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
/// A bounded single-vault projection supplied to the deterministic checker.
///
/// The `expected_*` hashes add authority only when an outer verifier obtains
/// them independently from a trusted commitment. Supplying this entire value
/// from one untrusted source proves internal equality, not external state
/// authenticity.
pub struct ZusdRuntimeMintProjectionInputV1 {
    pub projection_version: u32,
    pub chain_id: String,
    pub zusd_asset_id: String,
    pub actor_pubkey: String,
    pub expected_context_projection_hash: [u8; 32],
    pub expected_policy_projection_hash: [u8; 32],
    pub expected_authority_projection_hash: [u8; 32],
    pub expected_operation_projection_hash: [u8; 32],
    pub expected_pre_projection_hash: [u8; 32],
    pub expected_post_projection_hash: [u8; 32],
    pub policy: ZusdRuntimeMintPolicyProjectionV1,
    pub authority: ZusdRuntimeMintAuthorityProjectionV1,
    pub operation: ZusdRuntimeMintOperationProjectionV1,
    pub pre: ZusdRuntimeMintStateProjectionV1,
    pub claimed_post: ZusdRuntimeMintStateProjectionV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ZusdRuntimeMintProjectionJournalV1 {
    pub journal_version: u32,
    pub proof_type: String,
    pub chain_id: String,
    pub zusd_asset_id: String,
    pub actor_pubkey: String,
    pub context_projection_hash: [u8; 32],
    pub policy_projection_hash: [u8; 32],
    pub authority_projection_hash: [u8; 32],
    pub operation_projection_hash: [u8; 32],
    pub pre_projection_hash: [u8; 32],
    pub post_projection_hash: [u8; 32],
    pub nonce_before: u32,
    pub nonce_after: u32,
    pub principal_e8: u128,
    pub mint_fee_e8: u128,
    pub debt_delta_e8: u128,
    pub external_supply_delta_e8: u128,
    pub internal_fee_liability_delta_e8: u128,
    pub collateral_e8: u128,
    pub active_price_e8: u128,
    pub governed_mcr_bps: u32,
}

struct VerifiedMintDeltasV1 {
    mint_fee_e8: u128,
    debt_delta_e8: u128,
    external_supply_delta_e8: u128,
    internal_fee_liability_delta_e8: u128,
}

#[derive(Clone, Copy)]
struct FeeRouteAvailabilityV1 {
    host_present: bool,
    active_stake_total: u128,
    protocol_fee_recipient_available: bool,
}

#[derive(Clone, Copy)]
struct FeeRouteAmountsV1 {
    host_e8: u128,
    staking_e8: u128,
    protocol_e8: u128,
}

/// Reject proof-family substitution at the typed projection boundary.
///
/// The existing v1 zUSD proof combines a collateral deposit with a principal
/// mint. The mounted runtime `mint_zusd` transition leaves collateral fixed and
/// adds fee debt, so the two proof types are semantically distinct.
pub fn require_zusd_runtime_mint_projection_proof_type_v1(
    proof_type: &str,
) -> Result<(), TransitionError> {
    if proof_type == PROOF_TYPE_ZUSD_RUNTIME_MINT_PROJECTION_V1 {
        return Ok(());
    }
    if proof_type == PROOF_TYPE_ZUSD {
        return Err(TransitionError::Unsupported(
            "DepositMint v1 does not refine runtime mint_zusd",
        ));
    }
    Err(TransitionError::Unsupported(
        "unsupported zUSD runtime mint projection proof type",
    ))
}

/// Re-execute the bounded mint projection and construct its only admissible
/// projection journal.
///
/// This deterministic non-ZK checker proves equality only inside the typed
/// projection supplied here. It does not bind a complete Python monetary
/// state, a multi-vault state, Tau application root, RISC0 receipt, vault
/// opening, F21 gas reserve, CloseVault, RepayZUSD, F26 authorization, or F27
/// lockup provenance. It also does not authenticate caller-supplied expected
/// hashes. Those claims require independently trusted commitments, separate
/// versioned inputs, and cross-language parity evidence.
pub fn check_zusd_runtime_mint_projection_v1(
    input: &ZusdRuntimeMintProjectionInputV1,
) -> Result<ZusdRuntimeMintProjectionJournalV1, TransitionError> {
    validate_projection_header(input)?;
    validate_policy(&input.policy)?;
    validate_authority(&input.authority)?;
    validate_operation(&input.operation, &input.actor_pubkey)?;
    validate_state_projection(&input.pre, &input.policy)?;
    validate_pre_projection_hashes(input)?;

    let fee_bps = effective_borrow_fee_bps(&input.pre.core, &input.policy)?;
    let mint_fee_e8 = mul_div_up_bounded(
        input.operation.principal_e8,
        u128::from(fee_bps),
        BPS_SCALE,
        "runtime mint fee overflow",
    )?;
    let debt_delta_e8 = checked_add(
        input.operation.principal_e8,
        mint_fee_e8,
        "runtime mint debt delta overflow",
    )?;
    let expected_post = expected_post_projection(input, mint_fee_e8, debt_delta_e8)?;
    validate_claimed_post(&input.claimed_post, &expected_post)?;
    validate_state_projection(&expected_post, &input.policy)?;
    validate_post_projection_hash(input, &expected_post)?;

    let deltas = VerifiedMintDeltasV1 {
        mint_fee_e8,
        debt_delta_e8,
        external_supply_delta_e8: checked_sub(
            expected_post.liabilities.external_free_liability_e8,
            input.pre.liabilities.external_free_liability_e8,
            "runtime external supply delta underflow",
        )?,
        internal_fee_liability_delta_e8: checked_sub(
            total_internal_fee_liability(&expected_post.fees)?,
            total_internal_fee_liability(&input.pre.fees)?,
            "runtime internal fee liability delta underflow",
        )?,
    };
    if deltas.external_supply_delta_e8 != input.operation.principal_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime external supply delta mismatch",
        ));
    }
    if deltas.internal_fee_liability_delta_e8 != mint_fee_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime internal fee liability delta mismatch",
        ));
    }
    Ok(build_projection_journal(input, &expected_post, deltas))
}

fn validate_claimed_post(
    claimed: &ZusdRuntimeMintStateProjectionV1,
    expected: &ZusdRuntimeMintStateProjectionV1,
) -> Result<(), TransitionError> {
    if claimed.core != expected.core {
        return Err(TransitionError::InvalidInput(
            "runtime mint post core projection mismatch",
        ));
    }
    if claimed.fees != expected.fees {
        return Err(TransitionError::InvalidInput(
            "runtime mint post fee projection mismatch",
        ));
    }
    if claimed.liabilities != expected.liabilities {
        return Err(TransitionError::InvalidInput(
            "runtime mint post liability projection mismatch",
        ));
    }
    if claimed.shutdown_extension != expected.shutdown_extension {
        return Err(TransitionError::InvalidInput(
            "runtime mint post shutdown extension projection mismatch",
        ));
    }
    if claimed.vault_owner_pubkey != expected.vault_owner_pubkey
        || claimed.actor_monetary_nonce != expected.actor_monetary_nonce
    {
        return Err(TransitionError::InvalidInput(
            "runtime mint post authority projection mismatch",
        ));
    }
    Ok(())
}

fn build_projection_journal(
    input: &ZusdRuntimeMintProjectionInputV1,
    expected_post: &ZusdRuntimeMintStateProjectionV1,
    deltas: VerifiedMintDeltasV1,
) -> ZusdRuntimeMintProjectionJournalV1 {
    ZusdRuntimeMintProjectionJournalV1 {
        journal_version: ZUSD_RUNTIME_MINT_PROJECTION_VERSION_V1,
        proof_type: PROOF_TYPE_ZUSD_RUNTIME_MINT_PROJECTION_V1.into(),
        chain_id: input.chain_id.clone(),
        zusd_asset_id: input.zusd_asset_id.clone(),
        actor_pubkey: input.actor_pubkey.clone(),
        context_projection_hash: hash_context_projection_v1(input),
        policy_projection_hash: hash_policy_projection_v1(&input.policy),
        authority_projection_hash: hash_authority_projection_v1(&input.authority),
        operation_projection_hash: hash_operation_projection_v1(&input.operation),
        pre_projection_hash: hash_state_projection_v1(&input.pre),
        post_projection_hash: hash_state_projection_v1(expected_post),
        nonce_before: input.operation.nonce_before,
        nonce_after: input.operation.nonce_after,
        principal_e8: input.operation.principal_e8,
        mint_fee_e8: deltas.mint_fee_e8,
        debt_delta_e8: deltas.debt_delta_e8,
        external_supply_delta_e8: deltas.external_supply_delta_e8,
        internal_fee_liability_delta_e8: deltas.internal_fee_liability_delta_e8,
        collateral_e8: expected_post.core.collateral_e8,
        active_price_e8: expected_post.core.price_e8,
        governed_mcr_bps: input.policy.mcr_bps,
    }
}

fn validate_projection_header(
    input: &ZusdRuntimeMintProjectionInputV1,
) -> Result<(), TransitionError> {
    if input.projection_version != ZUSD_RUNTIME_MINT_PROJECTION_VERSION_V1 {
        return Err(TransitionError::Unsupported(
            "unsupported zUSD runtime mint projection version",
        ));
    }
    validate_chain_id(&input.chain_id)?;
    validate_fixed_hex(&input.zusd_asset_id, 32, "zUSD asset id noncanonical")?;
    if input.zusd_asset_id.as_bytes()[2..]
        .iter()
        .all(|byte| *byte == b'0')
    {
        return Err(TransitionError::InvalidInput("zUSD asset id is native"));
    }
    validate_fixed_hex(&input.actor_pubkey, 48, "actor pubkey noncanonical")?;
    if input.operation.actor_pubkey != input.actor_pubkey {
        return Err(TransitionError::InvalidInput(
            "runtime mint operation actor mismatch",
        ));
    }
    if input.pre.vault_owner_pubkey != input.actor_pubkey {
        return Err(TransitionError::InvalidInput(
            "runtime mint vault owner mismatch",
        ));
    }
    if input.pre.actor_monetary_nonce != input.operation.nonce_before {
        return Err(TransitionError::InvalidInput(
            "runtime mint pre nonce mismatch",
        ));
    }
    Ok(())
}

fn validate_pre_projection_hashes(
    input: &ZusdRuntimeMintProjectionInputV1,
) -> Result<(), TransitionError> {
    require_exact_projection_hash(
        input.expected_context_projection_hash,
        hash_context_projection_v1(input),
        "runtime mint context projection hash mismatch",
    )?;
    require_exact_projection_hash(
        input.expected_policy_projection_hash,
        hash_policy_projection_v1(&input.policy),
        "runtime mint policy projection hash mismatch",
    )?;
    require_exact_projection_hash(
        input.expected_authority_projection_hash,
        hash_authority_projection_v1(&input.authority),
        "runtime mint authority projection hash mismatch",
    )?;
    require_exact_projection_hash(
        input.expected_operation_projection_hash,
        hash_operation_projection_v1(&input.operation),
        "runtime mint operation projection hash mismatch",
    )?;
    require_exact_projection_hash(
        input.expected_pre_projection_hash,
        hash_state_projection_v1(&input.pre),
        "runtime mint pre projection hash mismatch",
    )
}

fn validate_post_projection_hash(
    input: &ZusdRuntimeMintProjectionInputV1,
    expected_post: &ZusdRuntimeMintStateProjectionV1,
) -> Result<(), TransitionError> {
    require_exact_projection_hash(
        input.expected_post_projection_hash,
        hash_state_projection_v1(expected_post),
        "runtime mint post projection hash mismatch",
    )?;
    if input.expected_pre_projection_hash == input.expected_post_projection_hash {
        return Err(TransitionError::InvalidInput(
            "runtime mint projection hashes unchanged",
        ));
    }
    Ok(())
}

fn require_exact_projection_hash(
    supplied: [u8; 32],
    recomputed: [u8; 32],
    message: &'static str,
) -> Result<(), TransitionError> {
    if supplied.iter().all(|byte| *byte == 0) || supplied != recomputed {
        return Err(TransitionError::InvalidInput(message));
    }
    Ok(())
}

fn validate_chain_id(chain_id: &str) -> Result<(), TransitionError> {
    if chain_id.is_empty() || chain_id.len() > 128 || !chain_id.is_ascii() {
        return Err(TransitionError::InvalidInput("chain id noncanonical"));
    }
    if !chain_id.bytes().all(|byte| {
        byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'.' | b'_' | b':' | b'/')
    }) {
        return Err(TransitionError::InvalidInput("chain id noncanonical"));
    }
    Ok(())
}

fn validate_fixed_hex(
    value: &str,
    byte_len: usize,
    error: &'static str,
) -> Result<(), TransitionError> {
    let expected_len = byte_len
        .checked_mul(2)
        .and_then(|value| value.checked_add(2))
        .ok_or(TransitionError::Arithmetic("hex length overflow"))?;
    if value.len() != expected_len || !value.starts_with("0x") {
        return Err(TransitionError::InvalidInput(error));
    }
    if !value.as_bytes()[2..]
        .iter()
        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(TransitionError::InvalidInput(error));
    }
    Ok(())
}

fn validate_policy(policy: &ZusdRuntimeMintPolicyProjectionV1) -> Result<(), TransitionError> {
    if policy.redemption_profile != ZusdRuntimeRedemptionProfileProjectionV1::LiquityV1Minimum
        || policy.mcr_bps != LIQUITY_V1_MCR_BPS
        || policy.ccr_bps != LIQUITY_V1_CCR_BPS
        || policy.min_debt_open_e8 != LIQUITY_V1_MIN_DEBT_OPEN_E8
    {
        return Err(TransitionError::InvalidInput(
            "runtime mint Liquity V1 baseline profile mismatch",
        ));
    }
    if policy.borrow_fee_floor_bps > policy.borrow_fee_max_bps
        || u128::from(policy.borrow_fee_max_bps) > BPS_SCALE
        || u128::from(policy.host_protocol_fee_share_bps) > BPS_SCALE
        || u128::from(policy.base_rate_decay_per_epoch_bps) > BPS_SCALE
        || u128::from(policy.base_rate_borrow_bump_bps) > BPS_SCALE
    {
        return Err(TransitionError::InvalidInput(
            "runtime mint fee policy invalid",
        ));
    }
    for value in [
        policy.min_debt_open_e8,
        policy.max_debt_e8,
        policy.max_debt_supply_e8,
        policy.max_oracle_staleness_epochs,
    ] {
        require_bounded(value, "runtime mint policy amount out of bounds")?;
    }
    if policy.max_debt_e8 > policy.max_debt_supply_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime mint debt caps invalid",
        ));
    }
    Ok(())
}

fn validate_authority(
    authority: &ZusdRuntimeMintAuthorityProjectionV1,
) -> Result<(), TransitionError> {
    if let Some(recipient) = &authority.protocol_fee_recipient_pubkey {
        validate_fixed_hex(recipient, 48, "runtime protocol fee recipient noncanonical")?;
    }
    Ok(())
}

fn validate_operation(
    operation: &ZusdRuntimeMintOperationProjectionV1,
    actor_pubkey: &str,
) -> Result<(), TransitionError> {
    if operation.module != "ZUSDFinance"
        || operation.operation_version != "0.1"
        || operation.action != "mint_zusd"
    {
        return Err(TransitionError::InvalidInput(
            "runtime mint operation vocabulary mismatch",
        ));
    }
    if operation.actor_pubkey != actor_pubkey {
        return Err(TransitionError::InvalidInput(
            "runtime mint operation actor mismatch",
        ));
    }
    require_bounded(
        operation.principal_e8,
        "runtime mint principal out of bounds",
    )?;
    if operation.principal_e8 == 0 || !operation.principal_e8.is_multiple_of(E8) {
        return Err(TransitionError::InvalidInput(
            "runtime mint principal must be whole positive zUSD",
        ));
    }
    let expected_nonce = operation
        .nonce_before
        .checked_add(1)
        .ok_or(TransitionError::Arithmetic("runtime mint nonce overflow"))?;
    if operation.nonce_after != expected_nonce {
        return Err(TransitionError::InvalidInput(
            "runtime mint nonce transition mismatch",
        ));
    }
    if operation.deadline == 0 || operation.block_timestamp > operation.deadline {
        return Err(TransitionError::InvalidInput(
            "runtime mint deadline expired",
        ));
    }
    if let Some(host) = &operation.host_pubkey {
        validate_fixed_hex(host, 48, "runtime mint host pubkey noncanonical")?;
    }
    Ok(())
}

fn validate_state_projection(
    state: &ZusdRuntimeMintStateProjectionV1,
    policy: &ZusdRuntimeMintPolicyProjectionV1,
) -> Result<(), TransitionError> {
    validate_fixed_hex(
        &state.vault_owner_pubkey,
        48,
        "runtime mint vault owner noncanonical",
    )?;
    validate_shutdown_extension(state.shutdown_extension.as_ref(), policy)?;
    validate_core_projection(&state.core, policy)?;
    validate_fee_projection(&state.fees)?;
    validate_liability_projection(&state.liabilities)?;

    let internal = total_internal_fee_liability(&state.fees)?;
    let expected_free = checked_add(
        checked_add(
            state.liabilities.external_free_liability_e8,
            state.liabilities.perps_zusd_liability_e8,
            "runtime liability cover overflow",
        )?,
        internal,
        "runtime liability cover overflow",
    )?;
    if expected_free != state.core.free_debt_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime free debt liability cover mismatch",
        ));
    }

    let actor_balance_e8 = checked_mul(
        state.liabilities.actor_external_balance_units,
        E8,
        "runtime actor balance overflow",
    )?;
    if actor_balance_e8 > state.liabilities.external_free_liability_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime actor balance exceeds external free liability",
        ));
    }
    let escrow_e8 = checked_mul(
        state.liabilities.stability_pool_escrow_balance_units,
        E8,
        "runtime stability pool escrow overflow",
    )?;
    if escrow_e8 != state.core.sp_debt_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime stability pool escrow mismatch",
        ));
    }
    Ok(())
}

fn validate_shutdown_extension(
    extension: Option<&ZusdRuntimeShutdownExtensionProjectionV1>,
    policy: &ZusdRuntimeMintPolicyProjectionV1,
) -> Result<(), TransitionError> {
    match (policy.shutdown_extension_profile, extension) {
        (None, None) => Ok(()),
        (Some(expected), Some(ZusdRuntimeShutdownExtensionProjectionV1::Open { profile }))
            if expected == *profile =>
        {
            Ok(())
        }
        (_, Some(ZusdRuntimeShutdownExtensionProjectionV1::Frozen { .. })) => Err(
            TransitionError::InvalidInput("runtime mint blocked by shutdown extension"),
        ),
        _ => Err(TransitionError::InvalidInput(
            "runtime mint shutdown extension profile mismatch",
        )),
    }
}

fn validate_core_projection(
    core: &ZusdRuntimeMintCoreProjectionV1,
    policy: &ZusdRuntimeMintPolicyProjectionV1,
) -> Result<(), TransitionError> {
    validate_core_bounds(core)?;
    validate_core_policy_binding(core, policy)?;
    validate_core_mode_and_time(core)?;
    validate_core_accounting(core, policy)
}

fn validate_core_bounds(core: &ZusdRuntimeMintCoreProjectionV1) -> Result<(), TransitionError> {
    for value in [
        core.now_epoch,
        core.oracle_last_update_epoch,
        core.oracle_pending_update_epoch,
        core.price_e8,
        core.price_pending_e8,
        core.max_oracle_staleness_epochs,
        core.collateral_e8,
        core.debt_e8,
        core.free_debt_e8,
        core.sp_debt_e8,
        core.sp_coll_e8,
        core.protocol_collateral_e8,
        core.protocol_revenue_zusd_cum_e8,
        core.liquidator_compensation_collateral_cum_e8,
        core.epoch_redemption_used_e8,
        core.min_debt_open_e8,
        core.max_debt_e8,
        core.max_debt_supply_e8,
        core.base_rate_last_epoch,
    ] {
        require_bounded(value, "runtime mint core amount out of bounds")?;
    }
    if u128::from(core.base_rate_bps) > BPS_SCALE {
        return Err(TransitionError::InvalidInput(
            "runtime mint base rate out of bounds",
        ));
    }
    Ok(())
}

fn validate_core_policy_binding(
    core: &ZusdRuntimeMintCoreProjectionV1,
    policy: &ZusdRuntimeMintPolicyProjectionV1,
) -> Result<(), TransitionError> {
    let matches = core.mcr_bps == policy.mcr_bps
        && core.ccr_bps == policy.ccr_bps
        && core.min_debt_open_e8 == policy.min_debt_open_e8
        && core.max_debt_e8 == policy.max_debt_e8
        && core.max_debt_supply_e8 == policy.max_debt_supply_e8
        && core.max_oracle_staleness_epochs == policy.max_oracle_staleness_epochs
        && core.base_rate_decay_per_epoch_bps == policy.base_rate_decay_per_epoch_bps
        && core.base_rate_borrow_bump_bps == policy.base_rate_borrow_bump_bps
        && core.borrow_fee_floor_bps == policy.borrow_fee_floor_bps
        && core.borrow_fee_max_bps == policy.borrow_fee_max_bps;
    if !matches {
        return Err(TransitionError::InvalidInput(
            "runtime mint policy/core projection mismatch",
        ));
    }
    Ok(())
}

fn validate_core_mode_and_time(
    core: &ZusdRuntimeMintCoreProjectionV1,
) -> Result<(), TransitionError> {
    if !core.oracle_seen || core.price_e8 == 0 || core.price_pending_e8 == 0 {
        return Err(TransitionError::InvalidInput(
            "runtime mint oracle unavailable",
        ));
    }
    if core.price_pending_e8 > core.price_e8
        || core.oracle_last_update_epoch > core.oracle_pending_update_epoch
        || core.oracle_pending_update_epoch > core.now_epoch
        || core.base_rate_last_epoch > core.now_epoch
    {
        return Err(TransitionError::InvalidInput(
            "runtime mint temporal state invalid",
        ));
    }
    Ok(())
}

fn validate_core_accounting(
    core: &ZusdRuntimeMintCoreProjectionV1,
    policy: &ZusdRuntimeMintPolicyProjectionV1,
) -> Result<(), TransitionError> {
    let total_split = checked_add(
        core.free_debt_e8,
        core.sp_debt_e8,
        "runtime debt split overflow",
    )?;
    if total_split != core.debt_e8 {
        return Err(TransitionError::InvalidInput("runtime debt split mismatch"));
    }
    if core.debt_e8 == 0 {
        return Err(TransitionError::Unsupported(
            "runtime mint projection excludes vault opening and F21 reserve creation",
        ));
    }
    if core.debt_e8 < policy.min_debt_open_e8 {
        return Err(TransitionError::InvalidInput("runtime debt floor violated"));
    }
    if !ratio_ok(core.collateral_e8, core.debt_e8, core.price_e8, 10_000)? {
        return Err(TransitionError::InvalidInput(
            "runtime active vault bad debt projection",
        ));
    }
    let custody_collateral = checked_add(
        checked_add(
            core.collateral_e8,
            core.sp_coll_e8,
            "runtime custody collateral overflow",
        )?,
        core.protocol_collateral_e8,
        "runtime custody collateral overflow",
    )?;
    if !ratio_ok(custody_collateral, core.debt_e8, core.price_e8, 10_000)? {
        return Err(TransitionError::InvalidInput(
            "runtime system bad debt projection",
        ));
    }
    Ok(())
}

fn validate_fee_projection(fees: &ZusdRuntimeMintFeeProjectionV1) -> Result<(), TransitionError> {
    validate_fee_scalars(fees)?;
    validate_host_fee_claims(fees)?;
    validate_staking_fee_claims(fees)
}

fn validate_fee_scalars(fees: &ZusdRuntimeMintFeeProjectionV1) -> Result<(), TransitionError> {
    if fees.host_fee_claims.len() > MAX_FEE_ACCOUNTS
        || fees.active_fee_stakes.len() > MAX_FEE_ACCOUNTS
    {
        return Err(TransitionError::InvalidInput(
            "runtime fee account count exceeds bound",
        ));
    }
    for value in [
        fees.protocol_zusd_fee_reserve_e8,
        fees.staking_zusd_fee_pool_e8,
        fees.staking_zusd_fee_acc_per_share_e8,
        fees.host_zusd_fee_pool_e8,
        fees.host_zusd_fee_cum_e8,
    ] {
        require_bounded(value, "runtime mint fee state out of bounds")?;
    }
    for value in [
        fees.protocol_zusd_fee_reserve_e8,
        fees.staking_zusd_fee_pool_e8,
        fees.host_zusd_fee_pool_e8,
    ] {
        if !value.is_multiple_of(E8) {
            return Err(TransitionError::InvalidInput(
                "runtime fee pool not transport exact",
            ));
        }
    }
    if fees.host_zusd_fee_pool_e8 > fees.host_zusd_fee_cum_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime host fee pool exceeds cumulative fees",
        ));
    }
    Ok(())
}

fn validate_host_fee_claims(fees: &ZusdRuntimeMintFeeProjectionV1) -> Result<(), TransitionError> {
    let host_claims = host_claims_map(&fees.host_fee_claims)?;
    let host_claim_total = host_claims.values().try_fold(0u128, |acc, value| {
        if !value.is_multiple_of(E8) {
            return Err(TransitionError::InvalidInput(
                "runtime host fee claim not transport exact",
            ));
        }
        checked_add(acc, *value, "runtime host fee claim total overflow")
    })?;
    if host_claim_total != fees.host_zusd_fee_pool_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime host fee claims mismatch",
        ));
    }
    Ok(())
}

fn validate_staking_fee_claims(
    fees: &ZusdRuntimeMintFeeProjectionV1,
) -> Result<(), TransitionError> {
    let stakes = stake_map(&fees.active_fee_stakes)?;
    let claimable_total = stakes.values().try_fold(0u128, |acc, entry| {
        let accrued = checked_mul(
            entry.active_shares,
            fees.staking_zusd_fee_acc_per_share_e8,
            "runtime staking accrued overflow",
        )? / FEE_ACC_SCALE;
        let claimable = accrued.saturating_sub(entry.reward_debt_e8);
        if !claimable.is_multiple_of(E8) {
            return Err(TransitionError::InvalidInput(
                "runtime staking claim not transport exact",
            ));
        }
        checked_add(acc, claimable, "runtime staking claim total overflow")
    })?;
    if claimable_total != fees.staking_zusd_fee_pool_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime staking fee claims mismatch",
        ));
    }
    Ok(())
}

fn validate_liability_projection(
    liabilities: &ZusdRuntimeMintLiabilityProjectionV1,
) -> Result<(), TransitionError> {
    for value in [
        liabilities.actor_external_balance_units,
        liabilities.stability_pool_escrow_balance_units,
        liabilities.external_free_liability_e8,
        liabilities.perps_zusd_liability_e8,
    ] {
        require_bounded(value, "runtime mint liability out of bounds")?;
    }
    if !liabilities.external_free_liability_e8.is_multiple_of(E8) {
        return Err(TransitionError::InvalidInput(
            "runtime external liability not transport exact",
        ));
    }
    Ok(())
}

fn expected_post_projection(
    input: &ZusdRuntimeMintProjectionInputV1,
    mint_fee_e8: u128,
    debt_delta_e8: u128,
) -> Result<ZusdRuntimeMintStateProjectionV1, TransitionError> {
    let mut expected = input.pre.clone();
    expected.actor_monetary_nonce = input.operation.nonce_after;
    expected.core = expected_core_projection(input, mint_fee_e8, debt_delta_e8)?;
    expected.fees = expected_fee_projection(
        &input.pre.fees,
        &input.policy,
        &input.authority,
        input.operation.host_pubkey.as_deref(),
        mint_fee_e8,
    )?;
    expected.liabilities = expected_liability_projection(input)?;
    Ok(expected)
}

fn expected_core_projection(
    input: &ZusdRuntimeMintProjectionInputV1,
    mint_fee_e8: u128,
    debt_delta_e8: u128,
) -> Result<ZusdRuntimeMintCoreProjectionV1, TransitionError> {
    let pre = &input.pre.core;
    require_risky_mint_allowed(pre, &input.policy)?;
    let new_debt = checked_add(pre.debt_e8, debt_delta_e8, "runtime mint debt overflow")?;
    let new_free_debt = checked_add(
        pre.free_debt_e8,
        debt_delta_e8,
        "runtime mint free debt overflow",
    )?;
    if new_debt > input.policy.max_debt_e8 || new_free_debt > input.policy.max_debt_supply_e8 {
        return Err(TransitionError::InvalidInput(
            "runtime mint debt cap exceeded",
        ));
    }
    if !ratio_ok(
        pre.collateral_e8,
        new_debt,
        pre.price_e8,
        input.policy.mcr_bps,
    )? {
        return Err(TransitionError::InvalidInput(
            "runtime mint would violate MCR",
        ));
    }
    if !ratio_ok(
        pre.collateral_e8,
        new_debt,
        pre.price_e8,
        input.policy.ccr_bps,
    )? {
        return Err(TransitionError::InvalidInput(
            "runtime mint would violate CCR",
        ));
    }
    let mut expected = pre.clone();
    expected.debt_e8 = new_debt;
    expected.free_debt_e8 = new_free_debt;
    expected.protocol_revenue_zusd_cum_e8 = checked_add(
        pre.protocol_revenue_zusd_cum_e8,
        mint_fee_e8,
        "runtime protocol revenue overflow",
    )?;
    let decayed = decayed_base_rate_bps(pre, &input.policy)?;
    expected.base_rate_bps = core::cmp::min(
        10_000,
        decayed
            .checked_add(input.policy.base_rate_borrow_bump_bps)
            .ok_or(TransitionError::Arithmetic("runtime base rate overflow"))?,
    );
    expected.base_rate_last_epoch = pre.now_epoch;
    Ok(expected)
}

fn expected_liability_projection(
    input: &ZusdRuntimeMintProjectionInputV1,
) -> Result<ZusdRuntimeMintLiabilityProjectionV1, TransitionError> {
    let mut expected = input.pre.liabilities.clone();
    let principal_units = input.operation.principal_e8 / E8;
    expected.actor_external_balance_units = checked_add(
        expected.actor_external_balance_units,
        principal_units,
        "runtime actor balance overflow",
    )?;
    expected.external_free_liability_e8 = checked_add(
        expected.external_free_liability_e8,
        input.operation.principal_e8,
        "runtime external liability overflow",
    )?;
    Ok(expected)
}

fn expected_fee_projection(
    pre: &ZusdRuntimeMintFeeProjectionV1,
    policy: &ZusdRuntimeMintPolicyProjectionV1,
    authority: &ZusdRuntimeMintAuthorityProjectionV1,
    host_pubkey: Option<&str>,
    mint_fee_e8: u128,
) -> Result<ZusdRuntimeMintFeeProjectionV1, TransitionError> {
    let mut expected = pre.clone();
    if mint_fee_e8 == 0 {
        return Ok(expected);
    }

    let active_total = pre.active_fee_stakes.iter().try_fold(0u128, |acc, entry| {
        checked_add(
            acc,
            entry.active_shares,
            "runtime active stake total overflow",
        )
    })?;
    let route = split_mint_fee_routes(
        mint_fee_e8,
        policy.host_protocol_fee_share_bps,
        FeeRouteAvailabilityV1 {
            host_present: host_pubkey.is_some(),
            active_stake_total: active_total,
            protocol_fee_recipient_available: authority.protocol_fee_recipient_pubkey.is_some(),
        },
    )?;
    credit_host_fee(&mut expected, pre, host_pubkey, route.host_e8)?;
    credit_staking_fee(&mut expected, pre, route.staking_e8, active_total)?;
    credit_protocol_fee(&mut expected, pre, route.protocol_e8)?;
    Ok(expected)
}

fn credit_host_fee(
    expected: &mut ZusdRuntimeMintFeeProjectionV1,
    pre: &ZusdRuntimeMintFeeProjectionV1,
    host_pubkey: Option<&str>,
    host_fee_e8: u128,
) -> Result<(), TransitionError> {
    if host_fee_e8 == 0 {
        return Ok(());
    }
    let host = host_pubkey.ok_or(TransitionError::InvalidInput(
        "runtime host fee missing host",
    ))?;
    let mut claims = host_claims_map(&pre.host_fee_claims)?;
    let previous = claims.get(host).copied().unwrap_or(0);
    claims.insert(
        host.into(),
        checked_add(previous, host_fee_e8, "runtime host claim overflow")?,
    );
    expected.host_fee_claims = host_claims_from_map(claims);
    expected.host_zusd_fee_pool_e8 = checked_add(
        pre.host_zusd_fee_pool_e8,
        host_fee_e8,
        "runtime host fee pool overflow",
    )?;
    expected.host_zusd_fee_cum_e8 = checked_add(
        pre.host_zusd_fee_cum_e8,
        host_fee_e8,
        "runtime cumulative host fee overflow",
    )?;
    Ok(())
}

fn credit_staking_fee(
    expected: &mut ZusdRuntimeMintFeeProjectionV1,
    pre: &ZusdRuntimeMintFeeProjectionV1,
    staking_fee_e8: u128,
    active_stake_total: u128,
) -> Result<(), TransitionError> {
    if staking_fee_e8 == 0 {
        return Ok(());
    }
    expected.staking_zusd_fee_pool_e8 = checked_add(
        pre.staking_zusd_fee_pool_e8,
        staking_fee_e8,
        "runtime staking fee pool overflow",
    )?;
    let acc_delta = checked_mul(
        staking_fee_e8,
        FEE_ACC_SCALE,
        "runtime staking accumulator overflow",
    )? / active_stake_total;
    expected.staking_zusd_fee_acc_per_share_e8 = checked_add(
        pre.staking_zusd_fee_acc_per_share_e8,
        acc_delta,
        "runtime staking accumulator overflow",
    )?;
    Ok(())
}

fn credit_protocol_fee(
    expected: &mut ZusdRuntimeMintFeeProjectionV1,
    pre: &ZusdRuntimeMintFeeProjectionV1,
    protocol_fee_e8: u128,
) -> Result<(), TransitionError> {
    if protocol_fee_e8 == 0 {
        return Ok(());
    }
    expected.protocol_zusd_fee_reserve_e8 = checked_add(
        pre.protocol_zusd_fee_reserve_e8,
        protocol_fee_e8,
        "runtime protocol fee reserve overflow",
    )?;
    Ok(())
}

fn split_mint_fee_routes(
    mint_fee_e8: u128,
    host_protocol_fee_share_bps: u32,
    availability: FeeRouteAvailabilityV1,
) -> Result<FeeRouteAmountsV1, TransitionError> {
    if u128::from(host_protocol_fee_share_bps) > BPS_SCALE {
        return Err(TransitionError::InvalidInput(
            "runtime host fee share out of bounds",
        ));
    }
    let host_fee_e8 = if availability.host_present {
        checked_mul(
            mint_fee_e8,
            u128::from(host_protocol_fee_share_bps),
            "runtime host fee overflow",
        )? / BPS_SCALE
    } else {
        0
    };
    partition_mint_fee_routes(
        mint_fee_e8,
        host_fee_e8,
        availability.active_stake_total > 0,
        availability.protocol_fee_recipient_available,
    )
}

fn partition_mint_fee_routes(
    mint_fee_e8: u128,
    host_fee_e8: u128,
    active_stake_present: bool,
    protocol_fee_recipient_available: bool,
) -> Result<FeeRouteAmountsV1, TransitionError> {
    let non_host_fee_e8 = checked_sub(mint_fee_e8, host_fee_e8, "runtime non-host fee underflow")?;
    if active_stake_present && non_host_fee_e8 > 0 {
        return Ok(FeeRouteAmountsV1 {
            host_e8: host_fee_e8,
            staking_e8: non_host_fee_e8,
            protocol_e8: 0,
        });
    }
    if non_host_fee_e8 > 0 && !protocol_fee_recipient_available {
        return Err(TransitionError::InvalidInput(
            "runtime protocol fee recipient missing",
        ));
    }
    Ok(FeeRouteAmountsV1 {
        host_e8: host_fee_e8,
        staking_e8: 0,
        protocol_e8: non_host_fee_e8,
    })
}

fn require_risky_mint_allowed(
    core: &ZusdRuntimeMintCoreProjectionV1,
    policy: &ZusdRuntimeMintPolicyProjectionV1,
) -> Result<(), TransitionError> {
    if core.price_pending_e8 != core.price_e8
        || core.oracle_pending_update_epoch != core.oracle_last_update_epoch
    {
        return Err(TransitionError::InvalidInput(
            "runtime mint oracle pending state frozen",
        ));
    }
    let age = checked_sub(
        core.now_epoch,
        core.oracle_last_update_epoch,
        "runtime oracle epoch underflow",
    )?;
    if age > policy.max_oracle_staleness_epochs {
        return Err(TransitionError::InvalidInput("runtime mint oracle stale"));
    }
    if !ratio_ok(
        core.collateral_e8,
        core.debt_e8,
        core.price_e8,
        policy.ccr_bps,
    )? {
        return Err(TransitionError::InvalidInput(
            "runtime mint blocked by recovery mode",
        ));
    }
    Ok(())
}

fn effective_borrow_fee_bps(
    core: &ZusdRuntimeMintCoreProjectionV1,
    policy: &ZusdRuntimeMintPolicyProjectionV1,
) -> Result<u32, TransitionError> {
    let decayed = decayed_base_rate_bps(core, policy)?;
    let floor_plus_base =
        policy
            .borrow_fee_floor_bps
            .checked_add(decayed)
            .ok_or(TransitionError::Arithmetic(
                "runtime effective fee overflow",
            ))?;
    Ok(core::cmp::min(
        10_000,
        core::cmp::min(floor_plus_base, policy.borrow_fee_max_bps),
    ))
}

fn decayed_base_rate_bps(
    core: &ZusdRuntimeMintCoreProjectionV1,
    policy: &ZusdRuntimeMintPolicyProjectionV1,
) -> Result<u32, TransitionError> {
    let elapsed = checked_sub(
        core.now_epoch,
        core.base_rate_last_epoch,
        "runtime base rate epoch underflow",
    )?;
    let decay = match elapsed.checked_mul(u128::from(policy.base_rate_decay_per_epoch_bps)) {
        Some(value) => value,
        None => return Ok(0),
    };
    if decay >= u128::from(core.base_rate_bps) {
        Ok(0)
    } else {
        u32::try_from(u128::from(core.base_rate_bps) - decay)
            .map_err(|_| TransitionError::Arithmetic("runtime decayed base rate overflow"))
    }
}

fn ratio_ok(
    collateral_e8: u128,
    debt_e8: u128,
    price_e8: u128,
    ratio_bps: u32,
) -> Result<bool, TransitionError> {
    if debt_e8 == 0 {
        return Ok(true);
    }
    let lhs = checked_mul(
        checked_mul(collateral_e8, price_e8, "runtime collateral ratio overflow")?,
        BPS_SCALE,
        "runtime collateral ratio overflow",
    )?;
    let rhs = checked_mul(
        checked_mul(
            debt_e8,
            u128::from(ratio_bps),
            "runtime debt ratio overflow",
        )?,
        E8,
        "runtime debt ratio overflow",
    )?;
    Ok(lhs >= rhs)
}

fn mul_div_up_bounded(
    a: u128,
    b: u128,
    denominator: u128,
    message: &'static str,
) -> Result<u128, TransitionError> {
    if denominator == 0 {
        return Err(TransitionError::Arithmetic(message));
    }
    if a == 0 || b == 0 {
        return Ok(0);
    }
    let product = checked_mul(a, b, message)?;
    let adjusted = checked_add(product, denominator - 1, message)?;
    Ok(adjusted / denominator)
}

fn total_internal_fee_liability(
    fees: &ZusdRuntimeMintFeeProjectionV1,
) -> Result<u128, TransitionError> {
    checked_add(
        checked_add(
            fees.protocol_zusd_fee_reserve_e8,
            fees.staking_zusd_fee_pool_e8,
            "runtime internal fee liability overflow",
        )?,
        fees.host_zusd_fee_pool_e8,
        "runtime internal fee liability overflow",
    )
}

fn host_claims_map(
    entries: &[ZusdRuntimeHostFeeEntryV1],
) -> Result<BTreeMap<String, u128>, TransitionError> {
    let mut out = BTreeMap::new();
    let mut previous: Option<&str> = None;
    for entry in entries {
        validate_fixed_hex(&entry.pubkey, 48, "runtime host fee pubkey noncanonical")?;
        require_bounded(entry.amount_e8, "runtime host fee claim out of bounds")?;
        if entry.amount_e8 == 0 || previous.is_some_and(|value| value >= entry.pubkey.as_str()) {
            return Err(TransitionError::InvalidInput(
                "runtime host fee claims not canonical",
            ));
        }
        previous = Some(entry.pubkey.as_str());
        out.insert(entry.pubkey.clone(), entry.amount_e8);
    }
    Ok(out)
}

fn host_claims_from_map(entries: BTreeMap<String, u128>) -> Vec<ZusdRuntimeHostFeeEntryV1> {
    entries
        .into_iter()
        .filter_map(|(pubkey, amount_e8)| {
            (amount_e8 > 0).then_some(ZusdRuntimeHostFeeEntryV1 { pubkey, amount_e8 })
        })
        .collect()
}

fn stake_map(
    entries: &[ZusdRuntimeFeeStakeEntryV1],
) -> Result<BTreeMap<String, ZusdRuntimeFeeStakeEntryV1>, TransitionError> {
    let mut out = BTreeMap::new();
    let mut previous: Option<&str> = None;
    for entry in entries {
        validate_fixed_hex(&entry.pubkey, 48, "runtime fee stake pubkey noncanonical")?;
        require_bounded(
            entry.active_shares,
            "runtime active fee stake out of bounds",
        )?;
        require_bounded(
            entry.reward_debt_e8,
            "runtime fee reward debt out of bounds",
        )?;
        if entry.active_shares == 0 || previous.is_some_and(|value| value >= entry.pubkey.as_str())
        {
            return Err(TransitionError::InvalidInput(
                "runtime active fee stakes not canonical",
            ));
        }
        previous = Some(entry.pubkey.as_str());
        out.insert(entry.pubkey.clone(), entry.clone());
    }
    Ok(out)
}

fn require_bounded(value: u128, message: &'static str) -> Result<(), TransitionError> {
    if value > MAX_AMOUNT_E8 {
        return Err(TransitionError::InvalidInput(message));
    }
    Ok(())
}

fn checked_add(a: u128, b: u128, message: &'static str) -> Result<u128, TransitionError> {
    a.checked_add(b).ok_or(TransitionError::Arithmetic(message))
}

fn checked_sub(a: u128, b: u128, message: &'static str) -> Result<u128, TransitionError> {
    a.checked_sub(b).ok_or(TransitionError::Arithmetic(message))
}

fn checked_mul(a: u128, b: u128, message: &'static str) -> Result<u128, TransitionError> {
    a.checked_mul(b).ok_or(TransitionError::Arithmetic(message))
}

fn hash_context_projection_v1(input: &ZusdRuntimeMintProjectionInputV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zusd.runtime_mint.context_projection.v1:");
    write_u32(&mut hasher, input.projection_version);
    write_str(&mut hasher, &input.chain_id);
    write_str(&mut hasher, &input.zusd_asset_id);
    write_str(&mut hasher, &input.actor_pubkey);
    hasher.finalize().into()
}

fn hash_policy_projection_v1(policy: &ZusdRuntimeMintPolicyProjectionV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zusd.runtime_mint.policy_projection.v1:");
    hasher.update([match policy.redemption_profile {
        ZusdRuntimeRedemptionProfileProjectionV1::LiquityV1Minimum => 0,
    }]);
    match policy.shutdown_extension_profile {
        None => hasher.update([0]),
        Some(ZusdRuntimeShutdownExtensionProfileProjectionV1::TerminalFreezeV1) => {
            hasher.update([1])
        }
    }
    write_u32(&mut hasher, policy.mcr_bps);
    write_u32(&mut hasher, policy.ccr_bps);
    write_u128(&mut hasher, policy.min_debt_open_e8);
    write_u128(&mut hasher, policy.max_debt_e8);
    write_u128(&mut hasher, policy.max_debt_supply_e8);
    write_u128(&mut hasher, policy.max_oracle_staleness_epochs);
    write_u32(&mut hasher, policy.base_rate_decay_per_epoch_bps);
    write_u32(&mut hasher, policy.base_rate_borrow_bump_bps);
    write_u32(&mut hasher, policy.borrow_fee_floor_bps);
    write_u32(&mut hasher, policy.borrow_fee_max_bps);
    write_u32(&mut hasher, policy.host_protocol_fee_share_bps);
    hasher.finalize().into()
}

fn hash_authority_projection_v1(authority: &ZusdRuntimeMintAuthorityProjectionV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zusd.runtime_mint.authority_projection.v1:");
    write_optional_str(
        &mut hasher,
        authority.protocol_fee_recipient_pubkey.as_deref(),
    );
    hasher.finalize().into()
}

fn hash_operation_projection_v1(operation: &ZusdRuntimeMintOperationProjectionV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zusd.runtime_mint.operation_projection.v1:");
    write_str(&mut hasher, &operation.module);
    write_str(&mut hasher, &operation.operation_version);
    write_str(&mut hasher, &operation.action);
    write_str(&mut hasher, &operation.actor_pubkey);
    write_u128(&mut hasher, operation.principal_e8);
    write_u32(&mut hasher, operation.nonce_before);
    write_u32(&mut hasher, operation.nonce_after);
    write_u32(&mut hasher, operation.deadline);
    write_u32(&mut hasher, operation.block_timestamp);
    write_optional_str(&mut hasher, operation.host_pubkey.as_deref());
    hasher.finalize().into()
}

fn hash_state_projection_v1(state: &ZusdRuntimeMintStateProjectionV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.zusd.runtime_mint.state_projection.v1:");
    write_str(&mut hasher, &state.vault_owner_pubkey);
    write_u32(&mut hasher, state.actor_monetary_nonce);
    hash_shutdown_extension(&mut hasher, state.shutdown_extension.as_ref());
    hash_core(&mut hasher, &state.core);
    hash_fees(&mut hasher, &state.fees);
    write_u128(&mut hasher, state.liabilities.actor_external_balance_units);
    write_u128(
        &mut hasher,
        state.liabilities.stability_pool_escrow_balance_units,
    );
    write_u128(&mut hasher, state.liabilities.external_free_liability_e8);
    write_u128(&mut hasher, state.liabilities.perps_zusd_liability_e8);
    hasher.finalize().into()
}

fn hash_shutdown_extension(
    hasher: &mut Sha256,
    extension: Option<&ZusdRuntimeShutdownExtensionProjectionV1>,
) {
    match extension {
        None => hasher.update([0]),
        Some(ZusdRuntimeShutdownExtensionProjectionV1::Open { profile }) => {
            hasher.update([1]);
            hash_shutdown_profile(hasher, *profile);
        }
        Some(ZusdRuntimeShutdownExtensionProjectionV1::Frozen {
            profile,
            epoch,
            oracle_observed_epoch,
            price_e8,
            collateral_e8,
            debt_e8,
            source_state_root,
        }) => {
            hasher.update([2]);
            hash_shutdown_profile(hasher, *profile);
            write_u128(hasher, *epoch);
            write_u128(hasher, *oracle_observed_epoch);
            write_u128(hasher, *price_e8);
            write_u128(hasher, *collateral_e8);
            write_u128(hasher, *debt_e8);
            hasher.update(source_state_root);
        }
    }
}

fn hash_shutdown_profile(
    hasher: &mut Sha256,
    profile: ZusdRuntimeShutdownExtensionProfileProjectionV1,
) {
    hasher.update([match profile {
        ZusdRuntimeShutdownExtensionProfileProjectionV1::TerminalFreezeV1 => 0,
    }]);
}

fn hash_core(hasher: &mut Sha256, core: &ZusdRuntimeMintCoreProjectionV1) {
    write_u128(hasher, core.now_epoch);
    hasher.update([u8::from(core.oracle_seen)]);
    write_u128(hasher, core.oracle_last_update_epoch);
    write_u128(hasher, core.oracle_pending_update_epoch);
    write_u128(hasher, core.price_e8);
    write_u128(hasher, core.price_pending_e8);
    write_u128(hasher, core.max_oracle_staleness_epochs);
    write_u128(hasher, core.collateral_e8);
    write_u128(hasher, core.debt_e8);
    write_u128(hasher, core.free_debt_e8);
    write_u128(hasher, core.sp_debt_e8);
    write_u128(hasher, core.sp_coll_e8);
    write_u128(hasher, core.protocol_collateral_e8);
    write_u128(hasher, core.protocol_revenue_zusd_cum_e8);
    write_u128(hasher, core.liquidator_compensation_collateral_cum_e8);
    write_u128(hasher, core.epoch_redemption_used_e8);
    write_u32(hasher, core.mcr_bps);
    write_u32(hasher, core.ccr_bps);
    write_u128(hasher, core.min_debt_open_e8);
    write_u128(hasher, core.max_debt_e8);
    write_u128(hasher, core.max_debt_supply_e8);
    write_u32(hasher, core.base_rate_bps);
    write_u128(hasher, core.base_rate_last_epoch);
    write_u32(hasher, core.base_rate_decay_per_epoch_bps);
    write_u32(hasher, core.base_rate_borrow_bump_bps);
    write_u32(hasher, core.borrow_fee_floor_bps);
    write_u32(hasher, core.borrow_fee_max_bps);
}

fn hash_fees(hasher: &mut Sha256, fees: &ZusdRuntimeMintFeeProjectionV1) {
    write_u128(hasher, fees.protocol_zusd_fee_reserve_e8);
    write_u128(hasher, fees.staking_zusd_fee_pool_e8);
    write_u128(hasher, fees.staking_zusd_fee_acc_per_share_e8);
    write_u128(hasher, fees.host_zusd_fee_pool_e8);
    write_u128(hasher, fees.host_zusd_fee_cum_e8);
    write_usize(hasher, fees.host_fee_claims.len());
    for entry in &fees.host_fee_claims {
        write_str(hasher, &entry.pubkey);
        write_u128(hasher, entry.amount_e8);
    }
    write_usize(hasher, fees.active_fee_stakes.len());
    for entry in &fees.active_fee_stakes {
        write_str(hasher, &entry.pubkey);
        write_u128(hasher, entry.active_shares);
        write_u128(hasher, entry.reward_debt_e8);
    }
}

fn write_u32(hasher: &mut Sha256, value: u32) {
    hasher.update(value.to_be_bytes());
}

fn write_u128(hasher: &mut Sha256, value: u128) {
    hasher.update(value.to_be_bytes());
}

fn write_usize(hasher: &mut Sha256, value: usize) {
    write_u128(hasher, value as u128);
}

fn write_str(hasher: &mut Sha256, value: &str) {
    write_usize(hasher, value.len());
    hasher.update(value.as_bytes());
}

fn write_optional_str(hasher: &mut Sha256, value: Option<&str>) {
    match value {
        Some(value) => {
            hasher.update([1u8]);
            write_str(hasher, value);
        }
        None => hasher.update([0u8]),
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    #[kani::proof]
    fn mint_fee_partition_conserves_full_u128_domain() {
        let mint_fee_e8: u128 = kani::any();
        let host_fee_e8: u128 = kani::any();
        let active_stake_present: bool = kani::any();
        kani::assume(host_fee_e8 <= mint_fee_e8);

        let route = partition_mint_fee_routes(mint_fee_e8, host_fee_e8, active_stake_present, true)
            .expect("host fee within total and present protocol recipient make routing total");

        assert_eq!(
            route
                .host_e8
                .checked_add(route.staking_e8)
                .and_then(|sum| sum.checked_add(route.protocol_e8)),
            Some(mint_fee_e8)
        );
        assert!(!(route.staking_e8 > 0 && route.protocol_e8 > 0));
        assert_eq!(route.host_e8, host_fee_e8);
    }

    #[kani::proof]
    fn mint_fee_partition_requires_recipient_exactly_for_protocol_route() {
        let mint_fee_e8: u128 = kani::any();
        let host_fee_e8: u128 = kani::any();
        let active_stake_present: bool = kani::any();
        kani::assume(host_fee_e8 <= mint_fee_e8);

        let result =
            partition_mint_fee_routes(mint_fee_e8, host_fee_e8, active_stake_present, false);
        if active_stake_present || host_fee_e8 == mint_fee_e8 {
            let route = result.expect(
                "active staking or zero non-host fee makes a protocol recipient unnecessary",
            );
            assert_eq!(route.host_e8, host_fee_e8);
            assert_eq!(route.protocol_e8, 0);
            assert_eq!(
                route.host_e8.checked_add(route.staking_e8),
                Some(mint_fee_e8)
            );
        } else {
            assert!(matches!(result, Err(TransitionError::InvalidInput(_))));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use alloc::string::ToString;
    use alloc::vec;

    const ACTOR: &str =
        "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const OTHER: &str =
        "0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
    const HOST: &str =
        "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    const ASSET: &str = "0x1111111111111111111111111111111111111111111111111111111111111111";

    fn policy() -> ZusdRuntimeMintPolicyProjectionV1 {
        ZusdRuntimeMintPolicyProjectionV1 {
            redemption_profile: ZusdRuntimeRedemptionProfileProjectionV1::LiquityV1Minimum,
            shutdown_extension_profile: Some(
                ZusdRuntimeShutdownExtensionProfileProjectionV1::TerminalFreezeV1,
            ),
            mcr_bps: LIQUITY_V1_MCR_BPS,
            ccr_bps: LIQUITY_V1_CCR_BPS,
            min_debt_open_e8: LIQUITY_V1_MIN_DEBT_OPEN_E8,
            max_debt_e8: 10_000_000 * E8,
            max_debt_supply_e8: 20_000_000 * E8,
            max_oracle_staleness_epochs: 100,
            base_rate_decay_per_epoch_bps: 0,
            base_rate_borrow_bump_bps: 0,
            borrow_fee_floor_bps: 100,
            borrow_fee_max_bps: 1_000,
            host_protocol_fee_share_bps: 5_000,
        }
    }

    fn authority() -> ZusdRuntimeMintAuthorityProjectionV1 {
        ZusdRuntimeMintAuthorityProjectionV1 {
            protocol_fee_recipient_pubkey: Some(OTHER.to_string()),
        }
    }

    fn empty_fees() -> ZusdRuntimeMintFeeProjectionV1 {
        ZusdRuntimeMintFeeProjectionV1 {
            protocol_zusd_fee_reserve_e8: 0,
            staking_zusd_fee_pool_e8: 0,
            staking_zusd_fee_acc_per_share_e8: 0,
            host_zusd_fee_pool_e8: 0,
            host_zusd_fee_cum_e8: 0,
            host_fee_claims: Vec::new(),
            active_fee_stakes: Vec::new(),
        }
    }

    fn core() -> ZusdRuntimeMintCoreProjectionV1 {
        let policy = policy();
        ZusdRuntimeMintCoreProjectionV1 {
            now_epoch: 10,
            oracle_seen: true,
            oracle_last_update_epoch: 10,
            oracle_pending_update_epoch: 10,
            price_e8: 2 * E8,
            price_pending_e8: 2 * E8,
            max_oracle_staleness_epochs: policy.max_oracle_staleness_epochs,
            collateral_e8: 2_000 * E8,
            debt_e8: 2_000 * E8,
            free_debt_e8: 2_000 * E8,
            sp_debt_e8: 0,
            sp_coll_e8: 0,
            protocol_collateral_e8: 0,
            protocol_revenue_zusd_cum_e8: 0,
            liquidator_compensation_collateral_cum_e8: 0,
            epoch_redemption_used_e8: 0,
            mcr_bps: policy.mcr_bps,
            ccr_bps: policy.ccr_bps,
            min_debt_open_e8: policy.min_debt_open_e8,
            max_debt_e8: policy.max_debt_e8,
            max_debt_supply_e8: policy.max_debt_supply_e8,
            base_rate_bps: 0,
            base_rate_last_epoch: 10,
            base_rate_decay_per_epoch_bps: policy.base_rate_decay_per_epoch_bps,
            base_rate_borrow_bump_bps: policy.base_rate_borrow_bump_bps,
            borrow_fee_floor_bps: policy.borrow_fee_floor_bps,
            borrow_fee_max_bps: policy.borrow_fee_max_bps,
        }
    }

    fn input() -> ZusdRuntimeMintProjectionInputV1 {
        let pre = ZusdRuntimeMintStateProjectionV1 {
            vault_owner_pubkey: ACTOR.to_string(),
            actor_monetary_nonce: 0,
            shutdown_extension: Some(ZusdRuntimeShutdownExtensionProjectionV1::Open {
                profile: ZusdRuntimeShutdownExtensionProfileProjectionV1::TerminalFreezeV1,
            }),
            core: core(),
            fees: empty_fees(),
            liabilities: ZusdRuntimeMintLiabilityProjectionV1 {
                actor_external_balance_units: 2_000,
                stability_pool_escrow_balance_units: 0,
                external_free_liability_e8: 2_000 * E8,
                perps_zusd_liability_e8: 0,
            },
        };
        let operation = ZusdRuntimeMintOperationProjectionV1 {
            module: "ZUSDFinance".to_string(),
            operation_version: "0.1".to_string(),
            action: "mint_zusd".to_string(),
            actor_pubkey: ACTOR.to_string(),
            principal_e8: 100 * E8,
            nonce_before: 0,
            nonce_after: 1,
            deadline: 100,
            block_timestamp: 99,
            host_pubkey: None,
        };
        let mut out = ZusdRuntimeMintProjectionInputV1 {
            projection_version: 1,
            chain_id: "tau-test-zusd".to_string(),
            zusd_asset_id: ASSET.to_string(),
            actor_pubkey: ACTOR.to_string(),
            expected_context_projection_hash: [0u8; 32],
            expected_policy_projection_hash: [0u8; 32],
            expected_authority_projection_hash: [0u8; 32],
            expected_operation_projection_hash: [0u8; 32],
            expected_pre_projection_hash: [0u8; 32],
            expected_post_projection_hash: [0u8; 32],
            policy: policy(),
            authority: authority(),
            operation,
            pre: pre.clone(),
            claimed_post: pre,
        };
        out.claimed_post = expected_post_projection(&out, E8, 101 * E8).unwrap();
        refresh_projection_hashes(&mut out);
        out
    }

    fn refresh_pre_projection_hashes(input: &mut ZusdRuntimeMintProjectionInputV1) {
        input.expected_context_projection_hash = hash_context_projection_v1(input);
        input.expected_policy_projection_hash = hash_policy_projection_v1(&input.policy);
        input.expected_authority_projection_hash = hash_authority_projection_v1(&input.authority);
        input.expected_operation_projection_hash = hash_operation_projection_v1(&input.operation);
        input.expected_pre_projection_hash = hash_state_projection_v1(&input.pre);
    }

    fn refresh_projection_hashes(input: &mut ZusdRuntimeMintProjectionInputV1) {
        refresh_pre_projection_hashes(input);
        input.expected_post_projection_hash = hash_state_projection_v1(&input.claimed_post);
    }

    #[test]
    fn runtime_mint_checker_constructs_exact_protocol_fee_projection() {
        let input = input();
        let journal = check_zusd_runtime_mint_projection_v1(&input).unwrap();

        assert_eq!(
            journal.proof_type,
            PROOF_TYPE_ZUSD_RUNTIME_MINT_PROJECTION_V1
        );
        assert_eq!(journal.principal_e8, 100 * E8);
        assert_eq!(journal.mint_fee_e8, E8);
        assert_eq!(journal.debt_delta_e8, 101 * E8);
        assert_eq!(journal.external_supply_delta_e8, 100 * E8);
        assert_eq!(journal.internal_fee_liability_delta_e8, E8);
        assert_eq!(input.claimed_post.actor_monetary_nonce, 1);
        assert_eq!(
            input.claimed_post.core.collateral_e8,
            input.pre.core.collateral_e8
        );
        assert_eq!(input.claimed_post.fees.protocol_zusd_fee_reserve_e8, E8);
    }

    #[test]
    fn runtime_mint_checker_rejects_existing_deposit_mint_proof_family() {
        assert!(matches!(
            require_zusd_runtime_mint_projection_proof_type_v1(PROOF_TYPE_ZUSD),
            Err(TransitionError::Unsupported(
                "DepositMint v1 does not refine runtime mint_zusd"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_fee_debt_omission() {
        let mut input = input();
        input.claimed_post.core.debt_e8 -= E8;
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint post core projection mismatch"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_supply_shift_that_preserves_total_debt() {
        let mut input = input();
        input.claimed_post.liabilities.external_free_liability_e8 -= E8;
        input.claimed_post.fees.protocol_zusd_fee_reserve_e8 += E8;
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint post fee projection mismatch"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_pending_oracle_detachment() {
        let mut input = input();
        input.pre.core.price_pending_e8 -= 1;
        input.claimed_post = input.pre.clone();
        refresh_pre_projection_hashes(&mut input);
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint oracle pending state frozen"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_frozen_shutdown_extension() {
        let mut input = input();
        input.pre.shutdown_extension = Some(ZusdRuntimeShutdownExtensionProjectionV1::Frozen {
            profile: ZusdRuntimeShutdownExtensionProfileProjectionV1::TerminalFreezeV1,
            epoch: 10,
            oracle_observed_epoch: 10,
            price_e8: 2 * E8,
            collateral_e8: 2_000 * E8,
            debt_e8: 2_000 * E8,
            source_state_root: [9u8; 32],
        });
        input.claimed_post = input.pre.clone();
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint blocked by shutdown extension"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_shutdown_profile_state_mismatch() {
        let mut input = input();
        input.policy.shutdown_extension_profile = None;

        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint shutdown extension profile mismatch"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_vault_owner_mismatch() {
        let mut input = input();
        input.pre.vault_owner_pubkey = OTHER.to_string();
        input.claimed_post = input.pre.clone();
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint vault owner mismatch"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_unbound_pre_nonce() {
        let mut input = input();
        input.pre.actor_monetary_nonce = 7;
        input.claimed_post = input.pre.clone();
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint pre nonce mismatch"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_requires_exact_nonzero_projection_hashes() {
        let cases = [
            ("context", "runtime mint context projection hash mismatch"),
            ("policy", "runtime mint policy projection hash mismatch"),
            (
                "authority",
                "runtime mint authority projection hash mismatch",
            ),
            (
                "operation",
                "runtime mint operation projection hash mismatch",
            ),
            ("pre", "runtime mint pre projection hash mismatch"),
            ("post", "runtime mint post projection hash mismatch"),
        ];

        for (field, expected_error) in cases {
            for bad_hash in [[0u8; 32], [9u8; 32]] {
                let mut input = input();
                match field {
                    "context" => input.expected_context_projection_hash = bad_hash,
                    "policy" => input.expected_policy_projection_hash = bad_hash,
                    "authority" => input.expected_authority_projection_hash = bad_hash,
                    "operation" => input.expected_operation_projection_hash = bad_hash,
                    "pre" => input.expected_pre_projection_hash = bad_hash,
                    "post" => input.expected_post_projection_hash = bad_hash,
                    _ => unreachable!(),
                }
                assert!(
                    matches!(
                        check_zusd_runtime_mint_projection_v1(&input),
                        Err(TransitionError::InvalidInput(message)) if message == expected_error
                    ),
                    "field={field}, bad_hash={bad_hash:?}"
                );
            }
        }
    }

    #[test]
    fn runtime_mint_checker_rejects_chain_and_asset_context_relabeling() {
        let mut chain_relabel = input();
        chain_relabel.chain_id = "tau-test-zusd-other".to_string();
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&chain_relabel),
            Err(TransitionError::InvalidInput(
                "runtime mint context projection hash mismatch"
            ))
        ));

        let mut asset_relabel = input();
        asset_relabel.zusd_asset_id =
            "0x2222222222222222222222222222222222222222222222222222222222222222".to_string();
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&asset_relabel),
            Err(TransitionError::InvalidInput(
                "runtime mint context projection hash mismatch"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_vault_opening_and_f21_substitution() {
        let mut input = input();
        input.pre.core.collateral_e8 = 0;
        input.pre.core.debt_e8 = 0;
        input.pre.core.free_debt_e8 = 0;
        input.pre.liabilities.actor_external_balance_units = 0;
        input.pre.liabilities.external_free_liability_e8 = 0;
        input.claimed_post = input.pre.clone();

        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::Unsupported(
                "runtime mint projection excludes vault opening and F21 reserve creation"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_caller_selected_mcr_below_liquity_baseline() {
        let mut input = input();
        input.policy.mcr_bps = 10_001;
        input.pre.core.mcr_bps = 10_001;

        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint Liquity V1 baseline profile mismatch"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_transition_from_exact_ccr_into_recovery() {
        let mut input = input();
        input.pre.core.collateral_e8 = 1_500 * E8;
        input.claimed_post = input.pre.clone();
        refresh_pre_projection_hashes(&mut input);

        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint would violate CCR"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_policy_core_drift() {
        let mut input = input();
        input.pre.core.borrow_fee_floor_bps += 1;
        input.claimed_post = input.pre.clone();
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime mint policy/core projection mismatch"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_stability_pool_escrow_mismatch() {
        let mut input = input();
        input.pre.liabilities.stability_pool_escrow_balance_units = 1;
        input.claimed_post = input.pre.clone();
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime stability pool escrow mismatch"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_noncanonical_fee_maps() {
        let mut input = input();
        input.pre.fees.host_fee_claims = vec![
            ZusdRuntimeHostFeeEntryV1 {
                pubkey: HOST.to_string(),
                amount_e8: 100 * E8,
            },
            ZusdRuntimeHostFeeEntryV1 {
                pubkey: ACTOR.to_string(),
                amount_e8: 100 * E8,
            },
        ];
        input.pre.fees.host_zusd_fee_pool_e8 = 200 * E8;
        input.pre.fees.host_zusd_fee_cum_e8 = 200 * E8;
        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime host fee claims not canonical"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_routes_exact_staking_fee() {
        let mut input = input();
        input.pre.fees.active_fee_stakes = vec![ZusdRuntimeFeeStakeEntryV1 {
            pubkey: ACTOR.to_string(),
            active_shares: FEE_ACC_SCALE,
            reward_debt_e8: 0,
        }];
        input.claimed_post = expected_post_projection(&input, E8, 101 * E8).unwrap();
        refresh_projection_hashes(&mut input);
        let journal = check_zusd_runtime_mint_projection_v1(&input).unwrap();
        assert_eq!(journal.internal_fee_liability_delta_e8, E8);
        assert_eq!(input.claimed_post.fees.staking_zusd_fee_pool_e8, E8);
        assert_eq!(
            input.claimed_post.fees.staking_zusd_fee_acc_per_share_e8,
            E8
        );
    }

    #[test]
    fn runtime_mint_checker_routes_exact_host_and_protocol_fee() {
        let mut input = input();
        input.operation.principal_e8 = 200 * E8;
        input.operation.host_pubkey = Some(HOST.to_string());
        input.claimed_post = expected_post_projection(&input, 2 * E8, 202 * E8).unwrap();
        refresh_projection_hashes(&mut input);
        let journal = check_zusd_runtime_mint_projection_v1(&input).unwrap();
        assert_eq!(journal.mint_fee_e8, 2 * E8);
        assert_eq!(input.claimed_post.fees.host_zusd_fee_pool_e8, E8);
        assert_eq!(input.claimed_post.fees.protocol_zusd_fee_reserve_e8, E8);
    }

    #[test]
    fn runtime_mint_checker_rejects_missing_protocol_fee_recipient_identity() {
        let mut input = input();
        input.authority.protocol_fee_recipient_pubkey = None;
        input.claimed_post = input.pre.clone();
        refresh_pre_projection_hashes(&mut input);

        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime protocol fee recipient missing"
            ))
        ));
    }

    #[test]
    fn runtime_mint_checker_rejects_noncanonical_protocol_fee_recipient_identity() {
        let mut input = input();
        input.authority.protocol_fee_recipient_pubkey = Some("0xABC".to_string());
        input.claimed_post = input.pre.clone();

        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime protocol fee recipient noncanonical"
            ))
        ));
    }

    #[test]
    fn runtime_mint_authority_hash_binds_protocol_fee_recipient_identity() {
        let baseline = check_zusd_runtime_mint_projection_v1(&input()).unwrap();
        let mut changed = input();
        changed.authority.protocol_fee_recipient_pubkey = Some(ACTOR.to_string());
        changed.claimed_post = expected_post_projection(&changed, E8, 101 * E8).unwrap();
        refresh_projection_hashes(&mut changed);
        let changed = check_zusd_runtime_mint_projection_v1(&changed).unwrap();

        assert_ne!(
            baseline.authority_projection_hash,
            changed.authority_projection_hash
        );
    }

    #[test]
    fn runtime_mint_projection_hash_binds_nonce_owner_escrow_and_fee_liability() {
        let input = input();
        let baseline = hash_state_projection_v1(&input.claimed_post);
        let mut changed = input.claimed_post.clone();
        changed.actor_monetary_nonce += 1;
        assert_ne!(baseline, hash_state_projection_v1(&changed));
        changed = input.claimed_post.clone();
        changed.vault_owner_pubkey = OTHER.to_string();
        assert_ne!(baseline, hash_state_projection_v1(&changed));
        changed = input.claimed_post.clone();
        changed.liabilities.stability_pool_escrow_balance_units += 1;
        assert_ne!(baseline, hash_state_projection_v1(&changed));
        changed = input.claimed_post.clone();
        changed.fees.protocol_zusd_fee_reserve_e8 += E8;
        assert_ne!(baseline, hash_state_projection_v1(&changed));
        changed = input.claimed_post;
        changed.shutdown_extension = None;
        assert_ne!(baseline, hash_state_projection_v1(&changed));
    }

    #[test]
    fn runtime_mint_projection_schema_rejects_unknown_critical_field() {
        let mut value = serde_json::to_value(input()).unwrap();
        value
            .as_object_mut()
            .unwrap()
            .insert("uncommitted_override".to_string(), serde_json::json!(true));

        let error = serde_json::from_value::<ZusdRuntimeMintProjectionInputV1>(value).unwrap_err();
        assert!(error.to_string().contains("unknown field"));
    }

    #[test]
    fn runtime_mint_projection_rejects_unbounded_fee_accounts() {
        let mut input = input();
        input.pre.fees.active_fee_stakes = (0..=MAX_FEE_ACCOUNTS)
            .map(|index| ZusdRuntimeFeeStakeEntryV1 {
                pubkey: format!("0x{index:096x}"),
                active_shares: 1,
                reward_debt_e8: 0,
            })
            .collect();

        assert!(matches!(
            check_zusd_runtime_mint_projection_v1(&input),
            Err(TransitionError::InvalidInput(
                "runtime fee account count exceeds bound"
            ))
        ));
    }

    #[test]
    fn runtime_mint_projection_hash_golden_vector() {
        let input = input();
        let journal = check_zusd_runtime_mint_projection_v1(&input).unwrap();
        assert_eq!(
            journal.context_projection_hash,
            [
                159, 127, 253, 5, 194, 93, 138, 119, 133, 37, 115, 46, 186, 109, 134, 162, 99, 115,
                9, 6, 57, 113, 216, 157, 181, 120, 90, 239, 222, 200, 19, 199,
            ]
        );
        assert_eq!(
            journal.policy_projection_hash,
            [
                12, 202, 179, 7, 152, 247, 169, 11, 104, 127, 68, 212, 121, 253, 39, 153, 242, 227,
                33, 59, 90, 204, 63, 181, 41, 159, 52, 108, 251, 124, 151, 186,
            ]
        );
        assert_eq!(
            journal.authority_projection_hash,
            [
                210, 180, 24, 169, 173, 220, 189, 76, 2, 187, 128, 225, 10, 18, 54, 110, 202, 161,
                24, 62, 18, 138, 228, 139, 73, 78, 135, 236, 60, 200, 42, 137,
            ]
        );
        assert_eq!(
            journal.operation_projection_hash,
            [
                190, 97, 228, 47, 193, 145, 36, 157, 222, 105, 15, 40, 10, 232, 124, 14, 111, 113,
                85, 74, 226, 15, 87, 240, 15, 137, 156, 190, 10, 111, 179, 1,
            ]
        );
        assert_eq!(
            journal.pre_projection_hash,
            [
                61, 170, 214, 186, 180, 48, 149, 200, 211, 129, 83, 69, 36, 163, 12, 14, 188, 112,
                67, 108, 43, 75, 2, 95, 151, 90, 106, 208, 155, 135, 192, 53,
            ]
        );
        assert_eq!(
            journal.post_projection_hash,
            [
                5, 106, 204, 41, 113, 206, 72, 145, 3, 140, 207, 46, 156, 235, 171, 193, 79, 40,
                36, 185, 30, 27, 53, 48, 189, 157, 169, 111, 186, 24, 126, 103,
            ]
        );
    }
}
