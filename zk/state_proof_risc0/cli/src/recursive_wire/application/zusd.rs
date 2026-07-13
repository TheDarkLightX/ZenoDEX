use serde_json::Value;

use super::{
    require_array_field, require_bool_field, require_bytes32_field, require_i128_field,
    require_object_field, require_single_variant, require_string_field, require_u128_field,
    require_u32_field, require_u32_words_field, require_u64_field, required_object,
};

const INPUT_FIELDS: &[&str] = &[
    "state_hash",
    "chain_id",
    "pre_app_hash_present",
    "pre_app_hash",
    "pre_state",
    "operation",
    "expected_post_app_hash",
    "risc0_image_id",
];
const SNAPSHOT_FIELDS: &[&str] = &["version", "vaults", "balances", "total_debt_zusd_e8"];
const VAULT_FIELDS: &[&str] = &[
    "pubkey",
    "collateral_asset",
    "collateral_amount_e8",
    "debt_zusd_e8",
    "nonce",
];
const BALANCE_FIELDS: &[&str] = &["pubkey", "amount_e8"];
const OPERATION_VARIANTS: &[&str] = &["DepositMint"];
const DEPOSIT_MINT_FIELDS: &[&str] = &[
    "pubkey",
    "collateral_asset",
    "deposit_amount_e8",
    "mint_amount_e8",
    "oracle",
    "mcr_bps",
    "nonce",
];
const ORACLE_FIELDS: &[&str] = &[
    "oracle_bridge_id",
    "oracle_bridge_hash",
    "price_e8",
    "price_timestamp",
    "max_staleness_seconds",
    "observed_at",
    "pre_price_batch_commitment",
];

pub(super) fn validate(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, INPUT_FIELDS)?;
    require_bytes32_field(object, context, "state_hash")?;
    require_string_field(object, context, "chain_id")?;
    require_bool_field(object, context, "pre_app_hash_present")?;
    require_bytes32_field(object, context, "pre_app_hash")?;
    require_object_field(object, context, "pre_state", validate_snapshot)?;
    require_object_field(object, context, "operation", validate_operation)?;
    require_bytes32_field(object, context, "expected_post_app_hash")?;
    require_u32_words_field(object, context, "risc0_image_id")
}

fn validate_snapshot(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, SNAPSHOT_FIELDS)?;
    require_u32_field(object, context, "version")?;
    require_array_field(object, context, "vaults", validate_vault)?;
    require_array_field(object, context, "balances", validate_balance)?;
    require_u128_field(object, context, "total_debt_zusd_e8")
}

fn validate_vault(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, VAULT_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_string_field(object, context, "collateral_asset")?;
    require_u128_field(object, context, "collateral_amount_e8")?;
    require_u128_field(object, context, "debt_zusd_e8")?;
    require_u64_field(object, context, "nonce")
}

fn validate_balance(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, BALANCE_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_u128_field(object, context, "amount_e8")
}

fn validate_operation(value: &Value, context: &str) -> Result<(), String> {
    let (variant, payload) = require_single_variant(value, context, OPERATION_VARIANTS)?;
    match variant {
        "DepositMint" => validate_deposit_mint(payload, &format!("{context}.{variant}")),
        _ => Err(format!(
            "{context} contains unsupported variant `{variant}`"
        )),
    }
}

fn validate_deposit_mint(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, DEPOSIT_MINT_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_string_field(object, context, "collateral_asset")?;
    require_u128_field(object, context, "deposit_amount_e8")?;
    require_u128_field(object, context, "mint_amount_e8")?;
    require_object_field(object, context, "oracle", validate_oracle)?;
    require_u32_field(object, context, "mcr_bps")?;
    require_u64_field(object, context, "nonce")
}

fn validate_oracle(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ORACLE_FIELDS)?;
    require_string_field(object, context, "oracle_bridge_id")?;
    require_string_field(object, context, "oracle_bridge_hash")?;
    require_i128_field(object, context, "price_e8")?;
    require_u64_field(object, context, "price_timestamp")?;
    require_u64_field(object, context, "max_staleness_seconds")?;
    require_u64_field(object, context, "observed_at")?;
    require_string_field(object, context, "pre_price_batch_commitment")
}
