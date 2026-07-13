use serde_json::Value;

use super::{
    require_array_field, require_bool_field, require_bytes32_field, require_i128_field,
    require_i32_field, require_object_field, require_optional_object_field, require_single_variant,
    require_string_field, require_u32_field, require_u32_words_field, require_u64_field,
    required_object,
};

const INPUT_FIELDS: &[&str] = &[
    "state_hash",
    "chain_id",
    "pre_app_hash_present",
    "pre_app_hash",
    "pre_state",
    "actions",
    "expected_post_app_hash",
    "risc0_image_id",
];
const SNAPSHOT_FIELDS: &[&str] = &[
    "version",
    "market_id",
    "collateral_asset",
    "index_price_e8",
    "params",
    "accounts",
    "pending_intents",
    "now_epoch",
    "fee_pool_e8",
    "insurance_e8",
    "insurance_ext_e8",
    "claims_paid_e8",
    "net_deposited_e8",
];
const PARAM_FIELDS: &[&str] = &[
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_oracle_move_bps",
    "funding_cap_bps",
    "max_position_abs",
    "min_notional_for_bounty_e8",
];
const ACCOUNT_FIELDS: &[&str] = &[
    "pubkey",
    "position_base",
    "entry_price_e8",
    "collateral_e8",
    "funding_paid_cum_e8",
    "nonce",
];
const INTENT_FIELDS: &[&str] = &[
    "pubkey",
    "target_base",
    "limit_price_e8",
    "min_fill_base",
    "expiry_epoch",
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
const COLLATERAL_BINDING_FIELDS: &[&str] = &[
    "source_proof_type",
    "source_state_hash",
    "balance_root_hash",
    "balance_delta_hash",
];
const ACTION_VARIANTS: &[&str] = &[
    "InitMarket",
    "DepositCollateral",
    "WithdrawCollateral",
    "SubmitIntent",
    "RunEpoch",
];
const INIT_MARKET_FIELDS: &[&str] = &[
    "market_id",
    "collateral_asset",
    "index_price_e8",
    "params",
    "insurance_seed_e8",
];
const DEPOSIT_FIELDS: &[&str] = &[
    "pubkey",
    "asset",
    "amount_e8",
    "nonce",
    "collateral_binding",
];
const WITHDRAW_FIELDS: &[&str] = &["pubkey", "asset", "amount_e8", "nonce"];
const SUBMIT_INTENT_FIELDS: &[&str] = &["intent"];
const RUN_EPOCH_FIELDS: &[&str] = &["oracle", "clearing_price_e8", "funding_rate_bps", "intents"];

pub(super) fn validate(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, INPUT_FIELDS)?;
    require_bytes32_field(object, context, "state_hash")?;
    require_string_field(object, context, "chain_id")?;
    require_bool_field(object, context, "pre_app_hash_present")?;
    require_bytes32_field(object, context, "pre_app_hash")?;
    require_object_field(object, context, "pre_state", validate_snapshot)?;
    require_array_field(object, context, "actions", validate_action)?;
    require_bytes32_field(object, context, "expected_post_app_hash")?;
    require_u32_words_field(object, context, "risc0_image_id")
}

fn validate_snapshot(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, SNAPSHOT_FIELDS)?;
    require_u32_field(object, context, "version")?;
    require_string_field(object, context, "market_id")?;
    require_string_field(object, context, "collateral_asset")?;
    require_i128_field(object, context, "index_price_e8")?;
    require_object_field(object, context, "params", validate_params)?;
    require_array_field(object, context, "accounts", validate_account)?;
    require_array_field(object, context, "pending_intents", validate_intent)?;
    require_u64_field(object, context, "now_epoch")?;
    for field in [
        "fee_pool_e8",
        "insurance_e8",
        "insurance_ext_e8",
        "claims_paid_e8",
        "net_deposited_e8",
    ] {
        require_i128_field(object, context, field)?;
    }
    Ok(())
}

fn validate_params(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, PARAM_FIELDS)?;
    for field in [
        "initial_margin_bps",
        "maintenance_margin_bps",
        "depeg_buffer_bps",
        "liquidation_penalty_bps",
        "max_oracle_move_bps",
    ] {
        require_u32_field(object, context, field)?;
    }
    require_i32_field(object, context, "funding_cap_bps")?;
    require_i128_field(object, context, "max_position_abs")?;
    require_i128_field(object, context, "min_notional_for_bounty_e8")
}

fn validate_account(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ACCOUNT_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    for field in [
        "position_base",
        "entry_price_e8",
        "collateral_e8",
        "funding_paid_cum_e8",
    ] {
        require_i128_field(object, context, field)?;
    }
    require_u64_field(object, context, "nonce")
}

fn validate_intent(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, INTENT_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_i128_field(object, context, "target_base")?;
    require_i128_field(object, context, "limit_price_e8")?;
    require_i128_field(object, context, "min_fill_base")?;
    require_u64_field(object, context, "expiry_epoch")?;
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

fn validate_collateral_binding(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, COLLATERAL_BINDING_FIELDS)?;
    for field in COLLATERAL_BINDING_FIELDS {
        require_string_field(object, context, field)?;
    }
    Ok(())
}

fn validate_action(value: &Value, context: &str) -> Result<(), String> {
    let (variant, payload) = require_single_variant(value, context, ACTION_VARIANTS)?;
    let payload_context = format!("{context}.{variant}");
    match variant {
        "InitMarket" => validate_init_market(payload, &payload_context),
        "DepositCollateral" => validate_deposit(payload, &payload_context),
        "WithdrawCollateral" => validate_withdraw(payload, &payload_context),
        "SubmitIntent" => validate_submit_intent(payload, &payload_context),
        "RunEpoch" => validate_run_epoch(payload, &payload_context),
        _ => Err(format!(
            "{context} contains unsupported variant `{variant}`"
        )),
    }
}

fn validate_init_market(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, INIT_MARKET_FIELDS)?;
    require_string_field(object, context, "market_id")?;
    require_string_field(object, context, "collateral_asset")?;
    require_i128_field(object, context, "index_price_e8")?;
    require_object_field(object, context, "params", validate_params)?;
    require_i128_field(object, context, "insurance_seed_e8")
}

fn validate_deposit(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, DEPOSIT_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_string_field(object, context, "asset")?;
    require_i128_field(object, context, "amount_e8")?;
    require_u64_field(object, context, "nonce")?;
    require_optional_object_field(
        object,
        context,
        "collateral_binding",
        validate_collateral_binding,
    )
}

fn validate_withdraw(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, WITHDRAW_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_string_field(object, context, "asset")?;
    require_i128_field(object, context, "amount_e8")?;
    require_u64_field(object, context, "nonce")
}

fn validate_submit_intent(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, SUBMIT_INTENT_FIELDS)?;
    require_object_field(object, context, "intent", validate_intent)
}

fn validate_run_epoch(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, RUN_EPOCH_FIELDS)?;
    require_object_field(object, context, "oracle", validate_oracle)?;
    require_i128_field(object, context, "clearing_price_e8")?;
    require_i32_field(object, context, "funding_rate_bps")?;
    require_array_field(object, context, "intents", validate_intent)
}
