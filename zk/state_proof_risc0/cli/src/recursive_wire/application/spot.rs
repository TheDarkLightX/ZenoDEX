use serde_json::Value;
use tau_state_proof_risc0_shared::{
    DEX_LP_AMOUNT_MAX, DEX_LP_SUPPLY_MAX, DEX_POOL_RESERVE_MAX, DEX_SWAP_AMOUNT_MAX,
};

use super::{
    require_array_field, require_bool_field, require_bytes32_field, require_object_field,
    require_optional_object_field, require_optional_string_field, require_optional_u64_field,
    require_single_variant, require_string_field, require_u128_field, require_u128_max_field,
    require_u32_array_field, require_u32_field, require_u64_field, required_object,
};

const INPUT_FIELDS: &[&str] = &[
    "state_hash",
    "block_timestamp",
    "pre_app_hash_present",
    "pre_app_hash",
    "pre_state",
    "txs",
    "pre_nonces",
    "tx_ingress",
    "chain_balances_post",
    "expected_post_app_hash",
    "protocol_fee_share_bps",
    "protocol_fee_recipient_pubkey",
    "tx_execution_order",
    "route_price_intervals",
    "route_price_interval_authority",
    "route_price_interval_authority_policy",
    "route_price_interval_max_width_bps",
    "shared_pool_frontier_signature_certificates",
];

const SNAPSHOT_FIELDS: &[&str] = &[
    "version",
    "balances",
    "pools",
    "lp_balances",
    "fee_accumulator",
    "vault",
    "oracle",
];
const BALANCE_FIELDS: &[&str] = &["pubkey", "asset", "amount"];
const POOL_FIELDS: &[&str] = &[
    "pool_id",
    "asset0",
    "asset1",
    "reserve0",
    "reserve1",
    "fee_bps",
    "lp_supply",
    "status",
    "created_at",
];
const LP_BALANCE_FIELDS: &[&str] = &["pubkey", "pool_id", "amount"];
const FEE_ACCUMULATOR_FIELDS: &[&str] = &["dust"];
const VAULT_FIELDS: &[&str] = &[
    "acc_reward_per_share",
    "last_update_acc",
    "pending_rewards",
    "reward_balance",
    "staked_lp_shares",
];
const ORACLE_FIELDS: &[&str] = &["max_staleness_seconds", "price_timestamp"];
const TX_FIELDS: &[&str] = &["sender_pubkey", "app_ops"];
const APP_OPS_FIELDS: &[&str] = &["has_faucet", "faucet_mint", "has_intents", "intents"];
const FAUCET_MINT_FIELDS: &[&str] = &["pubkey", "asset", "amount"];
const SIGNED_INTENT_FIELDS: &[&str] = &["intent", "signature"];
const NONCE_FIELDS: &[&str] = &["pubkey", "next_nonce"];
const INGRESS_FIELDS: &[&str] = &["sender_pubkey", "nonce"];
const CHAIN_BALANCE_FIELDS: &[&str] = &["pubkey", "amount"];
const ROUTE_INTERVAL_FIELDS: &[&str] = &["asset", "low_e8", "point_e8", "high_e8"];
const ROUTE_AUTHORITY_FIELDS: &[&str] = &[
    "schema",
    "source_id",
    "source_root",
    "price_timestamp",
    "max_staleness_seconds",
    "route_price_intervals_root",
];
const ROUTE_POLICY_FIELDS: &[&str] = &["schema", "policy_id", "sources"];
const ROUTE_POLICY_SOURCE_FIELDS: &[&str] = &[
    "source_id",
    "source_root",
    "verification_root",
    "verification_status",
];
const FRONTIER_CERT_FIELDS: &[&str] = &[
    "schema",
    "pool_id",
    "fee_bps",
    "row_states",
    "victims",
    "signatures",
    "claimed_frontier_states",
];
const FRONTIER_STATE_FIELDS: &[&str] = &["reserve_a_atoms", "reserve_b_atoms"];
const FRONTIER_FLOW_FIELDS: &[&str] = &["direction", "amount_in_atoms", "min_out_atoms"];
const FRONTIER_ROW_FIELDS: &[&str] = &["state", "suffix_signature_masks"];

const INTENT_VARIANTS: &[&str] = &[
    "CreatePool",
    "SwapExactIn",
    "AddLiquidity",
    "RemoveLiquidity",
    "SwapExactOut",
    "Route",
];

const CREATE_POOL_FIELDS: &[&str] = &[
    "module",
    "version",
    "intent_id",
    "sender_pubkey",
    "deadline",
    "asset0",
    "asset1",
    "fee_bps",
    "amount0",
    "amount1",
    "salt",
];
const SWAP_EXACT_IN_FIELDS: &[&str] = &[
    "module",
    "version",
    "intent_id",
    "sender_pubkey",
    "deadline",
    "pool_id",
    "asset_in",
    "asset_out",
    "amount_in",
    "min_amount_out",
    "recipient",
    "salt",
];
const ADD_LIQUIDITY_FIELDS: &[&str] = &[
    "module",
    "version",
    "intent_id",
    "sender_pubkey",
    "deadline",
    "pool_id",
    "amount0_desired",
    "amount1_desired",
    "amount0_min",
    "amount1_min",
    "recipient",
    "salt",
];
const REMOVE_LIQUIDITY_FIELDS: &[&str] = &[
    "module",
    "version",
    "intent_id",
    "sender_pubkey",
    "deadline",
    "pool_id",
    "lp_amount",
    "amount0_min",
    "amount1_min",
    "recipient",
    "salt",
];
const SWAP_EXACT_OUT_FIELDS: &[&str] = &[
    "module",
    "version",
    "intent_id",
    "sender_pubkey",
    "deadline",
    "pool_id",
    "asset_in",
    "asset_out",
    "amount_out",
    "max_amount_in",
    "recipient",
    "salt",
];
const ROUTE_FIELDS: &[&str] = &[
    "module",
    "version",
    "intent_id",
    "sender_pubkey",
    "deadline",
    "quote_receipt_hash",
    "asset_in",
    "asset_out",
    "leg_indices",
    "legs",
    "kind",
    "total_amount_in",
    "total_min_amount_out",
    "total_amount_out",
    "total_max_amount_in",
    "recipient",
    "salt",
];
const ROUTE_LEG_FIELDS: &[&str] = &["hops"];
const ROUTE_HOP_FIELDS: &[&str] = &["pool_id"];

pub(super) fn validate(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, INPUT_FIELDS)?;
    require_bytes32_field(object, context, "state_hash")?;
    require_u64_field(object, context, "block_timestamp")?;
    require_bool_field(object, context, "pre_app_hash_present")?;
    require_bytes32_field(object, context, "pre_app_hash")?;
    require_object_field(object, context, "pre_state", validate_snapshot)?;
    require_array_field(object, context, "txs", validate_tx)?;
    require_array_field(object, context, "pre_nonces", validate_nonce)?;
    require_array_field(object, context, "tx_ingress", validate_ingress)?;
    require_array_field(
        object,
        context,
        "chain_balances_post",
        validate_chain_balance,
    )?;
    require_bytes32_field(object, context, "expected_post_app_hash")?;
    require_u32_field(object, context, "protocol_fee_share_bps")?;
    require_optional_string_field(object, context, "protocol_fee_recipient_pubkey")?;
    require_u32_array_field(object, context, "tx_execution_order")?;
    require_array_field(
        object,
        context,
        "route_price_intervals",
        validate_route_interval,
    )?;
    require_optional_object_field(
        object,
        context,
        "route_price_interval_authority",
        validate_route_authority,
    )?;
    require_optional_object_field(
        object,
        context,
        "route_price_interval_authority_policy",
        validate_route_policy,
    )?;
    require_optional_u64_field(object, context, "route_price_interval_max_width_bps")?;
    require_array_field(
        object,
        context,
        "shared_pool_frontier_signature_certificates",
        validate_frontier_certificate,
    )
}

fn validate_snapshot(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, SNAPSHOT_FIELDS)?;
    require_u32_field(object, context, "version")?;
    require_array_field(object, context, "balances", validate_balance)?;
    require_array_field(object, context, "pools", validate_pool)?;
    require_array_field(object, context, "lp_balances", validate_lp_balance)?;
    require_object_field(object, context, "fee_accumulator", validate_fee_accumulator)?;
    require_optional_object_field(object, context, "vault", validate_vault)?;
    require_optional_object_field(object, context, "oracle", validate_oracle)
}

fn validate_balance(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, BALANCE_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_string_field(object, context, "asset")?;
    require_u128_field(object, context, "amount")
}

fn validate_pool(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, POOL_FIELDS)?;
    for field in ["pool_id", "asset0", "asset1", "status"] {
        require_string_field(object, context, field)?;
    }
    require_u128_max_field(object, context, "reserve0", DEX_POOL_RESERVE_MAX)?;
    require_u128_max_field(object, context, "reserve1", DEX_POOL_RESERVE_MAX)?;
    require_u128_max_field(object, context, "lp_supply", DEX_LP_SUPPLY_MAX)?;
    require_u32_field(object, context, "fee_bps")?;
    require_u64_field(object, context, "created_at")
}

fn validate_lp_balance(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, LP_BALANCE_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_string_field(object, context, "pool_id")?;
    require_u128_field(object, context, "amount")
}

fn validate_fee_accumulator(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, FEE_ACCUMULATOR_FIELDS)?;
    require_u128_field(object, context, "dust")
}

fn validate_vault(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, VAULT_FIELDS)?;
    for field in VAULT_FIELDS {
        require_u128_field(object, context, field)?;
    }
    Ok(())
}

fn validate_oracle(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ORACLE_FIELDS)?;
    require_u64_field(object, context, "max_staleness_seconds")?;
    require_u64_field(object, context, "price_timestamp")
}

fn validate_tx(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, TX_FIELDS)?;
    require_string_field(object, context, "sender_pubkey")?;
    require_object_field(object, context, "app_ops", validate_app_ops)
}

fn validate_app_ops(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, APP_OPS_FIELDS)?;
    require_bool_field(object, context, "has_faucet")?;
    require_array_field(object, context, "faucet_mint", validate_faucet_mint)?;
    require_bool_field(object, context, "has_intents")?;
    require_array_field(object, context, "intents", validate_signed_intent)
}

fn validate_faucet_mint(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, FAUCET_MINT_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_string_field(object, context, "asset")?;
    require_u128_field(object, context, "amount")
}

fn validate_signed_intent(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, SIGNED_INTENT_FIELDS)?;
    require_object_field(object, context, "intent", validate_intent)?;
    require_optional_string_field(object, context, "signature")
}

fn validate_intent(value: &Value, context: &str) -> Result<(), String> {
    let (variant, payload) = require_single_variant(value, context, INTENT_VARIANTS)?;
    let payload_context = format!("{context}.{variant}");
    match variant {
        "CreatePool" => validate_create_pool(payload, &payload_context),
        "SwapExactIn" => validate_swap_exact_in(payload, &payload_context),
        "AddLiquidity" => validate_add_liquidity(payload, &payload_context),
        "RemoveLiquidity" => validate_remove_liquidity(payload, &payload_context),
        "SwapExactOut" => validate_swap_exact_out(payload, &payload_context),
        "Route" => validate_route(payload, &payload_context),
        _ => Err(format!(
            "{context} contains unsupported variant `{variant}`"
        )),
    }
}

fn validate_intent_header(
    object: &serde_json::Map<String, Value>,
    context: &str,
) -> Result<(), String> {
    for field in ["module", "version", "intent_id", "sender_pubkey"] {
        require_string_field(object, context, field)?;
    }
    require_u64_field(object, context, "deadline")
}

fn validate_create_pool(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, CREATE_POOL_FIELDS)?;
    validate_intent_header(object, context)?;
    require_string_field(object, context, "asset0")?;
    require_string_field(object, context, "asset1")?;
    require_u32_field(object, context, "fee_bps")?;
    require_u128_max_field(object, context, "amount0", DEX_LP_AMOUNT_MAX)?;
    require_u128_max_field(object, context, "amount1", DEX_LP_AMOUNT_MAX)?;
    require_optional_string_field(object, context, "salt")
}

fn validate_swap_exact_in(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, SWAP_EXACT_IN_FIELDS)?;
    validate_intent_header(object, context)?;
    for field in ["pool_id", "asset_in", "asset_out", "recipient"] {
        require_string_field(object, context, field)?;
    }
    require_u128_max_field(object, context, "amount_in", DEX_SWAP_AMOUNT_MAX)?;
    require_u128_max_field(object, context, "min_amount_out", DEX_SWAP_AMOUNT_MAX)?;
    require_optional_string_field(object, context, "salt")
}

fn validate_add_liquidity(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ADD_LIQUIDITY_FIELDS)?;
    validate_intent_header(object, context)?;
    require_string_field(object, context, "pool_id")?;
    require_string_field(object, context, "recipient")?;
    for field in [
        "amount0_desired",
        "amount1_desired",
        "amount0_min",
        "amount1_min",
    ] {
        require_u128_max_field(object, context, field, DEX_LP_AMOUNT_MAX)?;
    }
    require_optional_string_field(object, context, "salt")
}

fn validate_remove_liquidity(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, REMOVE_LIQUIDITY_FIELDS)?;
    validate_intent_header(object, context)?;
    require_string_field(object, context, "pool_id")?;
    require_string_field(object, context, "recipient")?;
    require_u128_max_field(object, context, "lp_amount", DEX_LP_SUPPLY_MAX)?;
    require_u128_max_field(object, context, "amount0_min", DEX_POOL_RESERVE_MAX)?;
    require_u128_max_field(object, context, "amount1_min", DEX_POOL_RESERVE_MAX)?;
    require_optional_string_field(object, context, "salt")
}

fn validate_swap_exact_out(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, SWAP_EXACT_OUT_FIELDS)?;
    validate_intent_header(object, context)?;
    for field in ["pool_id", "asset_in", "asset_out", "recipient"] {
        require_string_field(object, context, field)?;
    }
    require_u128_max_field(object, context, "amount_out", DEX_SWAP_AMOUNT_MAX)?;
    require_u128_max_field(object, context, "max_amount_in", DEX_SWAP_AMOUNT_MAX)?;
    require_optional_string_field(object, context, "salt")
}

fn validate_route(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ROUTE_FIELDS)?;
    validate_intent_header(object, context)?;
    for field in [
        "quote_receipt_hash",
        "asset_in",
        "asset_out",
        "kind",
        "recipient",
    ] {
        require_string_field(object, context, field)?;
    }
    require_u32_array_field(object, context, "leg_indices")?;
    require_array_field(object, context, "legs", validate_route_leg)?;
    for field in [
        "total_amount_in",
        "total_min_amount_out",
        "total_amount_out",
        "total_max_amount_in",
    ] {
        require_u128_max_field(object, context, field, DEX_SWAP_AMOUNT_MAX)?;
    }
    require_optional_string_field(object, context, "salt")
}

fn validate_route_leg(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ROUTE_LEG_FIELDS)?;
    require_array_field(object, context, "hops", validate_route_hop)
}

fn validate_route_hop(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ROUTE_HOP_FIELDS)?;
    require_string_field(object, context, "pool_id")
}

fn validate_nonce(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, NONCE_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_u64_field(object, context, "next_nonce")
}

fn validate_ingress(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, INGRESS_FIELDS)?;
    require_string_field(object, context, "sender_pubkey")?;
    require_u64_field(object, context, "nonce")
}

fn validate_chain_balance(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, CHAIN_BALANCE_FIELDS)?;
    require_string_field(object, context, "pubkey")?;
    require_u128_field(object, context, "amount")
}

fn validate_route_interval(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ROUTE_INTERVAL_FIELDS)?;
    require_string_field(object, context, "asset")?;
    for field in ["low_e8", "point_e8", "high_e8"] {
        require_u128_field(object, context, field)?;
    }
    Ok(())
}

fn validate_route_authority(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ROUTE_AUTHORITY_FIELDS)?;
    require_string_field(object, context, "schema")?;
    require_string_field(object, context, "source_id")?;
    require_bytes32_field(object, context, "source_root")?;
    require_u64_field(object, context, "price_timestamp")?;
    require_u64_field(object, context, "max_staleness_seconds")?;
    require_bytes32_field(object, context, "route_price_intervals_root")
}

fn validate_route_policy(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ROUTE_POLICY_FIELDS)?;
    require_string_field(object, context, "schema")?;
    require_string_field(object, context, "policy_id")?;
    require_array_field(object, context, "sources", validate_route_policy_source)
}

fn validate_route_policy_source(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, ROUTE_POLICY_SOURCE_FIELDS)?;
    require_string_field(object, context, "source_id")?;
    require_bytes32_field(object, context, "source_root")?;
    require_bytes32_field(object, context, "verification_root")?;
    require_string_field(object, context, "verification_status")
}

fn validate_frontier_certificate(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, FRONTIER_CERT_FIELDS)?;
    require_string_field(object, context, "schema")?;
    require_string_field(object, context, "pool_id")?;
    require_u32_field(object, context, "fee_bps")?;
    require_array_field(object, context, "row_states", validate_frontier_state)?;
    require_array_field(object, context, "victims", validate_frontier_flow)?;
    require_array_field(object, context, "signatures", validate_frontier_row)?;
    require_array_field(
        object,
        context,
        "claimed_frontier_states",
        validate_frontier_state,
    )
}

fn validate_frontier_state(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, FRONTIER_STATE_FIELDS)?;
    require_u128_field(object, context, "reserve_a_atoms")?;
    require_u128_field(object, context, "reserve_b_atoms")
}

fn validate_frontier_flow(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, FRONTIER_FLOW_FIELDS)?;
    require_string_field(object, context, "direction")?;
    require_u128_field(object, context, "amount_in_atoms")?;
    require_u128_field(object, context, "min_out_atoms")
}

fn validate_frontier_row(value: &Value, context: &str) -> Result<(), String> {
    let object = required_object(value, context, FRONTIER_ROW_FIELDS)?;
    require_object_field(object, context, "state", validate_frontier_state)?;
    require_u32_array_field(object, context, "suffix_signature_masks")
}
