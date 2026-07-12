use serde_json::{Map, Value};

mod perps;
mod spot;
mod zusd;

type Validator = fn(&Value, &str) -> Result<(), String>;

pub(super) fn validate_spot(value: &Value, context: &str) -> Result<(), String> {
    spot::validate(value, context)
}

pub(super) fn validate_perps(value: &Value, context: &str) -> Result<(), String> {
    perps::validate(value, context)
}

pub(super) fn validate_zusd(value: &Value, context: &str) -> Result<(), String> {
    zusd::validate(value, context)
}

pub(super) fn required_object<'a>(
    value: &'a Value,
    context: &str,
    fields: &[&str],
) -> Result<&'a Map<String, Value>, String> {
    super::exact_required_object(value, context, fields)
}

pub(super) fn required_field<'a>(
    object: &'a Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<&'a Value, String> {
    object
        .get(field)
        .ok_or_else(|| format!("{context} missing required field `{field}`"))
}

pub(super) fn require_string_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<(), String> {
    let value = required_field(object, context, field)?;
    if value.is_string() {
        Ok(())
    } else {
        Err(format!("{context}.{field} must be a string"))
    }
}

pub(super) fn require_bool_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<(), String> {
    let value = required_field(object, context, field)?;
    if value.is_boolean() {
        Ok(())
    } else {
        Err(format!("{context}.{field} must be a boolean"))
    }
}

fn require_integer<T>(value: &Value, context: &str, description: &str) -> Result<(), String>
where
    T: core::str::FromStr,
{
    let Some(number) = value.as_number() else {
        return Err(format!("{context} must be {description}"));
    };
    if number.to_string().parse::<T>().is_err() {
        return Err(format!("{context} must be {description}"));
    }
    Ok(())
}

macro_rules! integer_field {
    ($name:ident, $ty:ty, $description:literal) => {
        pub(super) fn $name(
            object: &Map<String, Value>,
            context: &str,
            field: &str,
        ) -> Result<(), String> {
            require_integer::<$ty>(
                required_field(object, context, field)?,
                &format!("{context}.{field}"),
                $description,
            )
        }
    };
}

integer_field!(require_u32_field, u32, "an unsigned 32-bit integer");
integer_field!(require_u64_field, u64, "an unsigned 64-bit integer");
integer_field!(require_u128_field, u128, "an unsigned 128-bit integer");
integer_field!(require_i32_field, i32, "a signed 32-bit integer");
integer_field!(require_i128_field, i128, "a signed 128-bit integer");

pub(super) fn require_bytes32_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<(), String> {
    require_fixed_unsigned_array::<u8>(
        required_field(object, context, field)?,
        &format!("{context}.{field}"),
        32,
        "an unsigned 8-bit integer",
    )
}

pub(super) fn require_u32_words_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<(), String> {
    require_fixed_unsigned_array::<u32>(
        required_field(object, context, field)?,
        &format!("{context}.{field}"),
        8,
        "an unsigned 32-bit integer",
    )
}

fn require_fixed_unsigned_array<T>(
    value: &Value,
    context: &str,
    length: usize,
    description: &str,
) -> Result<(), String>
where
    T: core::str::FromStr,
{
    let items = value
        .as_array()
        .ok_or_else(|| format!("{context} must be a list of exactly {length} integers"))?;
    if items.len() != length {
        return Err(format!("{context} must contain exactly {length} integers"));
    }
    for (index, item) in items.iter().enumerate() {
        require_integer::<T>(item, &format!("{context}[{index}]"), description)?;
    }
    Ok(())
}

pub(super) fn require_object_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
    validate: Validator,
) -> Result<(), String> {
    validate(
        required_field(object, context, field)?,
        &format!("{context}.{field}"),
    )
}

pub(super) fn require_array_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
    validate: Validator,
) -> Result<(), String> {
    let field_context = format!("{context}.{field}");
    let items = required_field(object, context, field)?
        .as_array()
        .ok_or_else(|| format!("{field_context} must be a list"))?;
    for (index, item) in items.iter().enumerate() {
        validate(item, &format!("{field_context}[{index}]"))?;
    }
    Ok(())
}

pub(super) fn require_u32_array_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<(), String> {
    let field_context = format!("{context}.{field}");
    let items = required_field(object, context, field)?
        .as_array()
        .ok_or_else(|| format!("{field_context} must be a list"))?;
    for (index, item) in items.iter().enumerate() {
        require_integer::<u32>(
            item,
            &format!("{field_context}[{index}]"),
            "an unsigned 32-bit integer",
        )?;
    }
    Ok(())
}

pub(super) fn require_optional_string_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<(), String> {
    let value = required_field(object, context, field)?;
    if value.is_null() || value.is_string() {
        Ok(())
    } else {
        Err(format!("{context}.{field} must be null or a string"))
    }
}

pub(super) fn require_optional_u64_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<(), String> {
    let value = required_field(object, context, field)?;
    if value.is_null() {
        return Ok(());
    }
    require_integer::<u64>(
        value,
        &format!("{context}.{field}"),
        "null or an unsigned 64-bit integer",
    )
}

pub(super) fn require_optional_object_field(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
    validate: Validator,
) -> Result<(), String> {
    let value = required_field(object, context, field)?;
    if value.is_null() {
        return Ok(());
    }
    validate(value, &format!("{context}.{field}"))
}

pub(super) fn require_single_variant<'a>(
    value: &'a Value,
    context: &str,
    variants: &[&str],
) -> Result<(&'a str, &'a Value), String> {
    let object = value
        .as_object()
        .ok_or_else(|| format!("{context} must be an externally tagged object"))?;
    if object.len() != 1 {
        return Err(format!(
            "{context} must contain exactly one supported variant"
        ));
    }
    let Some((variant, payload)) = object.iter().next() else {
        return Err(format!(
            "{context} must contain exactly one supported variant"
        ));
    };
    if !variants.contains(&variant.as_str()) {
        return Err(format!(
            "{context} contains unsupported variant `{variant}`"
        ));
    }
    Ok((variant.as_str(), payload))
}

#[cfg(test)]
mod tests {
    use serde_json::{json, Map, Value};
    use tau_state_proof_risc0_shared::{
        DexIntentV1, PerpsNpActionV1, PerpsNpRecursiveLeafInputV1, SpotRecursiveLeafInputV1,
        ZusdOperationV1, ZusdRecursiveLeafInputV1,
    };

    type WireValidator = fn(&Value) -> Result<(), String>;

    struct SurfaceCase {
        name: &'static str,
        value: Value,
        validate: WireValidator,
    }

    fn bytes32(seed: u8) -> Value {
        json!(vec![seed; 32])
    }

    fn words8(seed: u32) -> Value {
        json!(vec![seed; 8])
    }

    fn wrapper(payload_field: &str, payload: Value, image_seed: u32) -> Value {
        let mut object = Map::new();
        object.insert("chain_id".to_string(), json!("tau-test"));
        object.insert("epoch_id".to_string(), json!(7));
        object.insert("lane_id".to_string(), json!("lane-a"));
        object.insert("risc0_image_id".to_string(), words8(image_seed));
        object.insert("public_policy_hash".to_string(), bytes32(10));
        object.insert("feature_suite_hash".to_string(), bytes32(11));
        object.insert("dependency_lock_hash".to_string(), bytes32(12));
        object.insert("toolchain_lock_hash".to_string(), bytes32(13));
        object.insert(payload_field.to_string(), payload);
        Value::Object(object)
    }

    fn intent_payload(kind: &str) -> Value {
        let common = || {
            json!({
                "module": "dex",
                "version": "1",
                "intent_id": format!("intent-{kind}"),
                "sender_pubkey": "alice",
                "deadline": 10,
                "salt": "salt"
            })
        };
        let mut payload = common();
        let object = payload.as_object_mut().unwrap();
        match kind {
            "CreatePool" => {
                object.insert("asset0".to_string(), json!("A"));
                object.insert("asset1".to_string(), json!("B"));
                object.insert("fee_bps".to_string(), json!(30));
                object.insert("amount0".to_string(), json!(1000));
                object.insert("amount1".to_string(), json!(2000));
            }
            "SwapExactIn" => {
                object.insert("pool_id".to_string(), json!("pool"));
                object.insert("asset_in".to_string(), json!("A"));
                object.insert("asset_out".to_string(), json!("B"));
                object.insert("amount_in".to_string(), json!(10));
                object.insert("min_amount_out".to_string(), json!(9));
                object.insert("recipient".to_string(), json!("alice"));
            }
            "AddLiquidity" => {
                object.insert("pool_id".to_string(), json!("pool"));
                object.insert("amount0_desired".to_string(), json!(10));
                object.insert("amount1_desired".to_string(), json!(20));
                object.insert("amount0_min".to_string(), json!(9));
                object.insert("amount1_min".to_string(), json!(19));
                object.insert("recipient".to_string(), json!("alice"));
            }
            "RemoveLiquidity" => {
                object.insert("pool_id".to_string(), json!("pool"));
                object.insert("lp_amount".to_string(), json!(10));
                object.insert("amount0_min".to_string(), json!(9));
                object.insert("amount1_min".to_string(), json!(19));
                object.insert("recipient".to_string(), json!("alice"));
            }
            "SwapExactOut" => {
                object.insert("pool_id".to_string(), json!("pool"));
                object.insert("asset_in".to_string(), json!("A"));
                object.insert("asset_out".to_string(), json!("B"));
                object.insert("amount_out".to_string(), json!(9));
                object.insert("max_amount_in".to_string(), json!(10));
                object.insert("recipient".to_string(), json!("alice"));
            }
            "Route" => {
                object.insert("quote_receipt_hash".to_string(), json!("quote"));
                object.insert("asset_in".to_string(), json!("A"));
                object.insert("asset_out".to_string(), json!("B"));
                object.insert("leg_indices".to_string(), json!([0]));
                object.insert("legs".to_string(), json!([{"hops": [{"pool_id": "pool"}]}]));
                object.insert("kind".to_string(), json!("exact_in"));
                object.insert("total_amount_in".to_string(), json!(10));
                object.insert("total_min_amount_out".to_string(), json!(9));
                object.insert("total_amount_out".to_string(), json!(9));
                object.insert("total_max_amount_in".to_string(), json!(10));
                object.insert("recipient".to_string(), json!("alice"));
            }
            _ => panic!("unsupported test intent kind"),
        }
        json!({kind: payload})
    }

    fn signed_intent(kind: &str) -> Value {
        json!({"intent": intent_payload(kind), "signature": "signature"})
    }

    fn spot_fixture() -> Value {
        let intents = [
            "CreatePool",
            "SwapExactIn",
            "AddLiquidity",
            "RemoveLiquidity",
            "SwapExactOut",
            "Route",
        ]
        .into_iter()
        .map(signed_intent)
        .collect::<Vec<_>>();
        wrapper(
            "spot_input",
            json!({
                "state_hash": bytes32(1),
                "block_timestamp": 1,
                "pre_app_hash_present": true,
                "pre_app_hash": bytes32(2),
                "pre_state": {
                    "version": 1,
                    "balances": [{"pubkey": "alice", "asset": "A", "amount": 100}],
                    "pools": [{
                        "pool_id": "pool", "asset0": "A", "asset1": "B",
                        "reserve0": 1000, "reserve1": 2000, "fee_bps": 30,
                        "lp_supply": 1000, "status": "active", "created_at": 1
                    }],
                    "lp_balances": [{"pubkey": "alice", "pool_id": "pool", "amount": 100}],
                    "fee_accumulator": {"dust": 0},
                    "vault": {
                        "acc_reward_per_share": 1, "last_update_acc": 2,
                        "pending_rewards": 3, "reward_balance": 4,
                        "staked_lp_shares": 5
                    },
                    "oracle": {"max_staleness_seconds": 30, "price_timestamp": 1}
                },
                "txs": [{
                    "sender_pubkey": "alice",
                    "app_ops": {
                        "has_faucet": true,
                        "faucet_mint": [{"pubkey": "alice", "asset": "A", "amount": 10}],
                        "has_intents": true,
                        "intents": intents
                    }
                }],
                "pre_nonces": [{"pubkey": "alice", "next_nonce": 1}],
                "tx_ingress": [{"sender_pubkey": "alice", "nonce": 1}],
                "chain_balances_post": [{"pubkey": "alice", "amount": 90}],
                "expected_post_app_hash": bytes32(3),
                "protocol_fee_share_bps": 25,
                "protocol_fee_recipient_pubkey": "fee-recipient",
                "tx_execution_order": [0],
                "route_price_intervals": [{
                    "asset": "A", "low_e8": 90, "point_e8": 100, "high_e8": 110
                }],
                "route_price_interval_authority": {
                    "schema": "authority.v1", "source_id": "oracle-a",
                    "source_root": bytes32(4), "price_timestamp": 1,
                    "max_staleness_seconds": 30,
                    "route_price_intervals_root": bytes32(5)
                },
                "route_price_interval_authority_policy": {
                    "schema": "policy.v1", "policy_id": "policy-a",
                    "sources": [{
                        "source_id": "oracle-a", "source_root": bytes32(4),
                        "verification_root": bytes32(6),
                        "verification_status": "verified"
                    }]
                },
                "route_price_interval_max_width_bps": 100,
                "shared_pool_frontier_signature_certificates": [{
                    "schema": "frontier.v1", "pool_id": "pool", "fee_bps": 30,
                    "row_states": [{"reserve_a_atoms": 1000, "reserve_b_atoms": 2000}],
                    "victims": [{"direction": "A_TO_B", "amount_in_atoms": 10, "min_out_atoms": 9}],
                    "signatures": [{
                        "state": {"reserve_a_atoms": 1000, "reserve_b_atoms": 2000},
                        "suffix_signature_masks": [1]
                    }],
                    "claimed_frontier_states": [{"reserve_a_atoms": 1010, "reserve_b_atoms": 1991}]
                }]
            }),
            41,
        )
    }

    fn perps_params() -> Value {
        json!({
            "initial_margin_bps": 1000,
            "maintenance_margin_bps": 500,
            "depeg_buffer_bps": 100,
            "liquidation_penalty_bps": 50,
            "max_oracle_move_bps": 500,
            "funding_cap_bps": -100,
            "max_position_abs": 1000000,
            "min_notional_for_bounty_e8": 100000000
        })
    }

    fn perps_intent(nonce: u64) -> Value {
        json!({
            "pubkey": "alice", "target_base": 10, "limit_price_e8": 100,
            "min_fill_base": 1, "expiry_epoch": 10, "nonce": nonce
        })
    }

    fn oracle_binding() -> Value {
        json!({
            "oracle_bridge_id": "oracle", "oracle_bridge_hash": "hash",
            "price_e8": 100, "price_timestamp": 1,
            "max_staleness_seconds": 30, "observed_at": 1,
            "pre_price_batch_commitment": "commitment"
        })
    }

    fn perps_fixture() -> Value {
        wrapper(
            "perps_input",
            json!({
                "state_hash": bytes32(1),
                "chain_id": "tau-test",
                "pre_app_hash_present": true,
                "pre_app_hash": bytes32(2),
                "pre_state": {
                    "version": 1, "market_id": "market", "collateral_asset": "zUSD",
                    "index_price_e8": 100, "params": perps_params(),
                    "accounts": [{
                        "pubkey": "alice", "position_base": -1, "entry_price_e8": 100,
                        "collateral_e8": 1000, "funding_paid_cum_e8": -2, "nonce": 1
                    }],
                    "pending_intents": [perps_intent(2)], "now_epoch": 1,
                    "fee_pool_e8": 1, "insurance_e8": 2, "insurance_ext_e8": 3,
                    "claims_paid_e8": 4, "net_deposited_e8": 5
                },
                "actions": [
                    {"InitMarket": {
                        "market_id": "market", "collateral_asset": "zUSD",
                        "index_price_e8": 100, "params": perps_params(),
                        "insurance_seed_e8": 10
                    }},
                    {"DepositCollateral": {
                        "pubkey": "alice", "asset": "zUSD", "amount_e8": 10, "nonce": 2,
                        "collateral_binding": {
                            "source_proof_type": "zusd", "source_state_hash": "state",
                            "balance_root_hash": "root", "balance_delta_hash": "delta"
                        }
                    }},
                    {"WithdrawCollateral": {
                        "pubkey": "alice", "asset": "zUSD", "amount_e8": 5, "nonce": 3
                    }},
                    {"SubmitIntent": {"intent": perps_intent(4)}},
                    {"RunEpoch": {
                        "oracle": oracle_binding(), "clearing_price_e8": 100,
                        "funding_rate_bps": -10, "intents": [perps_intent(5)]
                    }}
                ],
                "expected_post_app_hash": bytes32(3),
                "risc0_image_id": words8(42)
            }),
            42,
        )
    }

    fn zusd_fixture() -> Value {
        wrapper(
            "zusd_input",
            json!({
                "state_hash": bytes32(1),
                "chain_id": "tau-test",
                "pre_app_hash_present": true,
                "pre_app_hash": bytes32(2),
                "pre_state": {
                    "version": 1,
                    "vaults": [{
                        "pubkey": "alice", "collateral_asset": "A",
                        "collateral_amount_e8": 100, "debt_zusd_e8": 50, "nonce": 1
                    }],
                    "balances": [{"pubkey": "alice", "amount_e8": 50}],
                    "total_debt_zusd_e8": 50
                },
                "operation": {"DepositMint": {
                    "pubkey": "alice", "collateral_asset": "A",
                    "deposit_amount_e8": 10, "mint_amount_e8": 5,
                    "oracle": oracle_binding(), "mcr_bps": 15000, "nonce": 2
                }},
                "expected_post_app_hash": bytes32(3),
                "risc0_image_id": words8(43)
            }),
            43,
        )
    }

    fn validate_spot(value: &Value) -> Result<(), String> {
        super::super::validate_spot_leaf(value)
    }

    fn validate_perps(value: &Value) -> Result<(), String> {
        super::super::validate_perps_leaf(value)
    }

    fn validate_zusd(value: &Value) -> Result<(), String> {
        super::super::validate_zusd_leaf(value)
    }

    fn cases() -> Vec<SurfaceCase> {
        vec![
            SurfaceCase {
                name: "spot",
                value: spot_fixture(),
                validate: validate_spot,
            },
            SurfaceCase {
                name: "perps",
                value: perps_fixture(),
                validate: validate_perps,
            },
            SurfaceCase {
                name: "zusd",
                value: zusd_fixture(),
                validate: validate_zusd,
            },
        ]
    }

    fn spot_variant_name(intent: &DexIntentV1) -> &'static str {
        match intent {
            DexIntentV1::CreatePool(_) => "CreatePool",
            DexIntentV1::SwapExactIn(_) => "SwapExactIn",
            DexIntentV1::AddLiquidity(_) => "AddLiquidity",
            DexIntentV1::RemoveLiquidity(_) => "RemoveLiquidity",
            DexIntentV1::SwapExactOut(_) => "SwapExactOut",
            DexIntentV1::Route(_) => "Route",
        }
    }

    fn perps_variant_name(action: &PerpsNpActionV1) -> &'static str {
        match action {
            PerpsNpActionV1::InitMarket { .. } => "InitMarket",
            PerpsNpActionV1::DepositCollateral { .. } => "DepositCollateral",
            PerpsNpActionV1::WithdrawCollateral { .. } => "WithdrawCollateral",
            PerpsNpActionV1::SubmitIntent { .. } => "SubmitIntent",
            PerpsNpActionV1::RunEpoch { .. } => "RunEpoch",
        }
    }

    fn zusd_variant_name(operation: &ZusdOperationV1) -> &'static str {
        match operation {
            ZusdOperationV1::DepositMint { .. } => "DepositMint",
        }
    }

    fn child_pointer(parent: &str, child: &str) -> String {
        if parent.is_empty() {
            format!("/{child}")
        } else {
            format!("{parent}/{child}")
        }
    }

    fn collect_object_fields(value: &Value, pointer: &str, fields: &mut Vec<(String, String)>) {
        match value {
            Value::Object(object) => {
                for (key, child) in object {
                    fields.push((pointer.to_string(), key.clone()));
                    collect_object_fields(child, &child_pointer(pointer, key), fields);
                }
            }
            Value::Array(items) => {
                for (index, child) in items.iter().enumerate() {
                    collect_object_fields(
                        child,
                        &child_pointer(pointer, &index.to_string()),
                        fields,
                    );
                }
            }
            _ => {}
        }
    }

    fn collect_object_pointers(value: &Value, pointer: &str, pointers: &mut Vec<String>) {
        match value {
            Value::Object(object) => {
                pointers.push(pointer.to_string());
                for (key, child) in object {
                    collect_object_pointers(child, &child_pointer(pointer, key), pointers);
                }
            }
            Value::Array(items) => {
                for (index, child) in items.iter().enumerate() {
                    collect_object_pointers(
                        child,
                        &child_pointer(pointer, &index.to_string()),
                        pointers,
                    );
                }
            }
            _ => {}
        }
    }

    fn collect_value_pointers(value: &Value, pointer: &str, pointers: &mut Vec<String>) {
        match value {
            Value::Object(object) => {
                for (key, value) in object {
                    let child = child_pointer(pointer, key);
                    pointers.push(child.clone());
                    collect_value_pointers(value, &child, pointers);
                }
            }
            Value::Array(items) => {
                for (index, item) in items.iter().enumerate() {
                    let child = child_pointer(pointer, &index.to_string());
                    pointers.push(child.clone());
                    collect_value_pointers(item, &child, pointers);
                }
            }
            _ => {}
        }
    }

    fn object_mut_at<'a>(value: &'a mut Value, pointer: &str) -> &'a mut Map<String, Value> {
        let target = if pointer.is_empty() {
            value
        } else {
            value.pointer_mut(pointer).unwrap()
        };
        target.as_object_mut().unwrap()
    }

    fn wrong_type(value: &Value) -> Value {
        match value {
            Value::Null => Value::Bool(true),
            Value::Bool(_) => Value::String("wrong-type".to_string()),
            Value::Number(_) => Value::String("wrong-type".to_string()),
            Value::String(_) => Value::Bool(true),
            Value::Array(_) => Value::Object(Map::new()),
            Value::Object(_) => Value::Bool(true),
        }
    }

    #[test]
    fn rich_fixtures_cover_every_reachable_variant_and_match_typed_schemas() {
        let spot = spot_fixture();
        let perps = perps_fixture();
        let zusd = zusd_fixture();
        validate_spot(&spot).unwrap();
        validate_perps(&perps).unwrap();
        validate_zusd(&zusd).unwrap();
        let typed_spot = serde_json::from_value::<SpotRecursiveLeafInputV1>(spot.clone()).unwrap();
        let typed_perps =
            serde_json::from_value::<PerpsNpRecursiveLeafInputV1>(perps.clone()).unwrap();
        let typed_zusd = serde_json::from_value::<ZusdRecursiveLeafInputV1>(zusd.clone()).unwrap();
        assert_eq!(
            typed_spot.spot_input.txs[0]
                .app_ops
                .intents
                .iter()
                .map(|signed| spot_variant_name(&signed.intent))
                .collect::<Vec<_>>(),
            [
                "CreatePool",
                "SwapExactIn",
                "AddLiquidity",
                "RemoveLiquidity",
                "SwapExactOut",
                "Route",
            ]
        );
        assert_eq!(
            typed_perps
                .perps_input
                .actions
                .iter()
                .map(perps_variant_name)
                .collect::<Vec<_>>(),
            [
                "InitMarket",
                "DepositCollateral",
                "WithdrawCollateral",
                "SubmitIntent",
                "RunEpoch",
            ]
        );
        assert_eq!(
            zusd_variant_name(&typed_zusd.zusd_input.operation),
            "DepositMint"
        );
        assert_eq!(serde_json::to_value(typed_spot).unwrap(), spot);
        assert_eq!(serde_json::to_value(typed_perps).unwrap(), perps);
        assert_eq!(serde_json::to_value(typed_zusd).unwrap(), zusd);
    }

    #[test]
    fn every_reachable_application_object_field_is_required() {
        for case in cases() {
            let mut fields = Vec::new();
            collect_object_fields(&case.value, "", &mut fields);
            for (pointer, field) in fields {
                let mut mutated = case.value.clone();
                object_mut_at(&mut mutated, &pointer).remove(&field);
                assert!(
                    (case.validate)(&mutated).is_err(),
                    "{} accepted removal of {pointer}/{field}",
                    case.name
                );
            }
        }
    }

    #[test]
    fn every_reachable_application_object_rejects_unknown_fields() {
        for case in cases() {
            let mut pointers = Vec::new();
            collect_object_pointers(&case.value, "", &mut pointers);
            for pointer in pointers {
                let mut mutated = case.value.clone();
                object_mut_at(&mut mutated, &pointer)
                    .insert("__unknown".to_string(), Value::Bool(true));
                assert!(
                    (case.validate)(&mutated).is_err(),
                    "{} accepted unknown field at {pointer}",
                    case.name
                );
            }
        }
    }

    #[test]
    fn every_reachable_application_value_rejects_a_wrong_json_type() {
        for case in cases() {
            let mut pointers = Vec::new();
            collect_value_pointers(&case.value, "", &mut pointers);
            for pointer in pointers {
                let mut mutated = case.value.clone();
                let target = mutated.pointer_mut(&pointer).unwrap();
                *target = wrong_type(target);
                assert!(
                    (case.validate)(&mutated).is_err(),
                    "{} accepted wrong type at {pointer}",
                    case.name
                );
            }
        }
    }

    #[test]
    fn required_option_fields_accept_explicit_null_only_at_their_typed_positions() {
        let mut spot = spot_fixture();
        for pointer in [
            "/spot_input/pre_state/vault",
            "/spot_input/pre_state/oracle",
            "/spot_input/protocol_fee_recipient_pubkey",
            "/spot_input/route_price_interval_authority",
            "/spot_input/route_price_interval_authority_policy",
            "/spot_input/route_price_interval_max_width_bps",
        ] {
            *spot.pointer_mut(pointer).unwrap() = Value::Null;
        }
        for index in 0..6 {
            *spot
                .pointer_mut(&format!(
                    "/spot_input/txs/0/app_ops/intents/{index}/signature"
                ))
                .unwrap() = Value::Null;
            let intent = spot
                .pointer_mut(&format!("/spot_input/txs/0/app_ops/intents/{index}/intent"))
                .unwrap()
                .as_object_mut()
                .unwrap();
            let payload = intent.values_mut().next().unwrap();
            payload
                .as_object_mut()
                .unwrap()
                .insert("salt".to_string(), Value::Null);
        }
        validate_spot(&spot).unwrap();
        serde_json::from_value::<SpotRecursiveLeafInputV1>(spot).unwrap();

        let mut perps = perps_fixture();
        *perps
            .pointer_mut("/perps_input/actions/1/DepositCollateral/collateral_binding")
            .unwrap() = Value::Null;
        validate_perps(&perps).unwrap();
        serde_json::from_value::<PerpsNpRecursiveLeafInputV1>(perps).unwrap();
    }

    fn duplicate_field_json(value: &Value, key: &str, duplicate_value: &Value) -> String {
        let mut raw = serde_json::to_string(value).unwrap();
        let marker = format!("\"{key}\":");
        let position = raw.find(&marker).unwrap();
        let duplicate = format!(
            "\"{key}\":{},",
            serde_json::to_string(duplicate_value).unwrap()
        );
        raw.insert_str(position, &duplicate);
        raw
    }

    #[test]
    fn strict_request_parser_rejects_nested_duplicates_for_each_application_surface() {
        for (value, key, duplicate) in [
            (spot_fixture(), "block_timestamp", json!(1)),
            (perps_fixture(), "actions", json!([])),
            (zusd_fixture(), "operation", json!({})),
        ] {
            let raw = duplicate_field_json(&value, key, &duplicate);
            assert!(
                crate::parse_request_json(&raw)
                    .unwrap_err()
                    .contains("duplicate JSON object key"),
                "duplicate key {key} unexpectedly parsed"
            );
        }
    }

    #[test]
    fn source_json_bytes_remain_non_authoritative_for_leaf_generation_ingress() {
        for case in cases() {
            let compact = serde_json::to_string(&case.value).unwrap();
            let pretty = serde_json::to_string_pretty(&case.value).unwrap();
            assert_ne!(compact.as_bytes(), pretty.as_bytes());
            let compact_value = crate::parse_request_json(&compact).unwrap();
            let pretty_value = crate::parse_request_json(&pretty).unwrap();
            assert_eq!(compact_value, pretty_value);
            (case.validate)(&compact_value).unwrap();
            (case.validate)(&pretty_value).unwrap();
        }
    }

    fn arbitrary_number(raw: &str) -> Value {
        serde_json::from_str(raw).unwrap()
    }

    #[test]
    fn integer_fields_enforce_plain_decimal_lexemes_and_exact_rust_ranges() {
        let mut cases = Vec::new();

        let mut value = spot_fixture();
        value["public_policy_hash"][0] = arbitrary_number("256");
        cases.push(("u8 overflow", value, validate_spot as WireValidator));

        let mut value = spot_fixture();
        value["risc0_image_id"][0] = arbitrary_number("4294967296");
        cases.push(("u32 overflow", value, validate_spot as WireValidator));

        let mut value = spot_fixture();
        value["epoch_id"] = arbitrary_number("18446744073709551616");
        cases.push(("u64 overflow", value, validate_spot as WireValidator));

        let mut value = spot_fixture();
        value["spot_input"]["pre_state"]["balances"][0]["amount"] =
            arbitrary_number("340282366920938463463374607431768211456");
        cases.push(("u128 overflow", value, validate_spot as WireValidator));

        let mut value = perps_fixture();
        value["perps_input"]["actions"][4]["RunEpoch"]["funding_rate_bps"] =
            arbitrary_number("2147483648");
        cases.push(("i32 overflow", value, validate_perps as WireValidator));

        let mut value = perps_fixture();
        value["perps_input"]["pre_state"]["index_price_e8"] =
            arbitrary_number("170141183460469231731687303715884105728");
        cases.push(("i128 overflow", value, validate_perps as WireValidator));

        let mut value = spot_fixture();
        value["epoch_id"] = arbitrary_number("1e0");
        cases.push(("integer exponent", value, validate_spot as WireValidator));

        let mut value = perps_fixture();
        value["perps_input"]["pre_state"]["index_price_e8"] = arbitrary_number("1.0");
        cases.push(("integer fraction", value, validate_perps as WireValidator));

        for (name, value, validate) in cases {
            assert!(validate(&value).is_err(), "accepted {name}");
        }

        let mut maximum = spot_fixture();
        maximum["spot_input"]["pre_state"]["balances"][0]["amount"] =
            arbitrary_number("340282366920938463463374607431768211455");
        validate_spot(&maximum).unwrap();
        serde_json::from_value::<SpotRecursiveLeafInputV1>(maximum).unwrap();
    }

    #[test]
    fn reject_precedence_is_wrapper_then_payload_then_deeper_object() {
        let mut value = spot_fixture();
        value["__unknown"] = Value::Bool(true);
        value["spot_input"]["__unknown"] = Value::Bool(true);
        value["spot_input"]["pre_state"]["__unknown"] = Value::Bool(true);
        assert_eq!(
            validate_spot(&value).unwrap_err(),
            "spot_recursive_leaf_input contains unknown field `__unknown`"
        );
        value.as_object_mut().unwrap().remove("__unknown");
        assert_eq!(
            validate_spot(&value).unwrap_err(),
            "spot_recursive_leaf_input.spot_input contains unknown field `__unknown`"
        );
        value["spot_input"]
            .as_object_mut()
            .unwrap()
            .remove("__unknown");
        assert_eq!(
            validate_spot(&value).unwrap_err(),
            "spot_recursive_leaf_input.spot_input.pre_state contains unknown field `__unknown`"
        );
    }
}
