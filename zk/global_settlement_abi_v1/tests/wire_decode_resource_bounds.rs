use serde_json::{json, Value};
use zenodex_global_settlement_abi_v1::*;

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "wire resource-bound test root",
        false,
    )
    .unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(
        ZERO_ROOT_V1.to_owned(),
        "wire resource-bound zero root",
        true,
    )
    .unwrap()
}

fn state() -> GlobalEconomicStateV1 {
    GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "wire-resource-bound-test".to_owned(),
        deployment_root: root(1),
        writer_epoch: 1,
        height: 1,
        profile_root: root(2),
        lane_roots: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane_id)| LaneStateRootV1 {
                lane_id: *lane_id,
                module_release_id: root(100 + u64::try_from(index).unwrap()),
                enabled: false,
                state_root: zero_root(),
            })
            .collect(),
        balances: vec![],
        supplies: vec![],
        custody: vec![],
        liabilities: vec![],
        reserves: vec![],
        oracle_occurrences: vec![],
        replay_state: vec![],
        terminal_obligations: vec![],
        history_root: zero_root(),
        outbox: vec![],
    }
}

fn empty_plan() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

fn repeated(row: Value, count: usize) -> Value {
    Value::Array(vec![row; count])
}

fn assert_state_wire_bound(field: &str, row: Value, maximum: usize, label: &str) {
    let mut at_limit = serde_json::to_value(state()).unwrap();
    at_limit[field] = repeated(row.clone(), maximum);
    serde_json::from_value::<GlobalEconomicStateV1>(at_limit).unwrap();

    let mut above_limit = serde_json::to_value(state()).unwrap();
    above_limit[field] = repeated(row, maximum + 1);
    let error = serde_json::from_value::<GlobalEconomicStateV1>(above_limit).unwrap_err();
    assert!(
        error.to_string().contains(label),
        "unexpected decode error for {field}: {error}"
    );
}

fn assert_effect_wire_bound(field: &str, row: Value, maximum: usize, label: &str) {
    let mut at_limit = serde_json::to_value(empty_plan()).unwrap();
    at_limit[field] = repeated(row.clone(), maximum);
    serde_json::from_value::<GlobalEconomicEffectPlanV1>(at_limit).unwrap();

    let mut above_limit = serde_json::to_value(empty_plan()).unwrap();
    above_limit[field] = repeated(row, maximum + 1);
    let error = serde_json::from_value::<GlobalEconomicEffectPlanV1>(above_limit).unwrap_err();
    assert!(
        error.to_string().contains(label),
        "unexpected decode error for {field}: {error}"
    );
}

#[test]
fn global_state_wire_decode_enforces_every_collection_bound() {
    let fixture = state();
    assert_state_wire_bound(
        "lane_roots",
        serde_json::to_value(&fixture.lane_roots[0]).unwrap(),
        ALL_LANE_IDS_V1.len(),
        "global state lane roots",
    );
    let amount = json!({
        "owner": "alice",
        "asset": "USD",
        "custody_domain": "accounts",
        "amount_atoms": 1,
    });
    for (field, label) in [
        ("balances", "global state balances"),
        ("custody", "global state custody"),
        ("liabilities", "global state liabilities"),
        ("reserves", "global state reserves"),
    ] {
        assert_state_wire_bound(
            field,
            amount.clone(),
            MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
            label,
        );
    }
    assert_state_wire_bound(
        "supplies",
        json!({"asset": "USD", "amount_atoms": 1}),
        MAX_GLOBAL_SUPPLY_ROWS_V1,
        "global state supplies",
    );
    assert_state_wire_bound(
        "oracle_occurrences",
        json!({
            "oracle_id": "oracle-usd",
            "occurrence_root": root(10),
            "observed_height": 1,
            "finalized": true,
        }),
        MAX_GLOBAL_ORACLE_ROWS_V1,
        "global state oracle occurrences",
    );
    assert_state_wire_bound(
        "replay_state",
        json!({"replay_id": "replay-1", "occurrence_id": root(11)}),
        MAX_GLOBAL_REPLAY_ROWS_V1,
        "global state replay state",
    );
    assert_state_wire_bound(
        "terminal_obligations",
        json!({
            "obligation_id": "obligation-1",
            "lane_id": "ASSET_TRANSFER",
            "claimant": "alice",
            "asset": "USD",
            "amount_atoms": 1,
            "status": "OPEN",
        }),
        MAX_GLOBAL_TERMINAL_ROWS_V1,
        "global state terminal obligations",
    );
    assert_state_wire_bound(
        "outbox",
        json!({
            "effect_id": root(12),
            "destination_id": "registered-bridge",
            "payload_hash": root(13),
            "commit_id": root(14),
            "status": "PENDING",
        }),
        MAX_GLOBAL_OUTBOX_ROWS_V1,
        "global state outbox",
    );
}

#[test]
fn effect_plan_wire_decode_enforces_every_collection_bound() {
    assert_effect_wire_bound(
        "rows",
        json!({
            "kind": "ACCOUNT_MOVEMENT",
            "principal": "alice",
            "asset": "USD",
            "custody_domain": "accounts",
            "delta_atoms": 1,
        }),
        MAX_EFFECT_PLAN_ROWS_V1,
        "economic effect plan rows",
    );
    assert_effect_wire_bound(
        "asset_conservation",
        json!({
            "asset": "USD",
            "owned_and_custodied_pre_atoms": 0,
            "owned_and_custodied_post_atoms": 0,
            "supply_pre_atoms": 0,
            "supply_post_atoms": 0,
            "authorized_issue_atoms": 0,
            "authorized_burn_atoms": 0,
        }),
        MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1,
        "economic effect plan asset conservation rows",
    );
    assert_effect_wire_bound(
        "fee_conservation",
        json!({
            "asset": "USD",
            "fee_charged_atoms": 0,
            "current_allocations_atoms": 0,
            "carried_residue_atoms": 0,
        }),
        MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1,
        "economic effect plan fee conservation rows",
    );
    assert_effect_wire_bound(
        "lane_writes",
        json!({
            "lane_id": "ASSET_TRANSFER",
            "pre_root": root(1),
            "post_root": root(2),
        }),
        MAX_EFFECT_PLAN_LANE_WRITES_V1,
        "economic effect plan lane writes",
    );
    assert_effect_wire_bound(
        "occurrence_consumptions",
        serde_json::to_value(root(3)).unwrap(),
        MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1,
        "economic effect plan occurrence consumptions",
    );
    assert_effect_wire_bound(
        "external_outbox_enqueue",
        json!({
            "effect_id": root(4),
            "destination_id": "registered-bridge",
            "payload_hash": root(5),
            "adapter_profile_root": root(6),
        }),
        MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1,
        "economic effect plan external outbox rows",
    );
}

#[test]
fn state_decoder_rejects_at_first_excess_row_without_consuming_hostile_tail() {
    let fixture = state();
    let encoded = serde_json::to_string(&fixture).unwrap();
    let original_rows = serde_json::to_string(&fixture.lane_roots).unwrap();
    let row = serde_json::to_string(&fixture.lane_roots[0]).unwrap();
    let excess_rows = std::iter::repeat_n(row, ALL_LANE_IDS_V1.len() + 1)
        .collect::<Vec<_>>()
        .join(",");
    let hostile_rows = format!("[{excess_rows},THIS_TAIL_IS_NOT_JSON");
    let hostile = encoded.replacen(&original_rows, &hostile_rows, 1);

    let error = serde_json::from_str::<GlobalEconomicStateV1>(&hostile).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("global state lane roots exceeds the V1 bound"),
        "decoder consumed the hostile tail instead of rejecting the excess row: {error}"
    );
}

#[test]
fn valid_state_round_trip_preserves_canonical_bytes_and_root() {
    let original = state();
    let bytes = canonical_bytes_v1(&original).unwrap();
    let original_root = original.state_root().unwrap();

    let decoded: GlobalEconomicStateV1 = serde_json::from_slice(&bytes).unwrap();

    assert_eq!(canonical_bytes_v1(&decoded).unwrap(), bytes);
    assert_eq!(decoded.state_root().unwrap(), original_root);
}
