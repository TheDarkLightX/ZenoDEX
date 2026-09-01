//! Compiled binding of the V1 terminal and outbox projections (O-008 replay gate).
//!
//! The O-008 admission core scans the pinned source bytes; this gate binds the
//! *compiled* types: serde field order from direct struct serialisation, unknown
//! field rejection through the state container, and the exact wire key sets.
//! It is executed only under `--replay` and reported NOT_RUN otherwise.
//! Authority: NONE.

use serde_json::{json, Value};
use zenodex_global_settlement_abi_v1::{
    GlobalEconomicStateV1, LaneIdV1, OutboxStateV1, OutboxStatusV1, TerminalObligationStatusV1,
    TerminalObligationV1,
};

const TERMINAL_FIELDS: [&str; 6] = [
    "obligation_id",
    "lane_id",
    "claimant",
    "asset",
    "amount_atoms",
    "status",
];
const OUTBOX_FIELDS: [&str; 5] = [
    "effect_id",
    "destination_id",
    "payload_hash",
    "commit_id",
    "status",
];
const ROOT_HEX: &str = "0x1111111111111111111111111111111111111111111111111111111111111111";

fn terminal_value() -> Value {
    json!({
        "obligation_id": "terminal-1",
        "lane_id": "ASSET_TRANSFER",
        "claimant": "alice",
        "asset": "USD",
        "amount_atoms": 1,
        "status": "OPEN"
    })
}

fn outbox_value() -> Value {
    json!({
        "effect_id": ROOT_HEX,
        "destination_id": "dest-1",
        "payload_hash": ROOT_HEX,
        "commit_id": ROOT_HEX,
        "status": "PENDING"
    })
}

fn declared_order(serialised: &str) -> Vec<String> {
    // serde_json writes struct fields in declaration order; parse the raw text to
    // recover that order without the sorted-key canonical encoder.
    let mut keys = Vec::new();
    let mut rest = serialised;
    while let Some(start) = rest.find('"') {
        let after = &rest[start + 1..];
        let end = after.find('"').expect("closing quote");
        let key = &after[..end];
        let tail = &after[end + 1..];
        if tail.starts_with(':') {
            keys.push(key.to_owned());
            // skip the value up to the next comma at depth zero of this object
            let value_end = tail.find(',').unwrap_or(tail.len());
            rest = &tail[value_end..];
        } else {
            rest = tail;
        }
    }
    keys
}

#[test]
fn terminal_record_serialises_fields_in_declared_order() {
    let record: TerminalObligationV1 =
        serde_json::from_value(terminal_value()).expect("terminal decodes");
    assert_eq!(record.lane_id, LaneIdV1::ASSET_TRANSFER);
    assert_eq!(record.status, TerminalObligationStatusV1::OPEN);
    let raw = serde_json::to_string(&record).expect("terminal encodes");
    assert_eq!(declared_order(&raw), TERMINAL_FIELDS);
}

#[test]
fn outbox_record_serialises_fields_in_declared_order() {
    let record: OutboxStateV1 = serde_json::from_value(outbox_value()).expect("outbox decodes");
    assert_eq!(record.status, OutboxStatusV1::PENDING);
    let raw = serde_json::to_string(&record).expect("outbox encodes");
    assert_eq!(declared_order(&raw), OUTBOX_FIELDS);
}

#[test]
fn terminal_record_rejects_unknown_fields() {
    for extra in ["liability_domain", "custody_principal"] {
        let mut value = terminal_value();
        value[extra] = json!("hidden");
        let error = serde_json::from_value::<TerminalObligationV1>(value)
            .expect_err("unknown terminal field must be rejected");
        assert!(error.to_string().contains("unknown field"), "{error}");
    }
}

#[test]
fn outbox_record_rejects_unknown_fields() {
    for extra in ["asset", "amount_atoms"] {
        let mut value = outbox_value();
        value[extra] = json!(1);
        let error = serde_json::from_value::<OutboxStateV1>(value)
            .expect_err("unknown outbox field must be rejected");
        assert!(error.to_string().contains("unknown field"), "{error}");
    }
}

#[test]
fn state_container_rejects_unknown_terminal_field_through_the_compiled_type() {
    let template = include_str!("../../../tests/data/global_claimant_backing_guard_v1_golden.json");
    let fixture: Value = serde_json::from_str(template).expect("fixture is JSON");
    let (_, vector) = fixture["vectors"]
        .as_object()
        .expect("vectors")
        .iter()
        .find(|(_, v)| {
            !v["state"]["terminal_obligations"]
                .as_array()
                .unwrap()
                .is_empty()
        })
        .expect("a vector with a terminal row");
    let mut state = vector["state"].clone();
    let decoded: GlobalEconomicStateV1 =
        serde_json::from_value(state.clone()).expect("recorded state decodes");
    assert!(!decoded.terminal_obligations.is_empty());
    state["terminal_obligations"][0]["liability_domain"] = json!("hidden-domain");
    let error = serde_json::from_value::<GlobalEconomicStateV1>(state)
        .expect_err("container must reject the widened terminal row");
    assert!(error.to_string().contains("unknown field"), "{error}");
}
