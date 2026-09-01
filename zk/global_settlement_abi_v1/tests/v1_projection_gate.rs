//! Compiled binding of the V1 terminal and outbox projections (O-008 replay gate).
//!
//! The O-008 admission core scans the pinned source bytes; this gate binds the
//! *compiled* types: serde field order from direct struct serialisation, unknown
//! field rejection at the record and through both state containers, and a
//! seeded property test over generated unknown keys (the seed is printed so a
//! failure replays). The admission core pins this file's field tables and test
//! names, so the gate cannot be replaced by vacuous tests. It is executed only
//! under `--replay` and reported NOT_RUN otherwise. Authority: NONE.

use std::time::{SystemTime, UNIX_EPOCH};

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
const TERMINAL_FORBIDDEN: [&str; 6] = [
    "liability_domain",
    "control_domain",
    "custody_domain",
    "custody_principal",
    "controlling_principal",
    "source_principal",
];
const OUTBOX_FORBIDDEN: [&str; 2] = ["asset", "amount_atoms"];
const SEEDED_KEYS: usize = 64;
const ROOT_HEX: &str = "0x1111111111111111111111111111111111111111111111111111111111111111";
const FIXTURE: &str =
    include_str!("../../../tests/data/global_claimant_backing_guard_v1_golden.json");

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

/// Top-level object keys of a serialised JSON object, in wire order.
///
/// A small tokenizer that understands strings (with escapes) and nesting, so it
/// stays sound if a record ever gains a structured field.
fn declared_order(serialised: &str) -> Vec<String> {
    let bytes = serialised.as_bytes();
    let mut keys = Vec::new();
    let mut depth = 0usize;
    let mut index = 0usize;
    let mut expect_key = false;
    while index < bytes.len() {
        match bytes[index] {
            b'{' | b'[' => {
                depth += 1;
                expect_key = bytes[index] == b'{' && depth == 1;
                index += 1;
            }
            b'}' | b']' => {
                depth = depth.saturating_sub(1);
                index += 1;
            }
            b',' => {
                expect_key = depth == 1;
                index += 1;
            }
            b'"' => {
                let mut end = index + 1;
                let mut text = Vec::new();
                while end < bytes.len() && bytes[end] != b'"' {
                    if bytes[end] == b'\\' {
                        end += 1;
                    }
                    text.push(bytes[end]);
                    end += 1;
                }
                if expect_key && depth == 1 {
                    keys.push(String::from_utf8(text).expect("utf-8 key"));
                    expect_key = false;
                }
                index = end + 1;
            }
            _ => index += 1,
        }
    }
    keys
}

fn recorded_state() -> Value {
    let fixture: Value = serde_json::from_str(FIXTURE).expect("fixture is JSON");
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
    vector["state"].clone()
}

fn assert_unknown_field<T: serde::de::DeserializeOwned>(value: Value, label: &str) {
    let error = serde_json::from_value::<T>(value)
        .err()
        .unwrap_or_else(|| panic!("{label}: unknown field must be rejected"));
    assert!(
        error.to_string().contains("unknown field"),
        "{label}: {error}"
    );
}

fn seeded_keys() -> (u64, Vec<String>) {
    let seed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0)
        ^ u64::from(std::process::id()).rotate_left(32);
    let mut state = seed | 1;
    let mut keys = Vec::with_capacity(SEEDED_KEYS);
    for _ in 0..SEEDED_KEYS {
        // xorshift64*: deterministic from the printed seed.
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        let value = state.wrapping_mul(0x2545_F491_4F6C_DD1D);
        keys.push(format!("k_{value:016x}"));
    }
    (seed, keys)
}

#[test]
fn terminal_record_serialises_fields_in_declared_order() {
    let record: TerminalObligationV1 =
        serde_json::from_value(terminal_value()).expect("terminal decodes");
    assert_eq!(record.lane_id, LaneIdV1::ASSET_TRANSFER);
    assert_eq!(record.status, TerminalObligationStatusV1::OPEN);
    let raw = serde_json::to_string(&record).expect("terminal encodes");
    assert_eq!(declared_order(&raw), TERMINAL_FIELDS);
    let nested = "{\"a\":{\"x\":[1,2],\"y\":\"b,c\"},\"b\":\"q\\\"z\",\"c\":3}";
    assert_eq!(declared_order(nested), ["a", "b", "c"]);
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
    for extra in TERMINAL_FORBIDDEN {
        let mut value = terminal_value();
        value[extra] = json!("hidden");
        assert_unknown_field::<TerminalObligationV1>(value, extra);
    }
}

#[test]
fn outbox_record_rejects_unknown_fields() {
    for extra in OUTBOX_FORBIDDEN {
        let mut value = outbox_value();
        value[extra] = json!(1);
        assert_unknown_field::<OutboxStateV1>(value, extra);
    }
}

#[test]
fn state_container_rejects_unknown_terminal_field_through_the_compiled_type() {
    let state = recorded_state();
    let decoded: GlobalEconomicStateV1 =
        serde_json::from_value(state.clone()).expect("recorded state decodes");
    assert!(!decoded.terminal_obligations.is_empty());
    for extra in TERMINAL_FORBIDDEN {
        let mut widened = state.clone();
        widened["terminal_obligations"][0][extra] = json!("hidden-domain");
        assert_unknown_field::<GlobalEconomicStateV1>(widened, extra);
    }
}

#[test]
fn state_container_rejects_unknown_outbox_field_through_the_compiled_type() {
    let mut state = recorded_state();
    state["outbox"] = json!([outbox_value()]);
    let decoded: GlobalEconomicStateV1 =
        serde_json::from_value(state.clone()).expect("state with an outbox row decodes");
    assert_eq!(decoded.outbox.len(), 1);
    for extra in OUTBOX_FORBIDDEN {
        let mut widened = state.clone();
        widened["outbox"][0][extra] = json!(1);
        assert_unknown_field::<GlobalEconomicStateV1>(widened, extra);
    }
}

#[test]
fn records_and_containers_reject_seeded_unknown_keys() {
    let (seed, keys) = seeded_keys();
    println!("seeded_unknown_keys seed={seed:#018x}");
    let mut state = recorded_state();
    state["outbox"] = json!([outbox_value()]);
    for key in &keys {
        let mut terminal = terminal_value();
        terminal[key.as_str()] = json!("x");
        assert_unknown_field::<TerminalObligationV1>(terminal, key);
        let mut outbox = outbox_value();
        outbox[key.as_str()] = json!("x");
        assert_unknown_field::<OutboxStateV1>(outbox, key);
        let mut widened = state.clone();
        widened["terminal_obligations"][0][key.as_str()] = json!("x");
        assert_unknown_field::<GlobalEconomicStateV1>(widened, key);
        let mut widened = state.clone();
        widened["outbox"][0][key.as_str()] = json!("x");
        assert_unknown_field::<GlobalEconomicStateV1>(widened, key);
    }
}
