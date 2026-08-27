//! Bounded Rust refinement scenarios for the `ASSET_TRANSFER` corpus.
//!
//! The corpus in `tests/data/asset_transfer_refinement_v1.json` and its oracle in
//! `tools/check_asset_transfer_refinement_v1.py` are specified independently of
//! both runtimes. This file only adapts the fixture into typed values at the
//! comparison boundary and confronts the Rust transition with it.
//!
//! Authority: bounded executable research evidence. Nothing here creates
//! production, settlement, release, migration, proof, or value-moving authority,
//! and `custody_domain` stays an accounting-location/control-domain label.
//!
//! One case is a documented expected failing counterexample. See
//! `rust_transition_matches_the_intended_rule_on_the_ordering_counterexample`.

use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::PathBuf;

use serde_json::{json, Map, Value};
use zenodex_global_settlement_abi_v1::{
    transition_asset_transfer_v1, AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1,
    AssetTransferPolicyV1, AssetTransferRejectCodeV1, AssetTransferResultV1, AssetTransferStateV1,
    EconomicAmountV1, LaneIdV1, RootV1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

const CORPUS_SCHEMA_V1: &str = "zenodex/asset-transfer-refinement-corpus/v1";
const COUNTEREXAMPLE_ID: &str =
    "precedence-insufficient-balance-over-recipient-overflow-sender-sorts-last";
const CASE_KEYS: [&str; 11] = [
    "case_id",
    "title",
    "classes",
    "cross_language",
    "fee_owner_role",
    "precedence_pair",
    "rust_observed_code",
    "context",
    "pre_state",
    "command",
    "expected",
];
const CONTEXT_KEYS: [&str; 8] = [
    "chain_id",
    "deployment_root",
    "profile_root",
    "writer_epoch",
    "module_release_id",
    "command_occurrence_id",
    "subject_id",
    "grant_root",
];
const STATE_KEYS: [&str; 4] = ["module_release_id", "policies", "balances", "supplies"];
const POLICY_KEYS: [&str; 4] = ["asset", "fee_owner", "transfer_fee_atoms", "enabled"];
const BALANCE_KEYS: [&str; 4] = ["owner", "asset", "custody_domain", "amount_atoms"];
const SUPPLY_KEYS: [&str; 2] = ["asset", "amount_atoms"];
const COMMAND_KEYS: [&str; 6] = [
    "command_kind",
    "asset",
    "sender",
    "recipient",
    "amount_atoms",
    "max_fee_atoms",
];

fn corpus() -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/asset_transfer_refinement_v1.json");
    let value: Value = serde_json::from_slice(&fs::read(path).expect("corpus must be readable"))
        .expect("corpus must be valid JSON");
    assert_eq!(value["schema"].as_str(), Some(CORPUS_SCHEMA_V1));
    value
}

fn object<'a>(value: &'a Value, marker: &str, keys: &[&str]) -> &'a Map<String, Value> {
    let map = value
        .as_object()
        .unwrap_or_else(|| panic!("{marker} must be a JSON object"));
    let mut present = map.keys().map(String::as_str).collect::<Vec<_>>();
    present.sort_unstable();
    let mut declared = keys.to_vec();
    declared.sort_unstable();
    assert_eq!(
        present, declared,
        "{marker} must carry exactly the declared fields"
    );
    map
}

fn array<'a>(value: &'a Value, marker: &str) -> &'a Vec<Value> {
    value
        .as_array()
        .unwrap_or_else(|| panic!("{marker} must be a JSON array"))
}

fn text<'a>(map: &'a Map<String, Value>, key: &str, marker: &str) -> &'a str {
    map.get(key)
        .and_then(Value::as_str)
        .unwrap_or_else(|| panic!("{marker}.{key} must be a JSON string"))
}

fn atoms(map: &Map<String, Value>, key: &str, marker: &str) -> u128 {
    let raw = text(map, key, marker);
    let parsed = raw
        .parse::<u128>()
        .unwrap_or_else(|_| panic!("{marker}.{key} must be an unsigned 128-bit atom string"));
    assert_eq!(
        parsed.to_string(),
        raw,
        "{marker}.{key} must be canonical base 10"
    );
    parsed
}

fn flag(map: &Map<String, Value>, key: &str, marker: &str) -> bool {
    map.get(key)
        .and_then(Value::as_bool)
        .unwrap_or_else(|| panic!("{marker}.{key} must be a JSON boolean"))
}

fn epoch(map: &Map<String, Value>, key: &str, marker: &str) -> u64 {
    let value = map
        .get(key)
        .unwrap_or_else(|| panic!("{marker}.{key} is missing"));
    assert!(
        value.is_u64(),
        "{marker}.{key} must be a JSON integer with exact unsigned type"
    );
    value.as_u64().expect("checked immediately above")
}

fn root(map: &Map<String, Value>, key: &str, marker: &str) -> RootV1 {
    RootV1::parse(text(map, key, marker).to_owned(), "corpus root", false)
        .unwrap_or_else(|_| panic!("{marker}.{key} must be a canonical nonzero root"))
}

fn build_context(value: &Value) -> AssetTransferContextV1 {
    let map = object(value, "context", &CONTEXT_KEYS);
    AssetTransferContextV1 {
        chain_id: text(map, "chain_id", "context").to_owned(),
        deployment_root: root(map, "deployment_root", "context"),
        profile_root: root(map, "profile_root", "context"),
        writer_epoch: epoch(map, "writer_epoch", "context"),
        module_release_id: root(map, "module_release_id", "context"),
        command_occurrence_id: root(map, "command_occurrence_id", "context"),
        subject_id: text(map, "subject_id", "context").to_owned(),
        grant_root: root(map, "grant_root", "context"),
    }
}

fn build_state(value: &Value) -> AssetTransferStateV1 {
    let map = object(value, "pre_state", &STATE_KEYS);
    let policies = array(&map["policies"], "pre_state.policies")
        .iter()
        .map(|row| {
            let fields = object(row, "pre_state.policies[]", &POLICY_KEYS);
            AssetTransferPolicyV1 {
                asset: text(fields, "asset", "policy").to_owned(),
                fee_owner: text(fields, "fee_owner", "policy").to_owned(),
                transfer_fee_atoms: atoms(fields, "transfer_fee_atoms", "policy"),
                enabled: flag(fields, "enabled", "policy"),
            }
        })
        .collect();
    let balances = array(&map["balances"], "pre_state.balances")
        .iter()
        .map(|row| {
            let fields = object(row, "pre_state.balances[]", &BALANCE_KEYS);
            EconomicAmountV1 {
                owner: text(fields, "owner", "balance").to_owned(),
                asset: text(fields, "asset", "balance").to_owned(),
                custody_domain: text(fields, "custody_domain", "balance").to_owned(),
                amount_atoms: atoms(fields, "amount_atoms", "balance"),
            }
        })
        .collect();
    let supplies = array(&map["supplies"], "pre_state.supplies")
        .iter()
        .map(|row| {
            let fields = object(row, "pre_state.supplies[]", &SUPPLY_KEYS);
            AssetSupplyV1 {
                asset: text(fields, "asset", "supply").to_owned(),
                amount_atoms: atoms(fields, "amount_atoms", "supply"),
            }
        })
        .collect();
    AssetTransferStateV1 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(map, "module_release_id", "pre_state"),
        policies,
        balances,
        supplies,
    }
}

fn build_command(value: &Value) -> AssetTransferCommandV1 {
    let map = object(value, "command", &COMMAND_KEYS);
    AssetTransferCommandV1 {
        command_kind: text(map, "command_kind", "command").to_owned(),
        asset: text(map, "asset", "command").to_owned(),
        sender: text(map, "sender", "command").to_owned(),
        recipient: text(map, "recipient", "command").to_owned(),
        amount_atoms: atoms(map, "amount_atoms", "command"),
        max_fee_atoms: atoms(map, "max_fee_atoms", "command"),
    }
}

fn observed(pre_state: &AssetTransferStateV1, result: &AssetTransferResultV1) -> Value {
    let pre_root = pre_state.state_root().expect("pre state must hash");
    match result {
        AssetTransferResultV1::Rejected(rejected) => json!({
            "outcome": "rejected",
            "reject_code": serde_json::to_value(rejected.code).expect("code must serialize"),
            "effects_empty": rejected.effects.is_empty(),
            "state_root_unchanged": rejected.pre_state_root == pre_root
                && rejected.post_state_root == pre_root,
        }),
        AssetTransferResultV1::Accepted(accepted) => {
            let conservation = &accepted.effects.asset_conservation[0];
            json!({
                "outcome": "accepted",
                "post_balances": accepted
                    .post_state
                    .balances
                    .iter()
                    .map(|row| json!({
                        "owner": row.owner,
                        "asset": row.asset,
                        "custody_domain": row.custody_domain,
                        "amount_atoms": row.amount_atoms.to_string(),
                    }))
                    .collect::<Vec<_>>(),
                "effect_rows": accepted
                    .effects
                    .rows
                    .iter()
                    .map(|row| json!({
                        "kind": serde_json::to_value(row.kind).expect("kind must serialize"),
                        "principal": row.principal,
                        "asset": row.asset,
                        "custody_domain": row.custody_domain,
                        "delta_atoms": row.delta_atoms.to_string(),
                    }))
                    .collect::<Vec<_>>(),
                "fee_conservation": accepted
                    .effects
                    .fee_conservation
                    .iter()
                    .map(|row| json!({
                        "asset": row.asset,
                        "fee_charged_atoms": row.fee_charged_atoms.to_string(),
                        "current_allocations_atoms": row.current_allocations_atoms.to_string(),
                        "carried_residue_atoms": row.carried_residue_atoms.to_string(),
                    }))
                    .collect::<Vec<_>>(),
                "asset_conservation": json!({
                    "asset": conservation.asset,
                    "owned_and_custodied_pre_atoms":
                        conservation.owned_and_custodied_pre_atoms.to_string(),
                    "owned_and_custodied_post_atoms":
                        conservation.owned_and_custodied_post_atoms.to_string(),
                    "supply_pre_atoms": conservation.supply_pre_atoms.to_string(),
                    "supply_post_atoms": conservation.supply_post_atoms.to_string(),
                    "authorized_issue_atoms": conservation.authorized_issue_atoms.to_string(),
                    "authorized_burn_atoms": conservation.authorized_burn_atoms.to_string(),
                }),
                "occurrence_consumptions": accepted
                    .effects
                    .occurrence_consumptions
                    .iter()
                    .map(|value| Value::String(value.as_str().to_owned()))
                    .collect::<Vec<_>>(),
                "external_outbox_enqueue": Vec::<Value>::new(),
            })
        }
    }
}

fn assert_structural_obligations(pre_state: &AssetTransferStateV1, result: &AssetTransferResultV1) {
    match result {
        AssetTransferResultV1::Rejected(rejected) => {
            assert_eq!(rejected.pre_state_root, rejected.post_state_root);
            assert!(rejected.effects.is_empty());
            assert!(rejected.effects.rows.is_empty());
            assert!(rejected.effects.lane_writes.is_empty());
            assert!(rejected.effects.occurrence_consumptions.is_empty());
        }
        AssetTransferResultV1::Accepted(accepted) => {
            accepted.validate().expect("accepted result must validate");
            let asset = accepted.effects.asset_conservation[0].asset.as_str();
            let pre_total = pre_state
                .balances
                .iter()
                .filter(|row| row.asset == asset)
                .map(|row| row.amount_atoms)
                .sum::<u128>();
            let post_total = accepted
                .post_state
                .balances
                .iter()
                .filter(|row| row.asset == asset)
                .map(|row| row.amount_atoms)
                .sum::<u128>();
            assert_eq!(pre_total, post_total, "account totals must be conserved");
            assert_eq!(accepted.post_state.supplies, pre_state.supplies);
            assert_eq!(accepted.post_state.policies, pre_state.policies);
            assert!(accepted
                .post_state
                .balances
                .iter()
                .all(|row| row.amount_atoms > 0));
            assert!(accepted.effects.external_outbox_enqueue.is_empty());
            assert_eq!(accepted.effects.lane_writes.len(), 1);
            let write = &accepted.effects.lane_writes[0];
            assert_eq!(write.lane_id, LaneIdV1::ASSET_TRANSFER);
            assert_eq!(write.pre_root, pre_state.state_root().expect("pre root"));
            assert_eq!(
                write.post_root,
                accepted.post_state.state_root().expect("post root")
            );
            assert_eq!(
                accepted
                    .effects
                    .rows
                    .iter()
                    .filter(|row| serde_json::to_value(row.kind).expect("kind")
                        == Value::String("ACCOUNT_MOVEMENT".to_owned()))
                    .map(|row| row.delta_atoms)
                    .sum::<i128>(),
                0,
                "account movement deltas must net to zero"
            );
        }
    }
}

#[test]
fn rust_transition_refines_every_agreeing_corpus_case() {
    // Arrange
    let corpus = corpus();
    let repetitions = corpus["deterministic_replay_repetitions"]
        .as_u64()
        .expect("replay repetitions must be an integer");
    assert!(repetitions >= 2);
    let mut checked = 0_usize;

    for case in array(&corpus["cases"], "cases") {
        let fields = object(case, "case", &CASE_KEYS);
        if text(fields, "cross_language", "case") != "agree" {
            continue;
        }
        let case_id = text(fields, "case_id", "case");
        let context = build_context(&fields["context"]);
        let pre_state = build_state(&fields["pre_state"]);
        let command = build_command(&fields["command"]);

        // Act
        let mut replays = Vec::new();
        for _ in 0..repetitions {
            let result = transition_asset_transfer_v1(&context, &pre_state, &command)
                .expect("typed transition must evaluate");
            assert_structural_obligations(&pre_state, &result);
            replays.push(observed(&pre_state, &result));
        }

        // Assert
        assert_eq!(&replays[0], &fields["expected"], "case {case_id}");
        assert!(
            replays.iter().all(|replay| replay == &replays[0]),
            "case {case_id} must replay deterministically"
        );
        checked += 1;
    }
    assert!(
        checked >= 30,
        "the corpus must retain its agreeing cases, found {checked}"
    );
}

/// Expected failing counterexample until the Rust transition is repaired.
///
/// The corpus records the intended, principal-spelling-independent rule: sender
/// insufficiency outranks any credited-principal `BALANCE_OVERFLOW`. The current
/// Rust transition scans a lexicographically ordered `BTreeMap` of deltas, so a
/// sender whose name sorts after the recipient is evaluated last and the
/// recipient's overflow is reported instead. Python already applies the intended
/// semantic role order. This branch deliberately does not repair runtime code.
#[test]
fn rust_transition_matches_the_intended_rule_on_the_ordering_counterexample() {
    // Arrange
    let corpus = corpus();
    let case = array(&corpus["cases"], "cases")
        .iter()
        .find(|case| case["case_id"].as_str() == Some(COUNTEREXAMPLE_ID))
        .expect("the corpus must retain the recorded counterexample");
    let fields = object(case, "case", &CASE_KEYS);
    assert_eq!(text(fields, "cross_language", "case"), "rust_defect_pending_repair");
    let context = build_context(&fields["context"]);
    let pre_state = build_state(&fields["pre_state"]);
    let command = build_command(&fields["command"]);

    // Act
    let result = transition_asset_transfer_v1(&context, &pre_state, &command)
        .expect("typed transition must evaluate");

    // Assert
    assert_structural_obligations(&pre_state, &result);
    assert_eq!(
        &observed(&pre_state, &result),
        &fields["expected"],
        "known pre-existing defect: the corpus records rust_observed_code={} for {COUNTEREXAMPLE_ID}; \
         checking the sender before any credited principal, independently of principal spelling, turns this red into green",
        text(fields, "rust_observed_code", "case")
    );
}

#[test]
fn corpus_precedence_names_decode_to_the_runtime_reject_enum() {
    // Arrange
    let corpus = corpus();

    // Act / Assert
    for code in array(&corpus["reject_precedence"], "reject_precedence") {
        let decoded: AssetTransferRejectCodeV1 = serde_json::from_value(code.clone())
            .expect("every declared reject code must decode to the runtime enum");
        assert_eq!(&serde_json::to_value(decoded).expect("code must serialize"), code);
    }
    assert!(serde_json::from_value::<AssetTransferRejectCodeV1>(Value::String(
        "NOT_A_CODE".to_owned()
    ))
    .is_err());
}

#[test]
fn strict_corpus_decoding_rejects_unknown_fields_and_wrong_scalar_types() {
    // Arrange
    let corpus = corpus();
    let case = corpus["cases"][0].clone();
    let mut unknown_field = case.clone();
    unknown_field
        .as_object_mut()
        .expect("case must be an object")
        .insert("opaque_authority".to_owned(), Value::Bool(true));
    let mut bool_epoch = case.clone();
    bool_epoch["context"]["writer_epoch"] = Value::Bool(true);
    let mut float_epoch = case.clone();
    float_epoch["context"]["writer_epoch"] = json!(7.0);
    let mut numeric_atoms = case.clone();
    numeric_atoms["command"]["amount_atoms"] = json!(30);
    let mut noncanonical_atoms = case;
    noncanonical_atoms["command"]["amount_atoms"] = Value::String("030".to_owned());

    // Act / Assert
    let hostile: [(&str, Box<dyn Fn()>); 5] = [
        (
            "unknown_case_field",
            Box::new(move || {
                object(&unknown_field, "case", &CASE_KEYS);
            }),
        ),
        (
            "bool_as_writer_epoch",
            Box::new(move || {
                build_context(&bool_epoch["context"]);
            }),
        ),
        (
            "integral_float_writer_epoch",
            Box::new(move || {
                build_context(&float_epoch["context"]);
            }),
        ),
        (
            "atoms_as_json_int",
            Box::new(move || {
                build_command(&numeric_atoms["command"]);
            }),
        ),
        (
            "noncanonical_atoms",
            Box::new(move || {
                build_command(&noncanonical_atoms["command"]);
            }),
        ),
    ];
    for (name, mutation) in hostile {
        assert!(
            catch_unwind(AssertUnwindSafe(mutation)).is_err(),
            "{name} must fail closed"
        );
    }
}
