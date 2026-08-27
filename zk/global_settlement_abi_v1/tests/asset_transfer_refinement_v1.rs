//! Bounded Rust refinement scenarios for the `ASSET_TRANSFER` corpus.
//!
//! The corpus in `tests/data/asset_transfer_refinement_v1.json` and its oracle in
//! `tools/check_asset_transfer_refinement_v1.py` are specified independently of
//! both runtimes. This file only adapts the fixture into typed values at the
//! comparison boundary and confronts the Rust transition with it. Every case is
//! expected to pass: historical divergences survive only as `prior_defects`
//! prose whose named regression cases keep them dead.
//!
//! Authority: bounded executable research evidence. Nothing here creates
//! production, settlement, release, migration, proof, or value-moving authority,
//! and `custody_domain` stays an accounting-location/control-domain label.

use std::fs;
use std::path::PathBuf;

use serde_json::{json, Map, Value};
use zenodex_global_settlement_abi_v1::{
    transition_asset_transfer_v1, AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1,
    AssetTransferPolicyV1, AssetTransferRejectCodeV1, AssetTransferResultV1, AssetTransferStateV1,
    EconomicAmountV1, EconomicEffectKindV1, LaneIdV1, RootV1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

const CORPUS_SCHEMA_V1: &str = "zenodex/asset-transfer-refinement-corpus/v1";
const DEFECT_KILLED_V1: &str = "killed_by_this_corpus";
// Closed key sets, one space-separated spec per JSON object shape.
const CASE_KEYS: &str =
    "case_id title classes fee_owner_role precedence_pair context pre_state command expected";
const DEFECT_KEYS: &str = "defect status regression_case_ids";
const CONTEXT_KEYS: &str = "chain_id deployment_root profile_root writer_epoch module_release_id command_occurrence_id subject_id grant_root";
const STATE_KEYS: &str = "module_release_id policies balances supplies";
const POLICY_KEYS: &str = "asset fee_owner transfer_fee_atoms enabled";
const BALANCE_KEYS: &str = "owner asset custody_domain amount_atoms";
const SUPPLY_KEYS: &str = "asset amount_atoms";
const COMMAND_KEYS: &str = "command_kind asset sender recipient amount_atoms max_fee_atoms";

fn corpus() -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/asset_transfer_refinement_v1.json");
    let value: Value = serde_json::from_slice(&fs::read(path).expect("corpus must be readable"))
        .expect("corpus must be valid JSON");
    assert_eq!(value["schema"].as_str(), Some(CORPUS_SCHEMA_V1));
    value
}

/// Closed-schema predicate: exactly the declared keys, no more and no fewer.
fn exact_keys(value: &Value, spec: &str) -> bool {
    let keys = spec.split(' ').collect::<Vec<_>>();
    value
        .as_object()
        .is_some_and(|map| map.len() == keys.len() && keys.iter().all(|key| map.contains_key(*key)))
}

/// Exact-type predicate: an unsigned atom string with no alternative spelling.
fn canonical_atoms(value: &Value) -> Option<u128> {
    let raw = value.as_str()?;
    let parsed = raw.parse::<u128>().ok()?;
    (parsed.to_string() == raw).then_some(parsed)
}

/// Exact-type predicate: a JSON integer, never a bool and never an integral float.
fn exact_u64(value: &Value) -> Option<u64> {
    value
        .is_u64()
        .then(|| value.as_u64().expect("checked immediately above"))
}

fn object<'a>(value: &'a Value, marker: &str, spec: &str) -> &'a Map<String, Value> {
    assert!(
        exact_keys(value, spec),
        "{marker} must carry exactly the fields: {spec}"
    );
    value.as_object().expect("checked by exact_keys")
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
    map.get(key)
        .and_then(canonical_atoms)
        .unwrap_or_else(|| panic!("{marker}.{key} must be a canonical unsigned atom string"))
}

fn root(map: &Map<String, Value>, key: &str, marker: &str) -> RootV1 {
    RootV1::parse(text(map, key, marker).to_owned(), "corpus root", false)
        .unwrap_or_else(|_| panic!("{marker}.{key} must be a canonical nonzero root"))
}

/// Decode every row of a closed-schema array through `row`.
fn each<T>(v: &Value, mark: &str, spec: &str, row: impl Fn(&Map<String, Value>) -> T) -> Vec<T> {
    array(v, mark)
        .iter()
        .map(|item| row(object(item, mark, spec)))
        .collect()
}

fn build_context(value: &Value) -> AssetTransferContextV1 {
    let map = object(value, "context", CONTEXT_KEYS);
    AssetTransferContextV1 {
        chain_id: text(map, "chain_id", "context").to_owned(),
        deployment_root: root(map, "deployment_root", "context"),
        profile_root: root(map, "profile_root", "context"),
        writer_epoch: exact_u64(&map["writer_epoch"]).expect("writer_epoch must be an exact u64"),
        module_release_id: root(map, "module_release_id", "context"),
        command_occurrence_id: root(map, "command_occurrence_id", "context"),
        subject_id: text(map, "subject_id", "context").to_owned(),
        grant_root: root(map, "grant_root", "context"),
    }
}

fn build_state(value: &Value) -> AssetTransferStateV1 {
    let map = object(value, "pre_state", STATE_KEYS);
    AssetTransferStateV1 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(map, "module_release_id", "pre_state"),
        policies: each(&map["policies"], "policy", POLICY_KEYS, |row| {
            AssetTransferPolicyV1 {
                asset: text(row, "asset", "policy").to_owned(),
                fee_owner: text(row, "fee_owner", "policy").to_owned(),
                transfer_fee_atoms: atoms(row, "transfer_fee_atoms", "policy"),
                enabled: row["enabled"].as_bool().expect("enabled must be a bool"),
            }
        }),
        balances: each(&map["balances"], "balance", BALANCE_KEYS, |row| {
            EconomicAmountV1 {
                owner: text(row, "owner", "balance").to_owned(),
                asset: text(row, "asset", "balance").to_owned(),
                custody_domain: text(row, "custody_domain", "balance").to_owned(),
                amount_atoms: atoms(row, "amount_atoms", "balance"),
            }
        }),
        supplies: each(&map["supplies"], "supply", SUPPLY_KEYS, |row| {
            AssetSupplyV1 {
                asset: text(row, "asset", "supply").to_owned(),
                amount_atoms: atoms(row, "amount_atoms", "supply"),
            }
        }),
    }
}

fn build_command(value: &Value) -> AssetTransferCommandV1 {
    let map = object(value, "command", COMMAND_KEYS);
    AssetTransferCommandV1 {
        command_kind: text(map, "command_kind", "command").to_owned(),
        asset: text(map, "asset", "command").to_owned(),
        sender: text(map, "sender", "command").to_owned(),
        recipient: text(map, "recipient", "command").to_owned(),
        amount_atoms: atoms(map, "amount_atoms", "command"),
        max_fee_atoms: atoms(map, "max_fee_atoms", "command"),
    }
}

/// Project the runtime outcome into the exact shape the corpus records.
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
            let effects = &accepted.effects;
            let conserved = &effects.asset_conservation[0];
            json!({
                "outcome": "accepted",
                "post_balances": accepted.post_state.balances.iter().map(|row| json!({
                    "owner": row.owner, "asset": row.asset,
                    "custody_domain": row.custody_domain,
                    "amount_atoms": row.amount_atoms.to_string(),
                })).collect::<Vec<_>>(),
                "effect_rows": effects.rows.iter().map(|row| json!({
                    "kind": serde_json::to_value(row.kind).expect("kind must serialize"),
                    "principal": row.principal, "asset": row.asset,
                    "custody_domain": row.custody_domain,
                    "delta_atoms": row.delta_atoms.to_string(),
                })).collect::<Vec<_>>(),
                "fee_conservation": effects.fee_conservation.iter().map(|row| json!({
                    "asset": row.asset,
                    "fee_charged_atoms": row.fee_charged_atoms.to_string(),
                    "current_allocations_atoms": row.current_allocations_atoms.to_string(),
                    "carried_residue_atoms": row.carried_residue_atoms.to_string(),
                })).collect::<Vec<_>>(),
                "asset_conservation": json!({
                    "asset": conserved.asset,
                    "owned_and_custodied_pre_atoms": conserved.owned_and_custodied_pre_atoms.to_string(),
                    "owned_and_custodied_post_atoms": conserved.owned_and_custodied_post_atoms.to_string(),
                    "supply_pre_atoms": conserved.supply_pre_atoms.to_string(),
                    "supply_post_atoms": conserved.supply_post_atoms.to_string(),
                    "authorized_issue_atoms": conserved.authorized_issue_atoms.to_string(),
                    "authorized_burn_atoms": conserved.authorized_burn_atoms.to_string(),
                }),
                "occurrence_consumptions": effects.occurrence_consumptions.iter()
                    .map(|root| Value::String(root.as_str().to_owned())).collect::<Vec<_>>(),
                "external_outbox_enqueue": serde_json::to_value(&effects.external_outbox_enqueue)
                    .expect("outbox must serialize"),
            })
        }
    }
}

/// Obligations the recorded observation does not already pin exactly.
fn assert_structural_obligations(pre_state: &AssetTransferStateV1, result: &AssetTransferResultV1) {
    match result {
        AssetTransferResultV1::Rejected(rejected) => {
            assert_eq!(rejected.pre_state_root, rejected.post_state_root);
            assert!(rejected.effects.is_empty());
        }
        AssetTransferResultV1::Accepted(accepted) => {
            accepted.validate().expect("accepted result must validate");
            let asset = accepted.effects.asset_conservation[0].asset.as_str();
            let total = |state: &AssetTransferStateV1| -> u128 {
                let rows = state.balances.iter().filter(|row| row.asset == asset);
                rows.map(|row| row.amount_atoms).sum()
            };
            let post_total = total(&accepted.post_state);
            assert_eq!(total(pre_state), post_total, "account totals are conserved");
            assert_eq!(accepted.post_state.supplies, pre_state.supplies);
            assert_eq!(accepted.post_state.policies, pre_state.policies);
            assert_eq!(accepted.effects.lane_writes.len(), 1);
            let write = &accepted.effects.lane_writes[0];
            assert_eq!(write.lane_id, LaneIdV1::ASSET_TRANSFER);
            assert_eq!(write.pre_root, pre_state.state_root().expect("pre root"));
            let post_root = accepted.post_state.state_root().expect("post root");
            assert_eq!(write.post_root, post_root);
            let moved = EconomicEffectKindV1::ACCOUNT_MOVEMENT;
            let rows = accepted.effects.rows.iter().filter(|row| row.kind == moved);
            let net = rows.map(|row| row.delta_atoms).sum::<i128>();
            assert_eq!(net, 0, "account movement deltas must net to zero");
        }
    }
}

#[test]
fn rust_transition_refines_every_corpus_case_on_every_replay() {
    // Arrange
    let corpus = corpus();
    let repetitions = exact_u64(&corpus["deterministic_replay_repetitions"])
        .expect("replay repetitions must be an exact unsigned integer");
    assert!(repetitions >= 2);
    let mut checked = 0_usize;

    for case in array(&corpus["cases"], "cases") {
        let fields = object(case, "case", CASE_KEYS);
        let case_id = text(fields, "case_id", "case");
        let context = build_context(&fields["context"]);
        let pre_state = build_state(&fields["pre_state"]);
        let command = build_command(&fields["command"]);

        // Act
        let replays = (0..repetitions)
            .map(|_| {
                let result = transition_asset_transfer_v1(&context, &pre_state, &command)
                    .expect("typed transition must evaluate");
                assert_structural_obligations(&pre_state, &result);
                observed(&pre_state, &result)
            })
            .collect::<Vec<_>>();

        // Assert
        assert_eq!(&replays[0], &fields["expected"], "case {case_id}");
        assert!(
            replays.iter().all(|replay| replay == &replays[0]),
            "case {case_id} must replay deterministically"
        );
        checked += 1;
    }
    assert!(checked >= 37, "the corpus must keep its cases: {checked}");
}

#[test]
fn every_prior_defect_still_names_regression_cases_the_corpus_carries() {
    // Arrange
    let corpus = corpus();
    let case_ids = array(&corpus["cases"], "cases")
        .iter()
        .map(|case| case["case_id"].as_str().expect("case id must be a string"))
        .collect::<Vec<_>>();
    let mut named = 0_usize;

    // Act / Assert
    for defect in array(&corpus["prior_defects"], "prior_defects") {
        let fields = object(defect, "prior_defect", DEFECT_KEYS);
        assert_eq!(text(fields, "status", "prior_defect"), DEFECT_KILLED_V1);
        for case_id in array(&fields["regression_case_ids"], "regressions") {
            let name = case_id.as_str().expect("case id must be a string");
            assert!(case_ids.contains(&name), "{name} must stay in the corpus");
            named += 1;
        }
    }
    assert!(named >= 7, "prior defects must name regression cases");
}

#[test]
fn corpus_precedence_names_decode_to_the_runtime_reject_enum() {
    // Arrange
    let corpus = corpus();
    let unknown = Value::String("NOT_A_CODE".to_owned());

    // Act / Assert
    for code in array(&corpus["reject_precedence"], "reject_precedence") {
        let decoded: AssetTransferRejectCodeV1 = serde_json::from_value(code.clone())
            .expect("every declared reject code must decode to the runtime enum");
        assert_eq!(&serde_json::to_value(decoded).expect("serialize"), code);
    }
    assert!(serde_json::from_value::<AssetTransferRejectCodeV1>(unknown).is_err());
}

#[test]
fn strict_corpus_decoding_rejects_unknown_fields_and_wrong_scalar_types() {
    // Arrange
    let case = corpus()["cases"][0].clone();
    let mut extra = case.clone();
    extra["opaque_authority"] = Value::Bool(true);
    let absent = json!({"title": "a case carrying only one declared field"});
    let (number, boolean, decimal) = (json!(30), json!(true), json!(7.0));
    let (digits, signed) = (json!("7"), json!(-1));

    // Act / Assert
    assert!(exact_keys(&case, CASE_KEYS));
    assert!(!exact_keys(&extra, CASE_KEYS), "an unknown field must fail");
    assert!(!exact_keys(&absent, CASE_KEYS), "a missing field must fail");
    assert!(!exact_keys(&json!([]), CASE_KEYS), "a nonobject must fail");
    assert_eq!(canonical_atoms(&json!("30")), Some(30));
    assert_eq!(exact_u64(&json!(7)), Some(7));
    for hostile in ["030", "-30", "30 ", "", "0x1"] {
        assert!(canonical_atoms(&json!(hostile)).is_none(), "{hostile}");
    }
    for hostile in [&number, &boolean, &decimal] {
        assert!(canonical_atoms(hostile).is_none(), "atoms reject {hostile}");
    }
    for hostile in [&boolean, &decimal, &digits, &signed] {
        assert!(exact_u64(hostile).is_none(), "epochs reject {hostile}");
    }
}
