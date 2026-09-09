use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, transition_asset_lane_custody_bytes_v2, AbiErrorV2,
    AssetLaneCustodyResultV2, AssetLaneRejectCodeV2, AssetLaneRouteV2, AssetTransferRejectCodeV2,
    ManagedAssetLifecycleRejectCodeV2, RootV2, MAX_CANONICAL_INPUT_BYTES_V2,
};

const GOLDEN: &str = include_str!("../../../tests/data/asset_lane_custody_v2_golden.json");

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    authority: String,
    cases: Vec<Case>,
    nonclaim: String,
    schema: String,
    source_sha256: BTreeMap<String, String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Case {
    command: Value,
    command_type: String,
    context: Value,
    name: String,
    output: Value,
    pre_state: Value,
}

fn fixture() -> Fixture {
    serde_json::from_str(GOLDEN).expect("committed custody fixture must parse")
}

fn case(name: &str) -> Case {
    fixture()
        .cases
        .into_iter()
        .find(|case| case.name == name)
        .unwrap_or_else(|| panic!("golden case {name} must exist"))
}

fn raw(value: &Value) -> Vec<u8> {
    serde_json::to_vec(value).expect("golden value must serialize")
}

fn route(case: &Case) -> AssetLaneRouteV2 {
    match case.command_type.as_str() {
        "TRANSFER" => AssetLaneRouteV2::TRANSFER,
        "MANAGED_LIFECYCLE" => AssetLaneRouteV2::MANAGED_LIFECYCLE,
        other => panic!("unsupported golden command type {other}"),
    }
}

fn expected_root(output: &Value, field: &str) -> RootV2 {
    RootV2::parse(
        output[field]
            .as_str()
            .unwrap_or_else(|| panic!("golden output must contain string field {field}")),
        "golden expected root",
        false,
    )
    .expect("golden expected root must be canonical")
}

fn assert_canonical_value<T: Serialize>(actual: &T, expected: &Value, label: &str) {
    assert_eq!(
        canonical_bytes_v2(actual).expect("Rust output must encode canonically"),
        raw(expected),
        "exact canonical {label} bytes"
    );
}

fn assert_matches_golden(case: &Case, result: AssetLaneCustodyResultV2) {
    match (case.output["status"].as_str(), result) {
        (Some("ACCEPTED"), AssetLaneCustodyResultV2::Accepted(accepted)) => {
            assert_eq!(accepted.route().as_str(), case.output["route"]);
            assert_eq!(
                accepted.source_leaf_journal_root(),
                &expected_root(&case.output, "source_leaf_journal_root")
            );
            assert_eq!(
                accepted.source_leaf_receipt_root(),
                &expected_root(&case.output, "source_leaf_receipt_root")
            );
            assert_canonical_value(
                accepted.post_state(),
                &case.output["post_state"],
                "post-state",
            );
            assert_canonical_value(accepted.effects(), &case.output["effects"], "effects");
            assert_canonical_value(
                accepted.module_journal(),
                &case.output["module_journal"],
                "module journal",
            );
            accepted.validate().expect("accepted output must validate");
            assert_eq!(accepted.production_authority(), "NONE");
            assert_eq!(accepted.profile_authentication(), "SHADOW");
        }
        (Some("REJECTED"), AssetLaneCustodyResultV2::Rejected(rejected)) => {
            assert_eq!(rejected.route().as_str(), case.output["route"]);
            assert_eq!(rejected.code().as_str(), case.output["code"]);
            assert_eq!(
                rejected.pre_state_root(),
                &expected_root(&case.output, "pre_state_root")
            );
            assert_eq!(
                rejected.post_state_root(),
                &expected_root(&case.output, "post_state_root")
            );
            assert_canonical_value(rejected.effects(), &case.output["effects"], "effects");
            rejected.validate().expect("rejected output must validate");
            assert_eq!(rejected.production_authority(), "NONE");
            assert_eq!(rejected.profile_authentication(), "SHADOW");
        }
        (expected, actual) => panic!(
            "golden {} status mismatch: expected {expected:?}, got {actual:?}",
            case.name
        ),
    }
}

#[test]
fn bytes_boundary_replays_all_ten_golden_results_exactly() {
    let fixture = fixture();
    assert_eq!(fixture.schema, "zenodex/asset-lane-custody-v2-golden/v1");
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(
        fixture.nonclaim,
        "Listed-source bounded runtime parity; no signature, proof guest, publication or migration qualification."
    );
    assert_eq!(fixture.source_sha256.len(), 7);
    assert_eq!(fixture.cases.len(), 10);

    for case in &fixture.cases {
        let result = transition_asset_lane_custody_bytes_v2(
            route(case),
            &raw(&case.context),
            &raw(&case.pre_state),
            &raw(&case.command),
        )
        .unwrap_or_else(|error| panic!("golden {} must execute: {error}", case.name));
        assert_matches_golden(case, result);
    }
}

#[test]
fn coordinator_route_is_rejected_before_any_decode() {
    assert_eq!(
        transition_asset_lane_custody_bytes_v2(
            AssetLaneRouteV2::COORDINATOR,
            b"",
            b"{",
            b"not-json",
        ),
        Err(AbiErrorV2::InvalidBinding("asset lane custody input route"))
    );
}

#[test]
fn decode_order_is_context_then_state_then_selected_command() {
    let case = case("transfer_nonzero_custody");
    let context = raw(&case.context);
    let state = raw(&case.pre_state);
    let malformed_command = b"{";

    let mut wrong_context = case.context.clone();
    wrong_context["occurrence"]["schema"] = Value::String("wrong/context".to_owned());
    let mut wrong_state = case.pre_state.clone();
    wrong_state["schema"] = Value::String("wrong/state".to_owned());

    assert_eq!(
        transition_asset_lane_custody_bytes_v2(
            AssetLaneRouteV2::TRANSFER,
            &raw(&wrong_context),
            &raw(&wrong_state),
            malformed_command,
        ),
        Err(AbiErrorV2::InvalidSchema("economic command occurrence"))
    );
    assert_eq!(
        transition_asset_lane_custody_bytes_v2(
            AssetLaneRouteV2::TRANSFER,
            &context,
            &raw(&wrong_state),
            malformed_command,
        ),
        Err(AbiErrorV2::InvalidSchema("asset lane custody state"))
    );
    assert!(matches!(
        transition_asset_lane_custody_bytes_v2(
            AssetLaneRouteV2::TRANSFER,
            &context,
            &state,
            malformed_command,
        ),
        Err(AbiErrorV2::CanonicalEncoding(_))
    ));
}

#[test]
fn route_selects_one_closed_unchanged_command_shape() {
    let transfer = case("transfer_nonzero_custody");
    let managed = case("issue_nonzero_custody");

    for (selected_route, command) in [
        (AssetLaneRouteV2::MANAGED_LIFECYCLE, &transfer.command),
        (AssetLaneRouteV2::TRANSFER, &managed.command),
    ] {
        assert!(matches!(
            transition_asset_lane_custody_bytes_v2(
                selected_route,
                &raw(&transfer.context),
                &raw(&transfer.pre_state),
                &raw(command),
            ),
            Err(AbiErrorV2::CanonicalEncoding(_))
        ));
    }
}

#[test]
fn valid_unknown_command_kinds_remain_typed_leaf_noops() {
    let cases = [
        (
            "transfer_nonzero_custody",
            AssetLaneRouteV2::TRANSFER,
            "unknown_transfer",
            AssetLaneRejectCodeV2::Transfer(AssetTransferRejectCodeV2::UNKNOWN_COMMAND),
        ),
        (
            "issue_nonzero_custody",
            AssetLaneRouteV2::MANAGED_LIFECYCLE,
            "unknown_managed",
            AssetLaneRejectCodeV2::ManagedLifecycle(
                ManagedAssetLifecycleRejectCodeV2::UNKNOWN_COMMAND,
            ),
        ),
    ];

    for (case_name, route, unknown_kind, expected_code) in cases {
        let mut case = case(case_name);
        case.command["command_kind"] = Value::String(unknown_kind.to_owned());
        let result = transition_asset_lane_custody_bytes_v2(
            route,
            &raw(&case.context),
            &raw(&case.pre_state),
            &raw(&case.command),
        )
        .expect("unknown command kind remains a typed transition outcome");
        let AssetLaneCustodyResultV2::Rejected(rejected) = result else {
            panic!("unknown command kind must reject")
        };
        assert_eq!(rejected.route(), route);
        assert_eq!(rejected.code(), expected_code);
        assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
        assert!(rejected.effects().is_empty());
    }
}

#[test]
fn each_raw_input_has_the_exact_independent_one_mibibyte_cap() {
    assert_eq!(MAX_CANONICAL_INPUT_BYTES_V2, 1_048_576);
    let case = case("transfer_nonzero_custody");
    let context = raw(&case.context);
    let state = raw(&case.pre_state);
    let command = raw(&case.command);
    let oversized = vec![b' '; MAX_CANONICAL_INPUT_BYTES_V2 + 1];

    for result in [
        transition_asset_lane_custody_bytes_v2(
            AssetLaneRouteV2::TRANSFER,
            &oversized,
            &state,
            &command,
        ),
        transition_asset_lane_custody_bytes_v2(
            AssetLaneRouteV2::TRANSFER,
            &context,
            &oversized,
            &command,
        ),
        transition_asset_lane_custody_bytes_v2(
            AssetLaneRouteV2::TRANSFER,
            &context,
            &state,
            &oversized,
        ),
    ] {
        assert_eq!(
            result,
            Err(AbiErrorV2::InvalidBounds("canonical input bytes"))
        );
    }

    let exact_but_invalid = vec![b' '; MAX_CANONICAL_INPUT_BYTES_V2];
    assert!(matches!(
        transition_asset_lane_custody_bytes_v2(
            AssetLaneRouteV2::TRANSFER,
            &exact_but_invalid,
            &state,
            &command,
        ),
        Err(AbiErrorV2::CanonicalEncoding(_))
    ));
}

#[test]
fn malformed_noncanonical_deep_float_and_numeric_overflow_inputs_fail_totally() {
    let case = case("transfer_nonzero_custody");
    let context = raw(&case.context);
    let state = raw(&case.pre_state);
    let command = raw(&case.command);

    let mut noncanonical_context = context.clone();
    noncanonical_context.push(b'\n');
    let deep_context = format!("{}0{}", "[".repeat(256), "]".repeat(256)).into_bytes();
    for hostile_context in [&noncanonical_context, &deep_context] {
        assert!(matches!(
            transition_asset_lane_custody_bytes_v2(
                AssetLaneRouteV2::TRANSFER,
                hostile_context,
                &state,
                &command,
            ),
            Err(AbiErrorV2::CanonicalEncoding(_))
        ));
    }

    let mut float_command = case.command.clone();
    float_command["amount_atoms"] = serde_json::json!(1.5);
    let mut overflow_command = case.command.clone();
    overflow_command["amount_atoms"] =
        serde_json::from_str("340282366920938463463374607431768211456")
            .expect("one past u128 max is valid JSON");
    let malformed_command = b"{".to_vec();
    let float_command = raw(&float_command);
    let overflow_command = raw(&overflow_command);
    for hostile_command in [&malformed_command, &float_command, &overflow_command] {
        assert!(matches!(
            transition_asset_lane_custody_bytes_v2(
                AssetLaneRouteV2::TRANSFER,
                &context,
                &state,
                hostile_command,
            ),
            Err(AbiErrorV2::CanonicalEncoding(_))
        ));
    }
}
