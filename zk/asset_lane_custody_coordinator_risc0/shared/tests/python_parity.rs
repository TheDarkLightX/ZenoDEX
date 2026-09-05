use zenodex_asset_lane_custody_coordinator_risc0_shared::{
    canonical_asset_lane_custody_coordinator_input_bytes_v1,
    prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1,
    prepare_asset_lane_custody_coordinator_v1, AssetLaneCustodyCoordinatorGuestErrorV1,
    AssetLaneCustodyCoordinatorInputV1, PreparedAssetLaneCustodyCoordinatorV1,
};
use zenodex_global_settlement_abi_v1::{
    AssetLaneCompositionAcceptedV1, AssetTransferLaneModuleAcceptedV1, AssetTransferRejectCodeV1,
};

const FIXTURE: &str =
    include_str!("../../../../tests/data/asset_lane_custody_coordinator_v1_golden.json");

fn vectors() -> serde_json::Value {
    let value: serde_json::Value = serde_json::from_str(FIXTURE).expect("Python fixture JSON");
    assert_eq!(value["authority"], "NONE");
    assert_eq!(
        value["schema"],
        "zenodex/asset-lane-custody-coordinator-golden/v1"
    );
    assert_eq!(value["cases"].as_array().expect("cases").len(), 11);
    assert_eq!(value["history"].as_array().expect("history").len(), 3);
    value
}

fn input(case: &serde_json::Value) -> AssetLaneCustodyCoordinatorInputV1 {
    serde_json::from_value(case["input"].clone()).expect("Python coordinator input")
}

fn check_full_case(case: &serde_json::Value) -> PreparedAssetLaneCustodyCoordinatorV1 {
    let input = input(case);
    let bytes =
        canonical_asset_lane_custody_coordinator_input_bytes_v1(&input).expect("canonical input");
    assert_eq!(
        bytes,
        case["input_utf8"].as_str().expect("input bytes").as_bytes()
    );
    let prepared = prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&bytes)
        .expect("native coordinator accepts Python positive control");
    let expected_module: AssetTransferLaneModuleAcceptedV1 =
        serde_json::from_value(case["module_accepted"].clone()).expect("Python module value");
    let expected_lane: AssetLaneCompositionAcceptedV1 =
        serde_json::from_value(case["lane_accepted"].clone()).expect("Python lane value");
    assert_eq!(prepared.input, input, "{} owned input", case["name"]);
    assert_eq!(
        prepared.module_accepted, expected_module,
        "{} full module",
        case["name"]
    );
    assert_eq!(
        prepared.lane_accepted, expected_lane,
        "{} full lane",
        case["name"]
    );
    assert_eq!(
        prepared.module_journal_bytes,
        case["module_journal_utf8"]
            .as_str()
            .expect("module bytes")
            .as_bytes(),
        "{} exact Python module journal bytes",
        case["name"]
    );
    assert_eq!(
        prepared.lane_journal_bytes,
        case["lane_journal_utf8"]
            .as_str()
            .expect("lane bytes")
            .as_bytes(),
        "{} exact Python lane journal bytes",
        case["name"]
    );
    assert_eq!(
        prepare_asset_lane_custody_coordinator_v1(input).expect("typed preparation"),
        prepared,
        "{} typed/raw equality",
        case["name"]
    );
    let total = case["expected_total"]
        .as_str()
        .expect("total")
        .parse::<u128>()
        .expect("u128");
    assert_eq!(prepared.lane_accepted.effects.asset_conservation.len(), 1);
    let row = &prepared.lane_accepted.effects.asset_conservation[0];
    assert_eq!(row.owned_and_custodied_pre_atoms, total);
    assert_eq!(row.owned_and_custodied_post_atoms, total);
    prepared
}

#[test]
fn complete_python_lane_values_and_canonical_journals_match() {
    for case in vectors()["cases"].as_array().expect("cases") {
        check_full_case(case);
    }
}

#[test]
fn accepted_rejected_accepted_history_preserves_exact_state_and_custody() {
    let vectors = vectors();
    let events = vectors["history"].as_array().expect("history");
    let first = check_full_case(&events[0]);
    let rejected_input = input(&events[1]);
    assert_eq!(events[1]["reject_code"], "ZERO_AMOUNT");
    assert_eq!(
        rejected_input.module_input.pre_state,
        first.module_accepted.post_state
    );
    assert_eq!(
        rejected_input
            .module_input
            .pre_state
            .state_root()
            .expect("pre state root")
            .as_str(),
        events[1]["unchanged_module_state_root"]
            .as_str()
            .expect("unchanged root")
    );
    let rejected_bytes = canonical_asset_lane_custody_coordinator_input_bytes_v1(&rejected_input)
        .expect("canonical rejected input");
    assert_eq!(
        prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(&rejected_bytes),
        Err(AssetLaneCustodyCoordinatorGuestErrorV1::ModuleRejected(
            AssetTransferRejectCodeV1::ZERO_AMOUNT
        ))
    );
    assert_eq!(
        canonical_asset_lane_custody_coordinator_input_bytes_v1(&rejected_input)
            .expect("unchanged rejected input"),
        rejected_bytes
    );
    let second = check_full_case(&events[2]);
    assert_eq!(
        second.input.module_input.pre_state,
        first.module_accepted.post_state
    );
    assert_eq!(
        first.lane_accepted.lane_journal.post_lane_root,
        second.lane_accepted.lane_journal.pre_lane_root
    );
    assert_eq!(
        first.input.module_input.custody,
        second.lane_accepted.post_state.custody
    );
    assert_ne!(
        first.input.module_input.context.command_occurrence_id,
        second.input.module_input.context.command_occurrence_id
    );
    assert_eq!(
        second.input.module_input.context.command_occurrence_id,
        rejected_input.module_input.context.command_occurrence_id
    );
    assert_eq!(
        second
            .module_accepted
            .post_state
            .balances
            .iter()
            .find(|row| row.owner == "alice")
            .expect("Alice remains")
            .amount_atoms,
        65
    );
    // Repeating a pure preparation is deterministic. Replay consumption belongs
    // to publication and is deliberately outside this native candidate.
    assert_eq!(
        prepare_asset_lane_custody_coordinator_v1(second.input.clone()).expect("repeat"),
        second
    );
}
