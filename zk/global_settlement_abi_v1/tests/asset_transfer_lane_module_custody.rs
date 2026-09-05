//! Independent physical totals and complete Python/Rust value parity.
use zenodex_global_settlement_abi_v1::*;

fn vectors() -> serde_json::Value {
    serde_json::from_str(include_str!(
        "../../../tests/data/asset_transfer_lane_module_custody_v1_golden.json"
    ))
    .unwrap()
}

fn check_accepted(
    input: &AssetTransferLaneModuleInputV1,
    accepted: &AssetTransferLaneModuleAcceptedV1,
    case: &serde_json::Value,
) {
    let expected: AssetTransferLaneModuleAcceptedV1 =
        serde_json::from_value(case["accepted"].clone()).unwrap();
    assert_eq!(accepted, &expected, "{}", case["name"]);
    let total: u128 = case["expected_total"].as_str().unwrap().parse().unwrap();
    let row = &accepted.effects.asset_conservation[0];
    assert_eq!(row.owned_and_custodied_pre_atoms, total);
    assert_eq!(row.owned_and_custodied_post_atoms, total);
    assert_eq!(accepted.private_port.pre_state.custody, input.custody);
    assert_eq!(accepted.private_port.post_state.custody, input.custody);
    assert_eq!(
        recompute_asset_transfer_lane_module_custody_v1(input, accepted).unwrap(),
        *accepted
    );
    let AssetTransferLaneModuleResultV1::Accepted(old) =
        transition_asset_transfer_lane_module_v1(input).unwrap()
    else {
        panic!("legacy rejected")
    };
    assert_eq!(old.post_state, accepted.post_state);
    assert_eq!(old.effects.rows, accepted.effects.rows);
    if input.custody.is_empty() {
        assert_eq!(old.as_ref(), accepted);
    } else {
        assert!(recompute_asset_transfer_lane_module_custody_v1(input, &old).is_err());
        assert_ne!(
            old.module_journal.receipt_root,
            accepted.module_journal.receipt_root
        );
    }
}

#[test]
fn successor_matches_python_and_independent_totals_without_changing_legacy() {
    for case in vectors()["cases"].as_array().unwrap() {
        let input: AssetTransferLaneModuleInputV1 =
            serde_json::from_value(case["input"].clone()).unwrap();
        let saved = input.clone();
        match transition_asset_transfer_lane_module_custody_v1(&input).unwrap() {
            AssetTransferLaneModuleResultV1::Rejected(rejected) => {
                assert_eq!(
                    format!("{:?}", rejected.code),
                    case["reject_code"].as_str().unwrap()
                );
                assert_eq!(
                    transition_asset_transfer_lane_module_v1(&input).unwrap(),
                    AssetTransferLaneModuleResultV1::Rejected(rejected)
                );
            }
            AssetTransferLaneModuleResultV1::Accepted(accepted) => {
                check_accepted(&input, &accepted, case);
            }
        }
        assert_eq!(saved, input);
    }
}

#[test]
fn complete_totals_and_representable_deltas_allow_coordinator_composition() {
    let data = vectors();
    let context: AssetLaneCoordinatorContextV1 =
        serde_json::from_value(data["coordinator_context"].clone()).unwrap();
    for case in data["cases"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row.get("accepted").is_some())
    {
        let input = serde_json::from_value(case["input"].clone()).unwrap();
        let AssetTransferLaneModuleResultV1::Accepted(accepted) =
            transition_asset_transfer_lane_module_custody_v1(&input).unwrap()
        else {
            panic!("positive rejected")
        };
        let composed = compose_asset_lane_single_v1(
            &context,
            &accepted.module_journal,
            &accepted.private_port,
            &accepted.effects,
        )
        .unwrap();
        assert!(
            matches!(composed, AssetLaneCompositionResultV1::Accepted(_)),
            "{}: {:?}",
            case["name"],
            composed
        );
    }
}

#[test]
fn individually_valid_amounts_cannot_overflow_complete_projection() {
    let input: AssetTransferLaneModuleInputV1 =
        serde_json::from_value(vectors()["overflow_input"].clone()).unwrap();
    assert!(matches!(
        transition_asset_transfer_lane_module_custody_v1(&input),
        Err(AbiErrorV1::Conservation(
            "asset lane holding total overflow"
        ))
    ));
}
