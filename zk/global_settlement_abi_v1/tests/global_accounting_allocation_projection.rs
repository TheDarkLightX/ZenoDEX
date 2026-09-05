//! Shared public projection vectors. Receipt-witness paths are in the existing
//! receipt harness's allocation_projection child module. Fixture authority: NONE.

use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::*;

fn fixture() -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/data/global_accounting_allocation_projection_v1_golden.json");
    serde_json::from_slice(&fs::read(path).expect("fixture readable")).expect("fixture JSON")
}

#[test]
fn public_projection_matches_python_vectors_without_mutating_state() {
    let fixture = fixture();
    assert_eq!(fixture["authority"], "NONE");
    assert_eq!(
        fixture["fixture_schema"],
        "zenodex/global-accounting-allocation-projection-v1-golden/v1"
    );
    for (name, vector) in fixture["vectors"].as_object().expect("vectors object") {
        let state: GlobalEconomicStateV1 =
            serde_json::from_value(vector["state"].clone()).expect("typed state");
        let roots: Vec<(LaneIdV1, RootV1)> =
            serde_json::from_value(vector["binding_roots"].clone()).expect("roots");
        let before = canonical_bytes_v1(&state).expect("state bytes");
        assert_eq!(
            state.state_root().expect("state root").as_str(),
            vector["state_root"].as_str().expect("root"),
            "{name}"
        );
        let projected =
            project_allocation_certificate_v1(&state, &roots, &[]).expect("well-formed invocation");
        let explicit_empty =
            project_allocation_certificate_v1(&state, &roots, &EMPTY_LANE_WITNESS_SLOTS_V1)
                .expect("explicit slots");
        assert_eq!(projected, explicit_empty, "empty-slot spelling: {name}");
        match projected {
            Ok(certificate) => {
                assert_eq!(vector["expected"]["status"], "DERIVED", "{name}");
                assert_eq!(
                    hash_bytes_sha256_v1(
                        &canonical_bytes_v1(&certificate).expect("certificate bytes")
                    ),
                    vector["expected"]["certificate_sha256"]
                        .as_str()
                        .expect("digest"),
                    "{name}"
                );
                assert!(
                    matches!(
                        check_global_accounting_allocation_certificate_v1(
                            &certificate,
                            &state,
                            &EMPTY_LANE_WITNESS_SLOTS_V1
                        )
                        .expect("checker boundary"),
                        AllocationCertificateOutcomeV1::Accepted(_)
                    ),
                    "{name}"
                );
            }
            Err(rejected) => {
                assert_eq!(vector["expected"]["status"], "REJECT", "{name}");
                assert_eq!(
                    format!("{:?}", rejected.code),
                    vector["expected"]["code"].as_str().expect("code"),
                    "{name}"
                );
                assert_eq!(
                    rejected.detail,
                    vector["expected"]["detail"].as_str().expect("detail"),
                    "{name}"
                );
                assert_eq!(
                    rejected.state_root,
                    state.state_root().expect("unchanged state root"),
                    "{name}"
                );
            }
        }
        assert_eq!(
            canonical_bytes_v1(&state).expect("post bytes"),
            before,
            "{name}"
        );
    }
}

#[test]
fn producer_scope_and_complete_reject_family_match_python() {
    let fixture = fixture();
    let codes: Vec<_> = AllocationProjectionRejectCodeV1::ALL
        .iter()
        .map(|code| format!("{code:?}"))
        .collect();
    assert_eq!(
        serde_json::to_value(codes).expect("codes JSON"),
        fixture["reject_codes"]
    );
    let registry: Vec<_> = LANE_ALLOCATION_PRODUCER_REGISTRY_V1
        .iter()
        .map(|(lane, kind, _)| [format!("{lane:?}"), format!("{kind:?}")])
        .collect();
    assert_eq!(
        serde_json::to_value(registry).expect("registry JSON"),
        fixture["producer_registry"]
    );
    let receipt_lanes: Vec<_> = LANE_ALLOCATION_PRODUCER_REGISTRY_V1
        .iter()
        .filter(|(_, kind, _)| *kind == LaneProducerKindV1::RECEIPT_BACKED)
        .map(|(lane, _, _)| *lane)
        .collect();
    assert_eq!(
        receipt_lanes,
        [LaneIdV1::ASSET_TRANSFER],
        "a new producer requires projection scope review"
    );
}

#[test]
fn malformed_snapshots_and_invocations_fail_as_typed_boundary_errors() {
    let fixture = fixture();
    let state: GlobalEconomicStateV1 =
        serde_json::from_value(fixture["vectors"]["empty"]["state"].clone()).expect("empty state");
    assert!(matches!(
        project_allocation_certificate_v1(&state, &[], &[None]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
    let lane = LaneIdV1::ASSET_TRANSFER;
    let root = state.profile_root.clone();
    assert!(matches!(
        project_allocation_certificate_v1(&state, &[(lane, root.clone()), (lane, root)], &[]),
        Err(AbiErrorV1::InvalidOrder(_))
    ));
    let mut missing_lane = state.clone();
    missing_lane.lane_roots.pop();
    assert!(matches!(
        project_allocation_certificate_v1(&missing_lane, &[], &[]),
        Err(AbiErrorV1::InvalidOrder(_))
    ));
    let row = EconomicAmountV1 {
        owner: "alice".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "vault".to_owned(),
        amount_atoms: 1,
    };
    let mut over_bound = state;
    over_bound.custody = vec![row; MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1 + 1];
    assert_eq!(
        project_allocation_certificate_v1(&over_bound, &[], &[]),
        Err(AbiErrorV1::InvalidBounds("global state custody"))
    );
}

#[test]
fn maximum_state_rows_are_checked_through_the_final_entry() {
    let fixture = fixture();
    let vector = &fixture["vectors"]["enabled_empty"];
    let mut state: GlobalEconomicStateV1 =
        serde_json::from_value(vector["state"].clone()).expect("enabled state");
    let roots: Vec<(LaneIdV1, RootV1)> =
        serde_json::from_value(vector["binding_roots"].clone()).expect("binding roots");
    state.custody = (0..MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1)
        .map(|index| EconomicAmountV1 {
            owner: format!("owner{index:04}"),
            asset: "USD".to_owned(),
            custody_domain: "vault".to_owned(),
            amount_atoms: 1,
        })
        .collect();
    state.liabilities = state.custody.clone();
    let balanced = project_allocation_certificate_v1(&state, &roots, &[])
        .expect("maximum canonical state fits")
        .expect_err("balanced state still requires a witness");
    assert_eq!(
        balanced.code,
        AllocationProjectionRejectCodeV1::PROJECTION_WITNESS_REQUIRED
    );
    // Kills a traversal that silently drops the final row of either table.
    state
        .liabilities
        .last_mut()
        .expect("maximum state has rows")
        .amount_atoms = 2;
    let before = state.clone();
    let rejected = project_allocation_certificate_v1(&state, &roots, &[])
        .expect("well-formed overclaim")
        .expect_err("last liability row exceeds custody");
    assert_eq!(
        rejected.code,
        AllocationProjectionRejectCodeV1::PROJECTION_NEGATIVE_RESIDUAL
    );
    assert_eq!(state, before);
}
