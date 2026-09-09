use std::collections::BTreeMap;

use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, decode_canonical_v2, transition_asset_lane_custody_v2, AssetLaneCommandV2,
    AssetLaneContextV2, AssetLaneCustodyResultV2, AssetLaneCustodyStateV2, AssetTransferCommandV2,
    ManagedAssetLifecycleCommandV2, RootV2, ValidateCanonicalV2,
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

fn decode_value<T>(value: &Value, label: &str) -> T
where
    T: DeserializeOwned + Serialize + ValidateCanonicalV2,
{
    let bytes = serde_json::to_vec(value).expect("golden value must serialize");
    decode_canonical_v2(&bytes)
        .unwrap_or_else(|error| panic!("golden {label} must decode canonically: {error}"))
}

fn command(case: &Case) -> AssetLaneCommandV2 {
    match case.command_type.as_str() {
        "TRANSFER" => AssetLaneCommandV2::Transfer(decode_value::<AssetTransferCommandV2>(
            &case.command,
            "transfer command",
        )),
        "MANAGED_LIFECYCLE" => {
            AssetLaneCommandV2::ManagedLifecycle(decode_value::<ManagedAssetLifecycleCommandV2>(
                &case.command,
                "managed lifecycle command",
            ))
        }
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
    let actual_bytes = canonical_bytes_v2(actual).expect("Rust output must encode canonically");
    let expected_bytes = serde_json::to_vec(expected).expect("golden output must serialize");
    assert_eq!(
        actual_bytes, expected_bytes,
        "exact canonical {label} bytes"
    );
}

#[test]
fn python_and_rust_share_exact_custody_successor_results() {
    let fixture = fixture();
    assert_eq!(fixture.schema, "zenodex/asset-lane-custody-v2-golden/v1");
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(
        fixture.nonclaim,
        "Listed-source bounded runtime parity; no signature, proof guest, publication or migration qualification."
    );
    assert_eq!(fixture.source_sha256.len(), 7);
    assert!(fixture.source_sha256.values().all(|digest| {
        digest.len() == 64 && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
    }));
    assert_eq!(
        fixture
            .cases
            .iter()
            .map(|case| case.name.as_str())
            .collect::<Vec<_>>(),
        [
            "transfer_nonzero_custody",
            "transfer_zero_custody",
            "issue_nonzero_custody",
            "burn_nonzero_custody",
            "burn_accounts_to_vault_only",
            "issue_dormant_identity",
            "burn_to_dormant",
            "unauthorized",
            "zero_transfer",
            "insufficient_balance",
        ]
    );

    let mut accepted_count = 0;
    let mut rejected_count = 0;
    for case in &fixture.cases {
        let context: AssetLaneContextV2 = decode_value(&case.context, "context");
        let pre_state: AssetLaneCustodyStateV2 = decode_value(&case.pre_state, "pre-state");
        let command = command(case);
        let result = transition_asset_lane_custody_v2(&context, &pre_state, &command)
            .unwrap_or_else(|error| panic!("golden {} must execute: {error}", case.name));

        match (case.output["status"].as_str(), result) {
            (Some("ACCEPTED"), AssetLaneCustodyResultV2::Accepted(accepted)) => {
                accepted_count += 1;
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
                accepted
                    .validate()
                    .expect("golden accepted result must remain self-consistent");
                assert_eq!(accepted.production_authority(), "NONE");
                assert_eq!(accepted.profile_authentication(), "SHADOW");
            }
            (Some("REJECTED"), AssetLaneCustodyResultV2::Rejected(rejected)) => {
                rejected_count += 1;
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
                rejected
                    .validate()
                    .expect("golden rejection must remain an exact no-op");
                assert_eq!(rejected.production_authority(), "NONE");
                assert_eq!(rejected.profile_authentication(), "SHADOW");
            }
            (expected, actual) => panic!(
                "golden {} status mismatch: expected {expected:?}, got {actual:?}",
                case.name
            ),
        }
    }
    assert_eq!((accepted_count, rejected_count), (7, 3));
}
