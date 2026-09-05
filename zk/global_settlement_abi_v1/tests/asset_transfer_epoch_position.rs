//! Exact Python/Rust pure-relation vectors; no receipt or source authority.

use zenodex_global_settlement_abi_v1::*;

#[test]
fn epoch_position_relation_matches_independent_python_vectors() {
    let vectors: serde_json::Value = serde_json::from_str(include_str!(
        "../../../tests/data/asset_transfer_epoch_position_v1_golden.json"
    ))
    .expect("epoch position fixture");
    for row in vectors["cases"].as_array().expect("cases") {
        let accepted = serde_json::from_value(row["accepted"].clone()).unwrap();
        let occurrence = serde_json::from_value(row["occurrence"].clone()).unwrap();
        let predecessor = serde_json::from_value(row["predecessor"].clone()).unwrap();
        let current = serde_json::from_value(row["current"].clone()).unwrap();
        let source = serde_json::from_value(row["source"].clone()).unwrap();
        let index = usize::try_from(row["index"].as_u64().unwrap()).unwrap();
        let result = check_asset_transfer_epoch_allocation_v1(
            AssetTransferGlobalAllocationCandidateV1 {
                accepted: &accepted,
                occurrence: &occurrence,
                predecessor: &predecessor,
                current: &current,
            },
            AssetTransferEpochPositionV1 {
                epoch_source: &source,
                occurrence_index: index,
            },
        )
        .expect("epoch relation boundary");
        assert_eq!(
            result.map(|code| format!("{code:?}")),
            row["expected_code"].as_str().map(str::to_owned),
            "{}",
            row["name"]
        );
        assert!(check_asset_transfer_epoch_allocation_v1(
            AssetTransferGlobalAllocationCandidateV1 {
                accepted: &accepted,
                occurrence: &occurrence,
                predecessor: &predecessor,
                current: &current,
            },
            AssetTransferEpochPositionV1 {
                epoch_source: &source,
                occurrence_index: 64
            },
        )
        .is_err());
    }
}
