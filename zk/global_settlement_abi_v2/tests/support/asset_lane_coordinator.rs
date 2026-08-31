#![allow(dead_code)] // Each integration-test crate consumes a different fixture slice.

use std::collections::BTreeMap;

use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, decode_canonical_v2, hash_bytes_sha256_v2, AssetLaneCommandV2,
    AssetTransferRejectCodeV2, RootV2, ValidateCanonicalV2,
};

const GOLDEN: &str = include_str!(
    "../../../../tests/data/global_settlement_abi_v2_asset_lane_coordinator_golden.json"
);

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Fixture {
    pub fixture_schema: String,
    pub authority: String,
    pub profile_authentication: String,
    pub plan_sha256: String,
    pub limits: Limits,
    pub python_source_sha256: BTreeMap<String, String>,
    pub coordinator_reject_codes: Vec<String>,
    pub transfer_reject_codes: Vec<String>,
    pub managed_reject_codes: Vec<String>,
    pub accepted: BTreeMap<String, AcceptedCase>,
    pub rejections: BTreeMap<String, RejectionCase>,
    pub nonclaims: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Limits {
    pub max_assets: usize,
    pub max_balance_rows: usize,
    pub max_state_canonical_bytes: usize,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AcceptedCase {
    pub route: String,
    pub command_type: String,
    pub source_leaf_journal_root: RootV2,
    pub receipt_root: RootV2,
    pub vectors: BTreeMap<String, Vector>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RejectionCase {
    pub expected_route: String,
    pub expected_code: String,
    pub command_type: String,
    pub vectors: BTreeMap<String, Vector>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Vector {
    pub canonical: Value,
    pub canonical_bytes_sha256: String,
    pub expected_root: RootV2,
}

pub fn fixture() -> Fixture {
    serde_json::from_str(GOLDEN).expect("committed asset-lane fixture must parse")
}

pub fn vector_bytes(vectors: &BTreeMap<String, Vector>, name: &str) -> Vec<u8> {
    let vector = vectors.get(name).expect("golden vector must exist");
    let bytes = serde_json::to_vec(&vector.canonical).expect("golden value must serialize");
    assert_eq!(hash_bytes_sha256_v2(&bytes), vector.canonical_bytes_sha256);
    bytes
}

pub fn typed_vector<T>(vectors: &BTreeMap<String, Vector>, name: &str) -> T
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    decode_canonical_v2(&vector_bytes(vectors, name))
        .expect("golden vector must decode canonically")
}

pub fn command(vectors: &BTreeMap<String, Vector>, command_type: &str) -> AssetLaneCommandV2 {
    match command_type {
        "transfer" => AssetLaneCommandV2::Transfer(typed_vector(vectors, "command")),
        "managed_lifecycle" => {
            AssetLaneCommandV2::ManagedLifecycle(typed_vector(vectors, "command"))
        }
        _ => panic!("unknown golden command type"),
    }
}

pub fn command_bytes(command: &AssetLaneCommandV2) -> Vec<u8> {
    match command {
        AssetLaneCommandV2::Transfer(command) => {
            canonical_bytes_v2(command).expect("command bytes")
        }
        AssetLaneCommandV2::ManagedLifecycle(command) => {
            canonical_bytes_v2(command).expect("command bytes")
        }
    }
}

pub fn transfer_reject_codes() -> Vec<String> {
    use zenodex_global_settlement_abi_v2::AssetLaneRejectCodeV2;

    [
        AssetTransferRejectCodeV2::MISSING_OCCURRENCE,
        AssetTransferRejectCodeV2::OCCURRENCE_BINDING_MISMATCH,
        AssetTransferRejectCodeV2::RELEASE_MISMATCH,
        AssetTransferRejectCodeV2::UNKNOWN_COMMAND,
        AssetTransferRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH,
        AssetTransferRejectCodeV2::UNKNOWN_ASSET,
        AssetTransferRejectCodeV2::DISABLED_ASSET,
        AssetTransferRejectCodeV2::UNREGISTERED_ASSET,
        AssetTransferRejectCodeV2::ASSET_ORIGIN_MISMATCH,
        AssetTransferRejectCodeV2::NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
        AssetTransferRejectCodeV2::UNAUTHORIZED_SUBJECT,
        AssetTransferRejectCodeV2::SELF_TRANSFER,
        AssetTransferRejectCodeV2::ZERO_AMOUNT,
        AssetTransferRejectCodeV2::FEE_LIMIT_EXCEEDED,
        AssetTransferRejectCodeV2::EFFECT_DELTA_OVERFLOW,
        AssetTransferRejectCodeV2::INSUFFICIENT_BALANCE,
        AssetTransferRejectCodeV2::BALANCE_OVERFLOW,
    ]
    .map(|code| AssetLaneRejectCodeV2::Transfer(code).as_str().to_owned())
    .to_vec()
}
