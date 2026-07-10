use serde::{Deserialize, Serialize};
use tau_state_proof_risc0_shared::{
    PROOF_TYPE_RECURSIVE_SPOT_LEAF, RECURSIVE_SPOT_LEAF_PROFILE_V1,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SourceKindV1 {
    Spot,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourcePolicyV1 {
    pub source_kind: SourceKindV1,
    pub proof_type: &'static str,
    pub proof_profile: &'static str,
    pub lane_kind: &'static str,
    pub image_id: [u32; 8],
    pub program_sha256: [u8; 32],
    pub local_source_tree_root: [u8; 32],
}

pub const PINNED_SPOT_LEAF_IMAGE_ID_V1: [u32; 8] = [
    1_106_212_114,
    3_876_807_999,
    30_284_647,
    3_707_445_917,
    3_791_588_337,
    1_758_404_023,
    1_845_828_211,
    57_936_497,
];

pub const PINNED_SPOT_LEAF_PROGRAM_SHA256_V1: [u8; 32] = [
    209, 253, 137, 21, 163, 193, 101, 11, 66, 82, 126, 107, 135, 143, 32, 54, 121, 205, 68, 123,
    80, 105, 22, 198, 169, 165, 96, 8, 237, 9, 81, 168,
];

pub const PINNED_V1_LOCAL_SOURCE_TREE_ROOT: [u8; 32] = [
    122, 59, 237, 42, 29, 143, 255, 58, 210, 233, 63, 45, 64, 109, 244, 53, 169, 153, 13, 26, 156,
    4, 98, 255, 51, 35, 251, 2, 131, 39, 86, 78,
];

pub const SPOT_SOURCE_POLICY_V1: SourcePolicyV1 = SourcePolicyV1 {
    source_kind: SourceKindV1::Spot,
    proof_type: PROOF_TYPE_RECURSIVE_SPOT_LEAF,
    proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1,
    lane_kind: "spot",
    image_id: PINNED_SPOT_LEAF_IMAGE_ID_V1,
    program_sha256: PINNED_SPOT_LEAF_PROGRAM_SHA256_V1,
    local_source_tree_root: PINNED_V1_LOCAL_SOURCE_TREE_ROOT,
};

pub const fn source_policy_v1(source_kind: SourceKindV1) -> &'static SourcePolicyV1 {
    match source_kind {
        SourceKindV1::Spot => &SPOT_SOURCE_POLICY_V1,
    }
}
