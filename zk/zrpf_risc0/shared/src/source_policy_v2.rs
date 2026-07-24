use serde::{Deserialize, Serialize};
use tau_state_proof_risc0_shared::{
    PROOF_TYPE_RECURSIVE_SPOT_LEAF, RECURSIVE_SPOT_LEAF_PROFILE_V1,
};

use crate::{AdapterErrorV1, SourcePolicyV1};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SourceKindV2 {
    Spot,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourcePolicyV2 {
    pub source_kind: SourceKindV2,
    pub proof_type: &'static str,
    pub proof_profile: &'static str,
    pub lane_kind: &'static str,
    pub image_id: [u32; 8],
    pub program_sha256: [u8; 32],
    pub source_closure_root: [u8; 32],
}

// These zero sentinels are deliberately unpromoted. The deterministic source
// build must replace all three values before the V2 adapter can accept a
// source receipt. Keeping the pending checkout fail-closed prevents a stale V1
// identity from becoming the current-source authority by default.
pub const PINNED_CURRENT_SPOT_LEAF_IMAGE_ID_V2: [u32; 8] = [0; 8];
pub const PINNED_CURRENT_SPOT_LEAF_PROGRAM_SHA256_V2: [u8; 32] = [0; 32];
pub const PINNED_CURRENT_SPOT_SOURCE_CLOSURE_ROOT_V2: [u8; 32] = [0; 32];

pub const CURRENT_SPOT_SOURCE_POLICY_V2: SourcePolicyV2 = SourcePolicyV2 {
    source_kind: SourceKindV2::Spot,
    proof_type: PROOF_TYPE_RECURSIVE_SPOT_LEAF,
    proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1,
    lane_kind: "spot",
    image_id: PINNED_CURRENT_SPOT_LEAF_IMAGE_ID_V2,
    program_sha256: PINNED_CURRENT_SPOT_LEAF_PROGRAM_SHA256_V2,
    source_closure_root: PINNED_CURRENT_SPOT_SOURCE_CLOSURE_ROOT_V2,
};

// This policy exists solely to keep proof-neutral semantic and mutation tests
// executable while the final current-source identity remains deliberately
// unpinned. The feature is disabled by default and rejected on the zkVM target.
#[cfg(feature = "test-only-candidate-source-policy")]
const TEST_ONLY_CANDIDATE_SPOT_SOURCE_POLICY_V2: SourcePolicyV2 = SourcePolicyV2 {
    source_kind: SourceKindV2::Spot,
    proof_type: PROOF_TYPE_RECURSIVE_SPOT_LEAF,
    proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1,
    lane_kind: "spot",
    image_id: [
        0x7465_7374,
        0x2d6f_6e6c,
        0x792d_6361,
        0x6e64_6964,
        0x6174_652d,
        0x736f_7572,
        0x6365_2d76,
        0x3200_0001,
    ],
    program_sha256: [0xA5; 32],
    source_closure_root: [0x5A; 32],
};

pub fn source_policy_v2(
    source_kind: SourceKindV2,
) -> Result<&'static SourcePolicyV2, AdapterErrorV1> {
    #[cfg(feature = "test-only-candidate-source-policy")]
    let policy = match source_kind {
        SourceKindV2::Spot => &TEST_ONLY_CANDIDATE_SPOT_SOURCE_POLICY_V2,
    };
    #[cfg(not(feature = "test-only-candidate-source-policy"))]
    let policy = match source_kind {
        SourceKindV2::Spot => &CURRENT_SPOT_SOURCE_POLICY_V2,
    };
    validate_source_policy_v2(policy)?;
    Ok(policy)
}

pub(crate) fn validate_source_policy_v2(policy: &SourcePolicyV2) -> Result<(), AdapterErrorV1> {
    if policy.image_id.iter().all(|word| *word == 0) {
        return Err(AdapterErrorV1::SourcePolicyMismatch(
            "current_source_image_id_unpinned",
        ));
    }
    if policy.program_sha256.iter().all(|byte| *byte == 0) {
        return Err(AdapterErrorV1::SourcePolicyMismatch(
            "current_source_program_sha256_unpinned",
        ));
    }
    if policy.source_closure_root.iter().all(|byte| *byte == 0) {
        return Err(AdapterErrorV1::SourcePolicyMismatch(
            "current_source_closure_root_unpinned",
        ));
    }
    Ok(())
}

pub(crate) const fn compatibility_source_policy_v1_shape(
    policy: &SourcePolicyV2,
) -> SourcePolicyV1 {
    SourcePolicyV1 {
        source_kind: crate::SourceKindV1::Spot,
        proof_type: policy.proof_type,
        proof_profile: policy.proof_profile,
        lane_kind: policy.lane_kind,
        image_id: policy.image_id,
        program_sha256: policy.program_sha256,
        local_source_tree_root: policy.source_closure_root,
    }
}
