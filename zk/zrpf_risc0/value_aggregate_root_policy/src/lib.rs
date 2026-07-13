#![no_std]

//! Host-side root policy for the bounded ZRPF Value Aggregate V5 tree.
//!
//! This crate is deliberately absent from the L2 guest's normal, build, and
//! dev dependency closure. It may identify the final L2 program without
//! making that self identity compiler-visible to the program it identifies.

use core::fmt;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, NodeLevelV3, ProfileIdV3, ProgramIdV3};
use zenodex_zrpf_risc0_shared::{profile_id_v3, program_id_from_risc0_words_v3};

/// Final cycle-free L2 image identity recorded by the governed V5 build lane.
pub const PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5: [u32; 8] = [
    3_310_209_353,
    2_187_234_401,
    3_429_179_959,
    3_497_520_757,
    2_979_683_736,
    4_028_871_351,
    2_266_228_022,
    4_165_101_325,
];

const VALUE_AGGREGATE_L2_ROOT_PROFILE_V5: &str = "zrpf_value_aggregate_level_two_root_v5";
const VALUE_AGGREGATE_L2_ROOT_MANIFEST_DOMAIN_V5: &[u8] =
    b"zenodex.zrpf.value_aggregate_l2_root_manifest.v5";
const VALUE_AGGREGATE_L2_ROOT_MANIFEST_CLASS_V5: &[u8] =
    b"experimental_bounded_value_aggregate_level_two_root_v5";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueAggregateRootPolicyErrorV5 {
    InvalidProgram,
    InvalidLevel,
    InvalidProfile,
    InvalidManifest,
    FramingOverflow,
}

impl fmt::Display for ValueAggregateRootPolicyErrorV5 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidProgram => formatter.write_str("invalid pinned V5 L2 root program"),
            Self::InvalidLevel => formatter.write_str("invalid pinned V5 L2 root level"),
            Self::InvalidProfile => formatter.write_str("invalid V5 L2 root profile"),
            Self::InvalidManifest => formatter.write_str("invalid V5 L2 root manifest"),
            Self::FramingOverflow => formatter.write_str("V5 L2 root identity framing overflow"),
        }
    }
}

/// Complete outer identity expected for the final V5 L2 root receipt.
///
/// This value carries no receipt, ledger, release, settlement, or production
/// authority. A sealed verifier must authenticate the receipt under the pinned
/// image and bind this identity to the authenticated proposal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GovernedValueAggregateRootIdentityV5 {
    aggregate_level: NodeLevelV3,
    expected_image_id: [u32; 8],
    expected_program_id: ProgramIdV3,
    expected_profile_id: ProfileIdV3,
    expected_manifest_root: CommitmentV3,
}

impl GovernedValueAggregateRootIdentityV5 {
    pub const fn aggregate_level(self) -> NodeLevelV3 {
        self.aggregate_level
    }

    pub const fn expected_image_id(self) -> [u32; 8] {
        self.expected_image_id
    }

    pub const fn expected_program_id(self) -> ProgramIdV3 {
        self.expected_program_id
    }

    pub const fn expected_profile_id(self) -> ProfileIdV3 {
        self.expected_profile_id
    }

    pub const fn expected_manifest_root(self) -> CommitmentV3 {
        self.expected_manifest_root
    }
}

pub fn value_aggregate_level_two_root_profile_id_v5(
) -> Result<ProfileIdV3, ValueAggregateRootPolicyErrorV5> {
    profile_id_v3(VALUE_AGGREGATE_L2_ROOT_PROFILE_V5)
        .map_err(|_| ValueAggregateRootPolicyErrorV5::InvalidProfile)
}

pub fn value_aggregate_level_two_root_manifest_root_v5(
    program_id: ProgramIdV3,
) -> Result<CommitmentV3, ValueAggregateRootPolicyErrorV5> {
    let profile_id = value_aggregate_level_two_root_profile_id_v5()?;
    commitment_hash_framed(
        VALUE_AGGREGATE_L2_ROOT_MANIFEST_DOMAIN_V5,
        &[
            program_id.as_bytes(),
            profile_id.as_bytes(),
            VALUE_AGGREGATE_L2_ROOT_MANIFEST_CLASS_V5,
        ],
    )
}

pub fn pinned_value_aggregate_level_two_root_identity_v5(
) -> Result<GovernedValueAggregateRootIdentityV5, ValueAggregateRootPolicyErrorV5> {
    let expected_program_id = program_id_from_risc0_words_v3(PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5)
        .map_err(|_| ValueAggregateRootPolicyErrorV5::InvalidProgram)?;
    let aggregate_level =
        NodeLevelV3::new(2).map_err(|_| ValueAggregateRootPolicyErrorV5::InvalidLevel)?;
    Ok(GovernedValueAggregateRootIdentityV5 {
        aggregate_level,
        expected_image_id: PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
        expected_program_id,
        expected_profile_id: value_aggregate_level_two_root_profile_id_v5()?,
        expected_manifest_root: value_aggregate_level_two_root_manifest_root_v5(
            expected_program_id,
        )?,
    })
}

fn commitment_hash_framed(
    domain: &[u8],
    fields: &[&[u8]],
) -> Result<CommitmentV3, ValueAggregateRootPolicyErrorV5> {
    let mut hasher = Sha256::new();
    let domain_length = u16::try_from(domain.len())
        .map_err(|_| ValueAggregateRootPolicyErrorV5::FramingOverflow)?;
    hasher.update(domain_length.to_be_bytes());
    hasher.update(domain);
    for field in fields {
        let length = u32::try_from(field.len())
            .map_err(|_| ValueAggregateRootPolicyErrorV5::FramingOverflow)?;
        hasher.update(length.to_be_bytes());
        hasher.update(field);
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| ValueAggregateRootPolicyErrorV5::InvalidManifest)
}
