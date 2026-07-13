#![no_std]

//! Host-only governed identity for the source-opened Spot V6 settlement guest.
//!
//! Keeping this policy outside the settlement guest avoids a self-image cycle.
//! A receipt verifier must authenticate the exact settlement image before it
//! may attach this profile and manifest identity to the admission journal.

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    CommitmentV3, ProfileIdV3, ProgramIdV3, SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1,
    SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1,
};
use zenodex_zrpf_risc0_shared::{profile_id_v3, program_id_from_risc0_words_v3};
use zenodex_zrpf_risc0_spot_value_aggregate_root_policy_v6::pinned_source_opened_spot_value_aggregate_l2_root_identity_v6;

pub const PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6: [u32; 8] = [
    1_712_383_248,
    3_107_114_499,
    1_413_108_939,
    1_586_712_295,
    1_061_365_681,
    3_110_662_716,
    3_576_620_169,
    2_214_019_237,
];

const SETTLEMENT_PROFILE_V6: &str = "zrpf_source_opened_spot_settlement_v6";
const SETTLEMENT_MANIFEST_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot_settlement_manifest.v6";
const SETTLEMENT_MANIFEST_CLASS_V6: &[u8] =
    b"source_opened_spot_settlement_v6_exact_l2_and_admission_v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GovernedSourceOpenedSpotSettlementIdentityV6 {
    expected_image_id: [u32; 8],
    expected_program_id: ProgramIdV3,
    expected_profile_id: ProfileIdV3,
    expected_manifest_root: CommitmentV3,
}

impl GovernedSourceOpenedSpotSettlementIdentityV6 {
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

pub fn source_opened_spot_settlement_profile_id_v6() -> Result<ProfileIdV3, &'static str> {
    profile_id_v3(SETTLEMENT_PROFILE_V6).map_err(|_| "settlement profile")
}

pub fn source_opened_spot_settlement_manifest_root_v6(
    settlement_program_id: ProgramIdV3,
) -> Result<CommitmentV3, &'static str> {
    let l2 = pinned_source_opened_spot_value_aggregate_l2_root_identity_v6()
        .map_err(|_| "settlement L2 identity")?;
    let version = SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1.to_be_bytes();
    hash_framed(
        SETTLEMENT_MANIFEST_DOMAIN_V6,
        &[
            settlement_program_id.as_bytes(),
            source_opened_spot_settlement_profile_id_v6()?.as_bytes(),
            l2.expected_program_id().as_bytes(),
            l2.expected_profile_id().as_bytes(),
            l2.expected_manifest_root().as_bytes(),
            &SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1,
            &version,
            SETTLEMENT_MANIFEST_CLASS_V6,
        ],
    )
}

pub fn pinned_source_opened_spot_settlement_identity_v6(
) -> Result<GovernedSourceOpenedSpotSettlementIdentityV6, &'static str> {
    let program_id =
        program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6)
            .map_err(|_| "settlement program")?;
    Ok(GovernedSourceOpenedSpotSettlementIdentityV6 {
        expected_image_id: PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6,
        expected_program_id: program_id,
        expected_profile_id: source_opened_spot_settlement_profile_id_v6()?,
        expected_manifest_root: source_opened_spot_settlement_manifest_root_v6(program_id)?,
    })
}

fn hash_framed(domain: &[u8], fields: &[&[u8]]) -> Result<CommitmentV3, &'static str> {
    let mut hasher = Sha256::new();
    let domain_len = u16::try_from(domain.len()).map_err(|_| "settlement manifest domain")?;
    hasher.update(domain_len.to_be_bytes());
    hasher.update(domain);
    for field in fields {
        let field_len = u32::try_from(field.len()).map_err(|_| "settlement manifest field")?;
        hasher.update(field_len.to_be_bytes());
        hasher.update(field);
    }
    CommitmentV3::new(hasher.finalize().into()).map_err(|_| "settlement manifest")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn governed_identity_is_nonzero_and_self_consistent() -> Result<(), &'static str> {
        let identity = pinned_source_opened_spot_settlement_identity_v6()?;
        assert!(identity.expected_image_id().iter().any(|word| *word != 0));
        assert_eq!(
            source_opened_spot_settlement_manifest_root_v6(identity.expected_program_id())?,
            identity.expected_manifest_root()
        );
        Ok(())
    }
}
