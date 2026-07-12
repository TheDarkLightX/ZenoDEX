use sha2::{Digest, Sha256};

use super::base::{
    PrivacyClaimV1, ProofTaskKindV1, ProofTaskPriorityV1, ProofTaskPrivacyPolicyV1,
    TaskManifestErrorV1,
};
use crate::{CommitmentV3, TaskIdV3};

pub(super) fn domain_hasher(domain: &[u8]) -> Result<Sha256, TaskManifestErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| TaskManifestErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

pub(super) fn commitment(bytes: [u8; 32]) -> Result<CommitmentV3, TaskManifestErrorV1> {
    CommitmentV3::new(bytes).map_err(|_| TaskManifestErrorV1::InvalidDerivedIdentity("zero_hash"))
}

pub(super) fn write_optional_commitment(hasher: &mut Sha256, value: Option<CommitmentV3>) {
    match value {
        None => hasher.update([0]),
        Some(value) => {
            hasher.update([1]);
            hasher.update(value.as_bytes());
        }
    }
}

pub(super) fn write_optional_task(hasher: &mut Sha256, value: Option<TaskIdV3>) {
    match value {
        None => hasher.update([0]),
        Some(value) => {
            hasher.update([1]);
            hasher.update(value.as_bytes());
        }
    }
}

pub(super) fn write_optional_u64(hasher: &mut Sha256, value: Option<u64>) {
    match value {
        None => hasher.update([0]),
        Some(value) => {
            hasher.update([1]);
            hasher.update(value.to_be_bytes());
        }
    }
}

pub(super) const fn privacy_claim_tag(value: PrivacyClaimV1) -> u8 {
    match value {
        PrivacyClaimV1::PublicComputation => 0,
        PrivacyClaimV1::WitnessPrivate => 1,
    }
}

pub(super) const fn task_kind_tag(value: ProofTaskKindV1) -> u8 {
    match value {
        ProofTaskKindV1::Leaf => 0,
        ProofTaskKindV1::Aggregate => 1,
        ProofTaskKindV1::EpochCheckpoint => 2,
        ProofTaskKindV1::DataAvailability => 3,
    }
}

pub(super) const fn priority_tag(value: ProofTaskPriorityV1) -> u8 {
    match value {
        ProofTaskPriorityV1::Normal => 0,
        ProofTaskPriorityV1::Urgent => 1,
        ProofTaskPriorityV1::CriticalCheckpoint => 2,
    }
}

pub(super) const fn privacy_policy_tag(value: ProofTaskPrivacyPolicyV1) -> u8 {
    match value {
        ProofTaskPrivacyPolicyV1::PublicInputs => 0,
        ProofTaskPrivacyPolicyV1::PrivateWitnessAllowed => 1,
        ProofTaskPrivacyPolicyV1::PrivateWitnessRequired => 2,
    }
}
