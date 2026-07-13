use core::fmt;

use sha2::{Digest, Sha256};

use super::{CheckpointFinalityCertificateErrorV1, CheckpointFinalityCertificateV1};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

pub const CHECKPOINT_FINALITY_POLICY_VERSION_V1: u16 = 1;

const POLICY_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.checkpoint_finality.policy_root.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointFinalityPolicyInputV1 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub finality_network_id: CommitmentV3,
    pub finality_protocol_id: CommitmentV3,
    pub expected_external_finality_policy_hash: CommitmentV3,
    pub expected_finality_verifier_set_root: CommitmentV3,
    pub minimum_checkpoint_height: u64,
}

/// Application policy for one external finalized-checkpoint projection.
///
/// The root binds every governed acceptance parameter. It does not establish
/// that governance authorized the policy or that external consensus finalized
/// a checkpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointFinalityPolicyV1 {
    policy_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    finality_network_id: CommitmentV3,
    finality_protocol_id: CommitmentV3,
    expected_external_finality_policy_hash: CommitmentV3,
    expected_finality_verifier_set_root: CommitmentV3,
    minimum_checkpoint_height: u64,
}

/// Exact fields obtained from the independently governed finality adapter.
///
/// This is a data value, not an authentication capability. Production code
/// must derive it from an authenticated checkpoint/quorum or Tau-finality
/// verifier and keep that authority boundary outside this proof-neutral crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpectedFinalizedCheckpointBindingV1 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub epoch_id: u64,
    pub proof_journal_hash: CommitmentV3,
    pub post_state_root: CommitmentV3,
    pub checkpoint_height: u64,
    pub checkpoint_hash: CommitmentV3,
    pub finality_network_id: CommitmentV3,
    pub finality_protocol_id: CommitmentV3,
    pub external_finality_policy_hash: CommitmentV3,
    pub finality_verifier_set_root: CommitmentV3,
    pub finality_evidence_root: CommitmentV3,
}

pub struct CheckpointFinalityPolicyCheckInputV1<'a> {
    pub policy: &'a CheckpointFinalityPolicyV1,
    pub certificate: &'a CheckpointFinalityCertificateV1,
    pub expected: ExpectedFinalizedCheckpointBindingV1,
    /// Last checkpoint height atomically accepted for this exact governed
    /// scope. `None` is valid only for an empty admission cursor.
    pub previously_accepted_checkpoint_height: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckpointFinalityPolicyErrorV1 {
    ApplicationMismatch,
    DomainMismatch,
    ExpectedApplicationMismatch,
    ExpectedDomainMismatch,
    EpochMismatch { actual: u64, expected: u64 },
    ProofJournalMismatch,
    PostStateRootMismatch,
    CheckpointBelowMinimum { actual: u64, minimum: u64 },
    CheckpointHeightMismatch { actual: u64, expected: u64 },
    CheckpointNotNewerThanAccepted { actual: u64, previous: u64 },
    CheckpointHashMismatch,
    FinalityNetworkMismatch,
    FinalityProtocolMismatch,
    ExpectedFinalityNetworkMismatch,
    ExpectedFinalityProtocolMismatch,
    ExternalFinalityPolicyMismatch,
    FinalityVerifierSetMismatch,
    ExpectedExternalFinalityPolicyMismatch,
    ExpectedFinalityVerifierSetMismatch,
    FinalityEvidenceMismatch,
    FinalityPolicyRootMismatch,
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    Certificate(CheckpointFinalityCertificateErrorV1),
}

impl fmt::Display for CheckpointFinalityPolicyErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ApplicationMismatch => {
                formatter.write_str("checkpoint finality application mismatch")
            }
            Self::DomainMismatch => formatter.write_str("checkpoint finality domain mismatch"),
            Self::ExpectedApplicationMismatch => {
                formatter.write_str("authenticated checkpoint application mismatch")
            }
            Self::ExpectedDomainMismatch => {
                formatter.write_str("authenticated checkpoint domain mismatch")
            }
            Self::EpochMismatch { actual, expected } => write!(
                formatter,
                "checkpoint finality epoch {actual} differs from expected {expected}"
            ),
            Self::ProofJournalMismatch => {
                formatter.write_str("checkpoint finality proof journal mismatch")
            }
            Self::PostStateRootMismatch => {
                formatter.write_str("checkpoint finality post-state root mismatch")
            }
            Self::CheckpointBelowMinimum { actual, minimum } => write!(
                formatter,
                "checkpoint finality height {actual} is below policy minimum {minimum}"
            ),
            Self::CheckpointHeightMismatch { actual, expected } => write!(
                formatter,
                "checkpoint finality height {actual} differs from expected {expected}"
            ),
            Self::CheckpointNotNewerThanAccepted { actual, previous } => write!(
                formatter,
                "checkpoint finality height {actual} is not newer than accepted height {previous}"
            ),
            Self::CheckpointHashMismatch => {
                formatter.write_str("checkpoint finality checkpoint hash mismatch")
            }
            Self::FinalityNetworkMismatch => {
                formatter.write_str("checkpoint finality network mismatch")
            }
            Self::FinalityProtocolMismatch => {
                formatter.write_str("checkpoint finality protocol mismatch")
            }
            Self::ExpectedFinalityNetworkMismatch => {
                formatter.write_str("authenticated checkpoint finality network mismatch")
            }
            Self::ExpectedFinalityProtocolMismatch => {
                formatter.write_str("authenticated checkpoint finality protocol mismatch")
            }
            Self::ExternalFinalityPolicyMismatch => {
                formatter.write_str("external finality policy mismatch")
            }
            Self::FinalityVerifierSetMismatch => {
                formatter.write_str("checkpoint finality verifier-set mismatch")
            }
            Self::ExpectedExternalFinalityPolicyMismatch => {
                formatter.write_str("authenticated checkpoint external policy mismatch")
            }
            Self::ExpectedFinalityVerifierSetMismatch => {
                formatter.write_str("authenticated checkpoint verifier-set mismatch")
            }
            Self::FinalityEvidenceMismatch => {
                formatter.write_str("checkpoint finality evidence mismatch")
            }
            Self::FinalityPolicyRootMismatch => {
                formatter.write_str("checkpoint finality policy root mismatch")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => write!(
                formatter,
                "invalid derived checkpoint finality policy commitment: {field}"
            ),
            Self::Certificate(error) => write!(
                formatter,
                "checkpoint finality certificate rejected: {error}"
            ),
        }
    }
}

impl From<CheckpointFinalityCertificateErrorV1> for CheckpointFinalityPolicyErrorV1 {
    fn from(error: CheckpointFinalityCertificateErrorV1) -> Self {
        Self::Certificate(error)
    }
}

impl CheckpointFinalityPolicyV1 {
    pub const fn new(input: CheckpointFinalityPolicyInputV1) -> Self {
        Self {
            policy_version: CHECKPOINT_FINALITY_POLICY_VERSION_V1,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            finality_network_id: input.finality_network_id,
            finality_protocol_id: input.finality_protocol_id,
            expected_external_finality_policy_hash: input.expected_external_finality_policy_hash,
            expected_finality_verifier_set_root: input.expected_finality_verifier_set_root,
            minimum_checkpoint_height: input.minimum_checkpoint_height,
        }
    }

    pub fn policy_root(&self) -> Result<CommitmentV3, CheckpointFinalityPolicyErrorV1> {
        derive_policy_root_v1(self)
    }

    pub const fn policy_version(&self) -> u16 {
        self.policy_version
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn finality_network_id(&self) -> CommitmentV3 {
        self.finality_network_id
    }

    pub const fn finality_protocol_id(&self) -> CommitmentV3 {
        self.finality_protocol_id
    }

    pub const fn expected_external_finality_policy_hash(&self) -> CommitmentV3 {
        self.expected_external_finality_policy_hash
    }

    pub const fn expected_finality_verifier_set_root(&self) -> CommitmentV3 {
        self.expected_finality_verifier_set_root
    }

    pub const fn minimum_checkpoint_height(&self) -> u64 {
        self.minimum_checkpoint_height
    }
}

/// Check exact certificate fields against policy and authenticated expectations.
///
/// Successful return establishes only local field equality and policy
/// satisfaction. It grants no consensus, finality, settlement, release, or
/// production authority.
pub fn check_checkpoint_finality_policy_satisfied_v1(
    input: CheckpointFinalityPolicyCheckInputV1<'_>,
) -> Result<(), CheckpointFinalityPolicyErrorV1> {
    input.certificate.validate_self_consistency()?;
    require_policy_scope(&input)?;
    require_expected_checkpoint_binding(&input)
}

fn require_policy_scope(
    input: &CheckpointFinalityPolicyCheckInputV1<'_>,
) -> Result<(), CheckpointFinalityPolicyErrorV1> {
    let policy = input.policy;
    let certificate = input.certificate;
    if certificate.application_id() != policy.application_id {
        return Err(CheckpointFinalityPolicyErrorV1::ApplicationMismatch);
    }
    if certificate.chain_or_domain_id() != policy.chain_or_domain_id {
        return Err(CheckpointFinalityPolicyErrorV1::DomainMismatch);
    }
    if certificate.finality_network_id() != policy.finality_network_id {
        return Err(CheckpointFinalityPolicyErrorV1::FinalityNetworkMismatch);
    }
    if certificate.finality_protocol_id() != policy.finality_protocol_id {
        return Err(CheckpointFinalityPolicyErrorV1::FinalityProtocolMismatch);
    }
    if certificate.external_finality_policy_hash() != policy.expected_external_finality_policy_hash
    {
        return Err(CheckpointFinalityPolicyErrorV1::ExternalFinalityPolicyMismatch);
    }
    if certificate.finality_verifier_set_root() != policy.expected_finality_verifier_set_root {
        return Err(CheckpointFinalityPolicyErrorV1::FinalityVerifierSetMismatch);
    }
    if certificate.checkpoint_height() < policy.minimum_checkpoint_height {
        return Err(CheckpointFinalityPolicyErrorV1::CheckpointBelowMinimum {
            actual: certificate.checkpoint_height(),
            minimum: policy.minimum_checkpoint_height,
        });
    }
    if certificate.finality_policy_root() != policy.policy_root()? {
        return Err(CheckpointFinalityPolicyErrorV1::FinalityPolicyRootMismatch);
    }
    Ok(())
}

fn require_expected_checkpoint_binding(
    input: &CheckpointFinalityPolicyCheckInputV1<'_>,
) -> Result<(), CheckpointFinalityPolicyErrorV1> {
    let certificate = input.certificate;
    let expected = input.expected;
    if expected.application_id != input.policy.application_id {
        return Err(CheckpointFinalityPolicyErrorV1::ExpectedApplicationMismatch);
    }
    if expected.chain_or_domain_id != input.policy.chain_or_domain_id {
        return Err(CheckpointFinalityPolicyErrorV1::ExpectedDomainMismatch);
    }
    if expected.finality_network_id != input.policy.finality_network_id {
        return Err(CheckpointFinalityPolicyErrorV1::ExpectedFinalityNetworkMismatch);
    }
    if expected.finality_protocol_id != input.policy.finality_protocol_id {
        return Err(CheckpointFinalityPolicyErrorV1::ExpectedFinalityProtocolMismatch);
    }
    if expected.external_finality_policy_hash != input.policy.expected_external_finality_policy_hash
    {
        return Err(CheckpointFinalityPolicyErrorV1::ExpectedExternalFinalityPolicyMismatch);
    }
    if expected.finality_verifier_set_root != input.policy.expected_finality_verifier_set_root {
        return Err(CheckpointFinalityPolicyErrorV1::ExpectedFinalityVerifierSetMismatch);
    }
    if certificate.epoch_id() != expected.epoch_id {
        return Err(CheckpointFinalityPolicyErrorV1::EpochMismatch {
            actual: certificate.epoch_id(),
            expected: expected.epoch_id,
        });
    }
    if certificate.proof_journal_hash() != expected.proof_journal_hash {
        return Err(CheckpointFinalityPolicyErrorV1::ProofJournalMismatch);
    }
    if certificate.post_state_root() != expected.post_state_root {
        return Err(CheckpointFinalityPolicyErrorV1::PostStateRootMismatch);
    }
    if certificate.checkpoint_height() != expected.checkpoint_height {
        return Err(CheckpointFinalityPolicyErrorV1::CheckpointHeightMismatch {
            actual: certificate.checkpoint_height(),
            expected: expected.checkpoint_height,
        });
    }
    if let Some(previous) = input.previously_accepted_checkpoint_height {
        if certificate.checkpoint_height() <= previous {
            return Err(
                CheckpointFinalityPolicyErrorV1::CheckpointNotNewerThanAccepted {
                    actual: certificate.checkpoint_height(),
                    previous,
                },
            );
        }
    }
    if certificate.checkpoint_hash() != expected.checkpoint_hash {
        return Err(CheckpointFinalityPolicyErrorV1::CheckpointHashMismatch);
    }
    if certificate.finality_evidence_root() != expected.finality_evidence_root {
        return Err(CheckpointFinalityPolicyErrorV1::FinalityEvidenceMismatch);
    }
    Ok(())
}

fn derive_policy_root_v1(
    policy: &CheckpointFinalityPolicyV1,
) -> Result<CommitmentV3, CheckpointFinalityPolicyErrorV1> {
    let mut hasher = domain_hasher(POLICY_ROOT_DOMAIN_V1)?;
    hasher.update(policy.policy_version.to_be_bytes());
    hasher.update(policy.application_id.as_bytes());
    hasher.update(policy.chain_or_domain_id.as_bytes());
    hasher.update(policy.finality_network_id.as_bytes());
    hasher.update(policy.finality_protocol_id.as_bytes());
    hasher.update(policy.expected_external_finality_policy_hash.as_bytes());
    hasher.update(policy.expected_finality_verifier_set_root.as_bytes());
    hasher.update(policy.minimum_checkpoint_height.to_be_bytes());
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| CheckpointFinalityPolicyErrorV1::InvalidDerivedCommitment("policy_root"))
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, CheckpointFinalityPolicyErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| CheckpointFinalityPolicyErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}
