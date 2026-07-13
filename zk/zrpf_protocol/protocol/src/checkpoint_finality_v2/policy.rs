use core::fmt;

use sha2::{Digest, Sha256};

use super::{
    CheckedCheckpointFinalityTransitionV2, CheckpointCursorProposalV2,
    CheckpointFinalityCertificateErrorV2, CheckpointFinalityCertificateV2,
    DerivedCheckpointCursorV2, ProposedPriorApplicationCheckpointRecordInputV2,
    ProposedPriorApplicationCheckpointRecordV2,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

pub const CHECKPOINT_FINALITY_POLICY_VERSION_V2: u16 = 2;

const POLICY_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.checkpoint_finality.policy_root.v2";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointFinalityPolicyInputV2 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub finality_network_id: CommitmentV3,
    pub finality_protocol_id: CommitmentV3,
    pub expected_external_finality_policy_hash: CommitmentV3,
    pub expected_finality_verifier_set_root: CommitmentV3,
    pub genesis_application_checkpoint_sequence: u64,
    pub genesis_application_checkpoint_hash: CommitmentV3,
}

/// Governed scope and genesis anchor for a linear ZRPF application chain.
///
/// The root binds every field. Construction does not establish that governance
/// authorized the policy or that external finality evidence is valid.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointFinalityPolicyV2 {
    policy_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    finality_network_id: CommitmentV3,
    finality_protocol_id: CommitmentV3,
    expected_external_finality_policy_hash: CommitmentV3,
    expected_finality_verifier_set_root: CommitmentV3,
    genesis_application_checkpoint_sequence: u64,
    genesis_application_checkpoint_hash: CommitmentV3,
}

/// Supplied application-checkpoint and finality-binding projection.
///
/// This is an ordinary data value intended to be derived by a governed finality
/// verifier. The proof-neutral checker cannot establish its provenance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SuppliedCheckpointFinalityBindingV2 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub epoch_id: u64,
    pub proof_journal_hash: CommitmentV3,
    pub post_state_root: CommitmentV3,
    pub application_checkpoint_sequence: u64,
    pub application_checkpoint_hash: CommitmentV3,
    pub parent_application_checkpoint_hash: CommitmentV3,
    pub finality_network_id: CommitmentV3,
    pub finality_protocol_id: CommitmentV3,
    pub external_finality_policy_hash: CommitmentV3,
    pub finality_verifier_set_root: CommitmentV3,
    pub finality_evidence_root: CommitmentV3,
}

pub struct CheckpointFinalityPolicyCheckInputV2<'a> {
    pub policy: &'a CheckpointFinalityPolicyV2,
    pub certificate: &'a CheckpointFinalityCertificateV2,
    pub expected: SuppliedCheckpointFinalityBindingV2,
    pub prior_cursor_proposal: CheckpointCursorProposalV2,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckpointFinalityPolicyErrorV2 {
    ApplicationMismatch,
    DomainMismatch,
    SuppliedApplicationMismatch,
    SuppliedDomainMismatch,
    EpochMismatch {
        actual: u64,
        expected: u64,
    },
    ProofJournalMismatch,
    PostStateRootMismatch,
    ApplicationCheckpointSequenceMismatch {
        actual: u64,
        expected: u64,
    },
    ApplicationCheckpointHashMismatch,
    ParentApplicationCheckpointHashMismatch,
    FinalityNetworkMismatch,
    FinalityProtocolMismatch,
    SuppliedFinalityNetworkMismatch,
    SuppliedFinalityProtocolMismatch,
    ExternalFinalityPolicyMismatch,
    FinalityVerifierSetMismatch,
    SuppliedExternalFinalityPolicyMismatch,
    SuppliedFinalityVerifierSetMismatch,
    FinalityEvidenceMismatch,
    FinalityPolicyRootMismatch,
    PriorRecordVersionMismatch {
        actual: u16,
        expected: u16,
    },
    PriorRecordApplicationMismatch,
    PriorRecordDomainMismatch,
    PriorRecordFinalityNetworkMismatch,
    PriorRecordFinalityProtocolMismatch,
    PriorRecordExternalFinalityPolicyMismatch,
    PriorRecordFinalityVerifierSetMismatch,
    PriorRecordFinalityPolicyRootMismatch,
    PriorRecordBeforeGenesis {
        actual: u64,
        genesis: u64,
    },
    PriorRecordGenesisHashMismatch {
        actual: CommitmentV3,
        expected: CommitmentV3,
    },
    NextApplicationCheckpointSequenceOverflow {
        prior: u64,
    },
    ApplicationCheckpointIsNotExactSuccessor {
        actual: u64,
        expected: u64,
        prior: u64,
    },
    ApplicationCheckpointParentDoesNotMatchPrior {
        actual: CommitmentV3,
        expected: CommitmentV3,
    },
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    Certificate(CheckpointFinalityCertificateErrorV2),
}

impl fmt::Display for CheckpointFinalityPolicyErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ApplicationMismatch => {
                formatter.write_str("checkpoint finality V2 application mismatch")
            }
            Self::DomainMismatch => formatter.write_str("checkpoint finality V2 domain mismatch"),
            Self::SuppliedApplicationMismatch => {
                formatter.write_str("supplied checkpoint V2 application mismatch")
            }
            Self::SuppliedDomainMismatch => {
                formatter.write_str("supplied checkpoint V2 domain mismatch")
            }
            Self::EpochMismatch { actual, expected } => write!(
                formatter,
                "checkpoint finality V2 epoch {actual} differs from expected {expected}"
            ),
            Self::ProofJournalMismatch => {
                formatter.write_str("checkpoint finality V2 proof journal mismatch")
            }
            Self::PostStateRootMismatch => {
                formatter.write_str("checkpoint finality V2 post-state root mismatch")
            }
            Self::ApplicationCheckpointSequenceMismatch { actual, expected } => write!(
                formatter,
                "application checkpoint sequence {actual} differs from supplied sequence {expected}"
            ),
            Self::ApplicationCheckpointHashMismatch => {
                formatter.write_str("checkpoint finality V2 checkpoint hash mismatch")
            }
            Self::ParentApplicationCheckpointHashMismatch => {
                formatter.write_str("checkpoint finality V2 parent hash mismatch")
            }
            Self::FinalityNetworkMismatch => {
                formatter.write_str("checkpoint finality V2 network mismatch")
            }
            Self::FinalityProtocolMismatch => {
                formatter.write_str("checkpoint finality V2 protocol mismatch")
            }
            Self::SuppliedFinalityNetworkMismatch => {
                formatter.write_str("supplied checkpoint V2 finality network mismatch")
            }
            Self::SuppliedFinalityProtocolMismatch => {
                formatter.write_str("supplied checkpoint V2 finality protocol mismatch")
            }
            Self::ExternalFinalityPolicyMismatch => {
                formatter.write_str("checkpoint finality V2 external policy mismatch")
            }
            Self::FinalityVerifierSetMismatch => {
                formatter.write_str("checkpoint finality V2 verifier-set mismatch")
            }
            Self::SuppliedExternalFinalityPolicyMismatch => {
                formatter.write_str("supplied checkpoint V2 external policy mismatch")
            }
            Self::SuppliedFinalityVerifierSetMismatch => {
                formatter.write_str("supplied checkpoint V2 verifier-set mismatch")
            }
            Self::FinalityEvidenceMismatch => {
                formatter.write_str("checkpoint finality V2 evidence mismatch")
            }
            Self::FinalityPolicyRootMismatch => {
                formatter.write_str("checkpoint finality V2 policy root mismatch")
            }
            Self::PriorRecordVersionMismatch { actual, expected } => write!(
                formatter,
                "proposed prior checkpoint record version {actual} differs from {expected}"
            ),
            Self::PriorRecordApplicationMismatch => {
                formatter.write_str("proposed prior checkpoint record application mismatch")
            }
            Self::PriorRecordDomainMismatch => {
                formatter.write_str("proposed prior checkpoint record domain mismatch")
            }
            Self::PriorRecordFinalityNetworkMismatch => {
                formatter.write_str("proposed prior checkpoint record finality network mismatch")
            }
            Self::PriorRecordFinalityProtocolMismatch => {
                formatter.write_str("proposed prior checkpoint record finality protocol mismatch")
            }
            Self::PriorRecordExternalFinalityPolicyMismatch => {
                formatter.write_str("proposed prior checkpoint record external policy mismatch")
            }
            Self::PriorRecordFinalityVerifierSetMismatch => {
                formatter.write_str("proposed prior checkpoint record verifier-set mismatch")
            }
            Self::PriorRecordFinalityPolicyRootMismatch => {
                formatter.write_str("proposed prior checkpoint record local policy root mismatch")
            }
            Self::PriorRecordBeforeGenesis { actual, genesis } => write!(
                formatter,
                "proposed prior application checkpoint sequence {actual} precedes governed genesis {genesis}"
            ),
            Self::PriorRecordGenesisHashMismatch { .. } => {
                formatter.write_str("proposed prior record replaces governed application genesis hash")
            }
            Self::NextApplicationCheckpointSequenceOverflow { prior } => write!(
                formatter,
                "application checkpoint sequence after {prior} overflows u64"
            ),
            Self::ApplicationCheckpointIsNotExactSuccessor {
                actual,
                expected,
                prior,
            } => write!(
                formatter,
                "application checkpoint sequence {actual} is not exact successor {expected} of {prior}"
            ),
            Self::ApplicationCheckpointParentDoesNotMatchPrior { .. } => {
                formatter.write_str("application checkpoint parent hash does not match prior record")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => write!(
                formatter,
                "invalid derived checkpoint finality V2 policy commitment: {field}"
            ),
            Self::Certificate(error) => write!(
                formatter,
                "checkpoint finality V2 certificate rejected: {error}"
            ),
        }
    }
}

impl From<CheckpointFinalityCertificateErrorV2> for CheckpointFinalityPolicyErrorV2 {
    fn from(error: CheckpointFinalityCertificateErrorV2) -> Self {
        Self::Certificate(error)
    }
}

impl CheckpointFinalityPolicyV2 {
    pub const fn new(input: CheckpointFinalityPolicyInputV2) -> Self {
        Self {
            policy_version: CHECKPOINT_FINALITY_POLICY_VERSION_V2,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            finality_network_id: input.finality_network_id,
            finality_protocol_id: input.finality_protocol_id,
            expected_external_finality_policy_hash: input.expected_external_finality_policy_hash,
            expected_finality_verifier_set_root: input.expected_finality_verifier_set_root,
            genesis_application_checkpoint_sequence: input.genesis_application_checkpoint_sequence,
            genesis_application_checkpoint_hash: input.genesis_application_checkpoint_hash,
        }
    }

    pub fn policy_root(&self) -> Result<CommitmentV3, CheckpointFinalityPolicyErrorV2> {
        derive_policy_root_v2(self)
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

    pub const fn genesis_application_checkpoint_sequence(&self) -> u64 {
        self.genesis_application_checkpoint_sequence
    }

    pub const fn genesis_application_checkpoint_hash(&self) -> CommitmentV3 {
        self.genesis_application_checkpoint_hash
    }
}

/// Check one candidate against exact policy, supplied facts, and cursor proposal.
///
/// Success is a proof-neutral equality result. It grants no consensus,
/// settlement, release, bridge, or production authority.
pub fn check_checkpoint_finality_policy_satisfied_v2(
    input: CheckpointFinalityPolicyCheckInputV2<'_>,
) -> Result<CheckedCheckpointFinalityTransitionV2, CheckpointFinalityPolicyErrorV2> {
    input.certificate.validate_self_consistency()?;
    let policy_root = input.policy.policy_root()?;
    require_certificate_policy_scope(&input, policy_root)?;
    require_expected_policy_scope(&input)?;
    require_certificate_expected_binding(&input)?;
    let derived_next_cursor = require_exact_chain_successor(&input, policy_root)?;
    Ok(CheckedCheckpointFinalityTransitionV2::from_checked(
        policy_root,
        input.certificate.certificate_root(),
        input.expected,
        input.prior_cursor_proposal,
        derived_next_cursor,
    ))
}

fn require_certificate_policy_scope(
    input: &CheckpointFinalityPolicyCheckInputV2<'_>,
    policy_root: CommitmentV3,
) -> Result<(), CheckpointFinalityPolicyErrorV2> {
    let policy = input.policy;
    let certificate = input.certificate;
    if certificate.application_id() != policy.application_id {
        return Err(CheckpointFinalityPolicyErrorV2::ApplicationMismatch);
    }
    if certificate.chain_or_domain_id() != policy.chain_or_domain_id {
        return Err(CheckpointFinalityPolicyErrorV2::DomainMismatch);
    }
    if certificate.finality_network_id() != policy.finality_network_id {
        return Err(CheckpointFinalityPolicyErrorV2::FinalityNetworkMismatch);
    }
    if certificate.finality_protocol_id() != policy.finality_protocol_id {
        return Err(CheckpointFinalityPolicyErrorV2::FinalityProtocolMismatch);
    }
    if certificate.external_finality_policy_hash() != policy.expected_external_finality_policy_hash
    {
        return Err(CheckpointFinalityPolicyErrorV2::ExternalFinalityPolicyMismatch);
    }
    if certificate.finality_verifier_set_root() != policy.expected_finality_verifier_set_root {
        return Err(CheckpointFinalityPolicyErrorV2::FinalityVerifierSetMismatch);
    }
    if certificate.finality_policy_root() != policy_root {
        return Err(CheckpointFinalityPolicyErrorV2::FinalityPolicyRootMismatch);
    }
    Ok(())
}

fn require_expected_policy_scope(
    input: &CheckpointFinalityPolicyCheckInputV2<'_>,
) -> Result<(), CheckpointFinalityPolicyErrorV2> {
    let policy = input.policy;
    let expected = input.expected;
    if expected.application_id != policy.application_id {
        return Err(CheckpointFinalityPolicyErrorV2::SuppliedApplicationMismatch);
    }
    if expected.chain_or_domain_id != policy.chain_or_domain_id {
        return Err(CheckpointFinalityPolicyErrorV2::SuppliedDomainMismatch);
    }
    if expected.finality_network_id != policy.finality_network_id {
        return Err(CheckpointFinalityPolicyErrorV2::SuppliedFinalityNetworkMismatch);
    }
    if expected.finality_protocol_id != policy.finality_protocol_id {
        return Err(CheckpointFinalityPolicyErrorV2::SuppliedFinalityProtocolMismatch);
    }
    if expected.external_finality_policy_hash != policy.expected_external_finality_policy_hash {
        return Err(CheckpointFinalityPolicyErrorV2::SuppliedExternalFinalityPolicyMismatch);
    }
    if expected.finality_verifier_set_root != policy.expected_finality_verifier_set_root {
        return Err(CheckpointFinalityPolicyErrorV2::SuppliedFinalityVerifierSetMismatch);
    }
    Ok(())
}

fn require_certificate_expected_binding(
    input: &CheckpointFinalityPolicyCheckInputV2<'_>,
) -> Result<(), CheckpointFinalityPolicyErrorV2> {
    let certificate = input.certificate;
    let expected = input.expected;
    if certificate.epoch_id() != expected.epoch_id {
        return Err(CheckpointFinalityPolicyErrorV2::EpochMismatch {
            actual: certificate.epoch_id(),
            expected: expected.epoch_id,
        });
    }
    if certificate.proof_journal_hash() != expected.proof_journal_hash {
        return Err(CheckpointFinalityPolicyErrorV2::ProofJournalMismatch);
    }
    if certificate.post_state_root() != expected.post_state_root {
        return Err(CheckpointFinalityPolicyErrorV2::PostStateRootMismatch);
    }
    if certificate.application_checkpoint_sequence() != expected.application_checkpoint_sequence {
        return Err(
            CheckpointFinalityPolicyErrorV2::ApplicationCheckpointSequenceMismatch {
                actual: certificate.application_checkpoint_sequence(),
                expected: expected.application_checkpoint_sequence,
            },
        );
    }
    if certificate.application_checkpoint_hash() != expected.application_checkpoint_hash {
        return Err(CheckpointFinalityPolicyErrorV2::ApplicationCheckpointHashMismatch);
    }
    if certificate.parent_application_checkpoint_hash()
        != expected.parent_application_checkpoint_hash
    {
        return Err(CheckpointFinalityPolicyErrorV2::ParentApplicationCheckpointHashMismatch);
    }
    if certificate.finality_evidence_root() != expected.finality_evidence_root {
        return Err(CheckpointFinalityPolicyErrorV2::FinalityEvidenceMismatch);
    }
    Ok(())
}

fn require_exact_chain_successor(
    input: &CheckpointFinalityPolicyCheckInputV2<'_>,
    policy_root: CommitmentV3,
) -> Result<DerivedCheckpointCursorV2, CheckpointFinalityPolicyErrorV2> {
    let (prior_sequence, prior_hash) = match input.prior_cursor_proposal.prior_record() {
        None => (
            input.policy.genesis_application_checkpoint_sequence,
            input.policy.genesis_application_checkpoint_hash,
        ),
        Some(record) => {
            require_prior_record_scope(input.policy, policy_root, record)?;
            (
                record.application_checkpoint_sequence(),
                record.application_checkpoint_hash(),
            )
        }
    };
    let expected_sequence = prior_sequence.checked_add(1).ok_or(
        CheckpointFinalityPolicyErrorV2::NextApplicationCheckpointSequenceOverflow {
            prior: prior_sequence,
        },
    )?;
    if input.certificate.application_checkpoint_sequence() != expected_sequence {
        return Err(
            CheckpointFinalityPolicyErrorV2::ApplicationCheckpointIsNotExactSuccessor {
                actual: input.certificate.application_checkpoint_sequence(),
                expected: expected_sequence,
                prior: prior_sequence,
            },
        );
    }
    if input.certificate.parent_application_checkpoint_hash() != prior_hash {
        return Err(
            CheckpointFinalityPolicyErrorV2::ApplicationCheckpointParentDoesNotMatchPrior {
                actual: input.certificate.parent_application_checkpoint_hash(),
                expected: prior_hash,
            },
        );
    }
    Ok(DerivedCheckpointCursorV2::from_checked(
        ProposedPriorApplicationCheckpointRecordInputV2 {
            application_id: input.policy.application_id,
            chain_or_domain_id: input.policy.chain_or_domain_id,
            finality_network_id: input.policy.finality_network_id,
            finality_protocol_id: input.policy.finality_protocol_id,
            external_finality_policy_hash: input.policy.expected_external_finality_policy_hash,
            finality_verifier_set_root: input.policy.expected_finality_verifier_set_root,
            finality_policy_root: policy_root,
            application_checkpoint_sequence: input.certificate.application_checkpoint_sequence(),
            application_checkpoint_hash: input.certificate.application_checkpoint_hash(),
        },
    ))
}

fn require_prior_record_scope(
    policy: &CheckpointFinalityPolicyV2,
    policy_root: CommitmentV3,
    record: ProposedPriorApplicationCheckpointRecordV2,
) -> Result<(), CheckpointFinalityPolicyErrorV2> {
    if record.record_version() != super::CHECKPOINT_FINALITY_CURSOR_VERSION_V2 {
        return Err(
            CheckpointFinalityPolicyErrorV2::PriorRecordVersionMismatch {
                actual: record.record_version(),
                expected: super::CHECKPOINT_FINALITY_CURSOR_VERSION_V2,
            },
        );
    }
    if record.application_id() != policy.application_id {
        return Err(CheckpointFinalityPolicyErrorV2::PriorRecordApplicationMismatch);
    }
    if record.chain_or_domain_id() != policy.chain_or_domain_id {
        return Err(CheckpointFinalityPolicyErrorV2::PriorRecordDomainMismatch);
    }
    if record.finality_network_id() != policy.finality_network_id {
        return Err(CheckpointFinalityPolicyErrorV2::PriorRecordFinalityNetworkMismatch);
    }
    if record.finality_protocol_id() != policy.finality_protocol_id {
        return Err(CheckpointFinalityPolicyErrorV2::PriorRecordFinalityProtocolMismatch);
    }
    if record.external_finality_policy_hash() != policy.expected_external_finality_policy_hash {
        return Err(CheckpointFinalityPolicyErrorV2::PriorRecordExternalFinalityPolicyMismatch);
    }
    if record.finality_verifier_set_root() != policy.expected_finality_verifier_set_root {
        return Err(CheckpointFinalityPolicyErrorV2::PriorRecordFinalityVerifierSetMismatch);
    }
    if record.finality_policy_root() != policy_root {
        return Err(CheckpointFinalityPolicyErrorV2::PriorRecordFinalityPolicyRootMismatch);
    }
    if record.application_checkpoint_sequence() < policy.genesis_application_checkpoint_sequence {
        return Err(CheckpointFinalityPolicyErrorV2::PriorRecordBeforeGenesis {
            actual: record.application_checkpoint_sequence(),
            genesis: policy.genesis_application_checkpoint_sequence,
        });
    }
    if record.application_checkpoint_sequence() == policy.genesis_application_checkpoint_sequence
        && record.application_checkpoint_hash() != policy.genesis_application_checkpoint_hash
    {
        return Err(
            CheckpointFinalityPolicyErrorV2::PriorRecordGenesisHashMismatch {
                actual: record.application_checkpoint_hash(),
                expected: policy.genesis_application_checkpoint_hash,
            },
        );
    }
    Ok(())
}

fn derive_policy_root_v2(
    policy: &CheckpointFinalityPolicyV2,
) -> Result<CommitmentV3, CheckpointFinalityPolicyErrorV2> {
    let mut hasher = domain_hasher(POLICY_ROOT_DOMAIN_V2)?;
    hasher.update(policy.policy_version.to_be_bytes());
    hasher.update(policy.application_id.as_bytes());
    hasher.update(policy.chain_or_domain_id.as_bytes());
    hasher.update(policy.finality_network_id.as_bytes());
    hasher.update(policy.finality_protocol_id.as_bytes());
    hasher.update(policy.expected_external_finality_policy_hash.as_bytes());
    hasher.update(policy.expected_finality_verifier_set_root.as_bytes());
    hasher.update(policy.genesis_application_checkpoint_sequence.to_be_bytes());
    hasher.update(policy.genesis_application_checkpoint_hash.as_bytes());
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| CheckpointFinalityPolicyErrorV2::InvalidDerivedCommitment("policy_root"))
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, CheckpointFinalityPolicyErrorV2> {
    let length = u16::try_from(domain.len())
        .map_err(|_| CheckpointFinalityPolicyErrorV2::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}
