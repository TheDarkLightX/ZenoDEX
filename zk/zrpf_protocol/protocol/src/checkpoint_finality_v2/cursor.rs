use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

use super::CHECKPOINT_FINALITY_CURSOR_VERSION_V2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProposedPriorApplicationCheckpointRecordInputV2 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub finality_network_id: CommitmentV3,
    pub finality_protocol_id: CommitmentV3,
    pub external_finality_policy_hash: CommitmentV3,
    pub finality_verifier_set_root: CommitmentV3,
    pub finality_policy_root: CommitmentV3,
    pub application_checkpoint_sequence: u64,
    pub application_checkpoint_hash: CommitmentV3,
}

/// Caller-supplied prior application-checkpoint record.
///
/// This type deliberately says proposed. Any caller can construct it. It gains
/// no durability or authentication authority from its Rust type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProposedPriorApplicationCheckpointRecordV2 {
    record_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    finality_network_id: CommitmentV3,
    finality_protocol_id: CommitmentV3,
    external_finality_policy_hash: CommitmentV3,
    finality_verifier_set_root: CommitmentV3,
    finality_policy_root: CommitmentV3,
    application_checkpoint_sequence: u64,
    application_checkpoint_hash: CommitmentV3,
}

impl ProposedPriorApplicationCheckpointRecordV2 {
    pub const fn new(input: ProposedPriorApplicationCheckpointRecordInputV2) -> Self {
        Self {
            record_version: CHECKPOINT_FINALITY_CURSOR_VERSION_V2,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            finality_network_id: input.finality_network_id,
            finality_protocol_id: input.finality_protocol_id,
            external_finality_policy_hash: input.external_finality_policy_hash,
            finality_verifier_set_root: input.finality_verifier_set_root,
            finality_policy_root: input.finality_policy_root,
            application_checkpoint_sequence: input.application_checkpoint_sequence,
            application_checkpoint_hash: input.application_checkpoint_hash,
        }
    }

    pub const fn record_version(&self) -> u16 {
        self.record_version
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

    pub const fn external_finality_policy_hash(&self) -> CommitmentV3 {
        self.external_finality_policy_hash
    }

    pub const fn finality_verifier_set_root(&self) -> CommitmentV3 {
        self.finality_verifier_set_root
    }

    pub const fn finality_policy_root(&self) -> CommitmentV3 {
        self.finality_policy_root
    }

    pub const fn application_checkpoint_sequence(&self) -> u64 {
        self.application_checkpoint_sequence
    }

    pub const fn application_checkpoint_hash(&self) -> CommitmentV3 {
        self.application_checkpoint_hash
    }
}

/// Caller-supplied checkpoint-cursor proposal.
///
/// Empty means that the checker must use the policy-governed application
/// genesis anchor. A proposed prior record is checked against the complete
/// policy scope before it participates in the successor rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointCursorProposalV2 {
    prior_record: Option<ProposedPriorApplicationCheckpointRecordV2>,
}

impl CheckpointCursorProposalV2 {
    pub const fn empty() -> Self {
        Self { prior_record: None }
    }

    pub const fn from_prior_record(record: ProposedPriorApplicationCheckpointRecordV2) -> Self {
        Self {
            prior_record: Some(record),
        }
    }

    pub const fn prior_record(&self) -> Option<ProposedPriorApplicationCheckpointRecordV2> {
        self.prior_record
    }
}

/// Next application-checkpoint cursor derived only after the complete V2 check.
///
/// Fields are private and there is no public constructor. This remains a local
/// checked value; durable and rollback-resistant authority belongs to the
/// future atomic store that persists it.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::DerivedCheckpointCursorV2;
///
/// let _forged = DerivedCheckpointCursorV2 {};
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DerivedCheckpointCursorV2 {
    record_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    finality_network_id: CommitmentV3,
    finality_protocol_id: CommitmentV3,
    external_finality_policy_hash: CommitmentV3,
    finality_verifier_set_root: CommitmentV3,
    finality_policy_root: CommitmentV3,
    application_checkpoint_sequence: u64,
    application_checkpoint_hash: CommitmentV3,
}

impl DerivedCheckpointCursorV2 {
    pub(super) const fn from_checked(
        input: ProposedPriorApplicationCheckpointRecordInputV2,
    ) -> Self {
        Self {
            record_version: CHECKPOINT_FINALITY_CURSOR_VERSION_V2,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            finality_network_id: input.finality_network_id,
            finality_protocol_id: input.finality_protocol_id,
            external_finality_policy_hash: input.external_finality_policy_hash,
            finality_verifier_set_root: input.finality_verifier_set_root,
            finality_policy_root: input.finality_policy_root,
            application_checkpoint_sequence: input.application_checkpoint_sequence,
            application_checkpoint_hash: input.application_checkpoint_hash,
        }
    }

    pub const fn record_version(&self) -> u16 {
        self.record_version
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

    pub const fn external_finality_policy_hash(&self) -> CommitmentV3 {
        self.external_finality_policy_hash
    }

    pub const fn finality_verifier_set_root(&self) -> CommitmentV3 {
        self.finality_verifier_set_root
    }

    pub const fn finality_policy_root(&self) -> CommitmentV3 {
        self.finality_policy_root
    }

    pub const fn application_checkpoint_sequence(&self) -> u64 {
        self.application_checkpoint_sequence
    }

    pub const fn application_checkpoint_hash(&self) -> CommitmentV3 {
        self.application_checkpoint_hash
    }
}
