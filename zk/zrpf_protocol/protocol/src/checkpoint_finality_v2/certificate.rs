use serde::{de, Deserialize, Deserializer, Serialize};

use super::hash::derive_checkpoint_finality_certificate_root_v2;
use super::{CheckpointFinalityCertificateErrorV2, CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V2};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointFinalityCertificateInputV2 {
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
    pub finality_policy_root: CommitmentV3,
}

/// Canonical proof-neutral projection of one ZRPF application checkpoint.
///
/// Application sequence, hash, and parent fields describe the ZRPF application
/// checkpoint chain. External block or consensus anchors belong inside the
/// finality-evidence commitment. Construction proves field and root consistency
/// only; it does not verify external consensus, signatures, fork choice, or
/// freshness.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CheckpointFinalityCertificateV2 {
    certificate_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    proof_journal_hash: CommitmentV3,
    post_state_root: CommitmentV3,
    application_checkpoint_sequence: u64,
    application_checkpoint_hash: CommitmentV3,
    parent_application_checkpoint_hash: CommitmentV3,
    finality_network_id: CommitmentV3,
    finality_protocol_id: CommitmentV3,
    external_finality_policy_hash: CommitmentV3,
    finality_verifier_set_root: CommitmentV3,
    finality_evidence_root: CommitmentV3,
    finality_policy_root: CommitmentV3,
    certificate_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CheckpointFinalityCertificateWireV2 {
    certificate_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    proof_journal_hash: CommitmentV3,
    post_state_root: CommitmentV3,
    application_checkpoint_sequence: u64,
    application_checkpoint_hash: CommitmentV3,
    parent_application_checkpoint_hash: CommitmentV3,
    finality_network_id: CommitmentV3,
    finality_protocol_id: CommitmentV3,
    external_finality_policy_hash: CommitmentV3,
    finality_verifier_set_root: CommitmentV3,
    finality_evidence_root: CommitmentV3,
    finality_policy_root: CommitmentV3,
    certificate_root: CommitmentV3,
}

impl CheckpointFinalityCertificateV2 {
    pub fn derive(
        input: CheckpointFinalityCertificateInputV2,
    ) -> Result<Self, CheckpointFinalityCertificateErrorV2> {
        let certificate_root = derive_checkpoint_finality_certificate_root_v2(&input)?;
        let certificate = Self {
            certificate_version: CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V2,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            epoch_id: input.epoch_id,
            proof_journal_hash: input.proof_journal_hash,
            post_state_root: input.post_state_root,
            application_checkpoint_sequence: input.application_checkpoint_sequence,
            application_checkpoint_hash: input.application_checkpoint_hash,
            parent_application_checkpoint_hash: input.parent_application_checkpoint_hash,
            finality_network_id: input.finality_network_id,
            finality_protocol_id: input.finality_protocol_id,
            external_finality_policy_hash: input.external_finality_policy_hash,
            finality_verifier_set_root: input.finality_verifier_set_root,
            finality_evidence_root: input.finality_evidence_root,
            finality_policy_root: input.finality_policy_root,
            certificate_root,
        };
        certificate.validate_self_consistency()?;
        Ok(certificate)
    }

    pub fn validate_self_consistency(&self) -> Result<(), CheckpointFinalityCertificateErrorV2> {
        if self.certificate_version != CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V2 {
            return Err(CheckpointFinalityCertificateErrorV2::InvalidVersion(
                self.certificate_version,
            ));
        }
        if self.certificate_root
            != derive_checkpoint_finality_certificate_root_v2(&self.as_input())?
        {
            return Err(CheckpointFinalityCertificateErrorV2::CertificateRootMismatch);
        }
        Ok(())
    }

    pub const fn certificate_version(&self) -> u16 {
        self.certificate_version
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn epoch_id(&self) -> u64 {
        self.epoch_id
    }

    pub const fn proof_journal_hash(&self) -> CommitmentV3 {
        self.proof_journal_hash
    }

    pub const fn post_state_root(&self) -> CommitmentV3 {
        self.post_state_root
    }

    pub const fn application_checkpoint_sequence(&self) -> u64 {
        self.application_checkpoint_sequence
    }

    pub const fn application_checkpoint_hash(&self) -> CommitmentV3 {
        self.application_checkpoint_hash
    }

    pub const fn parent_application_checkpoint_hash(&self) -> CommitmentV3 {
        self.parent_application_checkpoint_hash
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

    pub const fn finality_evidence_root(&self) -> CommitmentV3 {
        self.finality_evidence_root
    }

    pub const fn finality_policy_root(&self) -> CommitmentV3 {
        self.finality_policy_root
    }

    pub const fn certificate_root(&self) -> CommitmentV3 {
        self.certificate_root
    }

    const fn as_input(&self) -> CheckpointFinalityCertificateInputV2 {
        CheckpointFinalityCertificateInputV2 {
            application_id: self.application_id,
            chain_or_domain_id: self.chain_or_domain_id,
            epoch_id: self.epoch_id,
            proof_journal_hash: self.proof_journal_hash,
            post_state_root: self.post_state_root,
            application_checkpoint_sequence: self.application_checkpoint_sequence,
            application_checkpoint_hash: self.application_checkpoint_hash,
            parent_application_checkpoint_hash: self.parent_application_checkpoint_hash,
            finality_network_id: self.finality_network_id,
            finality_protocol_id: self.finality_protocol_id,
            external_finality_policy_hash: self.external_finality_policy_hash,
            finality_verifier_set_root: self.finality_verifier_set_root,
            finality_evidence_root: self.finality_evidence_root,
            finality_policy_root: self.finality_policy_root,
        }
    }

    fn from_wire(
        wire: CheckpointFinalityCertificateWireV2,
    ) -> Result<Self, CheckpointFinalityCertificateErrorV2> {
        let certificate = Self {
            certificate_version: wire.certificate_version,
            application_id: wire.application_id,
            chain_or_domain_id: wire.chain_or_domain_id,
            epoch_id: wire.epoch_id,
            proof_journal_hash: wire.proof_journal_hash,
            post_state_root: wire.post_state_root,
            application_checkpoint_sequence: wire.application_checkpoint_sequence,
            application_checkpoint_hash: wire.application_checkpoint_hash,
            parent_application_checkpoint_hash: wire.parent_application_checkpoint_hash,
            finality_network_id: wire.finality_network_id,
            finality_protocol_id: wire.finality_protocol_id,
            external_finality_policy_hash: wire.external_finality_policy_hash,
            finality_verifier_set_root: wire.finality_verifier_set_root,
            finality_evidence_root: wire.finality_evidence_root,
            finality_policy_root: wire.finality_policy_root,
            certificate_root: wire.certificate_root,
        };
        certificate.validate_self_consistency()?;
        Ok(certificate)
    }
}

impl<'de> Deserialize<'de> for CheckpointFinalityCertificateV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(CheckpointFinalityCertificateWireV2::deserialize(
            deserializer,
        )?)
        .map_err(de::Error::custom)
    }
}
