use serde::{de, Deserialize, Deserializer, Serialize};

use super::hash::derive_settlement_certificate_journal_hash_v1;
use super::{SettlementEpochCertificateErrorV1, SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3, ProfileIdV3};

/// Closed proof-neutral semantic result carried by the certificate journal.
///
/// The variant labels the committed root kind. It does not establish profile
/// compatibility or authenticate the underlying semantic result.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SettlementSemanticRootV1 {
    SemanticEpoch(CommitmentV3),
    ValueSubtree(CommitmentV3),
}

impl SettlementSemanticRootV1 {
    pub const fn root(self) -> CommitmentV3 {
        match self {
            Self::SemanticEpoch(root) | Self::ValueSubtree(root) => root,
        }
    }

    pub(super) const fn hash_tag(self) -> u8 {
        match self {
            Self::SemanticEpoch(_) => 0,
            Self::ValueSubtree(_) => 1,
        }
    }
}

/// Untrusted fixed-field input for validated V1 certificate construction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SettlementEpochCertificateInputV1 {
    pub certificate_version: u16,
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub epoch_id: u64,
    pub semantic_profile_id: ProfileIdV3,
    pub semantic_journal_hash: CommitmentV3,
    pub semantic_claim_binding: CommitmentV3,
    pub proof_tree_root: CommitmentV3,
    pub semantic_root: SettlementSemanticRootV1,
    pub economic_action_batch_commitment: CommitmentV3,
    pub economic_action_ids_root: CommitmentV3,
    pub action_authorization_bindings_root: CommitmentV3,
    pub authorization_grant_spends_root: CommitmentV3,
    pub consumed_object_ids_root: CommitmentV3,
    pub settlement_effect_plan_commitment: CommitmentV3,
    pub pre_state_root: CommitmentV3,
    pub post_state_root: CommitmentV3,
    pub cell_writes_root: CommitmentV3,
    pub asset_effects_root: CommitmentV3,
    pub messages_root: CommitmentV3,
    pub carries_root: CommitmentV3,
    pub rewards_root: CommitmentV3,
    pub public_policy_hash: CommitmentV3,
    pub data_availability_certificate_root: CommitmentV3,
    pub schedule_certificate_root: CommitmentV3,
    pub carry_continuity_certificate_root: CommitmentV3,
    pub dependency_manifest_root: CommitmentV3,
}

/// Canonical proof-neutral settlement journal with validated private state.
///
/// Construction checks version, typed nonzero scope fields, and a changing
/// state root. It supplies no receipt, program, verifier, payment, settlement,
/// or ledger authority.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::{
///     SettlementEpochCertificateInputV1, SettlementEpochCertificateV1,
/// };
/// let input: SettlementEpochCertificateInputV1 = unimplemented!();
/// let _ = SettlementEpochCertificateV1(input);
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::SettlementEpochCertificateV1;
/// let certificate: SettlementEpochCertificateV1 = unimplemented!();
/// let _ = certificate.verified_runtime_image_id();
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub struct SettlementEpochCertificateV1(SettlementEpochCertificateInputV1);

impl SettlementEpochCertificateV1 {
    pub fn new(
        input: SettlementEpochCertificateInputV1,
    ) -> Result<Self, SettlementEpochCertificateErrorV1> {
        validate_input(&input)?;
        Ok(Self(input))
    }

    pub fn validate(&self) -> Result<(), SettlementEpochCertificateErrorV1> {
        validate_input(&self.0)
    }

    /// Derives the fixed-width V1 journal digest.
    ///
    /// The digest binds bytes deterministically and supplies no authentication.
    pub fn canonical_journal_hash(
        &self,
    ) -> Result<CommitmentV3, SettlementEpochCertificateErrorV1> {
        self.validate()?;
        derive_settlement_certificate_journal_hash_v1(self)
    }

    pub fn to_input(&self) -> SettlementEpochCertificateInputV1 {
        self.0.clone()
    }

    pub const fn certificate_version(&self) -> u16 {
        self.0.certificate_version
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.0.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.0.chain_or_domain_id
    }

    pub const fn epoch_id(&self) -> u64 {
        self.0.epoch_id
    }

    pub const fn semantic_profile_id(&self) -> ProfileIdV3 {
        self.0.semantic_profile_id
    }

    pub const fn semantic_journal_hash(&self) -> CommitmentV3 {
        self.0.semantic_journal_hash
    }

    /// Returns the proposed source claim binding.
    ///
    /// This proof-neutral type does not authenticate or derive the binding.
    pub const fn semantic_claim_binding(&self) -> CommitmentV3 {
        self.0.semantic_claim_binding
    }

    pub const fn proof_tree_root(&self) -> CommitmentV3 {
        self.0.proof_tree_root
    }

    pub const fn semantic_root(&self) -> SettlementSemanticRootV1 {
        self.0.semantic_root
    }

    pub const fn economic_action_batch_commitment(&self) -> CommitmentV3 {
        self.0.economic_action_batch_commitment
    }

    pub const fn economic_action_ids_root(&self) -> CommitmentV3 {
        self.0.economic_action_ids_root
    }

    pub const fn action_authorization_bindings_root(&self) -> CommitmentV3 {
        self.0.action_authorization_bindings_root
    }

    pub const fn authorization_grant_spends_root(&self) -> CommitmentV3 {
        self.0.authorization_grant_spends_root
    }

    pub const fn consumed_object_ids_root(&self) -> CommitmentV3 {
        self.0.consumed_object_ids_root
    }

    pub const fn settlement_effect_plan_commitment(&self) -> CommitmentV3 {
        self.0.settlement_effect_plan_commitment
    }

    pub const fn pre_state_root(&self) -> CommitmentV3 {
        self.0.pre_state_root
    }

    pub const fn post_state_root(&self) -> CommitmentV3 {
        self.0.post_state_root
    }

    pub const fn cell_writes_root(&self) -> CommitmentV3 {
        self.0.cell_writes_root
    }

    pub const fn asset_effects_root(&self) -> CommitmentV3 {
        self.0.asset_effects_root
    }

    pub const fn messages_root(&self) -> CommitmentV3 {
        self.0.messages_root
    }

    pub const fn carries_root(&self) -> CommitmentV3 {
        self.0.carries_root
    }

    pub const fn rewards_root(&self) -> CommitmentV3 {
        self.0.rewards_root
    }

    pub const fn public_policy_hash(&self) -> CommitmentV3 {
        self.0.public_policy_hash
    }

    pub const fn data_availability_certificate_root(&self) -> CommitmentV3 {
        self.0.data_availability_certificate_root
    }

    pub const fn schedule_certificate_root(&self) -> CommitmentV3 {
        self.0.schedule_certificate_root
    }

    pub const fn carry_continuity_certificate_root(&self) -> CommitmentV3 {
        self.0.carry_continuity_certificate_root
    }

    pub const fn dependency_manifest_root(&self) -> CommitmentV3 {
        self.0.dependency_manifest_root
    }
}

impl<'de> Deserialize<'de> for SettlementEpochCertificateV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(SettlementEpochCertificateInputV1::deserialize(
            deserializer,
        )?)
        .map_err(de::Error::custom)
    }
}

fn validate_input(
    input: &SettlementEpochCertificateInputV1,
) -> Result<(), SettlementEpochCertificateErrorV1> {
    if input.certificate_version != SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1 {
        return Err(SettlementEpochCertificateErrorV1::InvalidVersion(
            input.certificate_version,
        ));
    }
    if input.pre_state_root == input.post_state_root {
        return Err(SettlementEpochCertificateErrorV1::UnchangedStateRoot);
    }
    Ok(())
}
