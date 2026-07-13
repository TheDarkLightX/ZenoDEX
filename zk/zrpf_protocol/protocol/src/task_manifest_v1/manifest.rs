use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::Digest;

use super::base::{
    PrivacyClaimV1, ProofSystemIdV1, ProofSystemVersionIdV1, ReceiptCodecIdV1, TaskManifestErrorV1,
    PROGRAM_MANIFEST_VERSION_V1,
};
use super::hash::{
    commitment, domain_hasher, privacy_claim_tag, write_optional_commitment, write_optional_u64,
};
use crate::{CommitmentV3, ProgramIdV3};

const PROGRAM_MANIFEST_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.program_manifest_root.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramManifestInputV1 {
    pub proof_system_id: ProofSystemIdV1,
    pub proof_system_version_id: ProofSystemVersionIdV1,
    pub program_id: ProgramIdV3,
    pub source_tree_hash: CommitmentV3,
    pub compiler_hash: CommitmentV3,
    pub outer_cargo_hash: Option<CommitmentV3>,
    pub nested_cargo_hash: Option<CommitmentV3>,
    pub linker_hash: CommitmentV3,
    pub dependency_lock_hash: CommitmentV3,
    pub build_config_hash: CommitmentV3,
    pub verifier_binary_hash: CommitmentV3,
    pub verifier_policy_root: CommitmentV3,
    pub receipt_codec_id: ReceiptCodecIdV1,
    pub security_level_bits: u16,
    pub privacy_claim: PrivacyClaimV1,
    pub revocation_epoch: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProgramManifestV1 {
    manifest_version: u16,
    manifest_root: CommitmentV3,
    proof_system_id: ProofSystemIdV1,
    proof_system_version_id: ProofSystemVersionIdV1,
    program_id: ProgramIdV3,
    source_tree_hash: CommitmentV3,
    compiler_hash: CommitmentV3,
    outer_cargo_hash: Option<CommitmentV3>,
    nested_cargo_hash: Option<CommitmentV3>,
    linker_hash: CommitmentV3,
    dependency_lock_hash: CommitmentV3,
    build_config_hash: CommitmentV3,
    verifier_binary_hash: CommitmentV3,
    verifier_policy_root: CommitmentV3,
    receipt_codec_id: ReceiptCodecIdV1,
    security_level_bits: u16,
    privacy_claim: PrivacyClaimV1,
    revocation_epoch: Option<u64>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProgramManifestWireV1 {
    manifest_version: u16,
    manifest_root: CommitmentV3,
    proof_system_id: ProofSystemIdV1,
    proof_system_version_id: ProofSystemVersionIdV1,
    program_id: ProgramIdV3,
    source_tree_hash: CommitmentV3,
    compiler_hash: CommitmentV3,
    outer_cargo_hash: Option<CommitmentV3>,
    nested_cargo_hash: Option<CommitmentV3>,
    linker_hash: CommitmentV3,
    dependency_lock_hash: CommitmentV3,
    build_config_hash: CommitmentV3,
    verifier_binary_hash: CommitmentV3,
    verifier_policy_root: CommitmentV3,
    receipt_codec_id: ReceiptCodecIdV1,
    security_level_bits: u16,
    privacy_claim: PrivacyClaimV1,
    revocation_epoch: Option<u64>,
}

impl ProgramManifestV1 {
    pub fn derive(input: ProgramManifestInputV1) -> Result<Self, TaskManifestErrorV1> {
        validate_manifest_input(&input)?;
        let manifest_root = derive_program_manifest_root(&input)?;
        let value = Self {
            manifest_version: PROGRAM_MANIFEST_VERSION_V1,
            manifest_root,
            proof_system_id: input.proof_system_id,
            proof_system_version_id: input.proof_system_version_id,
            program_id: input.program_id,
            source_tree_hash: input.source_tree_hash,
            compiler_hash: input.compiler_hash,
            outer_cargo_hash: input.outer_cargo_hash,
            nested_cargo_hash: input.nested_cargo_hash,
            linker_hash: input.linker_hash,
            dependency_lock_hash: input.dependency_lock_hash,
            build_config_hash: input.build_config_hash,
            verifier_binary_hash: input.verifier_binary_hash,
            verifier_policy_root: input.verifier_policy_root,
            receipt_codec_id: input.receipt_codec_id,
            security_level_bits: input.security_level_bits,
            privacy_claim: input.privacy_claim,
            revocation_epoch: input.revocation_epoch,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> Result<(), TaskManifestErrorV1> {
        if self.manifest_version != PROGRAM_MANIFEST_VERSION_V1 {
            return Err(TaskManifestErrorV1::InvalidVersion {
                field: "program_manifest",
                actual: self.manifest_version,
            });
        }
        let input = self.input();
        validate_manifest_input(&input)?;
        if self.manifest_root != derive_program_manifest_root(&input)? {
            return Err(TaskManifestErrorV1::InvalidDerivedIdentity("manifest_root"));
        }
        Ok(())
    }

    fn input(&self) -> ProgramManifestInputV1 {
        ProgramManifestInputV1 {
            proof_system_id: self.proof_system_id,
            proof_system_version_id: self.proof_system_version_id,
            program_id: self.program_id,
            source_tree_hash: self.source_tree_hash,
            compiler_hash: self.compiler_hash,
            outer_cargo_hash: self.outer_cargo_hash,
            nested_cargo_hash: self.nested_cargo_hash,
            linker_hash: self.linker_hash,
            dependency_lock_hash: self.dependency_lock_hash,
            build_config_hash: self.build_config_hash,
            verifier_binary_hash: self.verifier_binary_hash,
            verifier_policy_root: self.verifier_policy_root,
            receipt_codec_id: self.receipt_codec_id,
            security_level_bits: self.security_level_bits,
            privacy_claim: self.privacy_claim,
            revocation_epoch: self.revocation_epoch,
        }
    }

    pub const fn manifest_root(&self) -> CommitmentV3 {
        self.manifest_root
    }

    pub const fn proof_system_id(&self) -> ProofSystemIdV1 {
        self.proof_system_id
    }

    pub const fn program_id(&self) -> ProgramIdV3 {
        self.program_id
    }

    pub const fn receipt_codec_id(&self) -> ReceiptCodecIdV1 {
        self.receipt_codec_id
    }

    pub const fn verifier_policy_root(&self) -> CommitmentV3 {
        self.verifier_policy_root
    }

    pub const fn privacy_claim(&self) -> PrivacyClaimV1 {
        self.privacy_claim
    }

    pub const fn security_level_bits(&self) -> u16 {
        self.security_level_bits
    }

    pub const fn revocation_epoch(&self) -> Option<u64> {
        self.revocation_epoch
    }
}

impl<'de> Deserialize<'de> for ProgramManifestV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProgramManifestWireV1::deserialize(deserializer)?;
        let value = Self {
            manifest_version: wire.manifest_version,
            manifest_root: wire.manifest_root,
            proof_system_id: wire.proof_system_id,
            proof_system_version_id: wire.proof_system_version_id,
            program_id: wire.program_id,
            source_tree_hash: wire.source_tree_hash,
            compiler_hash: wire.compiler_hash,
            outer_cargo_hash: wire.outer_cargo_hash,
            nested_cargo_hash: wire.nested_cargo_hash,
            linker_hash: wire.linker_hash,
            dependency_lock_hash: wire.dependency_lock_hash,
            build_config_hash: wire.build_config_hash,
            verifier_binary_hash: wire.verifier_binary_hash,
            verifier_policy_root: wire.verifier_policy_root,
            receipt_codec_id: wire.receipt_codec_id,
            security_level_bits: wire.security_level_bits,
            privacy_claim: wire.privacy_claim,
            revocation_epoch: wire.revocation_epoch,
        };
        value.validate().map_err(de::Error::custom)?;
        Ok(value)
    }
}

fn validate_manifest_input(input: &ProgramManifestInputV1) -> Result<(), TaskManifestErrorV1> {
    if input.security_level_bits == 0 || input.security_level_bits > 512 {
        return Err(TaskManifestErrorV1::InvalidSecurityLevel);
    }
    Ok(())
}

fn derive_program_manifest_root(
    input: &ProgramManifestInputV1,
) -> Result<CommitmentV3, TaskManifestErrorV1> {
    let mut hasher = domain_hasher(PROGRAM_MANIFEST_ROOT_DOMAIN_V1)?;
    hasher.update(PROGRAM_MANIFEST_VERSION_V1.to_be_bytes());
    hasher.update(input.proof_system_id.as_bytes());
    hasher.update(input.proof_system_version_id.as_bytes());
    hasher.update(input.program_id.as_bytes());
    for value in [input.source_tree_hash, input.compiler_hash] {
        hasher.update(value.as_bytes());
    }
    write_optional_commitment(&mut hasher, input.outer_cargo_hash);
    write_optional_commitment(&mut hasher, input.nested_cargo_hash);
    for value in [
        input.linker_hash,
        input.dependency_lock_hash,
        input.build_config_hash,
        input.verifier_binary_hash,
        input.verifier_policy_root,
    ] {
        hasher.update(value.as_bytes());
    }
    hasher.update(input.receipt_codec_id.as_bytes());
    hasher.update(input.security_level_bits.to_be_bytes());
    hasher.update([privacy_claim_tag(input.privacy_claim)]);
    write_optional_u64(&mut hasher, input.revocation_epoch);
    commitment(hasher.finalize().into())
}
