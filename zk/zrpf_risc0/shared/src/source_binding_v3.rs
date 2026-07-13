use serde::Serialize;
use sha2::Digest;
use tau_state_proof_risc0_shared::{
    recursive_child_journal_hash_v1, recursive_child_verification_claim_hash_v1,
    recursive_child_verifier_id_v1, recursive_effect_summary_hash_v1, RecursiveEffectSummaryV1,
};
use zenodex_zrpf_protocol_v3::{CommitmentV3, ProfileIdV3, ProgramIdV3, TaskIdV3};

use crate::hashing_v1::{
    commitment, domain_hasher, hash_fixed, hash_framed, profile_id_v3,
    program_id_from_risc0_words_v3, SOURCE_BINDING_DOMAIN, SOURCE_LANE_ID_DOMAIN,
    SOURCE_MANIFEST_DOMAIN, SOURCE_PROTOCOL_ID_DOMAIN, TASK_ID_DOMAIN,
};
use crate::{AdapterErrorV1, SourcePolicyV1};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceBindingV3 {
    source_protocol_id: CommitmentV3,
    source_program_id: ProgramIdV3,
    source_profile_id: ProfileIdV3,
    source_verifier_id: CommitmentV3,
    source_manifest_root: CommitmentV3,
    source_claim_hash: CommitmentV3,
    source_journal_hash: CommitmentV3,
    source_statement_hash: CommitmentV3,
    source_effect_hash: CommitmentV3,
    source_scope_hash: CommitmentV3,
    source_lane_id_hash: CommitmentV3,
}

impl SourceBindingV3 {
    pub fn canonical_hash(&self) -> Result<CommitmentV3, AdapterErrorV1> {
        let mut hasher = domain_hasher(SOURCE_BINDING_DOMAIN)?;
        for field in [
            self.source_protocol_id.as_bytes(),
            self.source_program_id.as_bytes(),
            self.source_profile_id.as_bytes(),
            self.source_verifier_id.as_bytes(),
            self.source_manifest_root.as_bytes(),
            self.source_claim_hash.as_bytes(),
            self.source_journal_hash.as_bytes(),
            self.source_statement_hash.as_bytes(),
            self.source_effect_hash.as_bytes(),
            self.source_scope_hash.as_bytes(),
            self.source_lane_id_hash.as_bytes(),
        ] {
            hasher.update(field);
        }
        commitment(hasher.finalize().into())
    }

    pub const fn source_program_id(&self) -> ProgramIdV3 {
        self.source_program_id
    }

    pub const fn source_profile_id(&self) -> ProfileIdV3 {
        self.source_profile_id
    }

    pub const fn source_claim_hash(&self) -> CommitmentV3 {
        self.source_claim_hash
    }

    pub const fn source_journal_hash(&self) -> CommitmentV3 {
        self.source_journal_hash
    }

    pub const fn source_statement_hash(&self) -> CommitmentV3 {
        self.source_statement_hash
    }

    pub const fn source_effect_hash(&self) -> CommitmentV3 {
        self.source_effect_hash
    }
}

pub(crate) fn derive_source_binding(
    summary: &RecursiveEffectSummaryV1,
    source_journal_bytes: &[u8],
    policy: &SourcePolicyV1,
    source_scope_hash: CommitmentV3,
) -> Result<SourceBindingV3, AdapterErrorV1> {
    let source_program_id = program_id_from_risc0_words_v3(policy.image_id)?;
    let source_profile_id = profile_id_v3(policy.proof_profile)?;
    let source_verifier_id = recursive_child_verifier_id_v1(&policy.image_id, policy.proof_profile)
        .map_err(|_| AdapterErrorV1::SourceDerivationFailed)?;
    let source_claim_hash =
        recursive_child_verification_claim_hash_v1(&policy.image_id, source_journal_bytes)
            .map_err(|_| AdapterErrorV1::SourceDerivationFailed)?;
    let source_journal_hash = recursive_child_journal_hash_v1(source_journal_bytes)
        .map_err(|_| AdapterErrorV1::SourceDerivationFailed)?;
    let source_effect_hash = recursive_effect_summary_hash_v1(summary);
    let source_manifest_root = hash_fixed(
        SOURCE_MANIFEST_DOMAIN,
        &[
            source_program_id.as_bytes(),
            &policy.program_sha256,
            &policy.local_source_tree_root,
            source_profile_id.as_bytes(),
            &summary.dependency_lock_hash,
            &summary.toolchain_lock_hash,
        ],
    )?;

    Ok(SourceBindingV3 {
        source_protocol_id: commitment(hash_framed(
            SOURCE_PROTOCOL_ID_DOMAIN,
            &[policy.proof_type.as_bytes()],
        )?)?,
        source_program_id,
        source_profile_id,
        source_verifier_id: commitment(source_verifier_id)?,
        source_manifest_root: commitment(source_manifest_root)?,
        source_claim_hash: commitment(source_claim_hash)?,
        source_journal_hash: commitment(source_journal_hash)?,
        source_statement_hash: commitment(summary.statement_hash)?,
        source_effect_hash: commitment(source_effect_hash)?,
        source_scope_hash,
        source_lane_id_hash: commitment(hash_framed(
            SOURCE_LANE_ID_DOMAIN,
            &[summary.lane_id.as_bytes()],
        )?)?,
    })
}

pub(crate) fn derive_task_id(source: &SourceBindingV3) -> Result<TaskIdV3, AdapterErrorV1> {
    let bytes = hash_fixed(
        TASK_ID_DOMAIN,
        &[
            source.source_scope_hash.as_bytes(),
            source.source_claim_hash.as_bytes(),
            source.source_statement_hash.as_bytes(),
            source.source_lane_id_hash.as_bytes(),
            source.source_profile_id.as_bytes(),
        ],
    )?;
    Ok(TaskIdV3::new(bytes)?)
}
