use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, PartitionV3, ProfileIdV3, ProgramIdV3, TaskIdV3};

use crate::AdapterErrorV1;

pub(crate) const APPLICATION_ID_DOMAIN: &[u8] = b"zenodex.zrpf.application_id.v3";
pub(crate) const DOMAIN_ID_DOMAIN: &[u8] = b"zenodex.zrpf.chain_or_domain_id.v3";
const PROFILE_ID_DOMAIN: &[u8] = b"zenodex.zrpf.profile_id.v3";
const COUNT_UNIT_ID_DOMAIN: &[u8] = b"zenodex.zrpf.count_unit_id.v3";
pub(crate) const SOURCE_PROTOCOL_ID_DOMAIN: &[u8] = b"zenodex.zrpf.source_protocol_id.v3";
pub(crate) const SOURCE_LANE_ID_DOMAIN: &[u8] = b"zenodex.zrpf.source_lane_id.v3";
pub(crate) const SOURCE_MANIFEST_DOMAIN: &[u8] = b"zenodex.zrpf.v1_source_manifest.v1";
pub(crate) const SOURCE_BINDING_DOMAIN: &[u8] = b"zenodex.zrpf.source_binding.v3";
const ADAPTER_MANIFEST_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_manifest.v1";
const ADAPTER_MANIFEST_CLASS: &[u8] = b"unreleased_compatibility_manifest";
pub(crate) const TASK_ID_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_task_id.v1";
const NODE_STATEMENT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_node_statement.v1";
pub(crate) const PROVENANCE_ROOT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_provenance_root.v1";
pub(crate) const TASK_SET_ROOT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_task_set_root.v1";
pub(crate) const SEMANTIC_SOURCE_SET_ROOT_DOMAIN: &[u8] =
    b"zenodex.zrpf.v1_adapter_semantic_source_set_root.v1";
const PARTITION_ENTRY_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_partition_entry.v1";
pub(crate) const PARTITION_PLAN_ROOT_DOMAIN: &[u8] =
    b"zenodex.zrpf.v1_adapter_partition_plan_root.v1";
pub(crate) const CONFLICT_SCHEDULE_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_conflict_schedule.v1";
pub(crate) const DA_PAYLOAD_ROOT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_da_payload_root.v1";
const UNSUPPORTED_FIELD_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_unsupported_field.v1";

pub(crate) struct NodeStatementInputV1 {
    pub adapter_program_id: ProgramIdV3,
    pub adapter_profile_id: ProfileIdV3,
    pub adapter_manifest_root: CommitmentV3,
    pub source_binding_hash: CommitmentV3,
    pub scope_hash: CommitmentV3,
    pub task_id: TaskIdV3,
    pub partition: PartitionV3,
    pub count_unit_id: CommitmentV3,
    pub commitments_hash: CommitmentV3,
}

pub(crate) fn derive_node_statement_hash(
    input: NodeStatementInputV1,
) -> Result<CommitmentV3, AdapterErrorV1> {
    commitment(hash_fixed(
        NODE_STATEMENT_DOMAIN,
        &[
            input.adapter_program_id.as_bytes(),
            input.adapter_profile_id.as_bytes(),
            input.adapter_manifest_root.as_bytes(),
            input.source_binding_hash.as_bytes(),
            input.scope_hash.as_bytes(),
            input.task_id.as_bytes(),
            &input.partition.start().to_be_bytes(),
            &input.partition.end_exclusive().to_be_bytes(),
            &1u64.to_be_bytes(),
            input.count_unit_id.as_bytes(),
            input.commitments_hash.as_bytes(),
        ],
    )?)
}

pub fn derive_v1_adapter_compatibility_manifest_root(
    adapter_program_id: ProgramIdV3,
    adapter_profile_id: ProfileIdV3,
) -> Result<CommitmentV3, AdapterErrorV1> {
    commitment(hash_framed(
        ADAPTER_MANIFEST_DOMAIN,
        &[
            adapter_program_id.as_bytes(),
            adapter_profile_id.as_bytes(),
            ADAPTER_MANIFEST_CLASS,
        ],
    )?)
}

pub(crate) fn hash_partition_entry(
    task_id: TaskIdV3,
    partition: PartitionV3,
) -> Result<[u8; 32], AdapterErrorV1> {
    hash_fixed(
        PARTITION_ENTRY_DOMAIN,
        &[
            task_id.as_bytes(),
            &partition.start().to_be_bytes(),
            &partition.end_exclusive().to_be_bytes(),
        ],
    )
}

pub(crate) fn unsupported_field(
    field: &[u8],
    source_binding_hash: CommitmentV3,
) -> Result<CommitmentV3, AdapterErrorV1> {
    commitment(hash_framed(
        UNSUPPORTED_FIELD_DOMAIN,
        &[field, source_binding_hash.as_bytes()],
    )?)
}

pub(crate) fn singleton_root(
    domain: &[u8],
    value: CommitmentV3,
) -> Result<CommitmentV3, AdapterErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    hasher.update(1u32.to_be_bytes());
    hasher.update(value.as_bytes());
    commitment(hasher.finalize().into())
}

pub fn profile_id_v3(profile: &str) -> Result<ProfileIdV3, AdapterErrorV1> {
    Ok(ProfileIdV3::new(hash_framed(
        PROFILE_ID_DOMAIN,
        &[profile.as_bytes()],
    )?)?)
}

pub fn program_id_from_risc0_words_v3(words: [u32; 8]) -> Result<ProgramIdV3, AdapterErrorV1> {
    Ok(ProgramIdV3::new(risc0_image_words_to_bytes(words))?)
}

pub fn risc0_image_words_to_bytes(words: [u32; 8]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (chunk, word) in bytes.chunks_exact_mut(4).zip(words) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    bytes
}

pub fn source_transition_receipt_count_unit_id_v3() -> Result<CommitmentV3, AdapterErrorV1> {
    commitment(hash_framed(
        COUNT_UNIT_ID_DOMAIN,
        &[b"source_transition_receipt"],
    )?)
}

pub(crate) fn commitment(bytes: [u8; 32]) -> Result<CommitmentV3, AdapterErrorV1> {
    Ok(CommitmentV3::new(bytes)?)
}

pub(crate) fn hash_fixed(domain: &[u8], fields: &[&[u8]]) -> Result<[u8; 32], AdapterErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    for field in fields {
        hasher.update(field);
    }
    Ok(hasher.finalize().into())
}

pub(crate) fn hash_framed(domain: &[u8], fields: &[&[u8]]) -> Result<[u8; 32], AdapterErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    for field in fields {
        let length =
            u32::try_from(field.len()).map_err(|_| AdapterErrorV1::SourceDerivationFailed)?;
        hasher.update(length.to_be_bytes());
        hasher.update(field);
    }
    Ok(hasher.finalize().into())
}

pub(crate) fn domain_hasher(domain: &[u8]) -> Result<Sha256, AdapterErrorV1> {
    let length = u16::try_from(domain.len()).map_err(|_| AdapterErrorV1::SourceDerivationFailed)?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}
