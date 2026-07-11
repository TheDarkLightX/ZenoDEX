use sha2::{Digest, Sha256};

use super::super::{
    write_bytes32, write_domain, write_u32, CommitmentV3, PartitionV3, ProfileIdV3, ProgramIdV3,
    TaskIdV3,
};
use super::SemanticEpochErrorV1;

const PROFILE_ID_DOMAIN_V3: &[u8] = b"zenodex.zrpf.profile_id.v3";
const COUNT_UNIT_ID_DOMAIN_V3: &[u8] = b"zenodex.zrpf.count_unit_id.v3";
const V1_ADAPTER_MANIFEST_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_manifest.v1";
const V1_ADAPTER_MANIFEST_CLASS: &[u8] = b"unreleased_compatibility_manifest";
const SEMANTIC_EPOCH_MANIFEST_DOMAIN: &[u8] = b"zenodex.zrpf.semantic_epoch_manifest.v1";
const SEMANTIC_EPOCH_MANIFEST_CLASS: &[u8] = b"unreleased_semantic_epoch_manifest";
const V1_ADAPTER_NODE_STATEMENT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_node_statement.v1";
const V1_ADAPTER_TASK_SET_ROOT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_task_set_root.v1";
const V1_ADAPTER_PROVENANCE_ROOT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_provenance_root.v1";
const V1_ADAPTER_SEMANTIC_SOURCE_SET_ROOT_DOMAIN: &[u8] =
    b"zenodex.zrpf.v1_adapter_semantic_source_set_root.v1";
const V1_ADAPTER_PARTITION_ENTRY_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_partition_entry.v1";
const V1_ADAPTER_PARTITION_PLAN_ROOT_DOMAIN: &[u8] =
    b"zenodex.zrpf.v1_adapter_partition_plan_root.v1";
const LEGACY_RECEIPT_IDS_ROOT_DOMAIN: &[u8] = b"zenodex.risc0.recursive.receipt_ids_root.v1";
const LEGACY_CROSS_SHARD_MESSAGES_ROOT_DOMAIN: &[u8] =
    b"zenodex.risc0.recursive.cross_shard_messages_root.v1";
const LEGACY_MESSAGE_IDS_ROOT_DOMAIN: &[u8] = b"zenodex.risc0.recursive.message_ids_root.v1";

pub(super) const LEAF_RECORD_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_leaf_record.v1";
pub(super) const LEAF_RECORDS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_leaf_records_root.v1";
pub(super) const PRE_STATE_ROOTS_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_pre_state_roots.v1";
pub(super) const POST_STATE_ROOTS_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_post_state_roots.v1";
pub(super) const TRANSACTION_ROOTS_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_transaction_roots.v1";
pub(super) const EFFECT_ROOTS_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_effect_roots.v1";
pub(super) const ASSET_DELTA_ROOTS_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_asset_delta_roots.v1";
pub(super) const SOURCE_CLAIMS_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.semantic_source_claim_ids_root.v1";
pub(super) const SEMANTIC_SOURCES_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.semantic_source_ids_root.v1";
pub(super) const TASK_IDS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_task_ids_root.v1";
pub(super) const COMMITMENTS_HASH_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_commitments_hash.v1";
pub(super) const EPOCH_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_epoch_root.v1";
pub(super) const PROPOSAL_HASH_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_epoch_proposal_hash.v1";

const V1_ADAPTER_PROFILE: &[u8] = b"zrpf_v1_leaf_adapter_compatibility_v1";
const V1_SEMANTIC_PROFILE: &[u8] = b"zrpf_semantic_v1_adapter_compatibility_v1";
const SOURCE_TRANSITION_RECEIPT_COUNT_UNIT: &[u8] = b"source_transition_receipt";

pub fn v1_adapter_profile_id_v1() -> Result<ProfileIdV3, SemanticEpochErrorV1> {
    Ok(ProfileIdV3::new(hash_framed(
        PROFILE_ID_DOMAIN_V3,
        &[V1_ADAPTER_PROFILE],
    )?)?)
}

pub fn semantic_epoch_profile_id_v1() -> Result<ProfileIdV3, SemanticEpochErrorV1> {
    Ok(ProfileIdV3::new(hash_framed(
        PROFILE_ID_DOMAIN_V3,
        &[V1_SEMANTIC_PROFILE],
    )?)?)
}

pub fn semantic_epoch_manifest_root_v1(
    semantic_program_id: ProgramIdV3,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    let profile_id = semantic_epoch_profile_id_v1()?;
    Ok(CommitmentV3::new(hash_framed(
        SEMANTIC_EPOCH_MANIFEST_DOMAIN,
        &[
            semantic_program_id.as_bytes(),
            profile_id.as_bytes(),
            SEMANTIC_EPOCH_MANIFEST_CLASS,
        ],
    )?)?)
}

pub fn v1_adapter_count_unit_id_v1() -> Result<CommitmentV3, SemanticEpochErrorV1> {
    Ok(CommitmentV3::new(hash_framed(
        COUNT_UNIT_ID_DOMAIN_V3,
        &[SOURCE_TRANSITION_RECEIPT_COUNT_UNIT],
    )?)?)
}

pub fn v1_adapter_manifest_root_v1(
    adapter_program_id: ProgramIdV3,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    let profile_id = v1_adapter_profile_id_v1()?;
    Ok(CommitmentV3::new(hash_framed(
        V1_ADAPTER_MANIFEST_DOMAIN,
        &[
            adapter_program_id.as_bytes(),
            profile_id.as_bytes(),
            V1_ADAPTER_MANIFEST_CLASS,
        ],
    )?)?)
}

pub fn v1_adapter_task_set_root_v1(
    task_id: TaskIdV3,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    let task_commitment = CommitmentV3::new(*task_id.as_bytes())?;
    singleton_root(V1_ADAPTER_TASK_SET_ROOT_DOMAIN, task_commitment)
}

pub fn v1_adapter_semantic_source_root_v1(
    semantic_source_id: CommitmentV3,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    singleton_root(
        V1_ADAPTER_SEMANTIC_SOURCE_SET_ROOT_DOMAIN,
        semantic_source_id,
    )
}

pub(super) fn v1_adapter_provenance_root_v1(
    semantic_source_id: CommitmentV3,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    singleton_root(V1_ADAPTER_PROVENANCE_ROOT_DOMAIN, semantic_source_id)
}

pub(super) fn v1_adapter_partition_plan_root_v1(
    task_id: TaskIdV3,
    partition: PartitionV3,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    let entry = CommitmentV3::new(hash_fixed(
        V1_ADAPTER_PARTITION_ENTRY_DOMAIN,
        &[
            task_id.as_bytes(),
            &partition.start().to_be_bytes(),
            &partition.end_exclusive().to_be_bytes(),
        ],
    )?)?;
    singleton_root(V1_ADAPTER_PARTITION_PLAN_ROOT_DOMAIN, entry)
}

pub(super) fn v1_adapter_empty_receipt_ids_root_v1() -> Result<CommitmentV3, SemanticEpochErrorV1> {
    legacy_empty_root(LEGACY_RECEIPT_IDS_ROOT_DOMAIN)
}

pub(super) fn v1_adapter_empty_cross_shard_messages_root_v1(
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    legacy_empty_root(LEGACY_CROSS_SHARD_MESSAGES_ROOT_DOMAIN)
}

pub(super) fn v1_adapter_empty_message_ids_root_v1() -> Result<CommitmentV3, SemanticEpochErrorV1> {
    legacy_empty_root(LEGACY_MESSAGE_IDS_ROOT_DOMAIN)
}

pub(super) struct V1AdapterNodeStatementInputV1 {
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

pub(super) fn v1_adapter_node_statement_hash_v1(
    input: V1AdapterNodeStatementInputV1,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    Ok(CommitmentV3::new(hash_fixed(
        V1_ADAPTER_NODE_STATEMENT_DOMAIN,
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
    )?)?)
}

pub(super) fn commitment_root(
    domain: &[u8],
    values: &[CommitmentV3],
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    bytes32_root(domain, values.iter().map(CommitmentV3::as_bytes))
}

pub(super) fn task_ids_root(
    domain: &[u8],
    values: &[TaskIdV3],
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    bytes32_root(domain, values.iter().map(TaskIdV3::as_bytes))
}

fn singleton_root(
    domain: &[u8],
    value: CommitmentV3,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    commitment_root(domain, &[value])
}

fn legacy_empty_root(domain: &[u8]) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(0u32.to_be_bytes());
    Ok(CommitmentV3::new(hasher.finalize().into())?)
}

fn bytes32_root<'a>(
    domain: &[u8],
    values: impl ExactSizeIterator<Item = &'a [u8; 32]>,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    let length = u32::try_from(values.len())
        .map_err(|_| SemanticEpochErrorV1::ArithmeticOverflow("commitment_list_length"))?;
    let mut hasher = Sha256::new();
    write_domain(&mut hasher, domain)?;
    write_u32(&mut hasher, length);
    for value in values {
        write_bytes32(&mut hasher, value);
    }
    Ok(CommitmentV3::new(hasher.finalize().into())?)
}

fn hash_fixed(domain: &[u8], fields: &[&[u8]]) -> Result<[u8; 32], SemanticEpochErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    for field in fields {
        hasher.update(field);
    }
    Ok(hasher.finalize().into())
}

fn hash_framed(domain: &[u8], fields: &[&[u8]]) -> Result<[u8; 32], SemanticEpochErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    for field in fields {
        let length = u32::try_from(field.len())
            .map_err(|_| SemanticEpochErrorV1::ArithmeticOverflow("hash_field_length"))?;
        hasher.update(length.to_be_bytes());
        hasher.update(field);
    }
    Ok(hasher.finalize().into())
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, SemanticEpochErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| SemanticEpochErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}
