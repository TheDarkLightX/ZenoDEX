use core::fmt;

use tau_state_proof_risc0_shared::{
    recursive_cross_shard_messages_root_v1, recursive_lane_state_vector_root_v1,
    recursive_message_ids_root_v1, recursive_receipt_ids_root_v1,
    validate_recursive_effect_summary_shape_v1, RecursiveEffectSummaryV1,
};
use zenodex_zrpf_protocol_v3::{
    ApplicationIdV3, CommitmentV3, DomainIdV3, LeafNodeInputV3, NodeCommitmentsInputV3,
    NodeCommitmentsV3, NodeJournalV3, NodeScopeInputV3, NodeScopeV3, PartitionV3, TaskIdV3,
    ZrpfErrorV3,
};

use crate::hashing_v1::{
    commitment, derive_node_statement_hash, derive_v1_adapter_compatibility_manifest_root,
    hash_fixed, hash_framed, hash_partition_entry, profile_id_v3, program_id_from_risc0_words_v3,
    singleton_root, source_transition_receipt_count_unit_id_v3, unsupported_field,
    NodeStatementInputV1, APPLICATION_ID_DOMAIN, CONFLICT_SCHEDULE_DOMAIN, DA_PAYLOAD_ROOT_DOMAIN,
    DOMAIN_ID_DOMAIN, PARTITION_PLAN_ROOT_DOMAIN, PROVENANCE_ROOT_DOMAIN,
    SEMANTIC_SOURCE_SET_ROOT_DOMAIN, TASK_SET_ROOT_DOMAIN,
};
use crate::source_binding_v3::{derive_source_binding, derive_task_id, SourceBindingV3};
use crate::{source_policy_v1, SourceKindV1, SourcePolicyV1};

pub const V1_SOURCE_JOURNAL_MAX_BYTES: usize = 4_096;
pub const V1_LEAF_ADAPTER_PROFILE: &str = "zrpf_v1_leaf_adapter_compatibility_v1";

const PRE_STATE_VECTOR_DOMAIN_V1: &[u8] = b"zenodex.risc0.recursive.pre_state_vector_root.v1";
const POST_STATE_VECTOR_DOMAIN_V1: &[u8] = b"zenodex.risc0.recursive.post_state_vector_root.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdapterErrorV1 {
    EmptyAdapterInput,
    AdapterInputTooLarge { actual: usize, maximum: usize },
    InvalidAdapterSchema(u16),
    ZeroAdapterImageId,
    EmptySourceJournal,
    SourceJournalTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    PostcardEncode,
    TrailingBytes,
    NonCanonicalEncoding,
    InvalidSourceSummary,
    SourcePolicyMismatch(&'static str),
    SourceDerivationFailed,
    AssignedLeafOrdinalOverflow,
    Protocol(ZrpfErrorV3),
}

impl fmt::Display for AdapterErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyAdapterInput => formatter.write_str("adapter input is empty"),
            Self::AdapterInputTooLarge { actual, maximum } => {
                write!(formatter, "adapter input length {actual} exceeds {maximum}")
            }
            Self::InvalidAdapterSchema(version) => {
                write!(formatter, "invalid adapter input schema: {version}")
            }
            Self::ZeroAdapterImageId => formatter.write_str("adapter image ID is zero"),
            Self::EmptySourceJournal => formatter.write_str("source journal is empty"),
            Self::SourceJournalTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "source journal length {actual} exceeds {maximum}"
                )
            }
            Self::PostcardDecode => formatter.write_str("source journal Postcard decode failed"),
            Self::PostcardEncode => formatter.write_str("source journal Postcard encode failed"),
            Self::TrailingBytes => formatter.write_str("source journal has trailing bytes"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("source journal is not canonically encoded")
            }
            Self::InvalidSourceSummary => formatter.write_str("source summary shape is invalid"),
            Self::SourcePolicyMismatch(field) => {
                write!(formatter, "source policy mismatch: {field}")
            }
            Self::SourceDerivationFailed => {
                formatter.write_str("source commitment derivation failed")
            }
            Self::AssignedLeafOrdinalOverflow => {
                formatter.write_str("assigned leaf ordinal overflows its partition")
            }
            Self::Protocol(error) => {
                write!(formatter, "ZRPF protocol rejected projection: {error}")
            }
        }
    }
}

impl From<ZrpfErrorV3> for AdapterErrorV1 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Protocol(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V1LeafProjectionV3 {
    pub source_binding: SourceBindingV3,
    pub journal: NodeJournalV3,
}

pub fn project_policy_bound_v1_journal(
    source_kind: SourceKindV1,
    source_journal_bytes: &[u8],
    assigned_leaf_ordinal: u64,
    expected_adapter_image_id: [u32; 8],
) -> Result<V1LeafProjectionV3, AdapterErrorV1> {
    let policy = source_policy_v1(source_kind);
    let summary = decode_exact_source_summary(source_journal_bytes)?;
    enforce_source_policy(&summary, policy)?;

    let partition = singleton_partition(assigned_leaf_ordinal)?;
    let scope = derive_scope(&summary)?;
    let scope_hash = scope.canonical_hash()?;
    let adapter_program_id = program_id_from_risc0_words_v3(expected_adapter_image_id)?;
    let adapter_profile_id = profile_id_v3(V1_LEAF_ADAPTER_PROFILE)?;
    let count_unit_id = source_transition_receipt_count_unit_id_v3()?;
    let source_binding = derive_source_binding(&summary, source_journal_bytes, policy, scope_hash)?;
    let source_binding_hash = source_binding.canonical_hash()?;
    let task_id = derive_task_id(&source_binding)?;
    let program_manifest_root =
        derive_v1_adapter_compatibility_manifest_root(adapter_program_id, adapter_profile_id)?;
    let commitments = derive_commitments(CommitmentInputV1 {
        summary: &summary,
        source_journal_bytes,
        source_binding: &source_binding,
        source_binding_hash,
        task_id,
        partition,
    })?;
    let node_statement_hash = derive_node_statement_hash(NodeStatementInputV1 {
        adapter_program_id,
        adapter_profile_id,
        adapter_manifest_root: program_manifest_root,
        source_binding_hash,
        scope_hash,
        task_id,
        partition,
        count_unit_id,
        commitments_hash: commitments.canonical_hash()?,
    })?;

    let journal = NodeJournalV3::new_leaf(LeafNodeInputV3 {
        task_id,
        partition,
        operation_count: 1,
        count_unit_id,
        scope,
        proof_profile_id: adapter_profile_id,
        actual_program_id: adapter_program_id,
        node_statement_hash,
        program_manifest_root,
        commitments,
    })?;

    Ok(V1LeafProjectionV3 {
        source_binding,
        journal,
    })
}

fn singleton_partition(assigned_leaf_ordinal: u64) -> Result<PartitionV3, AdapterErrorV1> {
    let end = assigned_leaf_ordinal
        .checked_add(1)
        .ok_or(AdapterErrorV1::AssignedLeafOrdinalOverflow)?;
    Ok(PartitionV3::new(assigned_leaf_ordinal, end)?)
}

fn decode_exact_source_summary(bytes: &[u8]) -> Result<RecursiveEffectSummaryV1, AdapterErrorV1> {
    if bytes.is_empty() {
        return Err(AdapterErrorV1::EmptySourceJournal);
    }
    if bytes.len() > V1_SOURCE_JOURNAL_MAX_BYTES {
        return Err(AdapterErrorV1::SourceJournalTooLarge {
            actual: bytes.len(),
            maximum: V1_SOURCE_JOURNAL_MAX_BYTES,
        });
    }
    let (summary, remainder) = postcard::take_from_bytes::<RecursiveEffectSummaryV1>(bytes)
        .map_err(|_| AdapterErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(AdapterErrorV1::TrailingBytes);
    }
    let canonical = postcard::to_allocvec(&summary).map_err(|_| AdapterErrorV1::PostcardEncode)?;
    if canonical.as_slice() != bytes {
        return Err(AdapterErrorV1::NonCanonicalEncoding);
    }
    validate_recursive_effect_summary_shape_v1(&summary)
        .map_err(|_| AdapterErrorV1::InvalidSourceSummary)?;
    Ok(summary)
}

fn enforce_source_policy(
    summary: &RecursiveEffectSummaryV1,
    policy: &SourcePolicyV1,
) -> Result<(), AdapterErrorV1> {
    if summary.risc0_image_id != policy.image_id {
        return Err(AdapterErrorV1::SourcePolicyMismatch("image_id"));
    }
    if summary.proof_profile != policy.proof_profile {
        return Err(AdapterErrorV1::SourcePolicyMismatch("proof_profile"));
    }
    if summary.lane_kind != policy.lane_kind {
        return Err(AdapterErrorV1::SourcePolicyMismatch("lane_kind"));
    }
    let empty_receipts =
        recursive_receipt_ids_root_v1(&[]).map_err(|_| AdapterErrorV1::SourceDerivationFailed)?;
    if summary.accepted_receipts_root != empty_receipts {
        return Err(AdapterErrorV1::SourcePolicyMismatch(
            "accepted_receipts_root",
        ));
    }
    if summary.rejected_receipts_root != empty_receipts {
        return Err(AdapterErrorV1::SourcePolicyMismatch(
            "rejected_receipts_root",
        ));
    }
    let empty_messages = recursive_cross_shard_messages_root_v1(&[])
        .map_err(|_| AdapterErrorV1::SourceDerivationFailed)?;
    if summary.cross_shard_outbox_root != empty_messages {
        return Err(AdapterErrorV1::SourcePolicyMismatch(
            "cross_shard_outbox_root",
        ));
    }
    if summary.cross_shard_inbox_root != empty_messages {
        return Err(AdapterErrorV1::SourcePolicyMismatch(
            "cross_shard_inbox_root",
        ));
    }
    Ok(())
}

fn derive_scope(summary: &RecursiveEffectSummaryV1) -> Result<NodeScopeV3, AdapterErrorV1> {
    Ok(NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new(hash_framed(APPLICATION_ID_DOMAIN, &[b"zenodex"])?)?,
        chain_or_domain_id: DomainIdV3::new(hash_framed(
            DOMAIN_ID_DOMAIN,
            &[summary.chain_id.as_bytes()],
        )?)?,
        epoch_start: summary.epoch_id,
        epoch_end: summary.epoch_id,
        public_policy_hash: commitment(summary.public_policy_hash)?,
        feature_suite_hash: commitment(summary.feature_suite_hash)?,
        dependency_lock_hash: commitment(summary.dependency_lock_hash)?,
        toolchain_lock_hash: commitment(summary.toolchain_lock_hash)?,
    })?)
}

struct CommitmentInputV1<'a> {
    summary: &'a RecursiveEffectSummaryV1,
    source_journal_bytes: &'a [u8],
    source_binding: &'a SourceBindingV3,
    source_binding_hash: CommitmentV3,
    task_id: TaskIdV3,
    partition: PartitionV3,
}

struct DerivedCompatibilityRootsV1 {
    pre_state_vector_root: CommitmentV3,
    post_state_vector_root: CommitmentV3,
    empty_message_ids_root: CommitmentV3,
    conflict_schedule_hash: CommitmentV3,
    data_availability_root: CommitmentV3,
    partition_entry: CommitmentV3,
}

fn derive_compatibility_roots(
    input: &CommitmentInputV1<'_>,
) -> Result<DerivedCompatibilityRootsV1, AdapterErrorV1> {
    let summary = input.summary;
    let pre_state_vector_root = commitment(
        recursive_lane_state_vector_root_v1(
            PRE_STATE_VECTOR_DOMAIN_V1,
            &[(summary.lane_id.clone(), summary.pre_state_root)],
        )
        .map_err(|_| AdapterErrorV1::SourceDerivationFailed)?,
    )?;
    let post_state_vector_root = commitment(
        recursive_lane_state_vector_root_v1(
            POST_STATE_VECTOR_DOMAIN_V1,
            &[(summary.lane_id.clone(), summary.post_state_root)],
        )
        .map_err(|_| AdapterErrorV1::SourceDerivationFailed)?,
    )?;
    let empty_message_ids_root = commitment(
        recursive_message_ids_root_v1(&[]).map_err(|_| AdapterErrorV1::SourceDerivationFailed)?,
    )?;
    let partition_entry = commitment(hash_partition_entry(input.task_id, input.partition)?)?;
    let conflict_schedule_hash = commitment(hash_fixed(
        CONFLICT_SCHEDULE_DOMAIN,
        &[
            input.task_id.as_bytes(),
            &input.partition.start().to_be_bytes(),
            &input.partition.end_exclusive().to_be_bytes(),
            &summary.write_set_root,
            &summary.statement_hash,
        ],
    )?)?;
    let source_journal_len = u32::try_from(input.source_journal_bytes.len())
        .map_err(|_| AdapterErrorV1::SourceDerivationFailed)?;
    let data_availability_root = commitment(hash_fixed(
        DA_PAYLOAD_ROOT_DOMAIN,
        &[
            input.source_binding.source_journal_hash().as_bytes(),
            &source_journal_len.to_be_bytes(),
        ],
    )?)?;
    Ok(DerivedCompatibilityRootsV1 {
        pre_state_vector_root,
        post_state_vector_root,
        empty_message_ids_root,
        conflict_schedule_hash,
        data_availability_root,
        partition_entry,
    })
}

fn derive_commitments(input: CommitmentInputV1<'_>) -> Result<NodeCommitmentsV3, AdapterErrorV1> {
    let roots = derive_compatibility_roots(&input)?;
    let summary = input.summary;

    Ok(NodeCommitmentsV3::new(NodeCommitmentsInputV3 {
        pre_state_vector_root: roots.pre_state_vector_root,
        post_state_vector_root: roots.post_state_vector_root,
        input_root: input.source_binding.source_claim_hash(),
        transaction_root: commitment(summary.tx_root)?,
        evidence_root: commitment(summary.evidence_root)?,
        provenance_root: singleton_root(PROVENANCE_ROOT_DOMAIN, input.source_binding_hash)?,
        receipt_root: commitment(summary.receipt_root)?,
        accepted_receipts_root: commitment(summary.accepted_receipts_root)?,
        rejected_receipts_root: commitment(summary.rejected_receipts_root)?,
        effect_root: input.source_binding.source_effect_hash(),
        write_set_root: commitment(summary.write_set_root)?,
        asset_delta_root: commitment(summary.asset_delta_root)?,
        cross_lane_outbox_root: commitment(summary.cross_shard_outbox_root)?,
        cross_lane_inbox_root: commitment(summary.cross_shard_inbox_root)?,
        cross_lane_message_ids_root: roots.empty_message_ids_root,
        conflict_schedule_hash: roots.conflict_schedule_hash,
        data_availability_root: roots.data_availability_root,
        data_availability_certificate_root: unsupported_field(
            b"data_availability_certificate",
            input.source_binding_hash,
        )?,
        carry_queue_pre_root: unsupported_field(b"carry_queue_pre", input.source_binding_hash)?,
        carry_queue_post_root: unsupported_field(b"carry_queue_post", input.source_binding_hash)?,
        task_set_root: singleton_root(
            TASK_SET_ROOT_DOMAIN,
            commitment(*input.task_id.as_bytes())?,
        )?,
        semantic_source_set_root: singleton_root(
            SEMANTIC_SOURCE_SET_ROOT_DOMAIN,
            input.source_binding_hash,
        )?,
        partition_plan_root: singleton_root(PARTITION_PLAN_ROOT_DOMAIN, roots.partition_entry)?,
    }))
}
