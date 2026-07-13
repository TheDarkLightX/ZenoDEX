use alloc::vec::Vec;
use core::fmt;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_node_journal_v3, AggregateNodeInputV3, CommitmentV3, NodeCommitmentsInputV3,
    NodeCommitmentsV3, NodeJournalV3, NodeLevelV3, ProfileIdV3, ProgramIdV3,
    ProjectedChildDescriptorV3, TaskIdV3, ZrpfErrorV3,
};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, derive_v1_adapter_compatibility_manifest_root,
    profile_id_v3, program_id_from_risc0_words_v3,
};

use crate::StructuralAggregateInputV1;

pub const STRUCTURAL_AGGREGATE_LEVEL_ONE_PROFILE_V1: &str =
    "zrpf_structural_aggregate_level_one_v1";
pub const STRUCTURAL_AGGREGATE_LEVEL_TWO_PROFILE_V1: &str =
    "zrpf_structural_aggregate_level_two_v1";
pub const V1_ADAPTER_CHILD_PROFILE: &str = "zrpf_v1_leaf_adapter_compatibility_v1";

const STRUCTURAL_MANIFEST_DOMAIN_V1: &[u8] = b"zenodex.zrpf.structural_aggregate_manifest.v1";
const STRUCTURAL_MANIFEST_CLASS_V1: &[u8] = b"unreleased_structural_aggregate_manifest";
const STRUCTURAL_PARENT_COMMITMENT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.structural_parent_commitment.v1";
const STRUCTURAL_TASK_DOMAIN_V1: &[u8] = b"zenodex.zrpf.structural_aggregate_task.v1";
const STRUCTURAL_STATEMENT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.structural_aggregate_statement.v1";
const LEVEL_ONE_ROLE: &[u8] = b"level_one_adapter_children";
const LEVEL_TWO_ROLE: &[u8] = b"level_two_level_one_children";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ChildManifestKindV1 {
    AdapterCompatibility,
    StructuralLevelOne,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StructuralAggregatePolicyV1 {
    expected_child_image_id: [u32; 8],
    expected_child_level: u8,
    expected_child_profile: &'static str,
    child_manifest_kind: ChildManifestKindV1,
    parent_profile: &'static str,
    parent_role: &'static [u8],
}

impl StructuralAggregatePolicyV1 {
    pub const fn level_one_adapter_children(expected_adapter_image_id: [u32; 8]) -> Self {
        Self {
            expected_child_image_id: expected_adapter_image_id,
            expected_child_level: 0,
            expected_child_profile: V1_ADAPTER_CHILD_PROFILE,
            child_manifest_kind: ChildManifestKindV1::AdapterCompatibility,
            parent_profile: STRUCTURAL_AGGREGATE_LEVEL_ONE_PROFILE_V1,
            parent_role: LEVEL_ONE_ROLE,
        }
    }

    pub const fn level_two_level_one_children(expected_level_one_image_id: [u32; 8]) -> Self {
        Self {
            expected_child_image_id: expected_level_one_image_id,
            expected_child_level: 1,
            expected_child_profile: STRUCTURAL_AGGREGATE_LEVEL_ONE_PROFILE_V1,
            child_manifest_kind: ChildManifestKindV1::StructuralLevelOne,
            parent_profile: STRUCTURAL_AGGREGATE_LEVEL_TWO_PROFILE_V1,
            parent_role: LEVEL_TWO_ROLE,
        }
    }

    pub const fn expected_child_image_id(self) -> [u32; 8] {
        self.expected_child_image_id
    }

    pub const fn expected_child_level(self) -> u8 {
        self.expected_child_level
    }

    pub const fn parent_profile(self) -> &'static str {
        self.parent_profile
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructuralAggregateErrorV1 {
    InvalidPolicy(&'static str),
    ChildJournalDecode(usize),
    ChildProgramMismatch(usize),
    ChildProfileMismatch(usize),
    ChildManifestMismatch(usize),
    ChildLevelMismatch(usize),
    Derivation(&'static str),
    Protocol(ZrpfErrorV3),
}

impl fmt::Display for StructuralAggregateErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPolicy(field) => write!(formatter, "invalid structural policy: {field}"),
            Self::ChildJournalDecode(index) => write!(formatter, "child {index} journal rejected"),
            Self::ChildProgramMismatch(index) => {
                write!(
                    formatter,
                    "child {index} program does not match compile-time policy"
                )
            }
            Self::ChildProfileMismatch(index) => {
                write!(
                    formatter,
                    "child {index} profile does not match compile-time policy"
                )
            }
            Self::ChildManifestMismatch(index) => {
                write!(
                    formatter,
                    "child {index} manifest does not match compile-time policy"
                )
            }
            Self::ChildLevelMismatch(index) => {
                write!(
                    formatter,
                    "child {index} level does not match compile-time policy"
                )
            }
            Self::Derivation(field) => write!(formatter, "structural derivation failed: {field}"),
            Self::Protocol(error) => write!(formatter, "ZRPF protocol rejected aggregate: {error}"),
        }
    }
}

impl From<ZrpfErrorV3> for StructuralAggregateErrorV1 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Protocol(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuralAggregateProjectionV1 {
    pub journal: NodeJournalV3,
    pub child_claim_bindings: Vec<CommitmentV3>,
}

struct ChildMaterialV1 {
    journal: NodeJournalV3,
    descriptor: ProjectedChildDescriptorV3,
    claim_binding: CommitmentV3,
    journal_hash: CommitmentV3,
    commitments_hash: CommitmentV3,
}

/// Deterministically recomposes the structural journal expected from exact
/// child journal bytes and a fixed policy.
///
/// This pure function conveys no receipt or proof authority. Authority-bearing
/// callers must first verify every exact child claim, then use
/// `compose_structural_aggregate_after_receipt_verification_v1`.
pub fn recompose_expected_structural_aggregate_v1(
    input: &StructuralAggregateInputV1,
    policy: StructuralAggregatePolicyV1,
) -> Result<StructuralAggregateProjectionV1, StructuralAggregateErrorV1> {
    input
        .validate()
        .map_err(|_| StructuralAggregateErrorV1::InvalidPolicy("input"))?;
    validate_policy(policy)?;
    let child_program_id = program_id_from_risc0_words_v3(policy.expected_child_image_id)
        .map_err(|_| StructuralAggregateErrorV1::Derivation("child_program_id"))?;
    let child_profile_id = profile_id_v3(policy.expected_child_profile)
        .map_err(|_| StructuralAggregateErrorV1::Derivation("child_profile_id"))?;
    let child_level = NodeLevelV3::new(policy.expected_child_level)?;
    let child_manifest = expected_child_manifest(policy, child_program_id, child_profile_id)?;
    let mut children = Vec::with_capacity(input.child_journal_bytes.len());

    for (index, journal_bytes) in input.child_journal_bytes.iter().enumerate() {
        let journal = decode_exact_node_journal_v3(journal_bytes)
            .map_err(|_| StructuralAggregateErrorV1::ChildJournalDecode(index))?;
        if journal.actual_program_id() != child_program_id {
            return Err(StructuralAggregateErrorV1::ChildProgramMismatch(index));
        }
        if journal.proof_profile_id() != child_profile_id {
            return Err(StructuralAggregateErrorV1::ChildProfileMismatch(index));
        }
        if journal.program_manifest_root() != child_manifest {
            return Err(StructuralAggregateErrorV1::ChildManifestMismatch(index));
        }
        if journal.node_level() != child_level {
            return Err(StructuralAggregateErrorV1::ChildLevelMismatch(index));
        }
        let claim_binding =
            derive_risc0_verified_claim_binding_v1(policy.expected_child_image_id, journal_bytes)?;
        let descriptor =
            ProjectedChildDescriptorV3::project_canonical_journal(claim_binding, journal_bytes)?;
        let journal_hash = journal.canonical_hash()?;
        let commitments_hash = journal.commitments().canonical_hash()?;
        children.push(ChildMaterialV1 {
            journal,
            descriptor,
            claim_binding,
            journal_hash,
            commitments_hash,
        });
    }
    children.sort_unstable_by(|left, right| {
        left.journal
            .partition()
            .start()
            .cmp(&right.journal.partition().start())
            .then_with(|| {
                left.journal
                    .partition()
                    .end_exclusive()
                    .cmp(&right.journal.partition().end_exclusive())
            })
            .then_with(|| left.journal.task_id().cmp(&right.journal.task_id()))
    });

    let first = children
        .first()
        .ok_or(StructuralAggregateErrorV1::InvalidPolicy("empty_children"))?;
    let scope = first.journal.scope().clone();
    let scope_hash = scope.canonical_hash()?;
    let count_unit_id = first.journal.count_unit_id();
    let parent_program_id = program_id_from_risc0_words_v3(input.expected_self_image_id)
        .map_err(|_| StructuralAggregateErrorV1::Derivation("parent_program_id"))?;
    let parent_profile_id = profile_id_v3(policy.parent_profile)
        .map_err(|_| StructuralAggregateErrorV1::Derivation("parent_profile_id"))?;
    let parent_manifest =
        derive_structural_manifest(parent_program_id, parent_profile_id, policy.parent_role)?;
    let commitments = derive_parent_commitments(&children)?;
    let task_id = derive_parent_task_id(
        &children,
        parent_profile_id,
        scope_hash,
        count_unit_id,
        policy,
    )?;
    let node_statement_hash = derive_parent_statement(
        &children,
        parent_program_id,
        parent_profile_id,
        parent_manifest,
        scope_hash,
        count_unit_id,
        task_id,
        commitments.canonical_hash()?,
        policy,
    )?;
    let descriptors = children
        .iter()
        .map(|child| child.descriptor.clone())
        .collect();
    let journal = NodeJournalV3::new_aggregate(AggregateNodeInputV3 {
        children: descriptors,
        task_id,
        count_unit_id,
        scope,
        proof_profile_id: parent_profile_id,
        actual_program_id: parent_program_id,
        node_statement_hash,
        program_manifest_root: parent_manifest,
        commitments,
    })?;
    Ok(StructuralAggregateProjectionV1 {
        journal,
        child_claim_bindings: children.iter().map(|child| child.claim_binding).collect(),
    })
}

/// Composes journals after the caller has verified each exact child claim under
/// `policy.expected_child_image_id()`.
///
/// The structural RISC0 guests enforce this precondition by calling
/// `env::verify` before entering this wrapper.
pub fn compose_structural_aggregate_after_receipt_verification_v1(
    input: &StructuralAggregateInputV1,
    policy: StructuralAggregatePolicyV1,
) -> Result<StructuralAggregateProjectionV1, StructuralAggregateErrorV1> {
    recompose_expected_structural_aggregate_v1(input, policy)
}

fn validate_policy(policy: StructuralAggregatePolicyV1) -> Result<(), StructuralAggregateErrorV1> {
    if policy.expected_child_image_id.iter().all(|word| *word == 0) {
        return Err(StructuralAggregateErrorV1::InvalidPolicy("child_image_id"));
    }
    if policy.expected_child_level > 1 {
        return Err(StructuralAggregateErrorV1::InvalidPolicy("child_level"));
    }
    if policy.expected_child_profile.is_empty()
        || policy.parent_profile.is_empty()
        || policy.parent_role.is_empty()
    {
        return Err(StructuralAggregateErrorV1::InvalidPolicy("profile_or_role"));
    }
    Ok(())
}

fn expected_child_manifest(
    policy: StructuralAggregatePolicyV1,
    child_program_id: ProgramIdV3,
    child_profile_id: ProfileIdV3,
) -> Result<CommitmentV3, StructuralAggregateErrorV1> {
    match policy.child_manifest_kind {
        ChildManifestKindV1::AdapterCompatibility => {
            derive_v1_adapter_compatibility_manifest_root(child_program_id, child_profile_id)
                .map_err(|_| StructuralAggregateErrorV1::Derivation("adapter_child_manifest"))
        }
        ChildManifestKindV1::StructuralLevelOne => {
            derive_structural_manifest(child_program_id, child_profile_id, LEVEL_ONE_ROLE)
        }
    }
}

fn derive_structural_manifest(
    program_id: ProgramIdV3,
    profile_id: ProfileIdV3,
    role: &[u8],
) -> Result<CommitmentV3, StructuralAggregateErrorV1> {
    commitment_hash_framed(
        STRUCTURAL_MANIFEST_DOMAIN_V1,
        &[
            program_id.as_bytes(),
            profile_id.as_bytes(),
            STRUCTURAL_MANIFEST_CLASS_V1,
            role,
        ],
    )
}

fn derive_parent_commitments(
    children: &[ChildMaterialV1],
) -> Result<NodeCommitmentsV3, StructuralAggregateErrorV1> {
    let values: Vec<NodeCommitmentsInputV3> = children
        .iter()
        .map(|child| child.journal.commitments().to_input())
        .collect();
    macro_rules! root {
        ($field:ident) => {
            structural_field_root(
                stringify!($field).as_bytes(),
                values.iter().map(|value| value.$field),
            )?
        };
    }
    Ok(NodeCommitmentsV3::new(NodeCommitmentsInputV3 {
        pre_state_vector_root: root!(pre_state_vector_root),
        post_state_vector_root: root!(post_state_vector_root),
        input_root: root!(input_root),
        transaction_root: root!(transaction_root),
        evidence_root: root!(evidence_root),
        provenance_root: root!(provenance_root),
        receipt_root: root!(receipt_root),
        accepted_receipts_root: root!(accepted_receipts_root),
        rejected_receipts_root: root!(rejected_receipts_root),
        effect_root: root!(effect_root),
        write_set_root: root!(write_set_root),
        asset_delta_root: root!(asset_delta_root),
        cross_lane_outbox_root: root!(cross_lane_outbox_root),
        cross_lane_inbox_root: root!(cross_lane_inbox_root),
        cross_lane_message_ids_root: root!(cross_lane_message_ids_root),
        conflict_schedule_hash: root!(conflict_schedule_hash),
        data_availability_root: root!(data_availability_root),
        data_availability_certificate_root: root!(data_availability_certificate_root),
        carry_queue_pre_root: root!(carry_queue_pre_root),
        carry_queue_post_root: root!(carry_queue_post_root),
        task_set_root: root!(task_set_root),
        semantic_source_set_root: root!(semantic_source_set_root),
        partition_plan_root: root!(partition_plan_root),
    }))
}

fn structural_field_root(
    field: &[u8],
    values: impl ExactSizeIterator<Item = CommitmentV3>,
) -> Result<CommitmentV3, StructuralAggregateErrorV1> {
    let field_length = u16::try_from(field.len())
        .map_err(|_| StructuralAggregateErrorV1::Derivation("field_name_length"))?;
    let count = u32::try_from(values.len())
        .map_err(|_| StructuralAggregateErrorV1::Derivation("field_value_count"))?;
    let mut hasher = domain_hasher(STRUCTURAL_PARENT_COMMITMENT_DOMAIN_V1)?;
    hasher.update(field_length.to_be_bytes());
    hasher.update(field);
    hasher.update(count.to_be_bytes());
    for value in values {
        hasher.update(value.as_bytes());
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| StructuralAggregateErrorV1::Derivation("field_root"))
}

fn derive_parent_task_id(
    children: &[ChildMaterialV1],
    parent_profile_id: ProfileIdV3,
    scope_hash: CommitmentV3,
    count_unit_id: CommitmentV3,
    policy: StructuralAggregatePolicyV1,
) -> Result<TaskIdV3, StructuralAggregateErrorV1> {
    let mut hasher = domain_hasher(STRUCTURAL_TASK_DOMAIN_V1)?;
    hasher.update(parent_profile_id.as_bytes());
    hasher.update(scope_hash.as_bytes());
    hasher.update(count_unit_id.as_bytes());
    write_framed(&mut hasher, policy.parent_role)?;
    write_u32_len(&mut hasher, children.len())?;
    for child in children {
        hasher.update(child.journal.task_id().as_bytes());
        hasher.update(child.claim_binding.as_bytes());
        hasher.update(child.journal_hash.as_bytes());
        hasher.update(child.journal.partition().start().to_be_bytes());
        hasher.update(child.journal.partition().end_exclusive().to_be_bytes());
    }
    TaskIdV3::new(hasher.finalize().into())
        .map_err(|_| StructuralAggregateErrorV1::Derivation("task_id"))
}

#[allow(clippy::too_many_arguments)]
fn derive_parent_statement(
    children: &[ChildMaterialV1],
    parent_program_id: ProgramIdV3,
    parent_profile_id: ProfileIdV3,
    parent_manifest: CommitmentV3,
    scope_hash: CommitmentV3,
    count_unit_id: CommitmentV3,
    task_id: TaskIdV3,
    commitments_hash: CommitmentV3,
    policy: StructuralAggregatePolicyV1,
) -> Result<CommitmentV3, StructuralAggregateErrorV1> {
    let mut hasher = domain_hasher(STRUCTURAL_STATEMENT_DOMAIN_V1)?;
    hasher.update(parent_program_id.as_bytes());
    hasher.update(parent_profile_id.as_bytes());
    hasher.update(parent_manifest.as_bytes());
    hasher.update(scope_hash.as_bytes());
    hasher.update(count_unit_id.as_bytes());
    hasher.update(task_id.as_bytes());
    hasher.update(commitments_hash.as_bytes());
    for word in policy.expected_child_image_id {
        hasher.update(word.to_be_bytes());
    }
    write_framed(&mut hasher, policy.expected_child_profile.as_bytes())?;
    hasher.update([policy.expected_child_level]);
    write_framed(&mut hasher, policy.parent_role)?;
    write_u32_len(&mut hasher, children.len())?;
    for child in children {
        hasher.update(child.journal.task_id().as_bytes());
        hasher.update(child.claim_binding.as_bytes());
        hasher.update(child.journal_hash.as_bytes());
        hasher.update(child.journal.node_statement_hash().as_bytes());
        hasher.update(child.commitments_hash.as_bytes());
        hasher.update(child.journal.partition().start().to_be_bytes());
        hasher.update(child.journal.partition().end_exclusive().to_be_bytes());
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| StructuralAggregateErrorV1::Derivation("node_statement"))
}

fn commitment_hash_framed(
    domain: &[u8],
    fields: &[&[u8]],
) -> Result<CommitmentV3, StructuralAggregateErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    for field in fields {
        write_framed(&mut hasher, field)?;
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| StructuralAggregateErrorV1::Derivation("commitment"))
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, StructuralAggregateErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| StructuralAggregateErrorV1::Derivation("domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn write_framed(hasher: &mut Sha256, value: &[u8]) -> Result<(), StructuralAggregateErrorV1> {
    let length = u32::try_from(value.len())
        .map_err(|_| StructuralAggregateErrorV1::Derivation("framed_length"))?;
    hasher.update(length.to_be_bytes());
    hasher.update(value);
    Ok(())
}

fn write_u32_len(hasher: &mut Sha256, length: usize) -> Result<(), StructuralAggregateErrorV1> {
    let length =
        u32::try_from(length).map_err(|_| StructuralAggregateErrorV1::Derivation("list_length"))?;
    hasher.update(length.to_be_bytes());
    Ok(())
}
