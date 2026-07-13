#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use serde::{de::DeserializeOwned, Deserialize, Serialize};
use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{
    compose_recursive_epoch_journal_v1, recursive_asset_delta_root_v1,
    recursive_authority_set_root_v1, recursive_child_journal_hash_v1,
    recursive_child_verification_claim_hash_v1, recursive_child_verifier_id_v1,
    recursive_cross_shard_messages_root_v1, recursive_effect_summary_hash_v1,
    recursive_receipt_ids_root_v1, recursive_verifier_set_root_v1, RecursiveChildEffectV1,
    RecursiveCompositionInputV1, RecursiveCompositionStatementV1, RecursiveEffectSummaryV1,
    RecursiveEpochJournalV1, TransitionError, RECURSIVE_DOMAIN_SEPARATOR_V1,
    RECURSIVE_EPOCH_PROFILE_V1, RECURSIVE_STATEMENT_VERSION_V1,
    RECURSIVE_STRICT_CROSS_SHARD_MODE_V1, RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
};

pub const PROOF_TYPE_RECURSIVE_NODE_V2: &str = "risc0.zenodex_recursive_node.v2";
pub const RECURSIVE_NODE_DOMAIN_SEPARATOR_V2: &str = "zenodex.risc0.recursive_node.v2";
pub const RECURSIVE_NODE_SCHEMA_VERSION_V2: u32 = 2;
pub const RECURSIVE_NODE_JOURNAL_VERSION_V2: u32 = 2;
pub const RECURSIVE_CLOSED_SUBTREE_PROFILE_V2: &str = "recursive_closed_subtree_v2";
pub const RECURSIVE_EPOCH_ROOT_PROFILE_V2: &str = "recursive_epoch_root_v2";
pub const RECURSIVE_NODE_V2_MAX_INPUT_BYTES: u32 = 4 * 1_048_576;
pub const RECURSIVE_NODE_V2_MAX_IMMEDIATE_CHILDREN: u32 = 8;
pub const RECURSIVE_NODE_V2_MAX_FLAT_LEAVES: u32 = 64;
pub const RECURSIVE_NODE_V2_MAX_CHILD_JOURNAL_BYTES: u32 = 4 * 1024;
pub const RECURSIVE_NODE_V2_MAX_TOTAL_CHILD_JOURNAL_BYTES: u32 = 32 * 1024;
pub const RECURSIVE_NODE_V2_MAX_FLAT_DISCLOSURE_BYTES: u32 = 2 * 1_048_576;
pub const RECURSIVE_NODE_V2_MAX_ASSET_DELTA_ROWS: u32 = 1024;
pub const RECURSIVE_NODE_V2_MAX_CROSS_SHARD_MESSAGES: u32 = 1024;
pub const RECURSIVE_NODE_V2_MAX_RECEIPT_IDS: u32 = 4096;
pub const RECURSIVE_NODE_V2_MAX_TREE_HEIGHT: u32 = 2;
pub const RECURSIVE_NODE_V2_MAX_SUBTREE_NODES: u32 = 73;

const NODE_STATEMENT_HASH_DOMAIN: &[u8] = b"zenodex.risc0.recursive.node_statement.v2";
const NODE_SCOPE_HASH_DOMAIN: &[u8] = b"zenodex.risc0.recursive.aggregation_scope.v2";
const NODE_JOURNAL_HASH_DOMAIN: &[u8] = b"zenodex.risc0.recursive.node_journal_bytes.v2";
const NODE_CLAIM_HASH_DOMAIN: &[u8] = b"zenodex.risc0.recursive.node_verification_claim.v2";
const NODE_VERIFIER_ID_DOMAIN: &[u8] = b"zenodex.risc0.recursive.node_verifier_id.v2";
const LEAF_SOURCE_ID_DOMAIN: &[u8] = b"zenodex.risc0.recursive.leaf_source_id.v2";
const ASSIGNED_LEAF_ID_DOMAIN: &[u8] = b"zenodex.risc0.recursive.assigned_leaf_id.v2";
const LEAF_DISCLOSURE_HASH_DOMAIN: &[u8] = b"zenodex.risc0.recursive.leaf_disclosure.v2";
const LEAF_DISCLOSURES_ROOT_DOMAIN: &[u8] = b"zenodex.risc0.recursive.leaf_disclosures_root.v2";
const ASSIGNED_LEAF_IDS_ROOT_DOMAIN: &[u8] = b"zenodex.risc0.recursive.assigned_leaf_ids_root.v2";
const DESCENDANT_CLAIMS_ROOT_DOMAIN: &[u8] = b"zenodex.risc0.recursive.descendant_claims_root.v2";
const DESCENDANT_SOURCES_ROOT_DOMAIN: &[u8] = b"zenodex.risc0.recursive.descendant_sources_root.v2";
const IMMEDIATE_CLAIMS_ROOT_DOMAIN: &[u8] =
    b"zenodex.risc0.recursive.immediate_child_claims_root.v2";
const IMMEDIATE_JOURNALS_ROOT_DOMAIN: &[u8] =
    b"zenodex.risc0.recursive.immediate_child_journals_root.v2";
const IMMEDIATE_VERIFIER_SET_ROOT_DOMAIN: &[u8] =
    b"zenodex.risc0.recursive.immediate_verifier_set_root.v2";
const PARTITION_ENTRY_DOMAIN: &[u8] = b"zenodex.risc0.recursive.partition_entry.v2";
const PARTITION_PLAN_ROOT_DOMAIN: &[u8] = b"zenodex.risc0.recursive.partition_plan_root.v2";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RecursiveNodeLevelV2 {
    ClosedSubtreeOverLeaves,
    EpochRootOverSubtrees,
}

impl RecursiveNodeLevelV2 {
    pub const fn tree_height(self) -> u32 {
        match self {
            Self::ClosedSubtreeOverLeaves => 1,
            Self::EpochRootOverSubtrees => 2,
        }
    }

    const fn code(self) -> u32 {
        self.tree_height()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecursiveNodeProfileV2 {
    #[serde(rename = "recursive_closed_subtree_v2")]
    ClosedSubtree,
    #[serde(rename = "recursive_epoch_root_v2")]
    EpochRoot,
}

impl RecursiveNodeProfileV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ClosedSubtree => RECURSIVE_CLOSED_SUBTREE_PROFILE_V2,
            Self::EpochRoot => RECURSIVE_EPOCH_ROOT_PROFILE_V2,
        }
    }

    const fn code(self) -> u32 {
        match self {
            Self::ClosedSubtree => 1,
            Self::EpochRoot => 2,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecursiveNodeBoundsV2 {
    pub max_immediate_children: u32,
    pub max_flat_leaves: u32,
    pub max_child_journal_bytes: u32,
    pub max_total_child_journal_bytes: u32,
    pub max_flat_disclosure_bytes: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecursiveNodeStatementV2 {
    pub schema_version: u32,
    pub domain_separator: String,
    pub level: RecursiveNodeLevelV2,
    pub profile: RecursiveNodeProfileV2,
    pub self_image_id: [u32; 8],
    pub flat_statement: RecursiveCompositionStatementV1,
    pub immediate_verifier_set_root: [u8; 32],
    pub expected_immediate_child_count: u32,
    pub expected_flat_leaf_count: u32,
    pub expected_tree_height: u32,
    pub expected_subtree_node_count: u32,
    pub expected_assigned_leaf_ids_root: [u8; 32],
    pub expected_descendant_claims_root: [u8; 32],
    pub expected_descendant_sources_root: [u8; 32],
    pub expected_partition_plan_root: [u8; 32],
    pub bounds: RecursiveNodeBoundsV2,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecursiveNodeChildDescriptorV2 {
    pub child_image_id: [u32; 8],
    pub child_profile: RecursiveNodeProfileV2,
    pub child_verifier_id: [u8; 32],
    pub child_verification_claim_hash: [u8; 32],
    pub child_journal_hash: [u8; 32],
    pub child_statement_hash: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RecursiveImmediateChildV2 {
    LeafV1 {
        child: Box<RecursiveChildEffectV1>,
    },
    NodeV2 {
        descriptor: Box<RecursiveNodeChildDescriptorV2>,
        journal_bytes: Box<Vec<u8>>,
        flat_leaf_disclosures: Box<Vec<RecursiveChildEffectV1>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecursiveNodeInputV2 {
    pub statement: RecursiveNodeStatementV2,
    pub allowed_immediate_verifier_ids: Vec<[u8; 32]>,
    pub allowed_flat_leaf_verifier_ids: Vec<[u8; 32]>,
    pub allowed_authority_roots: Vec<[u8; 32]>,
    pub children: Vec<RecursiveImmediateChildV2>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecursiveNodeJournalV2 {
    pub journal_version: u32,
    pub proof_type: String,
    pub domain_separator: String,
    pub level: RecursiveNodeLevelV2,
    pub profile: RecursiveNodeProfileV2,
    pub self_image_id: [u32; 8],
    pub statement_hash: [u8; 32],
    pub aggregation_scope_hash: [u8; 32],
    pub immediate_verifier_set_root: [u8; 32],
    pub immediate_child_count: u32,
    pub flat_leaf_count: u32,
    pub tree_height: u32,
    pub subtree_node_count: u32,
    pub immediate_child_claims_root: [u8; 32],
    pub immediate_child_journals_root: [u8; 32],
    pub leaf_disclosures_root: [u8; 32],
    pub assigned_leaf_ids_root: [u8; 32],
    pub descendant_claims_root: [u8; 32],
    pub descendant_sources_root: [u8; 32],
    pub partition_plan_root: [u8; 32],
    pub flat_v1_projection: RecursiveEpochJournalV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveImmediateClaimV2 {
    pub image_id: [u32; 8],
    pub journal_bytes: Vec<u8>,
}

#[derive(Clone, Debug)]
pub enum RecursiveNodeErrorV2 {
    InvalidInput(&'static str),
    Arithmetic(&'static str),
    Encoding(&'static str),
    V1(TransitionError),
}

impl From<TransitionError> for RecursiveNodeErrorV2 {
    fn from(value: TransitionError) -> Self {
        Self::V1(value)
    }
}

#[derive(Clone)]
struct DerivedLeafSetV2 {
    sorted_disclosures: Vec<RecursiveChildEffectV1>,
    disclosure_hashes: Vec<[u8; 32]>,
    assigned_ids: Vec<[u8; 32]>,
    claim_ids: Vec<[u8; 32]>,
    source_ids: Vec<[u8; 32]>,
    partition_plan_root: [u8; 32],
    subtree_node_count: u32,
}

struct LeafIdentitySetsV2 {
    disclosure_hashes: Vec<[u8; 32]>,
    assigned_ids: Vec<[u8; 32]>,
    claim_ids: Vec<[u8; 32]>,
    source_ids: Vec<[u8; 32]>,
}

fn write_u32(hasher: &mut Sha256, value: u32) {
    hasher.update(value.to_be_bytes());
}

fn write_u64(hasher: &mut Sha256, value: u64) {
    hasher.update(value.to_be_bytes());
}

fn write_bytes32(hasher: &mut Sha256, value: &[u8; 32]) {
    hasher.update(value);
}

fn write_image_id(hasher: &mut Sha256, value: &[u32; 8]) {
    for word in value {
        write_u32(hasher, *word);
    }
}

fn write_str(hasher: &mut Sha256, value: &str) -> Result<(), RecursiveNodeErrorV2> {
    let len = u32::try_from(value.len())
        .map_err(|_| RecursiveNodeErrorV2::Arithmetic("string length exceeds u32"))?;
    write_u32(hasher, len);
    hasher.update(value.as_bytes());
    Ok(())
}

fn checked_len(value: usize, error: &'static str) -> Result<u32, RecursiveNodeErrorV2> {
    u32::try_from(value).map_err(|_| RecursiveNodeErrorV2::Arithmetic(error))
}

fn require_nonzero_root(root: &[u8; 32], error: &'static str) -> Result<(), RecursiveNodeErrorV2> {
    if *root == [0; 32] {
        return Err(RecursiveNodeErrorV2::InvalidInput(error));
    }
    Ok(())
}

fn require_nonzero_image(
    image_id: &[u32; 8],
    error: &'static str,
) -> Result<(), RecursiveNodeErrorV2> {
    if image_id.iter().all(|word| *word == 0) {
        return Err(RecursiveNodeErrorV2::InvalidInput(error));
    }
    Ok(())
}

fn root_list_hash(domain: &[u8], values: &[[u8; 32]]) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    write_u32(
        &mut hasher,
        checked_len(values.len(), "root list length exceeds u32")?,
    );
    for value in values {
        write_bytes32(&mut hasher, value);
    }
    Ok(hasher.finalize().into())
}

fn require_sorted_unique_roots(
    values: &[[u8; 32]],
    error: &'static str,
) -> Result<(), RecursiveNodeErrorV2> {
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(RecursiveNodeErrorV2::InvalidInput(error));
    }
    if values.contains(&[0; 32]) {
        return Err(RecursiveNodeErrorV2::InvalidInput(error));
    }
    Ok(())
}

pub fn recursive_immediate_verifier_set_root_v2(
    verifier_ids: &[[u8; 32]],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    require_sorted_unique_roots(verifier_ids, "immediate verifier IDs not sorted unique")?;
    root_list_hash(IMMEDIATE_VERIFIER_SET_ROOT_DOMAIN, verifier_ids)
}

pub fn recursive_node_verifier_id_v2(
    image_id: &[u32; 8],
    profile: RecursiveNodeProfileV2,
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    require_nonzero_image(image_id, "node verifier image ID zero")?;
    let mut hasher = Sha256::new();
    hasher.update(NODE_VERIFIER_ID_DOMAIN);
    write_image_id(&mut hasher, image_id);
    write_str(&mut hasher, profile.as_str())?;
    write_u32(&mut hasher, RECURSIVE_NODE_JOURNAL_VERSION_V2);
    Ok(hasher.finalize().into())
}

pub fn recursive_node_journal_bytes_hash_v2(
    journal_bytes: &[u8],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    let mut hasher = Sha256::new();
    hasher.update(NODE_JOURNAL_HASH_DOMAIN);
    write_u32(
        &mut hasher,
        checked_len(journal_bytes.len(), "node journal length exceeds u32")?,
    );
    hasher.update(journal_bytes);
    Ok(hasher.finalize().into())
}

pub fn recursive_node_verification_claim_hash_v2(
    image_id: &[u32; 8],
    journal_bytes: &[u8],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    require_nonzero_image(image_id, "node claim image ID zero")?;
    let journal_hash = recursive_node_journal_bytes_hash_v2(journal_bytes)?;
    let mut hasher = Sha256::new();
    hasher.update(NODE_CLAIM_HASH_DOMAIN);
    write_image_id(&mut hasher, image_id);
    write_bytes32(&mut hasher, &journal_hash);
    Ok(hasher.finalize().into())
}

pub fn recursive_leaf_source_id_v2(
    source_namespace: &str,
    statement_hash: &[u8; 32],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    if source_namespace.is_empty() {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "leaf source namespace empty",
        ));
    }
    require_nonzero_root(statement_hash, "leaf source statement hash zero")?;
    let mut hasher = Sha256::new();
    hasher.update(LEAF_SOURCE_ID_DOMAIN);
    write_str(&mut hasher, source_namespace)?;
    write_bytes32(&mut hasher, statement_hash);
    Ok(hasher.finalize().into())
}

pub fn recursive_assigned_leaf_id_v2(
    scope_hash: &[u8; 32],
    lane_id: &str,
    source_id: &[u8; 32],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    require_nonzero_root(scope_hash, "aggregation scope hash zero")?;
    require_nonzero_root(source_id, "leaf source ID zero")?;
    if lane_id.is_empty() {
        return Err(RecursiveNodeErrorV2::InvalidInput("leaf lane ID empty"));
    }
    let mut hasher = Sha256::new();
    hasher.update(ASSIGNED_LEAF_ID_DOMAIN);
    write_bytes32(&mut hasher, scope_hash);
    write_str(&mut hasher, lane_id)?;
    write_bytes32(&mut hasher, source_id);
    Ok(hasher.finalize().into())
}

pub fn decode_exact_postcard_v2<T>(bytes: &[u8]) -> Result<T, RecursiveNodeErrorV2>
where
    T: DeserializeOwned + Serialize,
{
    let (value, remainder) = postcard::take_from_bytes(bytes)
        .map_err(|_| RecursiveNodeErrorV2::Encoding("postcard decode failed"))?;
    if !remainder.is_empty() {
        return Err(RecursiveNodeErrorV2::Encoding("postcard trailing bytes"));
    }
    let canonical = postcard::to_allocvec(&value)
        .map_err(|_| RecursiveNodeErrorV2::Encoding("postcard re-encode failed"))?;
    if canonical != bytes {
        return Err(RecursiveNodeErrorV2::Encoding(
            "postcard encoding is not canonical",
        ));
    }
    Ok(value)
}

fn write_flat_statement(
    hasher: &mut Sha256,
    statement: &RecursiveCompositionStatementV1,
) -> Result<(), RecursiveNodeErrorV2> {
    write_str(hasher, &statement.domain_separator)?;
    write_u32(hasher, statement.schema_version);
    write_str(hasher, &statement.chain_id)?;
    write_u64(hasher, statement.epoch_id);
    write_str(hasher, &statement.proof_profile)?;
    write_bytes32(hasher, &statement.verifier_set_root);
    write_bytes32(hasher, &statement.allowed_authority_roots_root);
    write_bytes32(hasher, &statement.public_policy_hash);
    write_bytes32(hasher, &statement.feature_suite_hash);
    write_bytes32(hasher, &statement.dependency_lock_hash);
    write_bytes32(hasher, &statement.toolchain_lock_hash);
    write_bytes32(hasher, &statement.expected_pre_state_root);
    write_bytes32(hasher, &statement.expected_post_state_root);
    write_bytes32(hasher, &statement.conflict_schedule_hash);
    write_bytes32(hasher, &statement.carry_queue_pre_root);
    write_bytes32(hasher, &statement.carry_queue_post_root);
    write_bytes32(hasher, &statement.data_availability_root);
    write_u32(hasher, statement.expected_child_count);
    write_u32(hasher, statement.max_children);
    write_u32(hasher, statement.max_child_journal_bytes);
    write_u32(hasher, statement.max_total_child_journal_bytes);
    write_u32(hasher, statement.max_asset_delta_rows);
    write_u32(hasher, statement.max_cross_shard_messages);
    write_u32(hasher, statement.max_receipt_ids);
    write_str(hasher, &statement.cross_shard_mode)?;
    Ok(())
}

pub fn recursive_node_statement_hash_v2(
    statement: &RecursiveNodeStatementV2,
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    let mut hasher = Sha256::new();
    hasher.update(NODE_STATEMENT_HASH_DOMAIN);
    write_u32(&mut hasher, statement.schema_version);
    write_str(&mut hasher, &statement.domain_separator)?;
    write_u32(&mut hasher, statement.level.code());
    write_u32(&mut hasher, statement.profile.code());
    write_image_id(&mut hasher, &statement.self_image_id);
    write_flat_statement(&mut hasher, &statement.flat_statement)?;
    write_bytes32(&mut hasher, &statement.immediate_verifier_set_root);
    write_u32(&mut hasher, statement.expected_immediate_child_count);
    write_u32(&mut hasher, statement.expected_flat_leaf_count);
    write_u32(&mut hasher, statement.expected_tree_height);
    write_u32(&mut hasher, statement.expected_subtree_node_count);
    write_bytes32(&mut hasher, &statement.expected_assigned_leaf_ids_root);
    write_bytes32(&mut hasher, &statement.expected_descendant_claims_root);
    write_bytes32(&mut hasher, &statement.expected_descendant_sources_root);
    write_bytes32(&mut hasher, &statement.expected_partition_plan_root);
    write_u32(&mut hasher, statement.bounds.max_immediate_children);
    write_u32(&mut hasher, statement.bounds.max_flat_leaves);
    write_u32(&mut hasher, statement.bounds.max_child_journal_bytes);
    write_u32(&mut hasher, statement.bounds.max_total_child_journal_bytes);
    write_u32(&mut hasher, statement.bounds.max_flat_disclosure_bytes);
    Ok(hasher.finalize().into())
}

pub fn recursive_aggregation_scope_hash_v2(
    statement: &RecursiveNodeStatementV2,
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    let flat = &statement.flat_statement;
    let mut hasher = Sha256::new();
    hasher.update(NODE_SCOPE_HASH_DOMAIN);
    write_u32(&mut hasher, RECURSIVE_NODE_SCHEMA_VERSION_V2);
    write_str(&mut hasher, RECURSIVE_NODE_DOMAIN_SEPARATOR_V2)?;
    write_str(&mut hasher, &flat.domain_separator)?;
    write_u32(&mut hasher, flat.schema_version);
    write_str(&mut hasher, &flat.chain_id)?;
    write_u64(&mut hasher, flat.epoch_id);
    write_str(&mut hasher, &flat.proof_profile)?;
    write_bytes32(&mut hasher, &flat.verifier_set_root);
    write_bytes32(&mut hasher, &flat.allowed_authority_roots_root);
    write_bytes32(&mut hasher, &flat.public_policy_hash);
    write_bytes32(&mut hasher, &flat.feature_suite_hash);
    write_bytes32(&mut hasher, &flat.dependency_lock_hash);
    write_bytes32(&mut hasher, &flat.toolchain_lock_hash);
    write_bytes32(&mut hasher, &flat.conflict_schedule_hash);
    write_bytes32(&mut hasher, &flat.carry_queue_pre_root);
    write_bytes32(&mut hasher, &flat.carry_queue_post_root);
    write_bytes32(&mut hasher, &flat.data_availability_root);
    write_str(&mut hasher, &flat.cross_shard_mode)?;
    write_str(&mut hasher, "schedule_commitment_only")?;
    write_str(&mut hasher, "data_availability_commitment_only")?;
    write_str(&mut hasher, "strict_closed_carry")?;
    Ok(hasher.finalize().into())
}

pub fn recursive_leaf_disclosure_hash_v2(
    child: &RecursiveChildEffectV1,
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    let claim_hash = recursive_child_verification_claim_hash_v1(
        &child.descriptor.child_image_id,
        &child.child_journal_bytes,
    )?;
    let journal_hash = recursive_child_journal_hash_v1(&child.child_journal_bytes)?;
    let summary_hash = recursive_effect_summary_hash_v1(&child.summary);
    let asset_root = recursive_asset_delta_root_v1(&child.asset_delta_rows)?;
    let outbox_root = recursive_cross_shard_messages_root_v1(&child.outbox_messages)?;
    let inbox_root = recursive_cross_shard_messages_root_v1(&child.inbox_messages)?;
    let accepted_root = recursive_receipt_ids_root_v1(&child.accepted_receipt_ids)?;
    let rejected_root = recursive_receipt_ids_root_v1(&child.rejected_receipt_ids)?;
    let source_id = recursive_leaf_source_id_v2(
        &child.summary.lane_kind,
        &child.descriptor.child_statement_hash,
    )?;
    let mut hasher = Sha256::new();
    hasher.update(LEAF_DISCLOSURE_HASH_DOMAIN);
    write_str(&mut hasher, &child.summary.lane_id)?;
    write_bytes32(&mut hasher, &source_id);
    write_bytes32(&mut hasher, &claim_hash);
    write_bytes32(&mut hasher, &journal_hash);
    write_bytes32(&mut hasher, &summary_hash);
    write_bytes32(&mut hasher, &asset_root);
    write_bytes32(&mut hasher, &outbox_root);
    write_bytes32(&mut hasher, &inbox_root);
    write_bytes32(&mut hasher, &accepted_root);
    write_bytes32(&mut hasher, &rejected_root);
    Ok(hasher.finalize().into())
}

fn leaf_set_roots(
    disclosures: &[RecursiveChildEffectV1],
    scope_hash: &[u8; 32],
) -> Result<LeafIdentitySetsV2, RecursiveNodeErrorV2> {
    let mut disclosure_hashes = Vec::with_capacity(disclosures.len());
    let mut assigned_ids = Vec::with_capacity(disclosures.len());
    let mut claim_ids = Vec::with_capacity(disclosures.len());
    let mut source_ids = Vec::with_capacity(disclosures.len());
    for child in disclosures {
        let claim = recursive_child_verification_claim_hash_v1(
            &child.descriptor.child_image_id,
            &child.child_journal_bytes,
        )?;
        let source = recursive_leaf_source_id_v2(
            &child.summary.lane_kind,
            &child.descriptor.child_statement_hash,
        )?;
        let assigned = recursive_assigned_leaf_id_v2(scope_hash, &child.summary.lane_id, &source)?;
        disclosure_hashes.push(recursive_leaf_disclosure_hash_v2(child)?);
        assigned_ids.push(assigned);
        claim_ids.push(claim);
        source_ids.push(source);
    }
    assigned_ids.sort_unstable();
    claim_ids.sort_unstable();
    source_ids.sort_unstable();
    require_sorted_unique_roots(&assigned_ids, "assigned leaf IDs not unique")?;
    require_sorted_unique_roots(&claim_ids, "descendant claim IDs not unique")?;
    require_sorted_unique_roots(&source_ids, "descendant source IDs not unique")?;
    Ok(LeafIdentitySetsV2 {
        disclosure_hashes,
        assigned_ids,
        claim_ids,
        source_ids,
    })
}

pub fn recursive_leaf_disclosures_root_v2(
    disclosures: &[RecursiveChildEffectV1],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    let mut sorted: Vec<&RecursiveChildEffectV1> = disclosures.iter().collect();
    sorted.sort_by(|left, right| left.summary.lane_id.cmp(&right.summary.lane_id));
    if sorted
        .windows(2)
        .any(|pair| pair[0].summary.lane_id >= pair[1].summary.lane_id)
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "leaf lanes not sorted unique",
        ));
    }
    let mut hashes = Vec::with_capacity(sorted.len());
    for child in sorted {
        hashes.push(recursive_leaf_disclosure_hash_v2(child)?);
    }
    root_list_hash(LEAF_DISCLOSURES_ROOT_DOMAIN, &hashes)
}

pub fn recursive_assigned_leaf_ids_root_v2(
    ids: &[[u8; 32]],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    require_sorted_unique_roots(ids, "assigned leaf IDs not sorted unique")?;
    root_list_hash(ASSIGNED_LEAF_IDS_ROOT_DOMAIN, ids)
}

pub fn recursive_descendant_claims_root_v2(
    ids: &[[u8; 32]],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    require_sorted_unique_roots(ids, "descendant claim IDs not sorted unique")?;
    root_list_hash(DESCENDANT_CLAIMS_ROOT_DOMAIN, ids)
}

pub fn recursive_descendant_sources_root_v2(
    ids: &[[u8; 32]],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    require_sorted_unique_roots(ids, "descendant source IDs not sorted unique")?;
    root_list_hash(DESCENDANT_SOURCES_ROOT_DOMAIN, ids)
}

fn profile_matches_level(statement: &RecursiveNodeStatementV2) -> bool {
    matches!(
        (statement.level, statement.profile),
        (
            RecursiveNodeLevelV2::ClosedSubtreeOverLeaves,
            RecursiveNodeProfileV2::ClosedSubtree
        ) | (
            RecursiveNodeLevelV2::EpochRootOverSubtrees,
            RecursiveNodeProfileV2::EpochRoot
        )
    )
}

fn validate_statement(statement: &RecursiveNodeStatementV2) -> Result<(), RecursiveNodeErrorV2> {
    if statement.schema_version != RECURSIVE_NODE_SCHEMA_VERSION_V2 {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "node schema version mismatch",
        ));
    }
    if statement.domain_separator != RECURSIVE_NODE_DOMAIN_SEPARATOR_V2 {
        return Err(RecursiveNodeErrorV2::InvalidInput("node domain mismatch"));
    }
    if !profile_matches_level(statement) {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "node profile/level mismatch",
        ));
    }
    require_nonzero_image(&statement.self_image_id, "node self image ID zero")?;
    require_nonzero_root(
        &statement.immediate_verifier_set_root,
        "immediate verifier set root zero",
    )?;
    for (root, error) in [
        (
            &statement.expected_assigned_leaf_ids_root,
            "expected assigned leaf root zero",
        ),
        (
            &statement.expected_descendant_claims_root,
            "expected descendant claims root zero",
        ),
        (
            &statement.expected_descendant_sources_root,
            "expected descendant sources root zero",
        ),
        (
            &statement.expected_partition_plan_root,
            "expected partition plan root zero",
        ),
    ] {
        require_nonzero_root(root, error)?;
    }
    let bounds = &statement.bounds;
    if bounds.max_immediate_children == 0
        || bounds.max_immediate_children > RECURSIVE_NODE_V2_MAX_IMMEDIATE_CHILDREN
        || bounds.max_flat_leaves == 0
        || bounds.max_flat_leaves > RECURSIVE_NODE_V2_MAX_FLAT_LEAVES
        || bounds.max_child_journal_bytes == 0
        || bounds.max_child_journal_bytes > RECURSIVE_NODE_V2_MAX_CHILD_JOURNAL_BYTES
        || bounds.max_total_child_journal_bytes == 0
        || bounds.max_total_child_journal_bytes > RECURSIVE_NODE_V2_MAX_TOTAL_CHILD_JOURNAL_BYTES
        || bounds.max_child_journal_bytes > bounds.max_total_child_journal_bytes
        || bounds.max_flat_disclosure_bytes == 0
        || bounds.max_flat_disclosure_bytes > RECURSIVE_NODE_V2_MAX_FLAT_DISCLOSURE_BYTES
    {
        return Err(RecursiveNodeErrorV2::InvalidInput("node bounds invalid"));
    }
    if statement.expected_immediate_child_count == 0
        || statement.expected_immediate_child_count > bounds.max_immediate_children
        || statement.expected_flat_leaf_count == 0
        || statement.expected_flat_leaf_count > bounds.max_flat_leaves
        || statement.expected_tree_height != statement.level.tree_height()
        || statement.expected_tree_height > RECURSIVE_NODE_V2_MAX_TREE_HEIGHT
        || statement.expected_subtree_node_count == 0
        || statement.expected_subtree_node_count > RECURSIVE_NODE_V2_MAX_SUBTREE_NODES
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "node expected counts invalid",
        ));
    }
    let flat = &statement.flat_statement;
    if flat.domain_separator != RECURSIVE_DOMAIN_SEPARATOR_V1
        || flat.schema_version != RECURSIVE_STATEMENT_VERSION_V1
        || flat.chain_id.is_empty()
        || flat.proof_profile != RECURSIVE_EPOCH_PROFILE_V1
        || flat.cross_shard_mode != RECURSIVE_STRICT_CROSS_SHARD_MODE_V1
        || flat.expected_child_count != statement.expected_flat_leaf_count
        || flat.expected_child_count > flat.max_children
        || flat.max_children == 0
        || flat.max_children > RECURSIVE_NODE_V2_MAX_FLAT_LEAVES
        || flat.max_child_journal_bytes == 0
        || flat.max_child_journal_bytes > RECURSIVE_NODE_V2_MAX_CHILD_JOURNAL_BYTES
        || flat.max_total_child_journal_bytes == 0
        || flat.max_total_child_journal_bytes > RECURSIVE_NODE_V2_MAX_TOTAL_CHILD_JOURNAL_BYTES
        || flat.max_child_journal_bytes > flat.max_total_child_journal_bytes
        || flat.max_asset_delta_rows == 0
        || flat.max_asset_delta_rows > RECURSIVE_NODE_V2_MAX_ASSET_DELTA_ROWS
        || flat.max_cross_shard_messages == 0
        || flat.max_cross_shard_messages > RECURSIVE_NODE_V2_MAX_CROSS_SHARD_MESSAGES
        || flat.max_receipt_ids == 0
        || flat.max_receipt_ids > RECURSIVE_NODE_V2_MAX_RECEIPT_IDS
        || flat.carry_queue_pre_root != flat.carry_queue_post_root
        || [
            flat.verifier_set_root,
            flat.allowed_authority_roots_root,
            flat.public_policy_hash,
            flat.feature_suite_hash,
            flat.dependency_lock_hash,
            flat.toolchain_lock_hash,
            flat.expected_pre_state_root,
            flat.expected_post_state_root,
            flat.conflict_schedule_hash,
            flat.data_availability_root,
        ]
        .contains(&[0; 32])
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "flat v1 bounds or profile invalid",
        ));
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveNodeCommitmentsV2 {
    pub immediate_child_count: u32,
    pub flat_leaf_count: u32,
    pub tree_height: u32,
    pub subtree_node_count: u32,
    pub leaf_disclosures_root: [u8; 32],
    pub assigned_leaf_ids_root: [u8; 32],
    pub descendant_claims_root: [u8; 32],
    pub descendant_sources_root: [u8; 32],
    pub partition_plan_root: [u8; 32],
}

fn child_disclosures(child: &RecursiveImmediateChildV2) -> &[RecursiveChildEffectV1] {
    match child {
        RecursiveImmediateChildV2::LeafV1 { child } => core::slice::from_ref(child.as_ref()),
        RecursiveImmediateChildV2::NodeV2 {
            flat_leaf_disclosures,
            ..
        } => flat_leaf_disclosures,
    }
}

fn partition_entry_hash(
    kind: u32,
    disclosures: &[RecursiveChildEffectV1],
    scope_hash: &[u8; 32],
) -> Result<[u8; 32], RecursiveNodeErrorV2> {
    if disclosures.is_empty() {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "child disclosure set empty",
        ));
    }
    if disclosures
        .windows(2)
        .any(|pair| pair[0].summary.lane_id.as_str() >= pair[1].summary.lane_id.as_str())
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "child disclosures not lane-sorted unique",
        ));
    }
    let identities = leaf_set_roots(disclosures, scope_hash)?;
    let mut hasher = Sha256::new();
    hasher.update(PARTITION_ENTRY_DOMAIN);
    write_u32(&mut hasher, kind);
    write_u32(
        &mut hasher,
        checked_len(disclosures.len(), "partition leaf count exceeds u32")?,
    );
    write_str(&mut hasher, &disclosures[0].summary.lane_id)?;
    write_str(
        &mut hasher,
        &disclosures[disclosures.len() - 1].summary.lane_id,
    )?;
    write_bytes32(
        &mut hasher,
        &recursive_assigned_leaf_ids_root_v2(&identities.assigned_ids)?,
    );
    write_bytes32(
        &mut hasher,
        &recursive_descendant_claims_root_v2(&identities.claim_ids)?,
    );
    write_bytes32(
        &mut hasher,
        &recursive_descendant_sources_root_v2(&identities.source_ids)?,
    );
    Ok(hasher.finalize().into())
}

fn derive_leaf_set(input: &RecursiveNodeInputV2) -> Result<DerivedLeafSetV2, RecursiveNodeErrorV2> {
    let scope_hash = recursive_aggregation_scope_hash_v2(&input.statement)?;
    let mut disclosures = Vec::new();
    let mut partition_entries = Vec::with_capacity(input.children.len());
    let mut disclosure_bytes = 0u32;
    let mut asset_rows = 0u32;
    let mut outbox_messages = 0u32;
    let mut inbox_messages = 0u32;
    let mut accepted_receipt_ids = 0u32;
    let mut rejected_receipt_ids = 0u32;

    for child in &input.children {
        let slice = child_disclosures(child);
        let kind = match child {
            RecursiveImmediateChildV2::LeafV1 { .. } => 1,
            RecursiveImmediateChildV2::NodeV2 { .. } => 2,
        };
        partition_entries.push(partition_entry_hash(kind, slice, &scope_hash)?);
        for disclosure in slice {
            let encoded = postcard::to_allocvec(disclosure)
                .map_err(|_| RecursiveNodeErrorV2::Encoding("leaf disclosure encode failed"))?;
            disclosure_bytes = disclosure_bytes
                .checked_add(checked_len(
                    encoded.len(),
                    "leaf disclosure byte length exceeds u32",
                )?)
                .ok_or(RecursiveNodeErrorV2::Arithmetic(
                    "flat disclosure byte count overflow",
                ))?;
            asset_rows = asset_rows
                .checked_add(checked_len(
                    disclosure.asset_delta_rows.len(),
                    "asset row count exceeds u32",
                )?)
                .ok_or(RecursiveNodeErrorV2::Arithmetic("asset row count overflow"))?;
            outbox_messages = outbox_messages
                .checked_add(checked_len(
                    disclosure.outbox_messages.len(),
                    "outbox message count exceeds u32",
                )?)
                .ok_or(RecursiveNodeErrorV2::Arithmetic(
                    "outbox message count overflow",
                ))?;
            inbox_messages = inbox_messages
                .checked_add(checked_len(
                    disclosure.inbox_messages.len(),
                    "inbox message count exceeds u32",
                )?)
                .ok_or(RecursiveNodeErrorV2::Arithmetic(
                    "inbox message count overflow",
                ))?;
            accepted_receipt_ids = accepted_receipt_ids
                .checked_add(checked_len(
                    disclosure.accepted_receipt_ids.len(),
                    "accepted receipt count exceeds u32",
                )?)
                .ok_or(RecursiveNodeErrorV2::Arithmetic(
                    "accepted receipt count overflow",
                ))?;
            rejected_receipt_ids = rejected_receipt_ids
                .checked_add(checked_len(
                    disclosure.rejected_receipt_ids.len(),
                    "rejected receipt count exceeds u32",
                )?)
                .ok_or(RecursiveNodeErrorV2::Arithmetic(
                    "rejected receipt count overflow",
                ))?;
            disclosures.push(disclosure.clone());
        }
    }
    if disclosure_bytes > input.statement.bounds.max_flat_disclosure_bytes {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "flat disclosure bytes exceed max",
        ));
    }
    if asset_rows > input.statement.flat_statement.max_asset_delta_rows
        || outbox_messages > input.statement.flat_statement.max_cross_shard_messages
        || inbox_messages > input.statement.flat_statement.max_cross_shard_messages
        || accepted_receipt_ids > input.statement.flat_statement.max_receipt_ids
        || rejected_receipt_ids > input.statement.flat_statement.max_receipt_ids
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "flat disclosure rows exceed max",
        ));
    }
    disclosures.sort_by(|left, right| left.summary.lane_id.cmp(&right.summary.lane_id));
    if disclosures.is_empty()
        || disclosures
            .windows(2)
            .any(|pair| pair[0].summary.lane_id.as_str() >= pair[1].summary.lane_id.as_str())
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "flat leaf lanes not sorted unique",
        ));
    }
    let identities = leaf_set_roots(&disclosures, &scope_hash)?;
    let flat_leaf_count = checked_len(disclosures.len(), "flat leaf count exceeds u32")?;
    let immediate_count = checked_len(input.children.len(), "child count exceeds u32")?;
    let subtree_node_count = match input.statement.level {
        RecursiveNodeLevelV2::ClosedSubtreeOverLeaves => 1u32.checked_add(flat_leaf_count),
        RecursiveNodeLevelV2::EpochRootOverSubtrees => 1u32
            .checked_add(immediate_count)
            .and_then(|value| value.checked_add(flat_leaf_count)),
    }
    .ok_or(RecursiveNodeErrorV2::Arithmetic(
        "subtree node count overflow",
    ))?;
    if subtree_node_count > RECURSIVE_NODE_V2_MAX_SUBTREE_NODES {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "subtree node count exceeds hard max",
        ));
    }
    Ok(DerivedLeafSetV2 {
        sorted_disclosures: disclosures,
        disclosure_hashes: identities.disclosure_hashes,
        assigned_ids: identities.assigned_ids,
        claim_ids: identities.claim_ids,
        source_ids: identities.source_ids,
        partition_plan_root: root_list_hash(PARTITION_PLAN_ROOT_DOMAIN, &partition_entries)?,
        subtree_node_count,
    })
}

pub fn derive_recursive_node_commitments_v2(
    input: &RecursiveNodeInputV2,
) -> Result<RecursiveNodeCommitmentsV2, RecursiveNodeErrorV2> {
    let derived = derive_leaf_set(input)?;
    Ok(RecursiveNodeCommitmentsV2 {
        immediate_child_count: checked_len(input.children.len(), "child count exceeds u32")?,
        flat_leaf_count: checked_len(
            derived.sorted_disclosures.len(),
            "flat leaf count exceeds u32",
        )?,
        tree_height: input.statement.level.tree_height(),
        subtree_node_count: derived.subtree_node_count,
        leaf_disclosures_root: root_list_hash(
            LEAF_DISCLOSURES_ROOT_DOMAIN,
            &derived.disclosure_hashes,
        )?,
        assigned_leaf_ids_root: recursive_assigned_leaf_ids_root_v2(&derived.assigned_ids)?,
        descendant_claims_root: recursive_descendant_claims_root_v2(&derived.claim_ids)?,
        descendant_sources_root: recursive_descendant_sources_root_v2(&derived.source_ids)?,
        partition_plan_root: derived.partition_plan_root,
    })
}

fn require_commitment_expectations(
    statement: &RecursiveNodeStatementV2,
    commitments: &RecursiveNodeCommitmentsV2,
) -> Result<(), RecursiveNodeErrorV2> {
    if commitments.immediate_child_count != statement.expected_immediate_child_count
        || commitments.flat_leaf_count != statement.expected_flat_leaf_count
        || commitments.tree_height != statement.expected_tree_height
        || commitments.subtree_node_count != statement.expected_subtree_node_count
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "node derived count mismatch",
        ));
    }
    if commitments.assigned_leaf_ids_root != statement.expected_assigned_leaf_ids_root {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "assigned leaf IDs root mismatch",
        ));
    }
    if commitments.descendant_claims_root != statement.expected_descendant_claims_root {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "descendant claims root mismatch",
        ));
    }
    if commitments.descendant_sources_root != statement.expected_descendant_sources_root {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "descendant sources root mismatch",
        ));
    }
    if commitments.partition_plan_root != statement.expected_partition_plan_root {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "partition plan root mismatch",
        ));
    }
    Ok(())
}

fn validate_leaf_immediate_claim(
    child: &RecursiveChildEffectV1,
    allowed: &BTreeSet<[u8; 32]>,
) -> Result<RecursiveImmediateClaimV2, RecursiveNodeErrorV2> {
    if child.summary.proof_profile == RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1
        || child.descriptor.child_profile == RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "summary test leaf is not admissible",
        ));
    }
    if child.descriptor.child_image_id != child.summary.risc0_image_id
        || child.descriptor.child_profile != child.summary.proof_profile
        || child.descriptor.child_statement_hash != child.summary.statement_hash
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "leaf descriptor/summary mismatch",
        ));
    }
    let verifier_id = recursive_child_verifier_id_v1(
        &child.descriptor.child_image_id,
        &child.descriptor.child_profile,
    )?;
    if verifier_id != child.descriptor.child_verifier_id || !allowed.contains(&verifier_id) {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "leaf immediate verifier is not allowed",
        ));
    }
    let claim = recursive_child_verification_claim_hash_v1(
        &child.descriptor.child_image_id,
        &child.child_journal_bytes,
    )?;
    let journal_hash = recursive_child_journal_hash_v1(&child.child_journal_bytes)?;
    if claim != child.descriptor.child_verification_claim_hash
        || journal_hash != child.descriptor.child_journal_hash
        || recursive_effect_summary_hash_v1(&child.summary)
            != child.descriptor.child_effect_summary_hash
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "leaf claim binding mismatch",
        ));
    }
    Ok(RecursiveImmediateClaimV2 {
        image_id: child.descriptor.child_image_id,
        journal_bytes: child.child_journal_bytes.clone(),
    })
}

fn validate_node_immediate_claim(
    descriptor: &RecursiveNodeChildDescriptorV2,
    journal_bytes: &[u8],
    allowed: &BTreeSet<[u8; 32]>,
) -> Result<RecursiveImmediateClaimV2, RecursiveNodeErrorV2> {
    if descriptor.child_profile != RecursiveNodeProfileV2::ClosedSubtree {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "epoch root cannot be used as child",
        ));
    }
    let verifier_id =
        recursive_node_verifier_id_v2(&descriptor.child_image_id, descriptor.child_profile)?;
    if verifier_id != descriptor.child_verifier_id || !allowed.contains(&verifier_id) {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "node immediate verifier is not allowed",
        ));
    }
    let claim =
        recursive_node_verification_claim_hash_v2(&descriptor.child_image_id, journal_bytes)?;
    let journal_hash = recursive_node_journal_bytes_hash_v2(journal_bytes)?;
    if claim != descriptor.child_verification_claim_hash
        || journal_hash != descriptor.child_journal_hash
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "node claim binding mismatch",
        ));
    }
    require_nonzero_root(
        &descriptor.child_statement_hash,
        "node child statement hash zero",
    )?;
    Ok(RecursiveImmediateClaimV2 {
        image_id: descriptor.child_image_id,
        journal_bytes: journal_bytes.to_vec(),
    })
}

pub fn preflight_recursive_node_input_v2(
    input: &RecursiveNodeInputV2,
) -> Result<Vec<RecursiveImmediateClaimV2>, RecursiveNodeErrorV2> {
    validate_statement(&input.statement)?;
    require_sorted_unique_roots(
        &input.allowed_immediate_verifier_ids,
        "immediate verifier IDs not sorted unique",
    )?;
    require_sorted_unique_roots(
        &input.allowed_flat_leaf_verifier_ids,
        "flat leaf verifier IDs not sorted unique",
    )?;
    require_sorted_unique_roots(
        &input.allowed_authority_roots,
        "authority roots not sorted unique",
    )?;
    if recursive_immediate_verifier_set_root_v2(&input.allowed_immediate_verifier_ids)?
        != input.statement.immediate_verifier_set_root
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "immediate verifier set root mismatch",
        ));
    }
    if recursive_verifier_set_root_v1(&input.allowed_flat_leaf_verifier_ids)?
        != input.statement.flat_statement.verifier_set_root
        || recursive_authority_set_root_v1(&input.allowed_authority_roots)?
            != input.statement.flat_statement.allowed_authority_roots_root
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "flat verifier or authority set root mismatch",
        ));
    }
    let child_count = checked_len(input.children.len(), "child count exceeds u32")?;
    if child_count == 0
        || child_count > input.statement.bounds.max_immediate_children
        || child_count != input.statement.expected_immediate_child_count
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "immediate child count mismatch",
        ));
    }

    let allowed: BTreeSet<[u8; 32]> = input
        .allowed_immediate_verifier_ids
        .iter()
        .copied()
        .collect();
    let mut claims = Vec::with_capacity(input.children.len());
    let mut total_journal_bytes = 0u32;
    for child in &input.children {
        let (journal_len, claim) = match (&input.statement.level, child) {
            (
                RecursiveNodeLevelV2::ClosedSubtreeOverLeaves,
                RecursiveImmediateChildV2::LeafV1 { child },
            ) => (
                checked_len(
                    child.child_journal_bytes.len(),
                    "leaf journal length exceeds u32",
                )?,
                validate_leaf_immediate_claim(child, &allowed)?,
            ),
            (
                RecursiveNodeLevelV2::EpochRootOverSubtrees,
                RecursiveImmediateChildV2::NodeV2 {
                    descriptor,
                    journal_bytes,
                    flat_leaf_disclosures,
                },
            ) => {
                if flat_leaf_disclosures.is_empty() {
                    return Err(RecursiveNodeErrorV2::InvalidInput(
                        "node child disclosures empty",
                    ));
                }
                (
                    checked_len(journal_bytes.len(), "node journal length exceeds u32")?,
                    validate_node_immediate_claim(descriptor, journal_bytes, &allowed)?,
                )
            }
            _ => {
                return Err(RecursiveNodeErrorV2::InvalidInput(
                    "wrong child kind for node level",
                ));
            }
        };
        if journal_len == 0 || journal_len > input.statement.bounds.max_child_journal_bytes {
            return Err(RecursiveNodeErrorV2::InvalidInput(
                "child journal bytes exceed max",
            ));
        }
        total_journal_bytes = total_journal_bytes.checked_add(journal_len).ok_or(
            RecursiveNodeErrorV2::Arithmetic("total child journal bytes overflow"),
        )?;
        if total_journal_bytes > input.statement.bounds.max_total_child_journal_bytes {
            return Err(RecursiveNodeErrorV2::InvalidInput(
                "total child journal bytes exceed max",
            ));
        }
        claims.push(claim);
    }
    let commitments = derive_recursive_node_commitments_v2(input)?;
    require_commitment_expectations(&input.statement, &commitments)?;
    Ok(claims)
}

fn validate_authenticated_node_child(
    descriptor: &RecursiveNodeChildDescriptorV2,
    journal_bytes: &[u8],
    disclosures: &[RecursiveChildEffectV1],
    expected_scope_hash: &[u8; 32],
) -> Result<(), RecursiveNodeErrorV2> {
    let journal: RecursiveNodeJournalV2 = decode_exact_postcard_v2(journal_bytes)?;
    if journal.journal_version != RECURSIVE_NODE_JOURNAL_VERSION_V2
        || journal.proof_type != PROOF_TYPE_RECURSIVE_NODE_V2
        || journal.domain_separator != RECURSIVE_NODE_DOMAIN_SEPARATOR_V2
        || journal.level != RecursiveNodeLevelV2::ClosedSubtreeOverLeaves
        || journal.profile != RecursiveNodeProfileV2::ClosedSubtree
        || journal.self_image_id != descriptor.child_image_id
        || journal.statement_hash != descriptor.child_statement_hash
        || journal.aggregation_scope_hash != *expected_scope_hash
        || journal.tree_height != 1
        || journal.flat_leaf_count
            != checked_len(disclosures.len(), "node disclosure count exceeds u32")?
        || journal.subtree_node_count
            != 1u32
                .checked_add(journal.flat_leaf_count)
                .ok_or(RecursiveNodeErrorV2::Arithmetic(
                    "child node count overflow",
                ))?
        || journal.leaf_disclosures_root != recursive_leaf_disclosures_root_v2(disclosures)?
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "authenticated child node journal mismatch",
        ));
    }
    let identities = leaf_set_roots(disclosures, expected_scope_hash)?;
    if journal.assigned_leaf_ids_root
        != recursive_assigned_leaf_ids_root_v2(&identities.assigned_ids)?
        || journal.descendant_claims_root
            != recursive_descendant_claims_root_v2(&identities.claim_ids)?
        || journal.descendant_sources_root
            != recursive_descendant_sources_root_v2(&identities.source_ids)?
        || journal.flat_v1_projection.child_count != journal.flat_leaf_count
    {
        return Err(RecursiveNodeErrorV2::InvalidInput(
            "authenticated child node disclosure commitments mismatch",
        ));
    }
    Ok(())
}

pub fn compose_recursive_node_journal_v2(
    input: &RecursiveNodeInputV2,
) -> Result<RecursiveNodeJournalV2, RecursiveNodeErrorV2> {
    preflight_recursive_node_input_v2(input)?;
    let scope_hash = recursive_aggregation_scope_hash_v2(&input.statement)?;
    for child in &input.children {
        match child {
            RecursiveImmediateChildV2::LeafV1 { child } => {
                let decoded: RecursiveEffectSummaryV1 =
                    decode_exact_postcard_v2(&child.child_journal_bytes)?;
                if decoded != child.summary {
                    return Err(RecursiveNodeErrorV2::InvalidInput(
                        "authenticated leaf journal mismatch",
                    ));
                }
            }
            RecursiveImmediateChildV2::NodeV2 {
                descriptor,
                journal_bytes,
                flat_leaf_disclosures,
            } => validate_authenticated_node_child(
                descriptor,
                journal_bytes,
                flat_leaf_disclosures,
                &scope_hash,
            )?,
        }
    }
    let derived = derive_leaf_set(input)?;
    let commitments = derive_recursive_node_commitments_v2(input)?;
    let flat_v1_projection = compose_recursive_epoch_journal_v1(&RecursiveCompositionInputV1 {
        statement: input.statement.flat_statement.clone(),
        allowed_verifier_ids: input.allowed_flat_leaf_verifier_ids.clone(),
        allowed_authority_roots: input.allowed_authority_roots.clone(),
        children: derived.sorted_disclosures,
    })?;
    let mut immediate_claims = Vec::with_capacity(input.children.len());
    let mut immediate_journals = Vec::with_capacity(input.children.len());
    for child in &input.children {
        match child {
            RecursiveImmediateChildV2::LeafV1 { child } => {
                immediate_claims.push(child.descriptor.child_verification_claim_hash);
                immediate_journals.push(child.descriptor.child_journal_hash);
            }
            RecursiveImmediateChildV2::NodeV2 { descriptor, .. } => {
                immediate_claims.push(descriptor.child_verification_claim_hash);
                immediate_journals.push(descriptor.child_journal_hash);
            }
        }
    }
    Ok(RecursiveNodeJournalV2 {
        journal_version: RECURSIVE_NODE_JOURNAL_VERSION_V2,
        proof_type: PROOF_TYPE_RECURSIVE_NODE_V2.to_string(),
        domain_separator: RECURSIVE_NODE_DOMAIN_SEPARATOR_V2.to_string(),
        level: input.statement.level,
        profile: input.statement.profile,
        self_image_id: input.statement.self_image_id,
        statement_hash: recursive_node_statement_hash_v2(&input.statement)?,
        aggregation_scope_hash: scope_hash,
        immediate_verifier_set_root: input.statement.immediate_verifier_set_root,
        immediate_child_count: commitments.immediate_child_count,
        flat_leaf_count: commitments.flat_leaf_count,
        tree_height: commitments.tree_height,
        subtree_node_count: commitments.subtree_node_count,
        immediate_child_claims_root: root_list_hash(
            IMMEDIATE_CLAIMS_ROOT_DOMAIN,
            &immediate_claims,
        )?,
        immediate_child_journals_root: root_list_hash(
            IMMEDIATE_JOURNALS_ROOT_DOMAIN,
            &immediate_journals,
        )?,
        leaf_disclosures_root: commitments.leaf_disclosures_root,
        assigned_leaf_ids_root: commitments.assigned_leaf_ids_root,
        descendant_claims_root: commitments.descendant_claims_root,
        descendant_sources_root: commitments.descendant_sources_root,
        partition_plan_root: commitments.partition_plan_root,
        flat_v1_projection,
    })
}
