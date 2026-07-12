#![no_std]

extern crate alloc;

mod economic_action_v1;
mod semantic_epoch_v1;
mod semantic_epoch_v2;
mod settlement_effect_v2;
mod task_manifest_v1;
mod value_node_v4;

pub use economic_action_v1::*;
pub use semantic_epoch_v1::*;
pub use semantic_epoch_v2::*;
pub use settlement_effect_v2::*;
pub use task_manifest_v1::*;
pub use value_node_v4::*;

use alloc::vec::Vec;
use core::fmt;

use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest, Sha256};

pub const NODE_JOURNAL_VERSION_V3: u16 = 3;
pub const MAX_IMMEDIATE_CHILDREN_V3: usize = 8;
pub const MAX_NODE_LEVEL_V3: u8 = 2;
pub const MAX_LEAF_COUNT_V3: u64 = 64;
pub const MAX_SUBTREE_NODE_COUNT_V3: u64 = 73;
pub const MAX_OPERATIONS_PER_LEAF_V3: u64 = 128;
pub const MAX_OPERATIONS_PER_ROOT_V3: u64 = MAX_OPERATIONS_PER_LEAF_V3 * MAX_LEAF_COUNT_V3;
pub const MAX_NODE_JOURNAL_BYTES_V3: usize = 4_096;

const NODE_JOURNAL_HASH_DOMAIN_V3: &[u8] = b"zenodex.zrpf.node_journal_hash.v3";
const NODE_SCOPE_HASH_DOMAIN_V3: &[u8] = b"zenodex.zrpf.node_scope_hash.v3";
const NODE_COMMITMENTS_HASH_DOMAIN_V3: &[u8] = b"zenodex.zrpf.node_commitments_hash.v3";
const VERIFIER_ID_DOMAIN_V3: &[u8] = b"zenodex.zrpf.verifier_id.v3";
const CHILD_DESCRIPTOR_HASH_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_descriptor_hash.v3";
const CHILD_TASKS_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_tasks_root.v3";
const CHILD_CLAIMS_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_claims_root.v3";
const CHILD_JOURNALS_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_journals_root.v3";
const CHILD_PROGRAMS_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_programs_root.v3";
const CHILD_PROFILES_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_profiles_root.v3";
const CHILD_VERIFIERS_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_verifiers_root.v3";
const IMMEDIATE_VERIFIER_SET_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.immediate_verifier_set_root.v3";
const CHILD_STATEMENTS_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_statements_root.v3";
const CHILD_MANIFESTS_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_manifests_root.v3";
const CHILD_EFFECTS_ROOT_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_effects_root.v3";
const CHILD_PROVENANCE_ROOTS_DOMAIN_V3: &[u8] = b"zenodex.zrpf.child_provenance_roots.v3";
const CHILD_DATA_AVAILABILITY_ROOTS_DOMAIN_V3: &[u8] =
    b"zenodex.zrpf.child_data_availability_roots.v3";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZrpfErrorV3 {
    InvalidJournalVersion(u16),
    InvalidEpochRange,
    ZeroCommitment(&'static str),
    InvalidPartition,
    PartitionLeafCountMismatch,
    ZeroOperationCount,
    OperationLimitExceeded { actual: u64, maximum: u64 },
    InvalidLeafLevel,
    InvalidAggregateLevel,
    InvalidLeafCounts,
    InvalidAggregateCounts,
    InvalidEmptyChildRoots,
    InvalidAggregateChildRoots,
    EmptyChildren,
    TooManyChildren { actual: usize, maximum: usize },
    DuplicateChildClaim,
    DuplicateChildJournal,
    DuplicateChildTask,
    ScopeMismatch,
    CountUnitMismatch,
    VerifierIdMismatch,
    OverlappingPartitions,
    NonContiguousPartitions,
    MixedChildLevels,
    MaximumTreeLevelExceeded,
    ArithmeticOverflow(&'static str),
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for ZrpfErrorV3 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidJournalVersion(version) => {
                write!(formatter, "invalid journal version: {version}")
            }
            Self::InvalidEpochRange => formatter.write_str("invalid epoch range"),
            Self::ZeroCommitment(field) => write!(formatter, "zero commitment: {field}"),
            Self::InvalidPartition => formatter.write_str("invalid half-open partition"),
            Self::PartitionLeafCountMismatch => {
                formatter.write_str("partition width does not match leaf count")
            }
            Self::ZeroOperationCount => formatter.write_str("operation count must be nonzero"),
            Self::OperationLimitExceeded { actual, maximum } => {
                write!(formatter, "operation count {actual} exceeds {maximum}")
            }
            Self::InvalidLeafLevel => formatter.write_str("leaf must have level zero"),
            Self::InvalidAggregateLevel => {
                formatter.write_str("aggregate must have a nonzero bounded level")
            }
            Self::InvalidLeafCounts => formatter.write_str("invalid leaf node counts"),
            Self::InvalidAggregateCounts => formatter.write_str("invalid aggregate node counts"),
            Self::InvalidEmptyChildRoots => {
                formatter.write_str("leaf child roots do not match canonical empty roots")
            }
            Self::InvalidAggregateChildRoots => {
                formatter.write_str("aggregate uses a canonical empty child root")
            }
            Self::EmptyChildren => formatter.write_str("aggregate child set is empty"),
            Self::TooManyChildren { actual, maximum } => {
                write!(formatter, "too many children: {actual} exceeds {maximum}")
            }
            Self::DuplicateChildClaim => formatter.write_str("duplicate child claim"),
            Self::DuplicateChildJournal => formatter.write_str("duplicate child journal"),
            Self::DuplicateChildTask => formatter.write_str("duplicate child task"),
            Self::ScopeMismatch => formatter.write_str("child execution scope differs from parent"),
            Self::CountUnitMismatch => {
                formatter.write_str("child operation count unit differs from parent")
            }
            Self::VerifierIdMismatch => {
                formatter.write_str("verifier ID is not derived from program and profile")
            }
            Self::OverlappingPartitions => formatter.write_str("child partitions overlap"),
            Self::NonContiguousPartitions => {
                formatter.write_str("child partitions are not contiguous")
            }
            Self::MixedChildLevels => formatter.write_str("child levels differ"),
            Self::MaximumTreeLevelExceeded => formatter.write_str("maximum tree level exceeded"),
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "input length {actual} exceeds {maximum}")
            }
            Self::PostcardDecode => formatter.write_str("postcard decode failed"),
            Self::TrailingBytes => formatter.write_str("postcard input has trailing bytes"),
            Self::NonCanonicalEncoding => formatter.write_str("postcard input is not canonical"),
        }
    }
}

macro_rules! nonzero_bytes32_type {
    ($name:ident, $label:literal) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name([u8; 32]);

        impl $name {
            pub fn new(bytes: [u8; 32]) -> Result<Self, ZrpfErrorV3> {
                if bytes == [0; 32] {
                    return Err(ZrpfErrorV3::ZeroCommitment($label));
                }
                Ok(Self(bytes))
            }

            pub const fn as_bytes(&self) -> &[u8; 32] {
                &self.0
            }

            pub const fn into_bytes(self) -> [u8; 32] {
                self.0
            }
        }

        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                self.0.serialize(serializer)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let bytes = <[u8; 32]>::deserialize(deserializer)?;
                Self::new(bytes).map_err(de::Error::custom)
            }
        }
    };
}

nonzero_bytes32_type!(CommitmentV3, "commitment");
nonzero_bytes32_type!(ApplicationIdV3, "application_id");
nonzero_bytes32_type!(DomainIdV3, "chain_or_domain_id");
nonzero_bytes32_type!(TaskIdV3, "task_id");
nonzero_bytes32_type!(ProgramIdV3, "program_id");
nonzero_bytes32_type!(ProfileIdV3, "profile_id");
nonzero_bytes32_type!(VerifierIdV3, "verifier_id");

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NodeScopeV3 {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_start: u64,
    epoch_end: u64,
    public_policy_hash: CommitmentV3,
    feature_suite_hash: CommitmentV3,
    dependency_lock_hash: CommitmentV3,
    toolchain_lock_hash: CommitmentV3,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodeScopeInputV3 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub epoch_start: u64,
    pub epoch_end: u64,
    pub public_policy_hash: CommitmentV3,
    pub feature_suite_hash: CommitmentV3,
    pub dependency_lock_hash: CommitmentV3,
    pub toolchain_lock_hash: CommitmentV3,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
struct NodeScopeWireV3 {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_start: u64,
    epoch_end: u64,
    public_policy_hash: CommitmentV3,
    feature_suite_hash: CommitmentV3,
    dependency_lock_hash: CommitmentV3,
    toolchain_lock_hash: CommitmentV3,
}

impl NodeScopeV3 {
    pub fn new(input: NodeScopeInputV3) -> Result<Self, ZrpfErrorV3> {
        if input.epoch_start > input.epoch_end {
            return Err(ZrpfErrorV3::InvalidEpochRange);
        }
        Ok(Self {
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            epoch_start: input.epoch_start,
            epoch_end: input.epoch_end,
            public_policy_hash: input.public_policy_hash,
            feature_suite_hash: input.feature_suite_hash,
            dependency_lock_hash: input.dependency_lock_hash,
            toolchain_lock_hash: input.toolchain_lock_hash,
        })
    }

    pub fn validate(&self) -> Result<(), ZrpfErrorV3> {
        if self.epoch_start > self.epoch_end {
            return Err(ZrpfErrorV3::InvalidEpochRange);
        }
        Ok(())
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, ZrpfErrorV3> {
        self.validate()?;
        let mut hasher = Sha256::new();
        write_domain(&mut hasher, NODE_SCOPE_HASH_DOMAIN_V3)?;
        self.update_hasher(&mut hasher);
        CommitmentV3::new(hasher.finalize().into())
    }

    pub const fn epoch_start(&self) -> u64 {
        self.epoch_start
    }

    pub const fn epoch_end(&self) -> u64 {
        self.epoch_end
    }

    pub const fn public_policy_hash(&self) -> CommitmentV3 {
        self.public_policy_hash
    }

    fn update_hasher(&self, hasher: &mut Sha256) {
        write_bytes32(hasher, self.application_id.as_bytes());
        write_bytes32(hasher, self.chain_or_domain_id.as_bytes());
        write_u64(hasher, self.epoch_start);
        write_u64(hasher, self.epoch_end);
        write_bytes32(hasher, self.public_policy_hash.as_bytes());
        write_bytes32(hasher, self.feature_suite_hash.as_bytes());
        write_bytes32(hasher, self.dependency_lock_hash.as_bytes());
        write_bytes32(hasher, self.toolchain_lock_hash.as_bytes());
    }
}

impl<'de> Deserialize<'de> for NodeScopeV3 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = NodeScopeWireV3::deserialize(deserializer)?;
        Self::new(NodeScopeInputV3 {
            application_id: wire.application_id,
            chain_or_domain_id: wire.chain_or_domain_id,
            epoch_start: wire.epoch_start,
            epoch_end: wire.epoch_end,
            public_policy_hash: wire.public_policy_hash,
            feature_suite_hash: wire.feature_suite_hash,
            dependency_lock_hash: wire.dependency_lock_hash,
            toolchain_lock_hash: wire.toolchain_lock_hash,
        })
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NodeCommitmentsV3 {
    pre_state_vector_root: CommitmentV3,
    post_state_vector_root: CommitmentV3,
    input_root: CommitmentV3,
    transaction_root: CommitmentV3,
    evidence_root: CommitmentV3,
    provenance_root: CommitmentV3,
    receipt_root: CommitmentV3,
    accepted_receipts_root: CommitmentV3,
    rejected_receipts_root: CommitmentV3,
    effect_root: CommitmentV3,
    write_set_root: CommitmentV3,
    asset_delta_root: CommitmentV3,
    cross_lane_outbox_root: CommitmentV3,
    cross_lane_inbox_root: CommitmentV3,
    cross_lane_message_ids_root: CommitmentV3,
    conflict_schedule_hash: CommitmentV3,
    data_availability_root: CommitmentV3,
    data_availability_certificate_root: CommitmentV3,
    carry_queue_pre_root: CommitmentV3,
    carry_queue_post_root: CommitmentV3,
    task_set_root: CommitmentV3,
    semantic_source_set_root: CommitmentV3,
    partition_plan_root: CommitmentV3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NodeCommitmentsInputV3 {
    pub pre_state_vector_root: CommitmentV3,
    pub post_state_vector_root: CommitmentV3,
    pub input_root: CommitmentV3,
    pub transaction_root: CommitmentV3,
    pub evidence_root: CommitmentV3,
    pub provenance_root: CommitmentV3,
    pub receipt_root: CommitmentV3,
    pub accepted_receipts_root: CommitmentV3,
    pub rejected_receipts_root: CommitmentV3,
    pub effect_root: CommitmentV3,
    pub write_set_root: CommitmentV3,
    pub asset_delta_root: CommitmentV3,
    pub cross_lane_outbox_root: CommitmentV3,
    pub cross_lane_inbox_root: CommitmentV3,
    pub cross_lane_message_ids_root: CommitmentV3,
    pub conflict_schedule_hash: CommitmentV3,
    pub data_availability_root: CommitmentV3,
    pub data_availability_certificate_root: CommitmentV3,
    pub carry_queue_pre_root: CommitmentV3,
    pub carry_queue_post_root: CommitmentV3,
    pub task_set_root: CommitmentV3,
    pub semantic_source_set_root: CommitmentV3,
    pub partition_plan_root: CommitmentV3,
}

impl NodeCommitmentsV3 {
    pub const fn new(input: NodeCommitmentsInputV3) -> Self {
        Self {
            pre_state_vector_root: input.pre_state_vector_root,
            post_state_vector_root: input.post_state_vector_root,
            input_root: input.input_root,
            transaction_root: input.transaction_root,
            evidence_root: input.evidence_root,
            provenance_root: input.provenance_root,
            receipt_root: input.receipt_root,
            accepted_receipts_root: input.accepted_receipts_root,
            rejected_receipts_root: input.rejected_receipts_root,
            effect_root: input.effect_root,
            write_set_root: input.write_set_root,
            asset_delta_root: input.asset_delta_root,
            cross_lane_outbox_root: input.cross_lane_outbox_root,
            cross_lane_inbox_root: input.cross_lane_inbox_root,
            cross_lane_message_ids_root: input.cross_lane_message_ids_root,
            conflict_schedule_hash: input.conflict_schedule_hash,
            data_availability_root: input.data_availability_root,
            data_availability_certificate_root: input.data_availability_certificate_root,
            carry_queue_pre_root: input.carry_queue_pre_root,
            carry_queue_post_root: input.carry_queue_post_root,
            task_set_root: input.task_set_root,
            semantic_source_set_root: input.semantic_source_set_root,
            partition_plan_root: input.partition_plan_root,
        }
    }

    fn update_hasher(&self, hasher: &mut Sha256) {
        write_bytes32(hasher, self.pre_state_vector_root.as_bytes());
        write_bytes32(hasher, self.post_state_vector_root.as_bytes());
        write_bytes32(hasher, self.input_root.as_bytes());
        write_bytes32(hasher, self.transaction_root.as_bytes());
        write_bytes32(hasher, self.evidence_root.as_bytes());
        write_bytes32(hasher, self.provenance_root.as_bytes());
        write_bytes32(hasher, self.receipt_root.as_bytes());
        write_bytes32(hasher, self.accepted_receipts_root.as_bytes());
        write_bytes32(hasher, self.rejected_receipts_root.as_bytes());
        write_bytes32(hasher, self.effect_root.as_bytes());
        write_bytes32(hasher, self.write_set_root.as_bytes());
        write_bytes32(hasher, self.asset_delta_root.as_bytes());
        write_bytes32(hasher, self.cross_lane_outbox_root.as_bytes());
        write_bytes32(hasher, self.cross_lane_inbox_root.as_bytes());
        write_bytes32(hasher, self.cross_lane_message_ids_root.as_bytes());
        write_bytes32(hasher, self.conflict_schedule_hash.as_bytes());
        write_bytes32(hasher, self.data_availability_root.as_bytes());
        write_bytes32(hasher, self.data_availability_certificate_root.as_bytes());
        write_bytes32(hasher, self.carry_queue_pre_root.as_bytes());
        write_bytes32(hasher, self.carry_queue_post_root.as_bytes());
        write_bytes32(hasher, self.task_set_root.as_bytes());
        write_bytes32(hasher, self.semantic_source_set_root.as_bytes());
        write_bytes32(hasher, self.partition_plan_root.as_bytes());
    }

    pub const fn effect_root(&self) -> CommitmentV3 {
        self.effect_root
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, ZrpfErrorV3> {
        let mut hasher = Sha256::new();
        write_domain(&mut hasher, NODE_COMMITMENTS_HASH_DOMAIN_V3)?;
        self.update_hasher(&mut hasher);
        CommitmentV3::new(hasher.finalize().into())
    }

    pub const fn provenance_root(&self) -> CommitmentV3 {
        self.provenance_root
    }

    pub const fn data_availability_root(&self) -> CommitmentV3 {
        self.data_availability_root
    }

    /// Returns the complete ordered commitment surface for deterministic
    /// profile-specific composition. This preserves the V3 field order and
    /// does not assign semantic meaning to any commitment.
    pub const fn to_input(&self) -> NodeCommitmentsInputV3 {
        NodeCommitmentsInputV3 {
            pre_state_vector_root: self.pre_state_vector_root,
            post_state_vector_root: self.post_state_vector_root,
            input_root: self.input_root,
            transaction_root: self.transaction_root,
            evidence_root: self.evidence_root,
            provenance_root: self.provenance_root,
            receipt_root: self.receipt_root,
            accepted_receipts_root: self.accepted_receipts_root,
            rejected_receipts_root: self.rejected_receipts_root,
            effect_root: self.effect_root,
            write_set_root: self.write_set_root,
            asset_delta_root: self.asset_delta_root,
            cross_lane_outbox_root: self.cross_lane_outbox_root,
            cross_lane_inbox_root: self.cross_lane_inbox_root,
            cross_lane_message_ids_root: self.cross_lane_message_ids_root,
            conflict_schedule_hash: self.conflict_schedule_hash,
            data_availability_root: self.data_availability_root,
            data_availability_certificate_root: self.data_availability_certificate_root,
            carry_queue_pre_root: self.carry_queue_pre_root,
            carry_queue_post_root: self.carry_queue_post_root,
            task_set_root: self.task_set_root,
            semantic_source_set_root: self.semantic_source_set_root,
            partition_plan_root: self.partition_plan_root,
        }
    }
}

pub fn derive_verifier_id_v3(
    program_id: ProgramIdV3,
    profile_id: ProfileIdV3,
) -> Result<VerifierIdV3, ZrpfErrorV3> {
    let mut hasher = Sha256::new();
    write_domain(&mut hasher, VERIFIER_ID_DOMAIN_V3)?;
    write_bytes32(&mut hasher, program_id.as_bytes());
    write_bytes32(&mut hasher, profile_id.as_bytes());
    write_u16(&mut hasher, NODE_JOURNAL_VERSION_V3);
    VerifierIdV3::new(hasher.finalize().into())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NodeKindV3 {
    Leaf,
    Aggregate,
}

impl NodeKindV3 {
    const fn tag(self) -> u8 {
        match self {
            Self::Leaf => 0,
            Self::Aggregate => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(transparent)]
pub struct NodeLevelV3(u8);

impl NodeLevelV3 {
    pub const LEAF: Self = Self(0);

    pub fn new(level: u8) -> Result<Self, ZrpfErrorV3> {
        if level > MAX_NODE_LEVEL_V3 {
            return Err(ZrpfErrorV3::MaximumTreeLevelExceeded);
        }
        Ok(Self(level))
    }

    pub const fn get(self) -> u8 {
        self.0
    }

    fn parent(self) -> Result<Self, ZrpfErrorV3> {
        let parent = self
            .0
            .checked_add(1)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("node_level"))?;
        Self::new(parent)
    }
}

impl<'de> Deserialize<'de> for NodeLevelV3 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let level = u8::deserialize(deserializer)?;
        Self::new(level).map_err(de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct PartitionV3 {
    start: u64,
    end_exclusive: u64,
}

impl PartitionV3 {
    pub fn new(start: u64, end_exclusive: u64) -> Result<Self, ZrpfErrorV3> {
        if start >= end_exclusive {
            return Err(ZrpfErrorV3::InvalidPartition);
        }
        Ok(Self {
            start,
            end_exclusive,
        })
    }

    pub const fn start(self) -> u64 {
        self.start
    }

    pub const fn end_exclusive(self) -> u64 {
        self.end_exclusive
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PartitionWireV3 {
    start: u64,
    end_exclusive: u64,
}

impl<'de> Deserialize<'de> for PartitionV3 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = PartitionWireV3::deserialize(deserializer)?;
        Self::new(wire.start, wire.end_exclusive).map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NodeJournalV3 {
    journal_version: u16,
    task_id: TaskIdV3,
    node_kind: NodeKindV3,
    node_level: NodeLevelV3,
    partition: PartitionV3,
    immediate_child_count: u8,
    leaf_count: u64,
    operation_count: u64,
    count_unit_id: CommitmentV3,
    subtree_node_count: u64,
    scope: NodeScopeV3,
    proof_profile_id: ProfileIdV3,
    actual_program_id: ProgramIdV3,
    verifier_id: VerifierIdV3,
    node_statement_hash: CommitmentV3,
    program_manifest_root: CommitmentV3,
    commitments: NodeCommitmentsV3,
    child_tasks_root: CommitmentV3,
    child_claims_root: CommitmentV3,
    child_journals_root: CommitmentV3,
    child_programs_root: CommitmentV3,
    child_profiles_root: CommitmentV3,
    child_verifiers_root: CommitmentV3,
    immediate_verifier_set_root: CommitmentV3,
    child_statements_root: CommitmentV3,
    child_manifests_root: CommitmentV3,
    child_effects_root: CommitmentV3,
    child_provenance_roots: CommitmentV3,
    child_data_availability_roots: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NodeJournalWireV3 {
    journal_version: u16,
    task_id: TaskIdV3,
    node_kind: NodeKindV3,
    node_level: NodeLevelV3,
    partition: PartitionV3,
    immediate_child_count: u8,
    leaf_count: u64,
    operation_count: u64,
    count_unit_id: CommitmentV3,
    subtree_node_count: u64,
    scope: NodeScopeV3,
    proof_profile_id: ProfileIdV3,
    actual_program_id: ProgramIdV3,
    verifier_id: VerifierIdV3,
    node_statement_hash: CommitmentV3,
    program_manifest_root: CommitmentV3,
    commitments: NodeCommitmentsV3,
    child_tasks_root: CommitmentV3,
    child_claims_root: CommitmentV3,
    child_journals_root: CommitmentV3,
    child_programs_root: CommitmentV3,
    child_profiles_root: CommitmentV3,
    child_verifiers_root: CommitmentV3,
    immediate_verifier_set_root: CommitmentV3,
    child_statements_root: CommitmentV3,
    child_manifests_root: CommitmentV3,
    child_effects_root: CommitmentV3,
    child_provenance_roots: CommitmentV3,
    child_data_availability_roots: CommitmentV3,
}

impl From<NodeJournalWireV3> for NodeJournalV3 {
    fn from(wire: NodeJournalWireV3) -> Self {
        Self {
            journal_version: wire.journal_version,
            task_id: wire.task_id,
            node_kind: wire.node_kind,
            node_level: wire.node_level,
            partition: wire.partition,
            immediate_child_count: wire.immediate_child_count,
            leaf_count: wire.leaf_count,
            operation_count: wire.operation_count,
            count_unit_id: wire.count_unit_id,
            subtree_node_count: wire.subtree_node_count,
            scope: wire.scope,
            proof_profile_id: wire.proof_profile_id,
            actual_program_id: wire.actual_program_id,
            verifier_id: wire.verifier_id,
            node_statement_hash: wire.node_statement_hash,
            program_manifest_root: wire.program_manifest_root,
            commitments: wire.commitments,
            child_tasks_root: wire.child_tasks_root,
            child_claims_root: wire.child_claims_root,
            child_journals_root: wire.child_journals_root,
            child_programs_root: wire.child_programs_root,
            child_profiles_root: wire.child_profiles_root,
            child_verifiers_root: wire.child_verifiers_root,
            immediate_verifier_set_root: wire.immediate_verifier_set_root,
            child_statements_root: wire.child_statements_root,
            child_manifests_root: wire.child_manifests_root,
            child_effects_root: wire.child_effects_root,
            child_provenance_roots: wire.child_provenance_roots,
            child_data_availability_roots: wire.child_data_availability_roots,
        }
    }
}

impl<'de> Deserialize<'de> for NodeJournalV3 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let journal = Self::from(NodeJournalWireV3::deserialize(deserializer)?);
        journal.validate().map_err(de::Error::custom)?;
        Ok(journal)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafNodeInputV3 {
    pub task_id: TaskIdV3,
    pub partition: PartitionV3,
    pub operation_count: u64,
    pub count_unit_id: CommitmentV3,
    pub scope: NodeScopeV3,
    pub proof_profile_id: ProfileIdV3,
    pub actual_program_id: ProgramIdV3,
    pub node_statement_hash: CommitmentV3,
    pub program_manifest_root: CommitmentV3,
    pub commitments: NodeCommitmentsV3,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectedChildDescriptorV3 {
    child_task_id: TaskIdV3,
    child_kind: NodeKindV3,
    child_level: NodeLevelV3,
    partition: PartitionV3,
    leaf_count: u64,
    operation_count: u64,
    count_unit_id: CommitmentV3,
    subtree_node_count: u64,
    child_profile_id: ProfileIdV3,
    child_program_id: ProgramIdV3,
    child_verifier_id: VerifierIdV3,
    child_claim_hash: CommitmentV3,
    child_journal_hash: CommitmentV3,
    child_node_statement_hash: CommitmentV3,
    child_program_manifest_root: CommitmentV3,
    child_scope_hash: CommitmentV3,
    child_effect_root: CommitmentV3,
    child_provenance_root: CommitmentV3,
    child_data_availability_root: CommitmentV3,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AggregateNodeInputV3 {
    pub children: Vec<ProjectedChildDescriptorV3>,
    pub task_id: TaskIdV3,
    pub count_unit_id: CommitmentV3,
    pub scope: NodeScopeV3,
    pub proof_profile_id: ProfileIdV3,
    pub actual_program_id: ProgramIdV3,
    pub node_statement_hash: CommitmentV3,
    pub program_manifest_root: CommitmentV3,
    pub commitments: NodeCommitmentsV3,
}

struct AggregateShapeV3 {
    parent_level: NodeLevelV3,
    partition: PartitionV3,
    immediate_child_count: u8,
    leaf_count: u64,
    operation_count: u64,
    subtree_node_count: u64,
}

struct ChildRootsV3 {
    tasks: CommitmentV3,
    claims: CommitmentV3,
    journals: CommitmentV3,
    programs: CommitmentV3,
    profiles: CommitmentV3,
    verifiers: CommitmentV3,
    verifier_set: CommitmentV3,
    statements: CommitmentV3,
    manifests: CommitmentV3,
    effects: CommitmentV3,
    provenance: CommitmentV3,
    data_availability: CommitmentV3,
}

impl NodeJournalV3 {
    pub fn new_leaf(input: LeafNodeInputV3) -> Result<Self, ZrpfErrorV3> {
        if input.operation_count == 0 {
            return Err(ZrpfErrorV3::ZeroOperationCount);
        }
        input.scope.validate()?;
        let verifier_id = derive_verifier_id_v3(input.actual_program_id, input.proof_profile_id)?;
        let journal = Self {
            journal_version: NODE_JOURNAL_VERSION_V3,
            task_id: input.task_id,
            node_kind: NodeKindV3::Leaf,
            node_level: NodeLevelV3::LEAF,
            partition: input.partition,
            immediate_child_count: 0,
            leaf_count: 1,
            operation_count: input.operation_count,
            count_unit_id: input.count_unit_id,
            subtree_node_count: 1,
            scope: input.scope,
            proof_profile_id: input.proof_profile_id,
            actual_program_id: input.actual_program_id,
            verifier_id,
            node_statement_hash: input.node_statement_hash,
            program_manifest_root: input.program_manifest_root,
            commitments: input.commitments,
            child_tasks_root: empty_root(CHILD_TASKS_ROOT_DOMAIN_V3)?,
            child_claims_root: empty_root(CHILD_CLAIMS_ROOT_DOMAIN_V3)?,
            child_journals_root: empty_root(CHILD_JOURNALS_ROOT_DOMAIN_V3)?,
            child_programs_root: empty_root(CHILD_PROGRAMS_ROOT_DOMAIN_V3)?,
            child_profiles_root: empty_root(CHILD_PROFILES_ROOT_DOMAIN_V3)?,
            child_verifiers_root: empty_root(CHILD_VERIFIERS_ROOT_DOMAIN_V3)?,
            immediate_verifier_set_root: empty_root(IMMEDIATE_VERIFIER_SET_ROOT_DOMAIN_V3)?,
            child_statements_root: empty_root(CHILD_STATEMENTS_ROOT_DOMAIN_V3)?,
            child_manifests_root: empty_root(CHILD_MANIFESTS_ROOT_DOMAIN_V3)?,
            child_effects_root: empty_root(CHILD_EFFECTS_ROOT_DOMAIN_V3)?,
            child_provenance_roots: empty_root(CHILD_PROVENANCE_ROOTS_DOMAIN_V3)?,
            child_data_availability_roots: empty_root(CHILD_DATA_AVAILABILITY_ROOTS_DOMAIN_V3)?,
        };
        journal.validate()?;
        Ok(journal)
    }

    pub fn new_aggregate(input: AggregateNodeInputV3) -> Result<Self, ZrpfErrorV3> {
        input.scope.validate()?;
        let scope_hash = input.scope.canonical_hash()?;
        let children = canonicalize_children(
            input.children,
            scope_hash,
            input.task_id,
            input.count_unit_id,
        )?;
        let shape = derive_aggregate_shape(&children)?;
        let roots = derive_child_roots(&children)?;
        let verifier_id = derive_verifier_id_v3(input.actual_program_id, input.proof_profile_id)?;

        let journal = Self {
            journal_version: NODE_JOURNAL_VERSION_V3,
            task_id: input.task_id,
            node_kind: NodeKindV3::Aggregate,
            node_level: shape.parent_level,
            partition: shape.partition,
            immediate_child_count: shape.immediate_child_count,
            leaf_count: shape.leaf_count,
            operation_count: shape.operation_count,
            count_unit_id: input.count_unit_id,
            subtree_node_count: shape.subtree_node_count,
            scope: input.scope,
            proof_profile_id: input.proof_profile_id,
            actual_program_id: input.actual_program_id,
            verifier_id,
            node_statement_hash: input.node_statement_hash,
            program_manifest_root: input.program_manifest_root,
            commitments: input.commitments,
            child_tasks_root: roots.tasks,
            child_claims_root: roots.claims,
            child_journals_root: roots.journals,
            child_programs_root: roots.programs,
            child_profiles_root: roots.profiles,
            child_verifiers_root: roots.verifiers,
            immediate_verifier_set_root: roots.verifier_set,
            child_statements_root: roots.statements,
            child_manifests_root: roots.manifests,
            child_effects_root: roots.effects,
            child_provenance_roots: roots.provenance,
            child_data_availability_roots: roots.data_availability,
        };
        journal.validate()?;
        Ok(journal)
    }

    pub fn validate(&self) -> Result<(), ZrpfErrorV3> {
        self.validate_common_fields()?;
        match self.node_kind {
            NodeKindV3::Leaf => self.validate_leaf_shape(),
            NodeKindV3::Aggregate => self.validate_aggregate_shape(),
        }
    }

    fn validate_common_fields(&self) -> Result<(), ZrpfErrorV3> {
        if self.journal_version != NODE_JOURNAL_VERSION_V3 {
            return Err(ZrpfErrorV3::InvalidJournalVersion(self.journal_version));
        }
        self.scope.validate()?;
        if self.verifier_id != derive_verifier_id_v3(self.actual_program_id, self.proof_profile_id)?
        {
            return Err(ZrpfErrorV3::VerifierIdMismatch);
        }
        PartitionV3::new(self.partition.start(), self.partition.end_exclusive())?;
        if self.operation_count == 0 {
            return Err(ZrpfErrorV3::ZeroOperationCount);
        }
        let partition_width = self
            .partition
            .end_exclusive()
            .checked_sub(self.partition.start())
            .ok_or(ZrpfErrorV3::InvalidPartition)?;
        if partition_width != self.leaf_count {
            return Err(ZrpfErrorV3::PartitionLeafCountMismatch);
        }
        let maximum_operations = self
            .leaf_count
            .checked_mul(MAX_OPERATIONS_PER_LEAF_V3)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("maximum_operation_count"))?;
        if self.operation_count > maximum_operations {
            return Err(ZrpfErrorV3::OperationLimitExceeded {
                actual: self.operation_count,
                maximum: maximum_operations,
            });
        }
        Ok(())
    }

    fn validate_leaf_shape(&self) -> Result<(), ZrpfErrorV3> {
        if self.node_level != NodeLevelV3::LEAF {
            return Err(ZrpfErrorV3::InvalidLeafLevel);
        }
        if self.immediate_child_count != 0 || self.leaf_count != 1 || self.subtree_node_count != 1 {
            return Err(ZrpfErrorV3::InvalidLeafCounts);
        }
        let has_nonempty_child_root = self.child_claims_root
            != empty_root(CHILD_CLAIMS_ROOT_DOMAIN_V3)?
            || self.child_tasks_root != empty_root(CHILD_TASKS_ROOT_DOMAIN_V3)?
            || self.child_journals_root != empty_root(CHILD_JOURNALS_ROOT_DOMAIN_V3)?
            || self.child_programs_root != empty_root(CHILD_PROGRAMS_ROOT_DOMAIN_V3)?
            || self.child_profiles_root != empty_root(CHILD_PROFILES_ROOT_DOMAIN_V3)?
            || self.child_verifiers_root != empty_root(CHILD_VERIFIERS_ROOT_DOMAIN_V3)?
            || self.immediate_verifier_set_root
                != empty_root(IMMEDIATE_VERIFIER_SET_ROOT_DOMAIN_V3)?
            || self.child_statements_root != empty_root(CHILD_STATEMENTS_ROOT_DOMAIN_V3)?
            || self.child_manifests_root != empty_root(CHILD_MANIFESTS_ROOT_DOMAIN_V3)?
            || self.child_effects_root != empty_root(CHILD_EFFECTS_ROOT_DOMAIN_V3)?
            || self.child_provenance_roots != empty_root(CHILD_PROVENANCE_ROOTS_DOMAIN_V3)?
            || self.child_data_availability_roots
                != empty_root(CHILD_DATA_AVAILABILITY_ROOTS_DOMAIN_V3)?;
        if has_nonempty_child_root {
            return Err(ZrpfErrorV3::InvalidEmptyChildRoots);
        }
        Ok(())
    }

    fn validate_aggregate_shape(&self) -> Result<(), ZrpfErrorV3> {
        if self.node_level == NodeLevelV3::LEAF {
            return Err(ZrpfErrorV3::InvalidAggregateLevel);
        }
        let minimum_nodes = minimum_subtree_node_count(self)?;
        let child_level = NodeLevelV3::new(self.node_level.get() - 1)?;
        let maximum_leaf_count = u64::from(self.immediate_child_count)
            .checked_mul(max_leaves_at_level(child_level)?)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("maximum_leaf_count"))?;
        if self.immediate_child_count == 0
            || usize::from(self.immediate_child_count) > MAX_IMMEDIATE_CHILDREN_V3
            || self.leaf_count < u64::from(self.immediate_child_count)
            || self.leaf_count > maximum_leaf_count
            || self.leaf_count > max_leaves_at_level(self.node_level)?
            || self.subtree_node_count != minimum_nodes
            || self.subtree_node_count > max_nodes_at_level(self.node_level)?
        {
            return Err(ZrpfErrorV3::InvalidAggregateCounts);
        }
        if self.has_empty_aggregate_child_root()? {
            return Err(ZrpfErrorV3::InvalidAggregateChildRoots);
        }
        Ok(())
    }

    fn has_empty_aggregate_child_root(&self) -> Result<bool, ZrpfErrorV3> {
        Ok(
            self.child_claims_root == empty_root(CHILD_CLAIMS_ROOT_DOMAIN_V3)?
                || self.child_tasks_root == empty_root(CHILD_TASKS_ROOT_DOMAIN_V3)?
                || self.child_journals_root == empty_root(CHILD_JOURNALS_ROOT_DOMAIN_V3)?
                || self.child_programs_root == empty_root(CHILD_PROGRAMS_ROOT_DOMAIN_V3)?
                || self.child_profiles_root == empty_root(CHILD_PROFILES_ROOT_DOMAIN_V3)?
                || self.child_verifiers_root == empty_root(CHILD_VERIFIERS_ROOT_DOMAIN_V3)?
                || self.immediate_verifier_set_root
                    == empty_root(IMMEDIATE_VERIFIER_SET_ROOT_DOMAIN_V3)?
                || self.child_statements_root == empty_root(CHILD_STATEMENTS_ROOT_DOMAIN_V3)?
                || self.child_manifests_root == empty_root(CHILD_MANIFESTS_ROOT_DOMAIN_V3)?
                || self.child_effects_root == empty_root(CHILD_EFFECTS_ROOT_DOMAIN_V3)?
                || self.child_provenance_roots == empty_root(CHILD_PROVENANCE_ROOTS_DOMAIN_V3)?
                || self.child_data_availability_roots
                    == empty_root(CHILD_DATA_AVAILABILITY_ROOTS_DOMAIN_V3)?,
        )
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, ZrpfErrorV3> {
        self.validate()?;
        let mut hasher = Sha256::new();
        write_domain(&mut hasher, NODE_JOURNAL_HASH_DOMAIN_V3)?;
        write_u16(&mut hasher, self.journal_version);
        write_bytes32(&mut hasher, self.task_id.as_bytes());
        write_u8(&mut hasher, self.node_kind.tag());
        write_u8(&mut hasher, self.node_level.get());
        write_u64(&mut hasher, self.partition.start());
        write_u64(&mut hasher, self.partition.end_exclusive());
        write_u8(&mut hasher, self.immediate_child_count);
        write_u64(&mut hasher, self.leaf_count);
        write_u64(&mut hasher, self.operation_count);
        write_bytes32(&mut hasher, self.count_unit_id.as_bytes());
        write_u64(&mut hasher, self.subtree_node_count);
        self.scope.update_hasher(&mut hasher);
        write_bytes32(&mut hasher, self.proof_profile_id.as_bytes());
        write_bytes32(&mut hasher, self.actual_program_id.as_bytes());
        write_bytes32(&mut hasher, self.verifier_id.as_bytes());
        write_bytes32(&mut hasher, self.node_statement_hash.as_bytes());
        write_bytes32(&mut hasher, self.program_manifest_root.as_bytes());
        self.commitments.update_hasher(&mut hasher);
        write_bytes32(&mut hasher, self.child_tasks_root.as_bytes());
        write_bytes32(&mut hasher, self.child_claims_root.as_bytes());
        write_bytes32(&mut hasher, self.child_journals_root.as_bytes());
        write_bytes32(&mut hasher, self.child_programs_root.as_bytes());
        write_bytes32(&mut hasher, self.child_profiles_root.as_bytes());
        write_bytes32(&mut hasher, self.child_verifiers_root.as_bytes());
        write_bytes32(&mut hasher, self.immediate_verifier_set_root.as_bytes());
        write_bytes32(&mut hasher, self.child_statements_root.as_bytes());
        write_bytes32(&mut hasher, self.child_manifests_root.as_bytes());
        write_bytes32(&mut hasher, self.child_effects_root.as_bytes());
        write_bytes32(&mut hasher, self.child_provenance_roots.as_bytes());
        write_bytes32(&mut hasher, self.child_data_availability_roots.as_bytes());
        CommitmentV3::new(hasher.finalize().into())
    }

    pub const fn node_kind(&self) -> NodeKindV3 {
        self.node_kind
    }

    pub const fn task_id(&self) -> TaskIdV3 {
        self.task_id
    }

    pub const fn scope(&self) -> &NodeScopeV3 {
        &self.scope
    }

    pub const fn node_level(&self) -> NodeLevelV3 {
        self.node_level
    }

    pub const fn partition(&self) -> PartitionV3 {
        self.partition
    }

    pub const fn immediate_child_count(&self) -> u8 {
        self.immediate_child_count
    }

    pub const fn leaf_count(&self) -> u64 {
        self.leaf_count
    }

    pub const fn operation_count(&self) -> u64 {
        self.operation_count
    }

    pub const fn count_unit_id(&self) -> CommitmentV3 {
        self.count_unit_id
    }

    pub const fn subtree_node_count(&self) -> u64 {
        self.subtree_node_count
    }

    pub const fn proof_profile_id(&self) -> ProfileIdV3 {
        self.proof_profile_id
    }

    pub const fn actual_program_id(&self) -> ProgramIdV3 {
        self.actual_program_id
    }

    pub const fn verifier_id(&self) -> VerifierIdV3 {
        self.verifier_id
    }

    pub const fn node_statement_hash(&self) -> CommitmentV3 {
        self.node_statement_hash
    }

    pub const fn program_manifest_root(&self) -> CommitmentV3 {
        self.program_manifest_root
    }

    pub const fn commitments(&self) -> &NodeCommitmentsV3 {
        &self.commitments
    }

    pub const fn child_claims_root(&self) -> CommitmentV3 {
        self.child_claims_root
    }

    pub const fn child_journals_root(&self) -> CommitmentV3 {
        self.child_journals_root
    }

    pub const fn child_programs_root(&self) -> CommitmentV3 {
        self.child_programs_root
    }

    pub const fn child_profiles_root(&self) -> CommitmentV3 {
        self.child_profiles_root
    }

    pub const fn child_verifiers_root(&self) -> CommitmentV3 {
        self.child_verifiers_root
    }

    pub const fn immediate_verifier_set_root(&self) -> CommitmentV3 {
        self.immediate_verifier_set_root
    }

    pub const fn child_tasks_root(&self) -> CommitmentV3 {
        self.child_tasks_root
    }

    pub const fn child_effects_root(&self) -> CommitmentV3 {
        self.child_effects_root
    }

    pub const fn child_provenance_roots(&self) -> CommitmentV3 {
        self.child_provenance_roots
    }
}

impl ProjectedChildDescriptorV3 {
    /// Projects exact canonical journal bytes into a bounded child descriptor.
    ///
    /// This proof-system-neutral function does not authenticate a receipt. A proof
    /// adapter must verify that the receipt claim commits to these exact bytes before
    /// passing the descriptor to an authority-bearing aggregate guest.
    pub fn project_canonical_journal(
        child_claim_hash: CommitmentV3,
        canonical_journal_bytes: &[u8],
    ) -> Result<Self, ZrpfErrorV3> {
        let journal = decode_exact_node_journal_v3(canonical_journal_bytes)?;
        journal.validate()?;
        let descriptor = Self {
            child_task_id: journal.task_id,
            child_kind: journal.node_kind,
            child_level: journal.node_level,
            partition: journal.partition,
            leaf_count: journal.leaf_count,
            operation_count: journal.operation_count,
            count_unit_id: journal.count_unit_id,
            subtree_node_count: journal.subtree_node_count,
            child_profile_id: journal.proof_profile_id,
            child_program_id: journal.actual_program_id,
            child_verifier_id: journal.verifier_id,
            child_claim_hash,
            child_journal_hash: journal.canonical_hash()?,
            child_node_statement_hash: journal.node_statement_hash,
            child_program_manifest_root: journal.program_manifest_root,
            child_scope_hash: journal.scope.canonical_hash()?,
            child_effect_root: journal.commitments.effect_root(),
            child_provenance_root: journal.commitments.provenance_root(),
            child_data_availability_root: journal.commitments.data_availability_root(),
        };
        descriptor.validate()?;
        Ok(descriptor)
    }

    pub fn validate(&self) -> Result<(), ZrpfErrorV3> {
        if self.child_verifier_id
            != derive_verifier_id_v3(self.child_program_id, self.child_profile_id)?
        {
            return Err(ZrpfErrorV3::VerifierIdMismatch);
        }
        PartitionV3::new(self.partition.start(), self.partition.end_exclusive())?;
        if self.operation_count == 0 {
            return Err(ZrpfErrorV3::ZeroOperationCount);
        }
        let partition_width = self
            .partition
            .end_exclusive()
            .checked_sub(self.partition.start())
            .ok_or(ZrpfErrorV3::InvalidPartition)?;
        if partition_width != self.leaf_count {
            return Err(ZrpfErrorV3::PartitionLeafCountMismatch);
        }
        let maximum_operations = self
            .leaf_count
            .checked_mul(MAX_OPERATIONS_PER_LEAF_V3)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("maximum_operation_count"))?;
        if self.operation_count > maximum_operations {
            return Err(ZrpfErrorV3::OperationLimitExceeded {
                actual: self.operation_count,
                maximum: maximum_operations,
            });
        }
        match self.child_kind {
            NodeKindV3::Leaf => {
                if self.child_level != NodeLevelV3::LEAF {
                    return Err(ZrpfErrorV3::InvalidLeafLevel);
                }
                if self.leaf_count != 1 || self.subtree_node_count != 1 {
                    return Err(ZrpfErrorV3::InvalidLeafCounts);
                }
            }
            NodeKindV3::Aggregate => {
                if self.child_level == NodeLevelV3::LEAF {
                    return Err(ZrpfErrorV3::InvalidAggregateLevel);
                }
                let minimum_subtree_node_count = self
                    .leaf_count
                    .checked_add(1)
                    .ok_or(ZrpfErrorV3::ArithmeticOverflow("subtree_node_count"))?;
                if self.leaf_count == 0
                    || self.leaf_count > max_leaves_at_level(self.child_level)?
                    || self.subtree_node_count < minimum_subtree_node_count
                    || self.subtree_node_count > max_nodes_at_level(self.child_level)?
                {
                    return Err(ZrpfErrorV3::InvalidAggregateCounts);
                }
            }
        }
        Ok(())
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, ZrpfErrorV3> {
        self.validate()?;
        let mut hasher = Sha256::new();
        write_domain(&mut hasher, CHILD_DESCRIPTOR_HASH_DOMAIN_V3)?;
        write_bytes32(&mut hasher, self.child_task_id.as_bytes());
        write_u8(&mut hasher, self.child_kind.tag());
        write_u8(&mut hasher, self.child_level.get());
        write_u64(&mut hasher, self.partition.start());
        write_u64(&mut hasher, self.partition.end_exclusive());
        write_u64(&mut hasher, self.leaf_count);
        write_u64(&mut hasher, self.operation_count);
        write_bytes32(&mut hasher, self.count_unit_id.as_bytes());
        write_u64(&mut hasher, self.subtree_node_count);
        write_bytes32(&mut hasher, self.child_profile_id.as_bytes());
        write_bytes32(&mut hasher, self.child_program_id.as_bytes());
        write_bytes32(&mut hasher, self.child_verifier_id.as_bytes());
        write_bytes32(&mut hasher, self.child_claim_hash.as_bytes());
        write_bytes32(&mut hasher, self.child_journal_hash.as_bytes());
        write_bytes32(&mut hasher, self.child_node_statement_hash.as_bytes());
        write_bytes32(&mut hasher, self.child_program_manifest_root.as_bytes());
        write_bytes32(&mut hasher, self.child_scope_hash.as_bytes());
        write_bytes32(&mut hasher, self.child_effect_root.as_bytes());
        write_bytes32(&mut hasher, self.child_provenance_root.as_bytes());
        write_bytes32(&mut hasher, self.child_data_availability_root.as_bytes());
        CommitmentV3::new(hasher.finalize().into())
    }

    pub const fn child_level(&self) -> NodeLevelV3 {
        self.child_level
    }

    pub const fn partition(&self) -> PartitionV3 {
        self.partition
    }

    pub const fn child_claim_hash(&self) -> CommitmentV3 {
        self.child_claim_hash
    }

    pub const fn child_journal_hash(&self) -> CommitmentV3 {
        self.child_journal_hash
    }
}

pub fn encode_node_journal_v3(journal: &NodeJournalV3) -> Result<Vec<u8>, ZrpfErrorV3> {
    journal.validate()?;
    postcard::to_allocvec(journal).map_err(|_| ZrpfErrorV3::PostcardDecode)
}

pub fn decode_exact_node_journal_v3(bytes: &[u8]) -> Result<NodeJournalV3, ZrpfErrorV3> {
    if bytes.len() > MAX_NODE_JOURNAL_BYTES_V3 {
        return Err(ZrpfErrorV3::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_NODE_JOURNAL_BYTES_V3,
        });
    }
    let (journal, remainder) = postcard::take_from_bytes::<NodeJournalV3>(bytes)
        .map_err(|_| ZrpfErrorV3::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ZrpfErrorV3::TrailingBytes);
    }
    journal.validate()?;
    let canonical = encode_node_journal_v3(&journal)?;
    if canonical.as_slice() != bytes {
        return Err(ZrpfErrorV3::NonCanonicalEncoding);
    }
    Ok(journal)
}

fn derive_aggregate_shape(
    children: &[ProjectedChildDescriptorV3],
) -> Result<AggregateShapeV3, ZrpfErrorV3> {
    let first = children.first().ok_or(ZrpfErrorV3::EmptyChildren)?;
    let last = children.last().ok_or(ZrpfErrorV3::EmptyChildren)?;
    let mut leaf_count = 0u64;
    let mut operation_count = 0u64;
    let mut descendant_node_count = 0u64;
    for child in children {
        leaf_count = leaf_count
            .checked_add(child.leaf_count)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("leaf_count"))?;
        operation_count = operation_count
            .checked_add(child.operation_count)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("operation_count"))?;
        descendant_node_count = descendant_node_count
            .checked_add(child.subtree_node_count)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("subtree_node_count"))?;
    }
    Ok(AggregateShapeV3 {
        parent_level: first.child_level.parent()?,
        partition: PartitionV3::new(first.partition.start(), last.partition.end_exclusive())?,
        immediate_child_count: u8::try_from(children.len())
            .map_err(|_| ZrpfErrorV3::ArithmeticOverflow("immediate_child_count"))?,
        leaf_count,
        operation_count,
        subtree_node_count: descendant_node_count
            .checked_add(1)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("subtree_node_count"))?,
    })
}

fn derive_child_roots(
    children: &[ProjectedChildDescriptorV3],
) -> Result<ChildRootsV3, ZrpfErrorV3> {
    let mut unique_verifiers: Vec<VerifierIdV3> = children
        .iter()
        .map(|child| child.child_verifier_id)
        .collect();
    unique_verifiers.sort_unstable();
    unique_verifiers.dedup();

    Ok(ChildRootsV3 {
        tasks: list_root(
            CHILD_TASKS_ROOT_DOMAIN_V3,
            children.iter().map(|child| child.child_task_id.as_bytes()),
        )?,
        claims: list_root(
            CHILD_CLAIMS_ROOT_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_claim_hash.as_bytes()),
        )?,
        journals: list_root(
            CHILD_JOURNALS_ROOT_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_journal_hash.as_bytes()),
        )?,
        programs: list_root(
            CHILD_PROGRAMS_ROOT_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_program_id.as_bytes()),
        )?,
        profiles: list_root(
            CHILD_PROFILES_ROOT_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_profile_id.as_bytes()),
        )?,
        verifiers: list_root(
            CHILD_VERIFIERS_ROOT_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_verifier_id.as_bytes()),
        )?,
        verifier_set: list_root(
            IMMEDIATE_VERIFIER_SET_ROOT_DOMAIN_V3,
            unique_verifiers.iter().map(VerifierIdV3::as_bytes),
        )?,
        statements: list_root(
            CHILD_STATEMENTS_ROOT_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_node_statement_hash.as_bytes()),
        )?,
        manifests: list_root(
            CHILD_MANIFESTS_ROOT_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_program_manifest_root.as_bytes()),
        )?,
        effects: list_root(
            CHILD_EFFECTS_ROOT_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_effect_root.as_bytes()),
        )?,
        provenance: list_root(
            CHILD_PROVENANCE_ROOTS_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_provenance_root.as_bytes()),
        )?,
        data_availability: list_root(
            CHILD_DATA_AVAILABILITY_ROOTS_DOMAIN_V3,
            children
                .iter()
                .map(|child| child.child_data_availability_root.as_bytes()),
        )?,
    })
}

fn canonicalize_children(
    mut children: Vec<ProjectedChildDescriptorV3>,
    expected_scope_hash: CommitmentV3,
    parent_task_id: TaskIdV3,
    expected_count_unit_id: CommitmentV3,
) -> Result<Vec<ProjectedChildDescriptorV3>, ZrpfErrorV3> {
    if children.is_empty() {
        return Err(ZrpfErrorV3::EmptyChildren);
    }
    if children.len() > MAX_IMMEDIATE_CHILDREN_V3 {
        return Err(ZrpfErrorV3::TooManyChildren {
            actual: children.len(),
            maximum: MAX_IMMEDIATE_CHILDREN_V3,
        });
    }
    validate_projected_children(
        &children,
        expected_scope_hash,
        parent_task_id,
        expected_count_unit_id,
    )?;
    reject_duplicate_projected_children(&children)?;
    children.sort_unstable_by(|left, right| {
        left.partition
            .start()
            .cmp(&right.partition.start())
            .then_with(|| {
                left.partition
                    .end_exclusive()
                    .cmp(&right.partition.end_exclusive())
            })
            .then_with(|| left.child_task_id.cmp(&right.child_task_id))
    });
    validate_canonical_child_topology(&children)?;
    Ok(children)
}

fn validate_projected_children(
    children: &[ProjectedChildDescriptorV3],
    expected_scope_hash: CommitmentV3,
    parent_task_id: TaskIdV3,
    expected_count_unit_id: CommitmentV3,
) -> Result<(), ZrpfErrorV3> {
    for child in children {
        child.validate()?;
        if child.child_scope_hash != expected_scope_hash {
            return Err(ZrpfErrorV3::ScopeMismatch);
        }
        if child.count_unit_id != expected_count_unit_id {
            return Err(ZrpfErrorV3::CountUnitMismatch);
        }
        if child.child_task_id == parent_task_id {
            return Err(ZrpfErrorV3::DuplicateChildTask);
        }
    }
    Ok(())
}

fn reject_duplicate_projected_children(
    children: &[ProjectedChildDescriptorV3],
) -> Result<(), ZrpfErrorV3> {
    for left in 0..children.len() {
        for right in (left + 1)..children.len() {
            if children[left].child_claim_hash == children[right].child_claim_hash {
                return Err(ZrpfErrorV3::DuplicateChildClaim);
            }
            if children[left].child_journal_hash == children[right].child_journal_hash {
                return Err(ZrpfErrorV3::DuplicateChildJournal);
            }
            if children[left].child_task_id == children[right].child_task_id {
                return Err(ZrpfErrorV3::DuplicateChildTask);
            }
        }
    }
    Ok(())
}

fn validate_canonical_child_topology(
    children: &[ProjectedChildDescriptorV3],
) -> Result<(), ZrpfErrorV3> {
    let expected_level = children
        .first()
        .ok_or(ZrpfErrorV3::EmptyChildren)?
        .child_level;
    if children
        .iter()
        .any(|child| child.child_level != expected_level)
    {
        return Err(ZrpfErrorV3::MixedChildLevels);
    }
    if children
        .windows(2)
        .any(|pair| pair[1].partition.start() < pair[0].partition.end_exclusive())
    {
        return Err(ZrpfErrorV3::OverlappingPartitions);
    }
    if children
        .windows(2)
        .any(|pair| pair[1].partition.start() != pair[0].partition.end_exclusive())
    {
        return Err(ZrpfErrorV3::NonContiguousPartitions);
    }
    Ok(())
}

fn max_leaves_at_level(level: NodeLevelV3) -> Result<u64, ZrpfErrorV3> {
    let mut leaves = 1u64;
    for _ in 0..level.get() {
        leaves = leaves
            .checked_mul(MAX_IMMEDIATE_CHILDREN_V3 as u64)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("max_leaf_count"))?;
    }
    Ok(leaves)
}

fn minimum_subtree_node_count(journal: &NodeJournalV3) -> Result<u64, ZrpfErrorV3> {
    match journal.node_level.get() {
        1 => journal
            .leaf_count
            .checked_add(1)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("subtree_node_count")),
        2 => journal
            .leaf_count
            .checked_add(u64::from(journal.immediate_child_count))
            .and_then(|count| count.checked_add(1))
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("subtree_node_count")),
        _ => Err(ZrpfErrorV3::InvalidAggregateLevel),
    }
}

fn max_nodes_at_level(level: NodeLevelV3) -> Result<u64, ZrpfErrorV3> {
    let mut nodes = 1u64;
    let mut width = 1u64;
    for _ in 0..level.get() {
        width = width
            .checked_mul(MAX_IMMEDIATE_CHILDREN_V3 as u64)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("max_subtree_node_count"))?;
        nodes = nodes
            .checked_add(width)
            .ok_or(ZrpfErrorV3::ArithmeticOverflow("max_subtree_node_count"))?;
    }
    Ok(nodes)
}

fn empty_root(domain: &[u8]) -> Result<CommitmentV3, ZrpfErrorV3> {
    list_root(domain, core::iter::empty::<&[u8; 32]>())
}

fn list_root<'a>(
    domain: &[u8],
    values: impl ExactSizeIterator<Item = &'a [u8; 32]>,
) -> Result<CommitmentV3, ZrpfErrorV3> {
    let length = u32::try_from(values.len())
        .map_err(|_| ZrpfErrorV3::ArithmeticOverflow("commitment_list_length"))?;
    let mut hasher = Sha256::new();
    write_domain(&mut hasher, domain)?;
    write_u32(&mut hasher, length);
    for value in values {
        write_bytes32(&mut hasher, value);
    }
    CommitmentV3::new(hasher.finalize().into())
}

fn write_domain(hasher: &mut Sha256, domain: &[u8]) -> Result<(), ZrpfErrorV3> {
    let length = u16::try_from(domain.len())
        .map_err(|_| ZrpfErrorV3::ArithmeticOverflow("hash_domain_length"))?;
    write_u16(hasher, length);
    hasher.update(domain);
    Ok(())
}

fn write_u8(hasher: &mut Sha256, value: u8) {
    hasher.update([value]);
}

fn write_u16(hasher: &mut Sha256, value: u16) {
    hasher.update(value.to_be_bytes());
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
