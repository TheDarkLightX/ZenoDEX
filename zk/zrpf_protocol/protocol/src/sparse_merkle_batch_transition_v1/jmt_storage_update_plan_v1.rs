//! Versioned JMT-style storage update plan for the existing sparse-Merkle transition.
//!
//! ZenoDEX already has a proof-neutral fixed-depth binary sparse-Merkle
//! transition witness. This module does not replace that hash relation and does
//! not claim wire compatibility with Diem, Aptos, or Penumbra JMT nodes.
//! Instead, it derives the 64-nibble boundary commitments implied by each
//! validated 256-bit witness and defines the immutable value boundary a future
//! storage adapter must satisfy: one tree identity, one strict successor
//! version, one exact derived new-node batch, and a canonical batch of
//! hash-bound stale-node indices.
//!
//! The validated value carries no receipt, proof, persistence, settlement, or
//! ledger authority. The imperative shell must still verify the concrete node
//! codec, compare the expected pre-root, and atomically commit the node payloads,
//! stale indices, state, receipt, replay data, and outbox.

use alloc::{collections::BTreeMap, vec::Vec};
use core::{cmp::Ordering, fmt};

use serde::{
    de::{self, IgnoredAny, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};
use sha2::{Digest, Sha256};

use super::{
    SparseMerkleBatchTransitionErrorV1, ValidatedSparseMerkleBatchTransitionV1,
    MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1, MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1,
};
use crate::{
    derive_sparse_merkle_internal_commitment_v1, derive_sparse_merkle_leaf_commitment_v1,
    CommitmentV3, SparseMerkleCellTransitionErrorV1, SparseMerkleCellTransitionWitnessV1,
    ValueHashV2, SPARSE_MERKLE_TREE_DEPTH_V1,
};

pub const JMT_STORAGE_UPDATE_PLAN_VERSION_V1: u16 = 1;

/// The only V1 profile: 64 nibble-addressed storage boundaries whose hashes
/// remain the existing ZenoDEX binary sparse-Merkle subtree commitments.
pub const JMT_STORAGE_PROFILE_SPARSE_MERKLE_BRIDGE_V1: u16 = 1;

/// A 256-bit key has 64 four-bit path components.
pub const JMT_NIBBLE_PATH_MAX_NIBBLES_V1: u8 = 64;

/// One changed key contributes at most the root, 63 internal nibble boundaries,
/// and one leaf boundary. Unioning a 64-write batch cannot exceed this bound.
pub const MAX_JMT_STORAGE_NEW_NODES_V1: usize = MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1
    * (JMT_NIBBLE_PATH_MAX_NIBBLES_V1 as usize + 1);

/// A write can make at most the same number of previously live boundaries stale.
pub const MAX_JMT_STORAGE_STALE_NODES_V1: usize = MAX_JMT_STORAGE_NEW_NODES_V1;

const JMT_NODE_RECORD_MAX_POSTCARD_BYTES_V1: usize = 80;
const JMT_STALE_NODE_INDEX_MAX_POSTCARD_BYTES_V1: usize = 96;
const JMT_STORAGE_UPDATE_PLAN_FIXED_SLACK_BYTES_V1: usize = 512;

/// Conservative hard ceiling before decoding. It covers the maximum existing
/// sparse-Merkle batch plus bounded versioned node and stale-index records.
pub const MAX_JMT_STORAGE_UPDATE_PLAN_BYTES_V1: usize =
    MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1
        + MAX_JMT_STORAGE_NEW_NODES_V1 * JMT_NODE_RECORD_MAX_POSTCARD_BYTES_V1
        + MAX_JMT_STORAGE_STALE_NODES_V1 * JMT_STALE_NODE_INDEX_MAX_POSTCARD_BYTES_V1
        + JMT_STORAGE_UPDATE_PLAN_FIXED_SLACK_BYTES_V1;

const JMT_STORAGE_UPDATE_PLAN_HASH_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.jmt_storage_update_plan_hash.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JmtStorageUpdatePlanErrorV1 {
    SparseMerkleBatch(SparseMerkleBatchTransitionErrorV1),
    SparseMerkleCell(SparseMerkleCellTransitionErrorV1),
    InvalidPlanVersion(u16),
    InvalidStorageProfile(u16),
    InvalidNibbleCount(u8),
    NonCanonicalNibblePath,
    VersionOverflow,
    NonSuccessorVersion {
        base_version: u64,
        target_version: u64,
    },
    EmptyNewNodeBatch,
    TooManyNewNodes {
        actual: usize,
        maximum: usize,
    },
    TooManyStaleNodes {
        actual: usize,
        maximum: usize,
    },
    BaseRootMismatch,
    PostRootMismatch,
    BoundaryRootMismatch(&'static str),
    NewNodeVersionMismatch {
        index: usize,
        actual: u64,
        expected: u64,
    },
    DuplicateNewNodeKey {
        index: usize,
    },
    NonCanonicalNewNodeOrder {
        index: usize,
    },
    NewNodeCountMismatch {
        actual: usize,
        expected: usize,
    },
    NewNodeMismatch {
        index: usize,
    },
    StaleSinceVersionMismatch {
        index: usize,
        actual: u64,
        expected: u64,
    },
    FutureStaleNode {
        index: usize,
        node_version: u64,
        base_version: u64,
    },
    DuplicateStalePath {
        index: usize,
    },
    NonCanonicalStaleNodeOrder {
        index: usize,
    },
    UntouchedStalePath {
        index: usize,
    },
    StaleNodeHashMismatch {
        index: usize,
    },
    ArithmeticOverflow(&'static str),
    AllocationFailed(&'static str),
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    PostcardEncode,
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
    DerivedZeroCommitment,
}

impl From<SparseMerkleBatchTransitionErrorV1> for JmtStorageUpdatePlanErrorV1 {
    fn from(error: SparseMerkleBatchTransitionErrorV1) -> Self {
        Self::SparseMerkleBatch(error)
    }
}

impl From<SparseMerkleCellTransitionErrorV1> for JmtStorageUpdatePlanErrorV1 {
    fn from(error: SparseMerkleCellTransitionErrorV1) -> Self {
        Self::SparseMerkleCell(error)
    }
}

impl fmt::Display for JmtStorageUpdatePlanErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SparseMerkleBatch(error) => {
                write!(formatter, "sparse-Merkle batch rejected: {error}")
            }
            Self::SparseMerkleCell(error) => {
                write!(formatter, "sparse-Merkle cell derivation rejected: {error}")
            }
            Self::InvalidPlanVersion(version) => {
                write!(formatter, "invalid JMT storage update plan version: {version}")
            }
            Self::InvalidStorageProfile(profile) => {
                write!(formatter, "invalid JMT storage profile: {profile}")
            }
            Self::InvalidNibbleCount(count) => {
                write!(formatter, "JMT nibble count {count} exceeds 64")
            }
            Self::NonCanonicalNibblePath => {
                formatter.write_str("JMT nibble path has nonzero unused bits")
            }
            Self::VersionOverflow => {
                formatter.write_str("JMT base version has no strict successor")
            }
            Self::NonSuccessorVersion {
                base_version,
                target_version,
            } => write!(
                formatter,
                "JMT target version {target_version} is not the strict successor of {base_version}"
            ),
            Self::EmptyNewNodeBatch => {
                formatter.write_str("JMT storage update has no new node records")
            }
            Self::TooManyNewNodes { actual, maximum } => write!(
                formatter,
                "JMT new-node count {actual} exceeds {maximum}"
            ),
            Self::TooManyStaleNodes { actual, maximum } => write!(
                formatter,
                "JMT stale-node count {actual} exceeds {maximum}"
            ),
            Self::BaseRootMismatch => {
                formatter.write_str("JMT plan base root differs from the transition pre-root")
            }
            Self::PostRootMismatch => {
                formatter.write_str("JMT plan post root differs from the transition post-root")
            }
            Self::BoundaryRootMismatch(phase) => write!(
                formatter,
                "derived {phase} nibble-boundary root differs from the witness root"
            ),
            Self::NewNodeVersionMismatch {
                index,
                actual,
                expected,
            } => write!(
                formatter,
                "JMT new node {index} uses version {actual}, expected {expected}"
            ),
            Self::DuplicateNewNodeKey { index } => {
                write!(formatter, "JMT new node {index} duplicates the prior node key")
            }
            Self::NonCanonicalNewNodeOrder { index } => write!(
                formatter,
                "JMT new node {index} is outside canonical node-key order"
            ),
            Self::NewNodeCountMismatch { actual, expected } => write!(
                formatter,
                "JMT new-node count {actual} differs from derived count {expected}"
            ),
            Self::NewNodeMismatch { index } => write!(
                formatter,
                "JMT new node {index} differs from the transition-derived boundary commitment"
            ),
            Self::StaleSinceVersionMismatch {
                index,
                actual,
                expected,
            } => write!(
                formatter,
                "JMT stale index {index} becomes stale at {actual}, expected {expected}"
            ),
            Self::FutureStaleNode {
                index,
                node_version,
                base_version,
            } => write!(
                formatter,
                "JMT stale index {index} references future node version {node_version} above base {base_version}"
            ),
            Self::DuplicateStalePath { index } => {
                write!(formatter, "JMT stale index {index} repeats one touched path")
            }
            Self::NonCanonicalStaleNodeOrder { index } => write!(
                formatter,
                "JMT stale index {index} is outside canonical path order"
            ),
            Self::UntouchedStalePath { index } => write!(
                formatter,
                "JMT stale index {index} refers to a path untouched by the transition"
            ),
            Self::StaleNodeHashMismatch { index } => write!(
                formatter,
                "JMT stale index {index} hash differs from the base boundary commitment"
            ),
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "JMT storage update arithmetic overflow: {field}")
            }
            Self::AllocationFailed(field) => {
                write!(formatter, "bounded JMT storage allocation failed: {field}")
            }
            Self::EmptyInput => formatter.write_str("JMT storage update input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "JMT storage update input length {actual} exceeds {maximum}"
            ),
            Self::PostcardEncode => {
                formatter.write_str("JMT storage update Postcard encode failed")
            }
            Self::PostcardDecode => {
                formatter.write_str("JMT storage update Postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("JMT storage update contains trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("JMT storage update encoding is not canonical")
            }
            Self::DerivedZeroCommitment => {
                formatter.write_str("JMT storage update hash produced a zero commitment")
            }
        }
    }
}

/// Canonical nibble path. Used nibbles occupy the high nibble first; every
/// unused low nibble and trailing byte is zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct JmtNibblePathV1 {
    nibble_count: u8,
    packed_nibbles: [u8; 32],
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct JmtNibblePathWireV1 {
    nibble_count: u8,
    packed_nibbles: [u8; 32],
}

impl JmtNibblePathV1 {
    pub fn new(
        nibble_count: u8,
        packed_nibbles: [u8; 32],
    ) -> Result<Self, JmtStorageUpdatePlanErrorV1> {
        let path = Self {
            nibble_count,
            packed_nibbles,
        };
        path.validate_self_consistency()?;
        Ok(path)
    }

    pub const fn root() -> Self {
        Self {
            nibble_count: 0,
            packed_nibbles: [0; 32],
        }
    }

    pub fn from_key_prefix(
        key: [u8; 32],
        nibble_count: u8,
    ) -> Result<Self, JmtStorageUpdatePlanErrorV1> {
        if nibble_count > JMT_NIBBLE_PATH_MAX_NIBBLES_V1 {
            return Err(JmtStorageUpdatePlanErrorV1::InvalidNibbleCount(
                nibble_count,
            ));
        }
        let mut packed_nibbles = key;
        let count = usize::from(nibble_count);
        let full_bytes = count / 2;
        if count % 2 == 0 {
            packed_nibbles[full_bytes..].fill(0);
        } else {
            packed_nibbles[full_bytes] &= 0xf0;
            packed_nibbles[full_bytes + 1..].fill(0);
        }
        Self::new(nibble_count, packed_nibbles)
    }

    pub fn validate_self_consistency(&self) -> Result<(), JmtStorageUpdatePlanErrorV1> {
        if self.nibble_count > JMT_NIBBLE_PATH_MAX_NIBBLES_V1 {
            return Err(JmtStorageUpdatePlanErrorV1::InvalidNibbleCount(
                self.nibble_count,
            ));
        }
        let count = usize::from(self.nibble_count);
        let full_bytes = count / 2;
        let noncanonical = if count % 2 == 0 {
            self.packed_nibbles[full_bytes..]
                .iter()
                .any(|byte| *byte != 0)
        } else {
            self.packed_nibbles[full_bytes] & 0x0f != 0
                || self.packed_nibbles[full_bytes + 1..]
                    .iter()
                    .any(|byte| *byte != 0)
        };
        if noncanonical {
            return Err(JmtStorageUpdatePlanErrorV1::NonCanonicalNibblePath);
        }
        Ok(())
    }

    pub const fn nibble_count(&self) -> u8 {
        self.nibble_count
    }

    pub const fn packed_nibbles(&self) -> &[u8; 32] {
        &self.packed_nibbles
    }

    pub const fn is_root(&self) -> bool {
        self.nibble_count == 0
    }
}

impl Ord for JmtNibblePathV1 {
    fn cmp(&self, other: &Self) -> Ordering {
        compare_nibble_paths(*self, *other)
    }
}

impl PartialOrd for JmtNibblePathV1 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'de> Deserialize<'de> for JmtNibblePathV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = JmtNibblePathWireV1::deserialize(deserializer)?;
        Self::new(wire.nibble_count, wire.packed_nibbles).map_err(de::Error::custom)
    }
}

/// Versioned storage identity for one JMT-style node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct JmtNodeKeyV1 {
    version: u64,
    nibble_path: JmtNibblePathV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct JmtNodeKeyWireV1 {
    version: u64,
    nibble_path: JmtNibblePathV1,
}

impl JmtNodeKeyV1 {
    pub const fn new(version: u64, nibble_path: JmtNibblePathV1) -> Self {
        Self {
            version,
            nibble_path,
        }
    }

    pub const fn version(&self) -> u64 {
        self.version
    }

    pub const fn nibble_path(&self) -> JmtNibblePathV1 {
        self.nibble_path
    }
}

impl<'de> Deserialize<'de> for JmtNodeKeyV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = JmtNodeKeyWireV1::deserialize(deserializer)?;
        wire.nibble_path
            .validate_self_consistency()
            .map_err(de::Error::custom)?;
        Ok(Self::new(wire.version, wire.nibble_path))
    }
}

/// One transition-derived subtree commitment to be written under a versioned
/// nibble-boundary node key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JmtNodeRecordV1 {
    node_key: JmtNodeKeyV1,
    node_hash: CommitmentV3,
}

impl JmtNodeRecordV1 {
    pub const fn new(node_key: JmtNodeKeyV1, node_hash: CommitmentV3) -> Self {
        Self {
            node_key,
            node_hash,
        }
    }

    pub const fn node_key(&self) -> JmtNodeKeyV1 {
        self.node_key
    }

    pub const fn node_hash(&self) -> CommitmentV3 {
        self.node_hash
    }
}

/// One previously live node that becomes prune-eligible from target version.
/// The expected hash prevents a storage adapter from marking an unrelated node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JmtStaleNodeIndexV1 {
    stale_since_version: u64,
    node_key: JmtNodeKeyV1,
    expected_node_hash: CommitmentV3,
}

impl JmtStaleNodeIndexV1 {
    pub const fn new(
        stale_since_version: u64,
        node_key: JmtNodeKeyV1,
        expected_node_hash: CommitmentV3,
    ) -> Self {
        Self {
            stale_since_version,
            node_key,
            expected_node_hash,
        }
    }

    pub const fn stale_since_version(&self) -> u64 {
        self.stale_since_version
    }

    pub const fn node_key(&self) -> JmtNodeKeyV1 {
        self.node_key
    }

    pub const fn expected_node_hash(&self) -> CommitmentV3 {
        self.expected_node_hash
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JmtStorageUpdatePlanInputV1 {
    pub plan_version: u16,
    pub storage_profile: u16,
    pub tree_id: CommitmentV3,
    pub base_version: u64,
    pub target_version: u64,
    pub base_root: CommitmentV3,
    pub post_root: CommitmentV3,
    pub transition: ValidatedSparseMerkleBatchTransitionV1,
    pub new_nodes: Vec<JmtNodeRecordV1>,
    pub stale_nodes: Vec<JmtStaleNodeIndexV1>,
}

/// Closed proof-neutral value binding one transition to one versioned storage
/// update plan.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ValidatedJmtStorageUpdatePlanV1;
/// let plan: ValidatedJmtStorageUpdatePlanV1 = unimplemented!();
/// let _ = plan.ledger_authority();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ValidatedJmtStorageUpdatePlanV1;
/// let _ = ValidatedJmtStorageUpdatePlanV1 {};
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ValidatedJmtStorageUpdatePlanV1 {
    plan_version: u16,
    storage_profile: u16,
    tree_id: CommitmentV3,
    base_version: u64,
    target_version: u64,
    base_root: CommitmentV3,
    post_root: CommitmentV3,
    transition: ValidatedSparseMerkleBatchTransitionV1,
    new_nodes: Vec<JmtNodeRecordV1>,
    stale_nodes: Vec<JmtStaleNodeIndexV1>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct JmtStorageUpdatePlanWireV1 {
    plan_version: u16,
    storage_profile: u16,
    tree_id: CommitmentV3,
    base_version: u64,
    target_version: u64,
    base_root: CommitmentV3,
    post_root: CommitmentV3,
    transition: ValidatedSparseMerkleBatchTransitionV1,
    #[serde(deserialize_with = "deserialize_new_nodes")]
    new_nodes: Vec<JmtNodeRecordV1>,
    #[serde(deserialize_with = "deserialize_stale_nodes")]
    stale_nodes: Vec<JmtStaleNodeIndexV1>,
}

impl ValidatedJmtStorageUpdatePlanV1 {
    pub fn new(
        input: JmtStorageUpdatePlanInputV1,
    ) -> Result<Self, JmtStorageUpdatePlanErrorV1> {
        let plan = Self {
            plan_version: input.plan_version,
            storage_profile: input.storage_profile,
            tree_id: input.tree_id,
            base_version: input.base_version,
            target_version: input.target_version,
            base_root: input.base_root,
            post_root: input.post_root,
            transition: input.transition,
            new_nodes: input.new_nodes,
            stale_nodes: input.stale_nodes,
        };
        plan.validate_self_consistency()?;
        Ok(plan)
    }

    pub fn validate_self_consistency(&self) -> Result<(), JmtStorageUpdatePlanErrorV1> {
        if self.plan_version != JMT_STORAGE_UPDATE_PLAN_VERSION_V1 {
            return Err(JmtStorageUpdatePlanErrorV1::InvalidPlanVersion(
                self.plan_version,
            ));
        }
        if self.storage_profile != JMT_STORAGE_PROFILE_SPARSE_MERKLE_BRIDGE_V1 {
            return Err(JmtStorageUpdatePlanErrorV1::InvalidStorageProfile(
                self.storage_profile,
            ));
        }
        let expected_target = self
            .base_version
            .checked_add(1)
            .ok_or(JmtStorageUpdatePlanErrorV1::VersionOverflow)?;
        if self.target_version != expected_target {
            return Err(JmtStorageUpdatePlanErrorV1::NonSuccessorVersion {
                base_version: self.base_version,
                target_version: self.target_version,
            });
        }
        require_new_node_count(self.new_nodes.len())?;
        require_stale_node_count(self.stale_nodes.len())?;
        self.transition.validate_self_consistency()?;
        if self.base_root != self.transition.batch_pre_root() {
            return Err(JmtStorageUpdatePlanErrorV1::BaseRootMismatch);
        }
        if self.post_root != self.transition.batch_post_root() {
            return Err(JmtStorageUpdatePlanErrorV1::PostRootMismatch);
        }

        let derived = derive_boundary_maps(&self.transition)?;
        let expected_new_nodes =
            materialize_new_nodes(&derived.post, self.target_version)?;
        validate_supplied_new_nodes(
            &self.new_nodes,
            &expected_new_nodes,
            self.target_version,
        )?;
        validate_stale_nodes(
            &self.stale_nodes,
            &derived.base,
            self.base_version,
            self.target_version,
        )?;
        Ok(())
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, JmtStorageUpdatePlanErrorV1> {
        derive_jmt_storage_update_plan_commitment_v1(self)
    }

    pub const fn plan_version(&self) -> u16 {
        self.plan_version
    }

    pub const fn storage_profile(&self) -> u16 {
        self.storage_profile
    }

    pub const fn tree_id(&self) -> CommitmentV3 {
        self.tree_id
    }

    pub const fn base_version(&self) -> u64 {
        self.base_version
    }

    pub const fn target_version(&self) -> u64 {
        self.target_version
    }

    pub const fn base_root(&self) -> CommitmentV3 {
        self.base_root
    }

    pub const fn post_root(&self) -> CommitmentV3 {
        self.post_root
    }

    pub const fn transition(&self) -> &ValidatedSparseMerkleBatchTransitionV1 {
        &self.transition
    }

    pub fn new_nodes(&self) -> &[JmtNodeRecordV1] {
        &self.new_nodes
    }

    pub fn stale_nodes(&self) -> &[JmtStaleNodeIndexV1] {
        &self.stale_nodes
    }
}

impl<'de> Deserialize<'de> for ValidatedJmtStorageUpdatePlanV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = JmtStorageUpdatePlanWireV1::deserialize(deserializer)?;
        Self::new(JmtStorageUpdatePlanInputV1 {
            plan_version: wire.plan_version,
            storage_profile: wire.storage_profile,
            tree_id: wire.tree_id,
            base_version: wire.base_version,
            target_version: wire.target_version,
            base_root: wire.base_root,
            post_root: wire.post_root,
            transition: wire.transition,
            new_nodes: wire.new_nodes,
            stale_nodes: wire.stale_nodes,
        })
        .map_err(de::Error::custom)
    }
}

/// Derive the exact canonical target-version nibble-boundary node commitments
/// from a validated sparse-Merkle batch. Shared paths use the final sequential
/// write in the already-canonical batch.
pub fn derive_jmt_storage_new_nodes_v1(
    transition: &ValidatedSparseMerkleBatchTransitionV1,
    target_version: u64,
) -> Result<Vec<JmtNodeRecordV1>, JmtStorageUpdatePlanErrorV1> {
    transition.validate_self_consistency()?;
    let derived = derive_boundary_maps(transition)?;
    materialize_new_nodes(&derived.post, target_version)
}

pub fn encode_jmt_storage_update_plan_v1(
    plan: &ValidatedJmtStorageUpdatePlanV1,
) -> Result<Vec<u8>, JmtStorageUpdatePlanErrorV1> {
    plan.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(plan)
        .map_err(|_| JmtStorageUpdatePlanErrorV1::PostcardEncode)?;
    if bytes.len() > MAX_JMT_STORAGE_UPDATE_PLAN_BYTES_V1 {
        return Err(JmtStorageUpdatePlanErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_JMT_STORAGE_UPDATE_PLAN_BYTES_V1,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_jmt_storage_update_plan_v1(
    bytes: &[u8],
) -> Result<ValidatedJmtStorageUpdatePlanV1, JmtStorageUpdatePlanErrorV1> {
    require_bounded_input(bytes)?;
    let (plan, remainder) =
        postcard::take_from_bytes::<ValidatedJmtStorageUpdatePlanV1>(bytes)
            .map_err(|_| JmtStorageUpdatePlanErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(JmtStorageUpdatePlanErrorV1::TrailingBytes);
    }
    if encode_jmt_storage_update_plan_v1(&plan)? != bytes {
        return Err(JmtStorageUpdatePlanErrorV1::NonCanonicalEncoding);
    }
    Ok(plan)
}

pub fn derive_jmt_storage_update_plan_commitment_v1(
    plan: &ValidatedJmtStorageUpdatePlanV1,
) -> Result<CommitmentV3, JmtStorageUpdatePlanErrorV1> {
    let bytes = encode_jmt_storage_update_plan_v1(plan)?;
    let domain_len = u16::try_from(JMT_STORAGE_UPDATE_PLAN_HASH_DOMAIN_V1.len())
        .map_err(|_| JmtStorageUpdatePlanErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_len.to_be_bytes());
    hasher.update(JMT_STORAGE_UPDATE_PLAN_HASH_DOMAIN_V1);
    hasher.update(bytes);
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| JmtStorageUpdatePlanErrorV1::DerivedZeroCommitment)
}

struct DerivedBoundaryMapsV1 {
    base: BTreeMap<JmtNibblePathV1, CommitmentV3>,
    post: BTreeMap<JmtNibblePathV1, CommitmentV3>,
}

fn derive_boundary_maps(
    transition: &ValidatedSparseMerkleBatchTransitionV1,
) -> Result<DerivedBoundaryMapsV1, JmtStorageUpdatePlanErrorV1> {
    let mut base = BTreeMap::new();
    let mut post = BTreeMap::new();

    for entry in transition.entries() {
        let witness = entry.witness();
        for (path, hash) in derive_witness_boundary_nodes(
            witness,
            witness.pre_value_hash(),
            witness.claimed_pre_root(),
            "pre",
        )? {
            base.entry(path).or_insert(hash);
        }
        for (path, hash) in derive_witness_boundary_nodes(
            witness,
            witness.post_value_hash(),
            witness.claimed_post_root(),
            "post",
        )? {
            let _ = post.insert(path, hash);
        }
    }

    Ok(DerivedBoundaryMapsV1 { base, post })
}

fn derive_witness_boundary_nodes(
    witness: &SparseMerkleCellTransitionWitnessV1,
    value_hash: ValueHashV2,
    expected_root: CommitmentV3,
    phase: &'static str,
) -> Result<Vec<(JmtNibblePathV1, CommitmentV3)>, JmtStorageUpdatePlanErrorV1> {
    let boundary_count = usize::from(JMT_NIBBLE_PATH_MAX_NIBBLES_V1)
        .checked_add(1)
        .ok_or(JmtStorageUpdatePlanErrorV1::ArithmeticOverflow(
            "boundary_count",
        ))?;
    let mut nodes = Vec::new();
    nodes.try_reserve_exact(boundary_count).map_err(|_| {
        JmtStorageUpdatePlanErrorV1::AllocationFailed("boundary_nodes")
    })?;

    let cell_key = witness.cell_key();
    let key_bytes = *cell_key.as_bytes();
    let mut current = derive_sparse_merkle_leaf_commitment_v1(cell_key, value_hash)?;
    nodes.push((
        JmtNibblePathV1::from_key_prefix(
            key_bytes,
            JMT_NIBBLE_PATH_MAX_NIBBLES_V1,
        )?,
        current,
    ));

    for depth in (0..SPARSE_MERKLE_TREE_DEPTH_V1).rev() {
        let path_byte = cell_key.as_bytes()[depth / 8];
        let path_bit = (path_byte >> (7 - (depth % 8))) & 1;
        let sibling = witness.sibling_commitments().as_array()[depth];
        current = if path_bit == 0 {
            derive_sparse_merkle_internal_commitment_v1(depth, current, sibling)?
        } else {
            derive_sparse_merkle_internal_commitment_v1(depth, sibling, current)?
        };

        if depth % 4 == 0 {
            let nibble_count = u8::try_from(depth / 4).map_err(|_| {
                JmtStorageUpdatePlanErrorV1::ArithmeticOverflow(
                    "nibble_boundary",
                )
            })?;
            nodes.push((
                JmtNibblePathV1::from_key_prefix(key_bytes, nibble_count)?,
                current,
            ));
        }
    }

    if current != expected_root {
        return Err(JmtStorageUpdatePlanErrorV1::BoundaryRootMismatch(
            phase,
        ));
    }
    if nodes.len() != boundary_count {
        return Err(JmtStorageUpdatePlanErrorV1::ArithmeticOverflow(
            "derived_boundary_count",
        ));
    }
    Ok(nodes)
}

fn materialize_new_nodes(
    post: &BTreeMap<JmtNibblePathV1, CommitmentV3>,
    target_version: u64,
) -> Result<Vec<JmtNodeRecordV1>, JmtStorageUpdatePlanErrorV1> {
    require_new_node_count(post.len())?;
    let mut nodes = Vec::new();
    nodes.try_reserve_exact(post.len()).map_err(|_| {
        JmtStorageUpdatePlanErrorV1::AllocationFailed("derived_new_nodes")
    })?;
    for (path, hash) in post {
        nodes.push(JmtNodeRecordV1::new(
            JmtNodeKeyV1::new(target_version, *path),
            *hash,
        ));
    }
    Ok(nodes)
}

fn validate_supplied_new_nodes(
    actual: &[JmtNodeRecordV1],
    expected: &[JmtNodeRecordV1],
    target_version: u64,
) -> Result<(), JmtStorageUpdatePlanErrorV1> {
    for (index, node) in actual.iter().enumerate() {
        let version = node.node_key().version();
        if version != target_version {
            return Err(JmtStorageUpdatePlanErrorV1::NewNodeVersionMismatch {
                index,
                actual: version,
                expected: target_version,
            });
        }
    }
    for (offset, pair) in actual.windows(2).enumerate() {
        let index = next_index(offset)?;
        match compare_node_keys(pair[0].node_key(), pair[1].node_key()) {
            Ordering::Equal => {
                return Err(JmtStorageUpdatePlanErrorV1::DuplicateNewNodeKey {
                    index,
                });
            }
            Ordering::Greater => {
                return Err(
                    JmtStorageUpdatePlanErrorV1::NonCanonicalNewNodeOrder {
                        index,
                    },
                );
            }
            Ordering::Less => {}
        }
    }
    if actual.len() != expected.len() {
        return Err(JmtStorageUpdatePlanErrorV1::NewNodeCountMismatch {
            actual: actual.len(),
            expected: expected.len(),
        });
    }
    for (index, (actual_node, expected_node)) in
        actual.iter().zip(expected).enumerate()
    {
        if actual_node != expected_node {
            return Err(JmtStorageUpdatePlanErrorV1::NewNodeMismatch {
                index,
            });
        }
    }
    Ok(())
}

fn validate_stale_nodes(
    nodes: &[JmtStaleNodeIndexV1],
    base_nodes: &BTreeMap<JmtNibblePathV1, CommitmentV3>,
    base_version: u64,
    target_version: u64,
) -> Result<(), JmtStorageUpdatePlanErrorV1> {
    for (index, stale) in nodes.iter().enumerate() {
        let actual = stale.stale_since_version();
        if actual != target_version {
            return Err(
                JmtStorageUpdatePlanErrorV1::StaleSinceVersionMismatch {
                    index,
                    actual,
                    expected: target_version,
                },
            );
        }
        let node_version = stale.node_key().version();
        if node_version > base_version {
            return Err(JmtStorageUpdatePlanErrorV1::FutureStaleNode {
                index,
                node_version,
                base_version,
            });
        }
    }
    for (offset, pair) in nodes.windows(2).enumerate() {
        let index = next_index(offset)?;
        match pair[0]
            .node_key()
            .nibble_path()
            .cmp(&pair[1].node_key().nibble_path())
        {
            Ordering::Equal => {
                return Err(JmtStorageUpdatePlanErrorV1::DuplicateStalePath {
                    index,
                });
            }
            Ordering::Greater => {
                return Err(
                    JmtStorageUpdatePlanErrorV1::NonCanonicalStaleNodeOrder {
                        index,
                    },
                );
            }
            Ordering::Less => {}
        }
    }
    for (index, stale) in nodes.iter().enumerate() {
        let path = stale.node_key().nibble_path();
        let expected = base_nodes
            .get(&path)
            .ok_or(JmtStorageUpdatePlanErrorV1::UntouchedStalePath {
                index,
            })?;
        if stale.expected_node_hash() != *expected {
            return Err(JmtStorageUpdatePlanErrorV1::StaleNodeHashMismatch {
                index,
            });
        }
    }
    Ok(())
}

fn compare_node_keys(left: JmtNodeKeyV1, right: JmtNodeKeyV1) -> Ordering {
    match left.version().cmp(&right.version()) {
        Ordering::Equal => left.nibble_path().cmp(&right.nibble_path()),
        ordering => ordering,
    }
}

fn compare_nibble_paths(left: JmtNibblePathV1, right: JmtNibblePathV1) -> Ordering {
    match left.packed_nibbles().cmp(right.packed_nibbles()) {
        Ordering::Equal => left.nibble_count().cmp(&right.nibble_count()),
        ordering => ordering,
    }
}

fn next_index(offset: usize) -> Result<usize, JmtStorageUpdatePlanErrorV1> {
    offset
        .checked_add(1)
        .ok_or(JmtStorageUpdatePlanErrorV1::ArithmeticOverflow(
            "ordered_index",
        ))
}

fn require_new_node_count(count: usize) -> Result<(), JmtStorageUpdatePlanErrorV1> {
    if count == 0 {
        return Err(JmtStorageUpdatePlanErrorV1::EmptyNewNodeBatch);
    }
    if count > MAX_JMT_STORAGE_NEW_NODES_V1 {
        return Err(JmtStorageUpdatePlanErrorV1::TooManyNewNodes {
            actual: count,
            maximum: MAX_JMT_STORAGE_NEW_NODES_V1,
        });
    }
    Ok(())
}

fn require_stale_node_count(count: usize) -> Result<(), JmtStorageUpdatePlanErrorV1> {
    if count > MAX_JMT_STORAGE_STALE_NODES_V1 {
        return Err(JmtStorageUpdatePlanErrorV1::TooManyStaleNodes {
            actual: count,
            maximum: MAX_JMT_STORAGE_STALE_NODES_V1,
        });
    }
    Ok(())
}

fn require_bounded_input(bytes: &[u8]) -> Result<(), JmtStorageUpdatePlanErrorV1> {
    if bytes.is_empty() {
        return Err(JmtStorageUpdatePlanErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_JMT_STORAGE_UPDATE_PLAN_BYTES_V1 {
        return Err(JmtStorageUpdatePlanErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_JMT_STORAGE_UPDATE_PLAN_BYTES_V1,
        });
    }
    Ok(())
}

fn deserialize_new_nodes<'de, D>(deserializer: D) -> Result<Vec<JmtNodeRecordV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct NewNodeVisitor;

    impl<'de> Visitor<'de> for NewNodeVisitor {
        type Value = Vec<JmtNodeRecordV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "1..={MAX_JMT_STORAGE_NEW_NODES_V1} JMT new node records"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence
                .size_hint()
                .ok_or_else(|| de::Error::custom("missing JMT new-node count"))?;
            require_new_node_count(declared).map_err(de::Error::custom)?;
            let mut nodes = Vec::new();
            nodes.try_reserve_exact(declared).map_err(|_| {
                de::Error::custom(JmtStorageUpdatePlanErrorV1::AllocationFailed(
                    "new_nodes",
                ))
            })?;
            for index in 0..declared {
                nodes.push(
                    sequence
                        .next_element()?
                        .ok_or_else(|| de::Error::invalid_length(index, &self))?,
                );
            }
            if sequence.next_element::<IgnoredAny>()?.is_some() {
                let excess = declared.checked_add(1).ok_or_else(|| {
                    de::Error::custom(JmtStorageUpdatePlanErrorV1::ArithmeticOverflow(
                        "new_node_count",
                    ))
                })?;
                return Err(de::Error::invalid_length(excess, &self));
            }
            Ok(nodes)
        }
    }

    deserializer.deserialize_seq(NewNodeVisitor)
}

fn deserialize_stale_nodes<'de, D>(deserializer: D) -> Result<Vec<JmtStaleNodeIndexV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct StaleNodeVisitor;

    impl<'de> Visitor<'de> for StaleNodeVisitor {
        type Value = Vec<JmtStaleNodeIndexV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "0..={MAX_JMT_STORAGE_STALE_NODES_V1} JMT stale node indices"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence
                .size_hint()
                .ok_or_else(|| de::Error::custom("missing JMT stale-node count"))?;
            require_stale_node_count(declared).map_err(de::Error::custom)?;
            let mut nodes = Vec::new();
            nodes.try_reserve_exact(declared).map_err(|_| {
                de::Error::custom(JmtStorageUpdatePlanErrorV1::AllocationFailed(
                    "stale_nodes",
                ))
            })?;
            for index in 0..declared {
                nodes.push(
                    sequence
                        .next_element()?
                        .ok_or_else(|| de::Error::invalid_length(index, &self))?,
                );
            }
            if sequence.next_element::<IgnoredAny>()?.is_some() {
                let excess = declared.checked_add(1).ok_or_else(|| {
                    de::Error::custom(JmtStorageUpdatePlanErrorV1::ArithmeticOverflow(
                        "stale_node_count",
                    ))
                })?;
                return Err(de::Error::invalid_length(excess, &self));
            }
            Ok(nodes)
        }
    }

    deserializer.deserialize_seq(StaleNodeVisitor)
}
