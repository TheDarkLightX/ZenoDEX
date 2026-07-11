use alloc::vec::Vec;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::super::{
    write_bytes32, write_domain, write_u16, write_u64, CommitmentV3, NodeScopeV3, PartitionV3,
    ProfileIdV3, ProgramIdV3, MAX_LEAF_COUNT_V3, MAX_OPERATIONS_PER_ROOT_V3,
};
use super::hash::{
    semantic_profile_id_v1, v1_adapter_count_unit_id_v1, COMMITMENTS_HASH_DOMAIN_V1,
    EPOCH_ROOT_DOMAIN_V1, PROPOSAL_HASH_DOMAIN_V1,
};
use super::sets::{derive_epoch_commitments, validate_leaf_set};
use super::{
    ProposedSemanticLeafV1, SemanticEpochErrorV1, MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1,
    SEMANTIC_EPOCH_VERSION_V1,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticEpochCommitmentsV1 {
    pub(super) leaf_records_root: CommitmentV3,
    pub(super) pre_state_roots_root: CommitmentV3,
    pub(super) post_state_roots_root: CommitmentV3,
    pub(super) transaction_roots_root: CommitmentV3,
    pub(super) effect_roots_root: CommitmentV3,
    pub(super) asset_delta_roots_root: CommitmentV3,
    pub(super) source_claim_ids_root: CommitmentV3,
    pub(super) semantic_source_ids_root: CommitmentV3,
    pub(super) task_ids_root: CommitmentV3,
}

impl SemanticEpochCommitmentsV1 {
    pub fn canonical_hash(&self) -> Result<CommitmentV3, SemanticEpochErrorV1> {
        let mut hasher = Sha256::new();
        write_domain(&mut hasher, COMMITMENTS_HASH_DOMAIN_V1)?;
        for value in self.as_ordered_values() {
            write_bytes32(&mut hasher, value.as_bytes());
        }
        Ok(CommitmentV3::new(hasher.finalize().into())?)
    }

    fn as_ordered_values(&self) -> [CommitmentV3; 9] {
        [
            self.leaf_records_root,
            self.pre_state_roots_root,
            self.post_state_roots_root,
            self.transaction_roots_root,
            self.effect_roots_root,
            self.asset_delta_roots_root,
            self.source_claim_ids_root,
            self.semantic_source_ids_root,
            self.task_ids_root,
        ]
    }

    pub const fn leaf_records_root(&self) -> CommitmentV3 {
        self.leaf_records_root
    }

    pub const fn pre_state_roots_root(&self) -> CommitmentV3 {
        self.pre_state_roots_root
    }

    pub const fn post_state_roots_root(&self) -> CommitmentV3 {
        self.post_state_roots_root
    }

    pub const fn transaction_roots_root(&self) -> CommitmentV3 {
        self.transaction_roots_root
    }

    pub const fn effect_roots_root(&self) -> CommitmentV3 {
        self.effect_roots_root
    }

    pub const fn asset_delta_roots_root(&self) -> CommitmentV3 {
        self.asset_delta_roots_root
    }

    pub const fn source_claim_ids_root(&self) -> CommitmentV3 {
        self.source_claim_ids_root
    }

    pub const fn semantic_source_ids_root(&self) -> CommitmentV3 {
        self.semantic_source_ids_root
    }

    pub const fn task_ids_root(&self) -> CommitmentV3 {
        self.task_ids_root
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Untrusted inputs for deterministic semantic proposal construction.
///
/// The proof-tree root and semantic guest identity remain proposals until a
/// proof guest derives them from authenticated structural receipts and an outer
/// verifier authenticates the exact proposal bytes.
pub struct SemanticEpochProposalInputV1 {
    pub leaves: Vec<ProposedSemanticLeafV1>,
    pub proof_tree_root: CommitmentV3,
    pub scope: NodeScopeV3,
    pub actual_program_id: ProgramIdV3,
    pub program_manifest_root: CommitmentV3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
/// Self-consistent proof-system-neutral semantic epoch proposal.
///
/// Decoding and internal validation establish deterministic shape and hashing
/// only. This type deliberately has no conversion into an authenticated receipt
/// or ledger-admissible object.
///
/// ```compile_fail
/// fn requires_deserialize<T: for<'de> serde::Deserialize<'de>>() {}
/// requires_deserialize::<zenodex_zrpf_protocol_v3::ProposedSemanticEpochV1>();
/// ```
pub struct ProposedSemanticEpochV1 {
    semantic_version: u16,
    scope: NodeScopeV3,
    semantic_profile_id: ProfileIdV3,
    partition: PartitionV3,
    leaf_count: u64,
    operation_count: u64,
    count_unit_id: CommitmentV3,
    proof_tree_root: CommitmentV3,
    commitments: SemanticEpochCommitmentsV1,
    semantic_epoch_root: CommitmentV3,
    actual_program_id: ProgramIdV3,
    program_manifest_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProposedSemanticEpochWireV1 {
    semantic_version: u16,
    scope: NodeScopeV3,
    semantic_profile_id: ProfileIdV3,
    partition: PartitionV3,
    leaf_count: u64,
    operation_count: u64,
    count_unit_id: CommitmentV3,
    proof_tree_root: CommitmentV3,
    commitments: SemanticEpochCommitmentsV1,
    semantic_epoch_root: CommitmentV3,
    actual_program_id: ProgramIdV3,
    program_manifest_root: CommitmentV3,
}

impl ProposedSemanticEpochV1 {
    pub fn derive(input: SemanticEpochProposalInputV1) -> Result<Self, SemanticEpochErrorV1> {
        validate_leaf_set(&input.leaves, &input.scope)?;
        let leaf_count = u64::try_from(input.leaves.len())
            .map_err(|_| SemanticEpochErrorV1::ArithmeticOverflow("leaf_count"))?;
        let partition = PartitionV3::new(0, leaf_count)?;
        let operation_count = input.leaves.iter().try_fold(0_u64, |sum, leaf| {
            sum.checked_add(leaf.operation_count())
                .ok_or(SemanticEpochErrorV1::ArithmeticOverflow("operation_count"))
        })?;
        let count_unit_id = input
            .leaves
            .first()
            .ok_or(SemanticEpochErrorV1::EmptyLeaves)?
            .count_unit_id();
        let commitments = derive_epoch_commitments(&input.leaves)?;
        let semantic_profile_id = semantic_profile_id_v1()?;
        let semantic_epoch_root = derive_semantic_epoch_root(SemanticRootInputV1 {
            scope: &input.scope,
            semantic_profile_id,
            partition,
            leaf_count,
            operation_count,
            count_unit_id,
            commitments: &commitments,
        })?;
        let proposal = Self {
            semantic_version: SEMANTIC_EPOCH_VERSION_V1,
            scope: input.scope,
            semantic_profile_id,
            partition,
            leaf_count,
            operation_count,
            count_unit_id,
            proof_tree_root: input.proof_tree_root,
            commitments,
            semantic_epoch_root,
            actual_program_id: input.actual_program_id,
            program_manifest_root: input.program_manifest_root,
        };
        proposal.validate_self_consistency()?;
        Ok(proposal)
    }

    pub fn validate_self_consistency(&self) -> Result<(), SemanticEpochErrorV1> {
        if self.semantic_version != SEMANTIC_EPOCH_VERSION_V1 {
            return Err(SemanticEpochErrorV1::InvalidVersion(self.semantic_version));
        }
        if self.semantic_profile_id != semantic_profile_id_v1()? {
            return Err(SemanticEpochErrorV1::InvalidSemanticProfile);
        }
        self.scope.canonical_hash()?;
        if self.partition.start() != 0 {
            return Err(SemanticEpochErrorV1::PartitionMustStartAtZero);
        }
        if self.leaf_count == 0
            || self.leaf_count > MAX_LEAF_COUNT_V3
            || self.partition.end_exclusive() != self.leaf_count
            || self.operation_count != self.leaf_count
            || self.operation_count > MAX_OPERATIONS_PER_ROOT_V3
            || self.count_unit_id != v1_adapter_count_unit_id_v1()?
        {
            return Err(SemanticEpochErrorV1::InvalidProposalShape);
        }
        self.commitments.canonical_hash()?;
        let expected_root = derive_semantic_epoch_root(SemanticRootInputV1 {
            scope: &self.scope,
            semantic_profile_id: self.semantic_profile_id,
            partition: self.partition,
            leaf_count: self.leaf_count,
            operation_count: self.operation_count,
            count_unit_id: self.count_unit_id,
            commitments: &self.commitments,
        })?;
        if self.semantic_epoch_root != expected_root {
            return Err(SemanticEpochErrorV1::SemanticRootMismatch);
        }
        Ok(())
    }

    pub fn proposal_hash(&self) -> Result<CommitmentV3, SemanticEpochErrorV1> {
        self.validate_self_consistency()?;
        let scope_hash = self.scope.canonical_hash()?;
        let commitments_hash = self.commitments.canonical_hash()?;
        let mut hasher = Sha256::new();
        write_domain(&mut hasher, PROPOSAL_HASH_DOMAIN_V1)?;
        write_u16(&mut hasher, self.semantic_version);
        write_bytes32(&mut hasher, self.semantic_profile_id.as_bytes());
        write_bytes32(&mut hasher, scope_hash.as_bytes());
        write_u64(&mut hasher, self.partition.start());
        write_u64(&mut hasher, self.partition.end_exclusive());
        write_u64(&mut hasher, self.leaf_count);
        write_u64(&mut hasher, self.operation_count);
        write_bytes32(&mut hasher, self.count_unit_id.as_bytes());
        write_bytes32(&mut hasher, self.proof_tree_root.as_bytes());
        write_bytes32(&mut hasher, commitments_hash.as_bytes());
        write_bytes32(&mut hasher, self.semantic_epoch_root.as_bytes());
        write_bytes32(&mut hasher, self.actual_program_id.as_bytes());
        write_bytes32(&mut hasher, self.program_manifest_root.as_bytes());
        Ok(CommitmentV3::new(hasher.finalize().into())?)
    }

    pub const fn semantic_version(&self) -> u16 {
        self.semantic_version
    }

    pub const fn scope(&self) -> &NodeScopeV3 {
        &self.scope
    }

    pub const fn semantic_profile_id(&self) -> ProfileIdV3 {
        self.semantic_profile_id
    }

    pub const fn partition(&self) -> PartitionV3 {
        self.partition
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

    pub const fn proof_tree_root(&self) -> CommitmentV3 {
        self.proof_tree_root
    }

    pub const fn commitments(&self) -> &SemanticEpochCommitmentsV1 {
        &self.commitments
    }

    pub const fn semantic_epoch_root(&self) -> CommitmentV3 {
        self.semantic_epoch_root
    }

    pub const fn actual_program_id(&self) -> ProgramIdV3 {
        self.actual_program_id
    }

    pub const fn program_manifest_root(&self) -> CommitmentV3 {
        self.program_manifest_root
    }

    fn from_wire(wire: ProposedSemanticEpochWireV1) -> Result<Self, SemanticEpochErrorV1> {
        let proposal = Self {
            semantic_version: wire.semantic_version,
            scope: wire.scope,
            semantic_profile_id: wire.semantic_profile_id,
            partition: wire.partition,
            leaf_count: wire.leaf_count,
            operation_count: wire.operation_count,
            count_unit_id: wire.count_unit_id,
            proof_tree_root: wire.proof_tree_root,
            commitments: wire.commitments,
            semantic_epoch_root: wire.semantic_epoch_root,
            actual_program_id: wire.actual_program_id,
            program_manifest_root: wire.program_manifest_root,
        };
        proposal.validate_self_consistency()?;
        Ok(proposal)
    }
}

pub fn encode_semantic_epoch_proposal_v1(
    proposal: &ProposedSemanticEpochV1,
) -> Result<Vec<u8>, SemanticEpochErrorV1> {
    proposal.validate_self_consistency()?;
    postcard::to_allocvec(proposal).map_err(|_| SemanticEpochErrorV1::PostcardDecode)
}

pub fn decode_exact_semantic_epoch_proposal_v1(
    bytes: &[u8],
) -> Result<ProposedSemanticEpochV1, SemanticEpochErrorV1> {
    if bytes.len() > MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1 {
        return Err(SemanticEpochErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1,
        });
    }
    let (wire, remainder) = postcard::take_from_bytes::<ProposedSemanticEpochWireV1>(bytes)
        .map_err(|_| SemanticEpochErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(SemanticEpochErrorV1::TrailingBytes);
    }
    let proposal = ProposedSemanticEpochV1::from_wire(wire)?;
    let canonical = encode_semantic_epoch_proposal_v1(&proposal)?;
    if canonical.as_slice() != bytes {
        return Err(SemanticEpochErrorV1::NonCanonicalEncoding);
    }
    Ok(proposal)
}

struct SemanticRootInputV1<'a> {
    scope: &'a NodeScopeV3,
    semantic_profile_id: ProfileIdV3,
    partition: PartitionV3,
    leaf_count: u64,
    operation_count: u64,
    count_unit_id: CommitmentV3,
    commitments: &'a SemanticEpochCommitmentsV1,
}

fn derive_semantic_epoch_root(
    input: SemanticRootInputV1<'_>,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    let scope_hash = input.scope.canonical_hash()?;
    let commitments_hash = input.commitments.canonical_hash()?;
    let mut hasher = Sha256::new();
    write_domain(&mut hasher, EPOCH_ROOT_DOMAIN_V1)?;
    write_u16(&mut hasher, SEMANTIC_EPOCH_VERSION_V1);
    write_bytes32(&mut hasher, input.semantic_profile_id.as_bytes());
    write_bytes32(&mut hasher, scope_hash.as_bytes());
    write_u64(&mut hasher, input.partition.start());
    write_u64(&mut hasher, input.partition.end_exclusive());
    write_u64(&mut hasher, input.leaf_count);
    write_u64(&mut hasher, input.operation_count);
    write_bytes32(&mut hasher, input.count_unit_id.as_bytes());
    write_bytes32(&mut hasher, commitments_hash.as_bytes());
    Ok(CommitmentV3::new(hasher.finalize().into())?)
}
