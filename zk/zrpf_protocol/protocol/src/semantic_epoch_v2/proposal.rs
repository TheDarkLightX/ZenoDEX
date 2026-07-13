use alloc::vec::Vec;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::super::{
    derive_epoch_commitments, derive_semantic_epoch_root, semantic_epoch_profile_id_v1,
    v1_adapter_count_unit_id_v1, validate_leaf_set, CommitmentV3, NodeScopeV3, PartitionV3,
    ProfileIdV3, ProposedSemanticLeafV1, SemanticEpochCommitmentsV1, SemanticRootInputV1,
    MAX_LEAF_COUNT_V3, MAX_OPERATIONS_PER_ROOT_V3, SEMANTIC_EPOCH_VERSION_V1,
};
use super::{
    SemanticEpochErrorV2, MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2,
    SEMANTIC_EPOCH_PROPOSAL_SCHEMA_VERSION_V2,
};

const PROPOSAL_HASH_DOMAIN_V2: &[u8] = b"zenodex.zrpf.semantic_epoch_proposal_hash.v2";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticEpochProposalInputV2 {
    pub leaves: Vec<ProposedSemanticLeafV1>,
    pub proof_tree_root: CommitmentV3,
    pub scope: NodeScopeV3,
    pub dependency_manifest_root: CommitmentV3,
}

/// Proof-system-neutral semantic statement without a runtime self-image field.
///
/// The actual semantic guest image and full runtime manifest become available
/// only from the sealed `VerifiedSemanticEpochReceiptV2` host type.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ProposedSemanticEpochV2;
/// let proposal: ProposedSemanticEpochV2 = unimplemented!();
/// let _ = proposal.actual_program_id();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ProposedSemanticEpochV2;
/// let proposal: ProposedSemanticEpochV2 = unimplemented!();
/// let _ = proposal.program_manifest_root();
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProposedSemanticEpochV2 {
    proposal_schema_version: u16,
    semantic_statement_version: u16,
    scope: NodeScopeV3,
    semantic_profile_id: ProfileIdV3,
    partition: PartitionV3,
    leaf_count: u64,
    operation_count: u64,
    count_unit_id: CommitmentV3,
    proof_tree_root: CommitmentV3,
    commitments: SemanticEpochCommitmentsV1,
    semantic_epoch_root: CommitmentV3,
    dependency_manifest_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProposedSemanticEpochWireV2 {
    proposal_schema_version: u16,
    semantic_statement_version: u16,
    scope: NodeScopeV3,
    semantic_profile_id: ProfileIdV3,
    partition: PartitionV3,
    leaf_count: u64,
    operation_count: u64,
    count_unit_id: CommitmentV3,
    proof_tree_root: CommitmentV3,
    commitments: SemanticEpochCommitmentsV1,
    semantic_epoch_root: CommitmentV3,
    dependency_manifest_root: CommitmentV3,
}

impl ProposedSemanticEpochV2 {
    pub fn derive(input: SemanticEpochProposalInputV2) -> Result<Self, SemanticEpochErrorV2> {
        validate_leaf_set(&input.leaves, &input.scope)?;
        let leaf_count = u64::try_from(input.leaves.len())
            .map_err(|_| SemanticEpochErrorV2::ArithmeticOverflow("leaf_count"))?;
        let partition = PartitionV3::new(0, leaf_count)?;
        let operation_count = input.leaves.iter().try_fold(0_u64, |sum, leaf| {
            sum.checked_add(leaf.operation_count())
                .ok_or(SemanticEpochErrorV2::ArithmeticOverflow("operation_count"))
        })?;
        let count_unit_id = input
            .leaves
            .first()
            .ok_or(SemanticEpochErrorV2::InvalidProposalShape)?
            .count_unit_id();
        let commitments = derive_epoch_commitments(&input.leaves)?;
        let semantic_profile_id = semantic_epoch_profile_id_v1()?;
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
            proposal_schema_version: SEMANTIC_EPOCH_PROPOSAL_SCHEMA_VERSION_V2,
            semantic_statement_version: SEMANTIC_EPOCH_VERSION_V1,
            scope: input.scope,
            semantic_profile_id,
            partition,
            leaf_count,
            operation_count,
            count_unit_id,
            proof_tree_root: input.proof_tree_root,
            commitments,
            semantic_epoch_root,
            dependency_manifest_root: input.dependency_manifest_root,
        };
        proposal.validate_self_consistency()?;
        Ok(proposal)
    }

    pub fn validate_self_consistency(&self) -> Result<(), SemanticEpochErrorV2> {
        if self.proposal_schema_version != SEMANTIC_EPOCH_PROPOSAL_SCHEMA_VERSION_V2 {
            return Err(SemanticEpochErrorV2::InvalidProposalSchema(
                self.proposal_schema_version,
            ));
        }
        if self.semantic_statement_version != SEMANTIC_EPOCH_VERSION_V1 {
            return Err(SemanticEpochErrorV2::InvalidSemanticStatementVersion(
                self.semantic_statement_version,
            ));
        }
        if self.semantic_profile_id != semantic_epoch_profile_id_v1()? {
            return Err(SemanticEpochErrorV2::InvalidSemanticProfile);
        }
        self.scope.canonical_hash()?;
        if self.partition.start() != 0
            || self.leaf_count == 0
            || self.leaf_count > MAX_LEAF_COUNT_V3
            || self.partition.end_exclusive() != self.leaf_count
            || self.operation_count != self.leaf_count
            || self.operation_count > MAX_OPERATIONS_PER_ROOT_V3
            || self.count_unit_id != v1_adapter_count_unit_id_v1()?
        {
            return Err(SemanticEpochErrorV2::InvalidProposalShape);
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
            return Err(SemanticEpochErrorV2::SemanticRootMismatch);
        }
        Ok(())
    }

    pub fn proposal_hash(&self) -> Result<CommitmentV3, SemanticEpochErrorV2> {
        self.validate_self_consistency()?;
        let scope_hash = self.scope.canonical_hash()?;
        let commitments_hash = self.commitments.canonical_hash()?;
        let mut hasher = Sha256::new();
        write_domain(&mut hasher, PROPOSAL_HASH_DOMAIN_V2)?;
        hasher.update(self.proposal_schema_version.to_be_bytes());
        hasher.update(self.semantic_statement_version.to_be_bytes());
        hasher.update(self.semantic_profile_id.as_bytes());
        hasher.update(scope_hash.as_bytes());
        hasher.update(self.partition.start().to_be_bytes());
        hasher.update(self.partition.end_exclusive().to_be_bytes());
        hasher.update(self.leaf_count.to_be_bytes());
        hasher.update(self.operation_count.to_be_bytes());
        hasher.update(self.count_unit_id.as_bytes());
        hasher.update(self.proof_tree_root.as_bytes());
        hasher.update(commitments_hash.as_bytes());
        hasher.update(self.semantic_epoch_root.as_bytes());
        hasher.update(self.dependency_manifest_root.as_bytes());
        Ok(CommitmentV3::new(hasher.finalize().into())?)
    }

    pub const fn proposal_schema_version(&self) -> u16 {
        self.proposal_schema_version
    }

    pub const fn semantic_statement_version(&self) -> u16 {
        self.semantic_statement_version
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

    pub const fn dependency_manifest_root(&self) -> CommitmentV3 {
        self.dependency_manifest_root
    }

    fn from_wire(wire: ProposedSemanticEpochWireV2) -> Result<Self, SemanticEpochErrorV2> {
        let proposal = Self {
            proposal_schema_version: wire.proposal_schema_version,
            semantic_statement_version: wire.semantic_statement_version,
            scope: wire.scope,
            semantic_profile_id: wire.semantic_profile_id,
            partition: wire.partition,
            leaf_count: wire.leaf_count,
            operation_count: wire.operation_count,
            count_unit_id: wire.count_unit_id,
            proof_tree_root: wire.proof_tree_root,
            commitments: wire.commitments,
            semantic_epoch_root: wire.semantic_epoch_root,
            dependency_manifest_root: wire.dependency_manifest_root,
        };
        proposal.validate_self_consistency()?;
        Ok(proposal)
    }
}

pub fn encode_semantic_epoch_proposal_v2(
    proposal: &ProposedSemanticEpochV2,
) -> Result<Vec<u8>, SemanticEpochErrorV2> {
    proposal.validate_self_consistency()?;
    let bytes =
        postcard::to_allocvec(proposal).map_err(|_| SemanticEpochErrorV2::PostcardDecode)?;
    if bytes.len() > MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2 {
        return Err(SemanticEpochErrorV2::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_semantic_epoch_proposal_v2(
    bytes: &[u8],
) -> Result<ProposedSemanticEpochV2, SemanticEpochErrorV2> {
    if bytes.len() > MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2 {
        return Err(SemanticEpochErrorV2::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2,
        });
    }
    let (wire, remainder) = postcard::take_from_bytes::<ProposedSemanticEpochWireV2>(bytes)
        .map_err(|_| SemanticEpochErrorV2::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(SemanticEpochErrorV2::TrailingBytes);
    }
    let proposal = ProposedSemanticEpochV2::from_wire(wire)?;
    if encode_semantic_epoch_proposal_v2(&proposal)?.as_slice() != bytes {
        return Err(SemanticEpochErrorV2::NonCanonicalEncoding);
    }
    Ok(proposal)
}

fn write_domain(hasher: &mut Sha256, domain: &[u8]) -> Result<(), SemanticEpochErrorV2> {
    let length = u16::try_from(domain.len())
        .map_err(|_| SemanticEpochErrorV2::ArithmeticOverflow("proposal_hash_domain"))?;
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(())
}
