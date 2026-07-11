use sha2::{Digest, Sha256};

use super::super::{
    write_bytes32, write_domain, write_u64, CommitmentV3, NodeCommitmentsV3, NodeJournalV3,
    NodeKindV3, NodeScopeV3, PartitionV3, ProfileIdV3, ProgramIdV3, TaskIdV3,
};
use super::hash::{
    v1_adapter_count_unit_id_v1, v1_adapter_empty_cross_shard_messages_root_v1,
    v1_adapter_empty_message_ids_root_v1, v1_adapter_empty_receipt_ids_root_v1,
    v1_adapter_manifest_root_v1, v1_adapter_node_statement_hash_v1,
    v1_adapter_partition_plan_root_v1, v1_adapter_profile_id_v1, v1_adapter_provenance_root_v1,
    v1_adapter_semantic_source_root_v1, v1_adapter_task_set_root_v1, V1AdapterNodeStatementInputV1,
    LEAF_RECORD_DOMAIN_V1,
};
use super::{SemanticEpochErrorV1, SemanticSourceIdV1, SourceClaimIdV1};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Untrusted opening for the V1 adapter's singleton semantic-source set.
///
/// The opening gains no authority on construction. `ProposedSemanticLeafV1`
/// accepts it only when its exact singleton root and the adapter statement both
/// match the structural leaf journal.
pub struct V1AdapterSemanticLeafOpeningV1 {
    semantic_source_binding_hash: CommitmentV3,
}

impl V1AdapterSemanticLeafOpeningV1 {
    pub const fn new(semantic_source_binding_hash: CommitmentV3) -> Self {
        Self {
            semantic_source_binding_hash,
        }
    }

    pub const fn semantic_source_binding_hash(self) -> CommitmentV3 {
        self.semantic_source_binding_hash
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Governed V1 adapter identity expected by a semantic projection caller.
///
/// This type is intentionally not deserializable. A future proof guest must
/// construct it from compiled or otherwise governed program policy.
pub struct ExpectedV1AdapterLeafIdentityV1 {
    adapter_program_id: ProgramIdV3,
    adapter_profile_id: ProfileIdV3,
    adapter_manifest_root: CommitmentV3,
    count_unit_id: CommitmentV3,
}

impl ExpectedV1AdapterLeafIdentityV1 {
    pub fn new(adapter_program_id: ProgramIdV3) -> Result<Self, SemanticEpochErrorV1> {
        Ok(Self {
            adapter_program_id,
            adapter_profile_id: v1_adapter_profile_id_v1()?,
            adapter_manifest_root: v1_adapter_manifest_root_v1(adapter_program_id)?,
            count_unit_id: v1_adapter_count_unit_id_v1()?,
        })
    }

    pub const fn adapter_program_id(self) -> ProgramIdV3 {
        self.adapter_program_id
    }

    pub const fn adapter_profile_id(self) -> ProfileIdV3 {
        self.adapter_profile_id
    }

    pub const fn adapter_manifest_root(self) -> CommitmentV3 {
        self.adapter_manifest_root
    }

    pub const fn count_unit_id(self) -> CommitmentV3 {
        self.count_unit_id
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Profile-specific semantic projection of one exact V1 adapter leaf journal.
///
/// Fields are private and this type is intentionally not deserializable. The
/// only public constructor validates the exact adapter profile, manifest,
/// count unit, task-set singleton, semantic-source singleton, and statement.
/// Receipt authentication remains a later guest/verifier responsibility.
///
/// ```compile_fail
/// fn requires_deserialize<T: for<'de> serde::Deserialize<'de>>() {}
/// requires_deserialize::<zenodex_zrpf_protocol_v3::ProposedSemanticLeafV1>();
/// ```
pub struct ProposedSemanticLeafV1 {
    partition: PartitionV3,
    operation_count: u64,
    count_unit_id: CommitmentV3,
    task_id: TaskIdV3,
    scope: NodeScopeV3,
    source_claim_id: SourceClaimIdV1,
    semantic_source_id: SemanticSourceIdV1,
    leaf_program_id: ProgramIdV3,
    leaf_profile_id: ProfileIdV3,
    leaf_statement_hash: CommitmentV3,
    leaf_program_manifest_root: CommitmentV3,
    commitments: NodeCommitmentsV3,
}

impl ProposedSemanticLeafV1 {
    pub fn bind_v1_adapter_journal(
        journal: &NodeJournalV3,
        opening: V1AdapterSemanticLeafOpeningV1,
        expected: &ExpectedV1AdapterLeafIdentityV1,
    ) -> Result<Self, SemanticEpochErrorV1> {
        journal.validate()?;
        if journal.node_kind() != NodeKindV3::Leaf {
            return Err(SemanticEpochErrorV1::LeafJournalRequired);
        }
        if journal.actual_program_id() != expected.adapter_program_id {
            return Err(SemanticEpochErrorV1::LeafProgramMismatch);
        }
        if journal.proof_profile_id() != expected.adapter_profile_id {
            return Err(SemanticEpochErrorV1::V1AdapterProfileMismatch);
        }
        if journal.program_manifest_root() != expected.adapter_manifest_root {
            return Err(SemanticEpochErrorV1::V1AdapterManifestMismatch);
        }
        if journal.count_unit_id() != expected.count_unit_id {
            return Err(SemanticEpochErrorV1::V1AdapterCountUnitMismatch);
        }
        let commitments = journal.commitments().clone();
        let commitment_input = commitments.to_input();
        let record = Self {
            partition: journal.partition(),
            operation_count: journal.operation_count(),
            count_unit_id: journal.count_unit_id(),
            task_id: journal.task_id(),
            scope: journal.scope().clone(),
            source_claim_id: SourceClaimIdV1::from_profile_bound_proposal(
                commitment_input.input_root,
            ),
            semantic_source_id: SemanticSourceIdV1::from_profile_bound_proposal(
                opening.semantic_source_binding_hash(),
            ),
            leaf_program_id: journal.actual_program_id(),
            leaf_profile_id: journal.proof_profile_id(),
            leaf_statement_hash: journal.node_statement_hash(),
            leaf_program_manifest_root: journal.program_manifest_root(),
            commitments,
        };
        record.validate_profile_projection()?;
        Ok(record)
    }

    pub(super) fn validate_profile_projection(&self) -> Result<(), SemanticEpochErrorV1> {
        let width = self
            .partition
            .end_exclusive()
            .checked_sub(self.partition.start())
            .ok_or(SemanticEpochErrorV1::NonSingletonLeafPartition)?;
        if width != 1 {
            return Err(SemanticEpochErrorV1::NonSingletonLeafPartition);
        }
        if self.operation_count != 1 {
            return Err(SemanticEpochErrorV1::InvalidLeafOperationCount);
        }
        let expected_profile = v1_adapter_profile_id_v1()?;
        if self.leaf_profile_id != expected_profile {
            return Err(SemanticEpochErrorV1::V1AdapterProfileMismatch);
        }
        let expected_count_unit = v1_adapter_count_unit_id_v1()?;
        if self.count_unit_id != expected_count_unit {
            return Err(SemanticEpochErrorV1::V1AdapterCountUnitMismatch);
        }
        let expected_manifest = v1_adapter_manifest_root_v1(self.leaf_program_id)?;
        if self.leaf_program_manifest_root != expected_manifest {
            return Err(SemanticEpochErrorV1::V1AdapterManifestMismatch);
        }
        let commitment_input = self.commitments.to_input();
        let semantic_source = self.semantic_source_id.into_commitment();
        let expected_provenance = v1_adapter_provenance_root_v1(semantic_source)?;
        if commitment_input.provenance_root != expected_provenance {
            return Err(SemanticEpochErrorV1::V1AdapterProvenanceMismatch);
        }
        let expected_task_set = v1_adapter_task_set_root_v1(self.task_id)?;
        if commitment_input.task_set_root != expected_task_set {
            return Err(SemanticEpochErrorV1::V1AdapterTaskSetMismatch);
        }
        let expected_semantic_source = v1_adapter_semantic_source_root_v1(semantic_source)?;
        if commitment_input.semantic_source_set_root != expected_semantic_source {
            return Err(SemanticEpochErrorV1::V1AdapterSemanticSourceMismatch);
        }
        let expected_partition_plan =
            v1_adapter_partition_plan_root_v1(self.task_id, self.partition)?;
        if commitment_input.partition_plan_root != expected_partition_plan {
            return Err(SemanticEpochErrorV1::V1AdapterPartitionPlanMismatch);
        }
        validate_empty_auxiliary_sets(&commitment_input)?;
        let expected_statement =
            v1_adapter_node_statement_hash_v1(V1AdapterNodeStatementInputV1 {
                adapter_program_id: self.leaf_program_id,
                adapter_profile_id: self.leaf_profile_id,
                adapter_manifest_root: self.leaf_program_manifest_root,
                source_binding_hash: semantic_source,
                scope_hash: self.scope.canonical_hash()?,
                task_id: self.task_id,
                partition: self.partition,
                count_unit_id: self.count_unit_id,
                commitments_hash: self.commitments.canonical_hash()?,
            })?;
        if self.leaf_statement_hash != expected_statement {
            return Err(SemanticEpochErrorV1::V1AdapterStatementMismatch);
        }
        Ok(())
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, SemanticEpochErrorV1> {
        self.validate_profile_projection()?;
        let commitments_hash = self.commitments.canonical_hash()?;
        let scope_hash = self.scope.canonical_hash()?;
        let mut hasher = Sha256::new();
        write_domain(&mut hasher, LEAF_RECORD_DOMAIN_V1)?;
        write_u64(&mut hasher, self.partition.start());
        write_u64(&mut hasher, self.partition.end_exclusive());
        write_u64(&mut hasher, self.operation_count);
        write_bytes32(&mut hasher, self.count_unit_id.as_bytes());
        write_bytes32(&mut hasher, self.task_id.as_bytes());
        write_bytes32(&mut hasher, scope_hash.as_bytes());
        write_bytes32(&mut hasher, self.source_claim_id.as_bytes());
        write_bytes32(&mut hasher, self.semantic_source_id.as_bytes());
        write_bytes32(&mut hasher, self.leaf_program_id.as_bytes());
        write_bytes32(&mut hasher, self.leaf_profile_id.as_bytes());
        write_bytes32(&mut hasher, self.leaf_statement_hash.as_bytes());
        write_bytes32(&mut hasher, self.leaf_program_manifest_root.as_bytes());
        write_bytes32(&mut hasher, commitments_hash.as_bytes());
        Ok(CommitmentV3::new(hasher.finalize().into())?)
    }

    pub const fn partition(&self) -> PartitionV3 {
        self.partition
    }

    pub const fn operation_count(&self) -> u64 {
        self.operation_count
    }

    pub const fn count_unit_id(&self) -> CommitmentV3 {
        self.count_unit_id
    }

    pub const fn task_id(&self) -> TaskIdV3 {
        self.task_id
    }

    pub const fn scope(&self) -> &NodeScopeV3 {
        &self.scope
    }

    pub const fn source_claim_id(&self) -> SourceClaimIdV1 {
        self.source_claim_id
    }

    pub const fn semantic_source_id(&self) -> SemanticSourceIdV1 {
        self.semantic_source_id
    }

    pub const fn leaf_program_id(&self) -> ProgramIdV3 {
        self.leaf_program_id
    }

    pub const fn leaf_profile_id(&self) -> ProfileIdV3 {
        self.leaf_profile_id
    }

    pub const fn leaf_statement_hash(&self) -> CommitmentV3 {
        self.leaf_statement_hash
    }

    pub const fn leaf_program_manifest_root(&self) -> CommitmentV3 {
        self.leaf_program_manifest_root
    }

    pub const fn commitments(&self) -> &NodeCommitmentsV3 {
        &self.commitments
    }
}

fn validate_empty_auxiliary_sets(
    commitments: &super::super::NodeCommitmentsInputV3,
) -> Result<(), SemanticEpochErrorV1> {
    let empty_receipts = v1_adapter_empty_receipt_ids_root_v1()?;
    for (field, actual) in [
        ("accepted_receipts_root", commitments.accepted_receipts_root),
        ("rejected_receipts_root", commitments.rejected_receipts_root),
    ] {
        if actual != empty_receipts {
            return Err(SemanticEpochErrorV1::V1AdapterAuxiliarySetMustBeEmpty(
                field,
            ));
        }
    }
    let empty_messages = v1_adapter_empty_cross_shard_messages_root_v1()?;
    for (field, actual) in [
        ("cross_lane_outbox_root", commitments.cross_lane_outbox_root),
        ("cross_lane_inbox_root", commitments.cross_lane_inbox_root),
    ] {
        if actual != empty_messages {
            return Err(SemanticEpochErrorV1::V1AdapterAuxiliarySetMustBeEmpty(
                field,
            ));
        }
    }
    if commitments.cross_lane_message_ids_root != v1_adapter_empty_message_ids_root_v1()? {
        return Err(SemanticEpochErrorV1::V1AdapterAuxiliarySetMustBeEmpty(
            "cross_lane_message_ids_root",
        ));
    }
    Ok(())
}
