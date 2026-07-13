use zenodex_zrpf_protocol_v3::{
    CommitmentV3, LeafNodeInputV3, NodeJournalV3, PartitionV3, ProfileIdV3, ProgramIdV3, TaskIdV3,
};

use crate::hashing_v1::{
    commitment, hash_fixed, hash_framed, profile_id_v3, program_id_from_risc0_words_v3,
    source_transition_receipt_count_unit_id_v3,
};
use crate::source_binding_v3::{derive_source_binding, derive_task_id};
use crate::source_policy_v2::{
    compatibility_source_policy_v1_shape, source_policy_v2, SourceKindV2, SourcePolicyV2,
};
use crate::v1_leaf_adapter::{
    decode_exact_source_summary, derive_commitments, derive_scope, enforce_source_policy,
    singleton_partition, CommitmentInputV1,
};
use crate::{AdapterErrorV1, SourceBindingV3};

pub const V2_LEAF_ADAPTER_PROFILE: &str = "zrpf_v2_leaf_adapter_compatibility_v2";

const ADAPTER_MANIFEST_DOMAIN_V2: &[u8] = b"zenodex.zrpf.v2_adapter_manifest.v2";
const ADAPTER_MANIFEST_CLASS_V2: &[u8] = b"unpromoted_current_source_compatibility_manifest";
const NODE_STATEMENT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.v2_adapter_node_statement.v2";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V2LeafProjectionV3 {
    pub source_binding: SourceBindingV3,
    pub journal: NodeJournalV3,
}

pub fn project_policy_bound_v2_journal(
    source_kind: SourceKindV2,
    source_journal_bytes: &[u8],
    assigned_leaf_ordinal: u64,
    expected_adapter_image_id: [u32; 8],
) -> Result<V2LeafProjectionV3, AdapterErrorV1> {
    let policy = source_policy_v2(source_kind)?;
    project_with_source_policy_v2(
        policy,
        source_journal_bytes,
        assigned_leaf_ordinal,
        expected_adapter_image_id,
    )
}

fn project_with_source_policy_v2(
    policy: &SourcePolicyV2,
    source_journal_bytes: &[u8],
    assigned_leaf_ordinal: u64,
    expected_adapter_image_id: [u32; 8],
) -> Result<V2LeafProjectionV3, AdapterErrorV1> {
    let compatibility_policy = compatibility_source_policy_v1_shape(policy);
    let summary = decode_exact_source_summary(source_journal_bytes)?;
    enforce_source_policy(&summary, &compatibility_policy)?;

    let partition = singleton_partition(assigned_leaf_ordinal)?;
    let scope = derive_scope(&summary)?;
    let scope_hash = scope.canonical_hash()?;
    let adapter_program_id = program_id_from_risc0_words_v3(expected_adapter_image_id)?;
    let adapter_profile_id = profile_id_v3(V2_LEAF_ADAPTER_PROFILE)?;
    let count_unit_id = source_transition_receipt_count_unit_id_v3()?;
    let source_binding = derive_source_binding(
        &summary,
        source_journal_bytes,
        &compatibility_policy,
        scope_hash,
    )?;
    let source_binding_hash = source_binding.canonical_hash()?;
    let task_id = derive_task_id(&source_binding)?;
    let program_manifest_root =
        derive_v2_adapter_manifest_root(adapter_program_id, adapter_profile_id)?;
    let commitments = derive_commitments(CommitmentInputV1 {
        summary: &summary,
        source_journal_bytes,
        source_binding: &source_binding,
        source_binding_hash,
        task_id,
        partition,
    })?;
    let node_statement_hash = derive_v2_node_statement_hash(NodeStatementInputV2 {
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

    Ok(V2LeafProjectionV3 {
        source_binding,
        journal,
    })
}

struct NodeStatementInputV2 {
    adapter_program_id: ProgramIdV3,
    adapter_profile_id: ProfileIdV3,
    adapter_manifest_root: CommitmentV3,
    source_binding_hash: CommitmentV3,
    scope_hash: CommitmentV3,
    task_id: TaskIdV3,
    partition: PartitionV3,
    count_unit_id: CommitmentV3,
    commitments_hash: CommitmentV3,
}

fn derive_v2_adapter_manifest_root(
    adapter_program_id: ProgramIdV3,
    adapter_profile_id: ProfileIdV3,
) -> Result<CommitmentV3, AdapterErrorV1> {
    commitment(hash_framed(
        ADAPTER_MANIFEST_DOMAIN_V2,
        &[
            adapter_program_id.as_bytes(),
            adapter_profile_id.as_bytes(),
            ADAPTER_MANIFEST_CLASS_V2,
        ],
    )?)
}

fn derive_v2_node_statement_hash(
    input: NodeStatementInputV2,
) -> Result<CommitmentV3, AdapterErrorV1> {
    commitment(hash_fixed(
        NODE_STATEMENT_DOMAIN_V2,
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

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use tau_state_proof_risc0_shared::{
        recursive_cross_shard_messages_root_v1, recursive_receipt_ids_root_v1,
        RecursiveEffectSummaryV1,
    };
    use zenodex_zrpf_protocol_v3::{
        ExpectedV1AdapterLeafIdentityV1, ExpectedV2AdapterLeafIdentityV2, NodeKindV3,
        ProposedSemanticLeafV1, SemanticEpochErrorV1, V1AdapterSemanticLeafOpeningV1,
        V2AdapterSemanticLeafOpeningV2,
    };

    use super::*;
    use crate::{profile_id_v3, AdapterErrorV1, SourcePolicyV2, CURRENT_SPOT_SOURCE_POLICY_V2};

    const SOURCE_IMAGE: [u32; 8] = [11, 12, 13, 14, 15, 16, 17, 18];
    const ADAPTER_IMAGE: [u32; 8] = [21, 22, 23, 24, 25, 26, 27, 28];

    fn root(seed: u8) -> [u8; 32] {
        [seed; 32]
    }

    fn policy() -> SourcePolicyV2 {
        SourcePolicyV2 {
            source_kind: SourceKindV2::Spot,
            proof_type: CURRENT_SPOT_SOURCE_POLICY_V2.proof_type,
            proof_profile: CURRENT_SPOT_SOURCE_POLICY_V2.proof_profile,
            lane_kind: CURRENT_SPOT_SOURCE_POLICY_V2.lane_kind,
            image_id: SOURCE_IMAGE,
            program_sha256: root(31),
            source_closure_root: root(32),
        }
    }

    fn summary() -> RecursiveEffectSummaryV1 {
        let empty_receipts = recursive_receipt_ids_root_v1(&[]).unwrap();
        let empty_messages = recursive_cross_shard_messages_root_v1(&[]).unwrap();
        RecursiveEffectSummaryV1 {
            summary_version: 1,
            lane_id: "spot-current-lane".to_string(),
            lane_kind: "spot".to_string(),
            chain_id: "zenodex-test".to_string(),
            epoch_id: 41,
            proof_profile: CURRENT_SPOT_SOURCE_POLICY_V2.proof_profile.to_string(),
            risc0_image_id: SOURCE_IMAGE,
            statement_hash: root(1),
            pre_state_root: root(2),
            post_state_root: root(3),
            tx_root: root(4),
            evidence_root: root(5),
            receipt_root: root(6),
            accepted_receipts_root: empty_receipts,
            rejected_receipts_root: empty_receipts,
            asset_delta_root: root(7),
            cross_shard_outbox_root: empty_messages,
            cross_shard_inbox_root: empty_messages,
            write_set_root: root(8),
            public_policy_hash: root(9),
            feature_suite_hash: root(10),
            dependency_lock_hash: root(11),
            toolchain_lock_hash: root(12),
        }
    }

    #[test]
    fn pending_policy_fails_closed_before_source_interpretation() {
        let result = project_policy_bound_v2_journal(SourceKindV2::Spot, &[0xff], 0, ADAPTER_IMAGE);
        assert_eq!(
            result,
            Err(AdapterErrorV1::SourcePolicyMismatch(
                "current_source_image_id_unpinned"
            ))
        );
    }

    #[test]
    fn candidate_policy_projects_under_distinct_v2_profile() {
        let source = postcard::to_allocvec(&summary()).unwrap();
        let projection =
            project_with_source_policy_v2(&policy(), &source, 7, ADAPTER_IMAGE).unwrap();

        assert_eq!(projection.journal.node_kind(), NodeKindV3::Leaf);
        assert_eq!(projection.journal.partition().start(), 7);
        assert_eq!(projection.journal.partition().end_exclusive(), 8);
        assert_eq!(
            projection.journal.proof_profile_id(),
            profile_id_v3(V2_LEAF_ADAPTER_PROFILE).unwrap()
        );
        assert_ne!(
            projection.journal.proof_profile_id(),
            profile_id_v3(crate::V1_LEAF_ADAPTER_PROFILE).unwrap()
        );
        assert_eq!(
            projection.source_binding.source_program_id().into_bytes(),
            {
                let mut bytes = [0u8; 32];
                for (chunk, word) in bytes.chunks_exact_mut(4).zip(SOURCE_IMAGE) {
                    chunk.copy_from_slice(&word.to_le_bytes());
                }
                bytes
            }
        );
        projection.journal.validate().unwrap();
        let source_binding_hash = projection.source_binding.canonical_hash().unwrap();
        let adapter_program_id = projection.journal.actual_program_id();
        let semantic_leaf = ProposedSemanticLeafV1::bind_v2_adapter_journal(
            &projection.journal,
            V2AdapterSemanticLeafOpeningV2::new(source_binding_hash),
            &ExpectedV2AdapterLeafIdentityV2::new(adapter_program_id).unwrap(),
        )
        .unwrap();
        assert_eq!(
            semantic_leaf.semantic_source_id().into_commitment(),
            source_binding_hash
        );
        assert_eq!(
            ProposedSemanticLeafV1::bind_v1_adapter_journal(
                &projection.journal,
                V1AdapterSemanticLeafOpeningV1::new(source_binding_hash),
                &ExpectedV1AdapterLeafIdentityV1::new(adapter_program_id).unwrap(),
            ),
            Err(SemanticEpochErrorV1::V1AdapterProfileMismatch)
        );
    }

    #[test]
    fn v2_input_codec_is_exact_versioned_and_bounded() {
        let input = crate::V2LeafAdapterInputV2 {
            schema_version: crate::V2_LEAF_ADAPTER_INPUT_SCHEMA_VERSION,
            source_kind: SourceKindV2::Spot,
            source_journal_bytes: postcard::to_allocvec(&summary()).unwrap(),
            assigned_leaf_ordinal: 7,
            expected_adapter_image_id: ADAPTER_IMAGE,
        };
        let canonical = postcard::to_allocvec(&input).unwrap();
        assert_eq!(
            crate::decode_exact_adapter_input_v2(&canonical).unwrap(),
            input
        );

        let mut trailing = canonical.clone();
        trailing.push(0);
        assert_eq!(
            crate::decode_exact_adapter_input_v2(&trailing),
            Err(AdapterErrorV1::TrailingBytes)
        );
        let mut stale = input;
        stale.schema_version = 1;
        assert_eq!(
            crate::decode_exact_adapter_input_v2(&postcard::to_allocvec(&stale).unwrap()),
            Err(AdapterErrorV1::InvalidAdapterSchema(1))
        );
    }
}
