use std::collections::BTreeSet;
use std::fmt::Write;

use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{
    recursive_child_verification_claim_hash_v1, recursive_cross_shard_messages_root_v1,
    recursive_effect_summary_hash_v1, recursive_lane_state_vector_root_v1,
    recursive_receipt_ids_root_v1, RecursiveEffectSummaryV1, RECURSIVE_SPOT_LEAF_PROFILE_V1,
    RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, CommitmentV3, NodeKindV3, NodeLevelV3, ProgramIdV3,
};
use zenodex_zrpf_risc0_shared::{
    decode_exact_adapter_input_v1, project_policy_bound_v1_journal, risc0_image_words_to_bytes,
    source_transition_receipt_count_unit_id_v3, AdapterErrorV1, SourceKindV1, V1LeafAdapterInputV1,
    PINNED_SPOT_LEAF_IMAGE_ID_V1, V1_LEAF_ADAPTER_INPUT_SCHEMA_VERSION,
    V1_LEAF_ADAPTER_MAX_INPUT_BYTES, V1_SOURCE_JOURNAL_MAX_BYTES,
};

const ADAPTER_IMAGE_ID: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
const PRE_STATE_VECTOR_DOMAIN_V1: &[u8] = b"zenodex.risc0.recursive.pre_state_vector_root.v1";
const POST_STATE_VECTOR_DOMAIN_V1: &[u8] = b"zenodex.risc0.recursive.post_state_vector_root.v1";

fn root(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn summary() -> RecursiveEffectSummaryV1 {
    let empty_receipts = recursive_receipt_ids_root_v1(&[]).unwrap();
    let empty_messages = recursive_cross_shard_messages_root_v1(&[]).unwrap();
    RecursiveEffectSummaryV1 {
        summary_version: 1,
        lane_id: "spot-lane-1".to_owned(),
        lane_kind: "spot".to_owned(),
        chain_id: "zenodex-test".to_owned(),
        epoch_id: 17,
        proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1.to_owned(),
        risc0_image_id: PINNED_SPOT_LEAF_IMAGE_ID_V1,
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

fn encode(summary: &RecursiveEffectSummaryV1) -> Vec<u8> {
    postcard::to_allocvec(summary).unwrap()
}

fn hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(&mut encoded, "{byte:02x}").unwrap();
    }
    encoded
}

#[test]
fn current_spot_summary_projects_to_a_closed_compatibility_leaf() {
    let source = summary();
    let bytes = encode(&source);

    let projection =
        project_policy_bound_v1_journal(SourceKindV1::Spot, &bytes, 4, ADAPTER_IMAGE_ID).unwrap();

    assert_eq!(projection.journal.node_kind(), NodeKindV3::Leaf);
    assert_eq!(projection.journal.node_level(), NodeLevelV3::LEAF);
    assert_eq!(projection.journal.partition().start(), 4);
    assert_eq!(projection.journal.partition().end_exclusive(), 5);
    assert_eq!(projection.journal.leaf_count(), 1);
    assert_eq!(projection.journal.operation_count(), 1);
    assert_eq!(projection.journal.subtree_node_count(), 1);
    assert_eq!(
        projection.journal.count_unit_id(),
        source_transition_receipt_count_unit_id_v3().unwrap()
    );
    assert_eq!(
        projection.journal.actual_program_id(),
        ProgramIdV3::new(risc0_image_words_to_bytes(ADAPTER_IMAGE_ID)).unwrap()
    );
    assert_eq!(
        projection.source_binding.source_program_id(),
        ProgramIdV3::new(risc0_image_words_to_bytes(PINNED_SPOT_LEAF_IMAGE_ID_V1)).unwrap()
    );
    assert_eq!(
        projection.source_binding.source_claim_hash().into_bytes(),
        recursive_child_verification_claim_hash_v1(&PINNED_SPOT_LEAF_IMAGE_ID_V1, &bytes).unwrap()
    );
    assert_eq!(
        projection.source_binding.source_effect_hash().into_bytes(),
        recursive_effect_summary_hash_v1(&source)
    );
    projection.journal.validate().unwrap();
}

#[test]
fn spot_projection_matches_the_independent_cross_language_vector() {
    let source_bytes = encode(&summary());
    let projection =
        project_policy_bound_v1_journal(SourceKindV1::Spot, &source_bytes, 4, ADAPTER_IMAGE_ID)
            .unwrap();
    let journal_bytes = encode_node_journal_v3(&projection.journal).unwrap();

    assert_eq!(source_bytes.len(), 605);
    assert_eq!(
        hex(&Sha256::digest(&source_bytes)),
        "96f78b062f04c8d77e02335815b98ac220f81112cbf7793c22ad588dc0618103"
    );
    assert_eq!(
        hex(projection
            .source_binding
            .canonical_hash()
            .unwrap()
            .as_bytes()),
        "99af2b45e51e5f0a95f0d655bb844305ddcb57f41206f43bfb588da8d92d4705"
    );
    assert_eq!(
        hex(projection.journal.task_id().as_bytes()),
        "c7ddf09572c68cac733fd9457d53f45e9ae4f2a47860dfe017ae6b70bece91dc"
    );
    assert_eq!(
        hex(projection
            .journal
            .commitments()
            .canonical_hash()
            .unwrap()
            .as_bytes()),
        "33532707000fa8b33f194cca95f3070415b7df1769a252460562e501072e56be"
    );
    assert_eq!(
        hex(projection.journal.node_statement_hash().as_bytes()),
        "7bdbc7a88ccfa6d8544ea489f5cb113ef627acd90b77e3766d99fc0e753cc4a1"
    );
    assert_eq!(
        hex(projection.journal.canonical_hash().unwrap().as_bytes()),
        "1c54cfb1bb753dc898b6375563a0f8c8e223e0f9cc72f6154af6380b69a8ca53"
    );
    assert_eq!(journal_bytes.len(), 1_547);
    assert_eq!(
        hex(&Sha256::digest(journal_bytes)),
        "64ab9d838fd84fc3fec1643dba0c2c551746df35f96b1dd40b21753e77d6a1a3"
    );
}

#[test]
fn adapter_envelope_exact_decoder_is_bounded_canonical_and_versioned() {
    let input = V1LeafAdapterInputV1 {
        schema_version: V1_LEAF_ADAPTER_INPUT_SCHEMA_VERSION,
        source_kind: SourceKindV1::Spot,
        source_journal_bytes: encode(&summary()),
        assigned_leaf_ordinal: 4,
        expected_adapter_image_id: ADAPTER_IMAGE_ID,
    };
    let canonical = postcard::to_allocvec(&input).unwrap();
    assert_eq!(decode_exact_adapter_input_v1(&canonical).unwrap(), input);
    let mut unknown = serde_json::to_value(&input).unwrap();
    unknown["caller_selected_profile"] = serde_json::Value::from("unsafe");
    assert!(serde_json::from_value::<V1LeafAdapterInputV1>(unknown).is_err());

    let mut trailing = canonical.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_adapter_input_v1(&trailing),
        Err(AdapterErrorV1::TrailingBytes)
    );
    let mut nonminimal = vec![0x81, 0x00];
    nonminimal.extend_from_slice(&canonical[1..]);
    assert!(matches!(
        decode_exact_adapter_input_v1(&nonminimal),
        Err(AdapterErrorV1::PostcardDecode | AdapterErrorV1::NonCanonicalEncoding)
    ));
    assert_eq!(
        decode_exact_adapter_input_v1(&vec![0; V1_LEAF_ADAPTER_MAX_INPUT_BYTES + 1]),
        Err(AdapterErrorV1::AdapterInputTooLarge {
            actual: V1_LEAF_ADAPTER_MAX_INPUT_BYTES + 1,
            maximum: V1_LEAF_ADAPTER_MAX_INPUT_BYTES,
        })
    );

    let mut stale = input.clone();
    stale.schema_version = 2;
    assert_eq!(
        decode_exact_adapter_input_v1(&postcard::to_allocvec(&stale).unwrap()),
        Err(AdapterErrorV1::InvalidAdapterSchema(2))
    );
    let mut zero_image = input;
    zero_image.expected_adapter_image_id = [0; 8];
    assert_eq!(
        decode_exact_adapter_input_v1(&postcard::to_allocvec(&zero_image).unwrap()),
        Err(AdapterErrorV1::ZeroAdapterImageId)
    );
}

#[test]
fn spot_image_words_use_canonical_risc0_digest_byte_order() {
    assert_eq!(
        risc0_image_words_to_bytes(PINNED_SPOT_LEAF_IMAGE_ID_V1),
        [
            0x12, 0x75, 0xef, 0x41, 0x3f, 0x65, 0x13, 0xe7, 0x67, 0x1b, 0xce, 0x01, 0x9d, 0x22,
            0xfb, 0xdc, 0xf1, 0x0b, 0xff, 0xe1, 0xb7, 0x1d, 0xcf, 0x68, 0x73, 0x1a, 0x05, 0x6e,
            0x71, 0x0a, 0x74, 0x03,
        ]
    );
}

#[test]
fn adapter_manifest_identity_is_independent_of_source_lock_values() {
    let baseline = summary();
    let baseline_projection = project_policy_bound_v1_journal(
        SourceKindV1::Spot,
        &encode(&baseline),
        4,
        ADAPTER_IMAGE_ID,
    )
    .unwrap();
    let mut changed_locks = baseline;
    changed_locks.dependency_lock_hash[0] ^= 1;
    changed_locks.toolchain_lock_hash[0] ^= 1;
    let changed_projection = project_policy_bound_v1_journal(
        SourceKindV1::Spot,
        &encode(&changed_locks),
        4,
        ADAPTER_IMAGE_ID,
    )
    .unwrap();

    assert_eq!(
        baseline_projection.journal.program_manifest_root(),
        changed_projection.journal.program_manifest_root()
    );
    assert_ne!(
        baseline_projection.source_binding.canonical_hash().unwrap(),
        changed_projection.source_binding.canonical_hash().unwrap()
    );
    assert_ne!(
        baseline_projection.journal.node_statement_hash(),
        changed_projection.journal.node_statement_hash()
    );
}

#[test]
fn every_commitment_is_present_and_direct_v1_mappings_are_exact() {
    let source = summary();
    let bytes = encode(&source);
    let projection =
        project_policy_bound_v1_journal(SourceKindV1::Spot, &bytes, 4, ADAPTER_IMAGE_ID).unwrap();
    let commitments = serde_json::to_value(projection.journal.commitments()).unwrap();
    let object = commitments.as_object().unwrap();

    assert_eq!(object.len(), 23);
    let expected_fields: BTreeSet<&str> = [
        "pre_state_vector_root",
        "post_state_vector_root",
        "input_root",
        "transaction_root",
        "evidence_root",
        "provenance_root",
        "receipt_root",
        "accepted_receipts_root",
        "rejected_receipts_root",
        "effect_root",
        "write_set_root",
        "asset_delta_root",
        "cross_lane_outbox_root",
        "cross_lane_inbox_root",
        "cross_lane_message_ids_root",
        "conflict_schedule_hash",
        "data_availability_root",
        "data_availability_certificate_root",
        "carry_queue_pre_root",
        "carry_queue_post_root",
        "task_set_root",
        "semantic_source_set_root",
        "partition_plan_root",
    ]
    .into_iter()
    .collect();
    assert_eq!(
        object.keys().map(String::as_str).collect::<BTreeSet<_>>(),
        expected_fields
    );

    let expected_pre = recursive_lane_state_vector_root_v1(
        PRE_STATE_VECTOR_DOMAIN_V1,
        &[(source.lane_id.clone(), source.pre_state_root)],
    )
    .unwrap();
    let expected_post = recursive_lane_state_vector_root_v1(
        POST_STATE_VECTOR_DOMAIN_V1,
        &[(source.lane_id.clone(), source.post_state_root)],
    )
    .unwrap();
    let direct = [
        ("pre_state_vector_root", expected_pre),
        ("post_state_vector_root", expected_post),
        (
            "input_root",
            projection.source_binding.source_claim_hash().into_bytes(),
        ),
        ("transaction_root", source.tx_root),
        ("evidence_root", source.evidence_root),
        ("receipt_root", source.receipt_root),
        ("accepted_receipts_root", source.accepted_receipts_root),
        ("rejected_receipts_root", source.rejected_receipts_root),
        ("effect_root", recursive_effect_summary_hash_v1(&source)),
        ("write_set_root", source.write_set_root),
        ("asset_delta_root", source.asset_delta_root),
        ("cross_lane_outbox_root", source.cross_shard_outbox_root),
        ("cross_lane_inbox_root", source.cross_shard_inbox_root),
    ];
    for (field, expected) in direct {
        assert_eq!(object[field], serde_json::to_value(expected).unwrap());
    }
    for value in object.values() {
        assert_ne!(value, &serde_json::to_value([0u8; 32]).unwrap());
    }
    assert_ne!(
        object["data_availability_certificate_root"],
        object["carry_queue_pre_root"]
    );
    assert_ne!(
        object["carry_queue_pre_root"],
        object["carry_queue_post_root"]
    );
}

#[test]
fn wrong_image_profile_lane_and_summary_test_profile_reject() {
    let mut wrong_image = summary();
    wrong_image.risc0_image_id[0] ^= 1;
    assert_eq!(
        project_policy_bound_v1_journal(
            SourceKindV1::Spot,
            &encode(&wrong_image),
            0,
            ADAPTER_IMAGE_ID,
        ),
        Err(AdapterErrorV1::SourcePolicyMismatch("image_id"))
    );

    let mut wrong_profile = summary();
    wrong_profile.proof_profile = "wrong".to_owned();
    assert_eq!(
        project_policy_bound_v1_journal(
            SourceKindV1::Spot,
            &encode(&wrong_profile),
            0,
            ADAPTER_IMAGE_ID,
        ),
        Err(AdapterErrorV1::SourcePolicyMismatch("proof_profile"))
    );

    let mut wrong_lane = summary();
    wrong_lane.lane_kind = "perps_np".to_owned();
    assert_eq!(
        project_policy_bound_v1_journal(
            SourceKindV1::Spot,
            &encode(&wrong_lane),
            0,
            ADAPTER_IMAGE_ID,
        ),
        Err(AdapterErrorV1::SourcePolicyMismatch("lane_kind"))
    );

    let mut summary_test = summary();
    summary_test.proof_profile = RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1.to_owned();
    assert_eq!(
        project_policy_bound_v1_journal(
            SourceKindV1::Spot,
            &encode(&summary_test),
            0,
            ADAPTER_IMAGE_ID,
        ),
        Err(AdapterErrorV1::SourcePolicyMismatch("proof_profile"))
    );
}

#[test]
fn undisclosed_receipt_and_message_sets_reject() {
    let mut accepted = summary();
    accepted.accepted_receipts_root = root(91);
    assert_eq!(
        project_policy_bound_v1_journal(
            SourceKindV1::Spot,
            &encode(&accepted),
            0,
            ADAPTER_IMAGE_ID,
        ),
        Err(AdapterErrorV1::SourcePolicyMismatch(
            "accepted_receipts_root"
        ))
    );

    let mut outbox = summary();
    outbox.cross_shard_outbox_root = root(92);
    assert_eq!(
        project_policy_bound_v1_journal(SourceKindV1::Spot, &encode(&outbox), 0, ADAPTER_IMAGE_ID,),
        Err(AdapterErrorV1::SourcePolicyMismatch(
            "cross_shard_outbox_root"
        ))
    );

    let mut rejected = summary();
    rejected.rejected_receipts_root = root(93);
    assert_eq!(
        project_policy_bound_v1_journal(
            SourceKindV1::Spot,
            &encode(&rejected),
            0,
            ADAPTER_IMAGE_ID,
        ),
        Err(AdapterErrorV1::SourcePolicyMismatch(
            "rejected_receipts_root"
        ))
    );

    let mut inbox = summary();
    inbox.cross_shard_inbox_root = root(94);
    assert_eq!(
        project_policy_bound_v1_journal(SourceKindV1::Spot, &encode(&inbox), 0, ADAPTER_IMAGE_ID,),
        Err(AdapterErrorV1::SourcePolicyMismatch(
            "cross_shard_inbox_root"
        ))
    );
}

#[test]
fn zero_legacy_commitment_that_v1_shape_does_not_cover_rejects() {
    let mut source = summary();
    source.asset_delta_root = [0; 32];

    assert!(matches!(
        project_policy_bound_v1_journal(SourceKindV1::Spot, &encode(&source), 0, ADAPTER_IMAGE_ID,),
        Err(AdapterErrorV1::Protocol(_))
    ));
}

#[test]
fn exact_source_decoder_rejects_empty_oversize_trailing_and_nonminimal_bytes() {
    assert_eq!(
        project_policy_bound_v1_journal(SourceKindV1::Spot, &[], 0, ADAPTER_IMAGE_ID),
        Err(AdapterErrorV1::EmptySourceJournal)
    );
    let oversized = vec![0u8; V1_SOURCE_JOURNAL_MAX_BYTES + 1];
    assert_eq!(
        project_policy_bound_v1_journal(SourceKindV1::Spot, &oversized, 0, ADAPTER_IMAGE_ID),
        Err(AdapterErrorV1::SourceJournalTooLarge {
            actual: V1_SOURCE_JOURNAL_MAX_BYTES + 1,
            maximum: V1_SOURCE_JOURNAL_MAX_BYTES,
        })
    );

    let canonical = encode(&summary());
    let mut trailing = canonical.clone();
    trailing.push(0);
    assert_eq!(
        project_policy_bound_v1_journal(SourceKindV1::Spot, &trailing, 0, ADAPTER_IMAGE_ID),
        Err(AdapterErrorV1::TrailingBytes)
    );

    assert_eq!(canonical[0], 1);
    let mut nonminimal = vec![0x81, 0x00];
    nonminimal.extend_from_slice(&canonical[1..]);
    assert!(matches!(
        project_policy_bound_v1_journal(SourceKindV1::Spot, &nonminimal, 0, ADAPTER_IMAGE_ID),
        Err(AdapterErrorV1::PostcardDecode | AdapterErrorV1::NonCanonicalEncoding)
    ));
}

#[test]
fn ordinal_overflow_and_zero_adapter_image_reject() {
    let bytes = encode(&summary());
    assert_eq!(
        project_policy_bound_v1_journal(SourceKindV1::Spot, &bytes, u64::MAX, ADAPTER_IMAGE_ID),
        Err(AdapterErrorV1::AssignedLeafOrdinalOverflow)
    );
    assert!(matches!(
        project_policy_bound_v1_journal(SourceKindV1::Spot, &bytes, 0, [0; 8]),
        Err(AdapterErrorV1::Protocol(_))
    ));
}

#[test]
fn task_identity_is_source_bound_and_independent_of_partition_assignment() {
    let bytes = encode(&summary());
    let first =
        project_policy_bound_v1_journal(SourceKindV1::Spot, &bytes, 0, ADAPTER_IMAGE_ID).unwrap();
    let second =
        project_policy_bound_v1_journal(SourceKindV1::Spot, &bytes, 9, ADAPTER_IMAGE_ID).unwrap();

    assert_eq!(first.source_binding, second.source_binding);
    assert_eq!(first.journal.task_id(), second.journal.task_id());
    assert_ne!(first.journal.partition(), second.journal.partition());
    assert_ne!(
        first.journal.node_statement_hash(),
        second.journal.node_statement_hash()
    );
    assert_ne!(
        first.journal.canonical_hash().unwrap(),
        second.journal.canonical_hash().unwrap()
    );
}

#[test]
fn source_statement_mutation_changes_provenance_task_and_node_statement() {
    let original = summary();
    let mut changed = original.clone();
    changed.statement_hash[0] ^= 1;
    let original = project_policy_bound_v1_journal(
        SourceKindV1::Spot,
        &encode(&original),
        0,
        ADAPTER_IMAGE_ID,
    )
    .unwrap();
    let changed =
        project_policy_bound_v1_journal(SourceKindV1::Spot, &encode(&changed), 0, ADAPTER_IMAGE_ID)
            .unwrap();

    assert_ne!(
        original.source_binding.canonical_hash().unwrap(),
        changed.source_binding.canonical_hash().unwrap()
    );
    assert_ne!(original.journal.task_id(), changed.journal.task_id());
    assert_ne!(
        original.journal.commitments().provenance_root(),
        changed.journal.commitments().provenance_root()
    );
    assert_ne!(
        original.journal.node_statement_hash(),
        changed.journal.node_statement_hash()
    );
}

#[test]
fn compatibility_sentinels_are_nonzero_commitments() {
    let bytes = encode(&summary());
    let projection =
        project_policy_bound_v1_journal(SourceKindV1::Spot, &bytes, 0, ADAPTER_IMAGE_ID).unwrap();
    assert_ne!(
        projection
            .journal
            .commitments()
            .provenance_root()
            .into_bytes(),
        [0; 32]
    );
    assert_ne!(
        CommitmentV3::new(
            projection
                .journal
                .commitments()
                .data_availability_root()
                .into_bytes()
        )
        .unwrap()
        .into_bytes(),
        [0; 32]
    );
}
