use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_node_journal_v4, decode_exact_semantic_subtree_v2, encode_node_journal_v3,
    encode_node_journal_v4, encode_semantic_subtree_v2, AggregateNodeInputV3, ApplicationIdV3,
    CommitmentV3, DomainIdV3, LeafNodeInputV3, NodeCommitmentsInputV3, NodeCommitmentsV3,
    NodeJournalInputV4, NodeJournalV3, NodeJournalV4, NodeScopeInputV3, NodeScopeV3, PartitionV3,
    ProfileIdV3, ProgramIdV3, ProjectedChildDescriptorV3, SemanticAssetFlowInputV2,
    SemanticAssetFlowV2, SemanticAuthorityUseInputV2, SemanticAuthorityUseV2,
    SemanticSubtreeInputV2, SemanticSubtreeV2, SemanticValueLeafRecordInputV2,
    SemanticValueLeafRecordV2, TaskIdV3, ValueNodeErrorV4, MAX_IMMEDIATE_CHILDREN_V3,
    MAX_NODE_JOURNAL_BYTES_V4, MAX_SEMANTIC_ASSET_FLOWS_V2, MAX_SEMANTIC_AUTHORITY_USES_V2,
    MAX_SEMANTIC_SUBTREE_BYTES_V2, MAX_SEMANTIC_VALUE_RECORDS_V2, NODE_JOURNAL_VERSION_V4,
};

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}

fn commitment_bytes(bytes: [u8; 32]) -> CommitmentV3 {
    CommitmentV3::new(bytes).unwrap()
}

fn indexed_commitment(prefix: u8, index: usize) -> CommitmentV3 {
    let mut bytes = [prefix.max(1); 32];
    bytes[30..].copy_from_slice(&(index as u16).to_be_bytes());
    commitment_bytes(bytes)
}

fn asset_id(index: usize) -> [u8; 32] {
    let mut bytes = [0; 32];
    bytes[30..].copy_from_slice(&((index + 1) as u16).to_be_bytes());
    bytes
}

fn program(seed: u8) -> ProgramIdV3 {
    ProgramIdV3::new([seed; 32]).unwrap()
}

fn profile(seed: u8) -> ProfileIdV3 {
    ProfileIdV3::new([seed; 32]).unwrap()
}

fn task(seed: u8) -> TaskIdV3 {
    TaskIdV3::new([seed; 32]).unwrap()
}

fn task_index(index: usize) -> TaskIdV3 {
    let mut bytes = [111; 32];
    bytes[30..].copy_from_slice(&(index as u16).to_be_bytes());
    TaskIdV3::new(bytes).unwrap()
}

fn scope() -> NodeScopeV3 {
    NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new([201; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([202; 32]).unwrap(),
        epoch_start: 77,
        epoch_end: 77,
        public_policy_hash: commitment(203),
        feature_suite_hash: commitment(204),
        dependency_lock_hash: commitment(205),
        toolchain_lock_hash: commitment(206),
    })
    .unwrap()
}

fn commitments(seed: u8) -> NodeCommitmentsV3 {
    let root = |index: u8| {
        let mut bytes = [seed.max(1); 32];
        bytes[0] = index.max(1);
        CommitmentV3::new(bytes).unwrap()
    };
    NodeCommitmentsV3::new(NodeCommitmentsInputV3 {
        pre_state_vector_root: root(1),
        post_state_vector_root: root(2),
        input_root: root(3),
        transaction_root: root(4),
        evidence_root: root(5),
        provenance_root: root(6),
        receipt_root: root(7),
        accepted_receipts_root: root(8),
        rejected_receipts_root: root(9),
        effect_root: root(10),
        write_set_root: root(11),
        asset_delta_root: root(12),
        cross_lane_outbox_root: root(13),
        cross_lane_inbox_root: root(14),
        cross_lane_message_ids_root: root(15),
        conflict_schedule_hash: root(16),
        data_availability_root: root(17),
        data_availability_certificate_root: root(18),
        carry_queue_pre_root: root(19),
        carry_queue_post_root: root(20),
        task_set_root: root(21),
        semantic_source_set_root: root(22),
        partition_plan_root: root(23),
    })
}

fn structural_leaf(start: u64, seed: u8) -> NodeJournalV3 {
    NodeJournalV3::new_leaf(LeafNodeInputV3 {
        task_id: task(seed),
        partition: PartitionV3::new(start, start + 1).unwrap(),
        operation_count: 1,
        count_unit_id: commitment(207),
        scope: scope(),
        proof_profile_id: profile(208),
        actual_program_id: program(seed.wrapping_add(1)),
        node_statement_hash: commitment(seed.wrapping_add(2)),
        program_manifest_root: commitment(seed.wrapping_add(3)),
        commitments: commitments(seed.wrapping_add(20)),
    })
    .unwrap()
}

fn descriptor(journal: &NodeJournalV3, claim_seed: u8) -> ProjectedChildDescriptorV3 {
    ProjectedChildDescriptorV3::project_canonical_journal(
        commitment(claim_seed),
        &encode_node_journal_v3(journal).unwrap(),
    )
    .unwrap()
}

fn structural_aggregate(children: Vec<NodeJournalV3>, seed: u8) -> NodeJournalV3 {
    let descriptors = children
        .iter()
        .enumerate()
        .map(|(index, child)| descriptor(child, 150 + index as u8))
        .collect();
    NodeJournalV3::new_aggregate(AggregateNodeInputV3 {
        children: descriptors,
        task_id: task(seed),
        count_unit_id: commitment(207),
        scope: scope(),
        proof_profile_id: profile(208),
        actual_program_id: program(seed.wrapping_add(1)),
        node_statement_hash: commitment(seed.wrapping_add(2)),
        program_manifest_root: commitment(seed.wrapping_add(3)),
        commitments: commitments(seed.wrapping_add(20)),
    })
    .unwrap()
}

fn leaf_record(
    start: u64,
    index: usize,
    raw_pre: CommitmentV3,
    raw_post: CommitmentV3,
) -> SemanticValueLeafRecordV2 {
    SemanticValueLeafRecordV2::new(SemanticValueLeafRecordInputV2 {
        partition: PartitionV3::new(start, start + 1).unwrap(),
        semantic_leaf_hash: indexed_commitment(10, index),
        source_claim_id: indexed_commitment(20, index),
        semantic_source_id: indexed_commitment(30, index),
        task_id: task_index(index),
        pre_state_vector_root: indexed_commitment(40, index),
        post_state_vector_root: indexed_commitment(50, index),
        transaction_root: indexed_commitment(60, index),
        effect_root: indexed_commitment(70, index),
        asset_delta_root: indexed_commitment(80, index),
        raw_pre_state_root: raw_pre,
        raw_post_state_root: raw_post,
    })
    .unwrap()
}

fn flow(
    index: usize,
    outflow_atoms: u128,
    inflow_atoms: u128,
    issued_atoms: u128,
    destroyed_atoms: u128,
) -> SemanticAssetFlowV2 {
    SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
        asset_id: asset_id(index),
        outflow_atoms,
        inflow_atoms,
        issued_atoms,
        destroyed_atoms,
    })
    .unwrap()
}

fn authority_use(
    record: &SemanticValueLeafRecordV2,
    index: usize,
    atoms: u128,
) -> SemanticAuthorityUseV2 {
    SemanticAuthorityUseV2::new(SemanticAuthorityUseInputV2 {
        source_claim_id: record.source_claim_id(),
        leaf_ordinal: record.partition().start(),
        asset_id: asset_id(index),
        atoms,
        legacy_authority_root: indexed_commitment(90, index),
    })
    .unwrap()
}

fn subtree_with_records(
    records: Vec<SemanticValueLeafRecordV2>,
    represented_row_count: u64,
    flows: Vec<SemanticAssetFlowV2>,
    uses: Vec<SemanticAuthorityUseV2>,
) -> Result<SemanticSubtreeV2, ValueNodeErrorV4> {
    let first = records.first().unwrap();
    let last = records.last().unwrap();
    SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: commitment(211),
        accounting_domain_id: commitment(212),
        atoms_unit_id: commitment(213),
        state_root_scheme_id: commitment(214),
        scope_hash: scope().canonical_hash().unwrap(),
        lane_id_hash: commitment(215),
        partition: PartitionV3::new(first.partition().start(), last.partition().end_exclusive())
            .unwrap(),
        raw_subtree_pre_state_root: first.raw_pre_state_root(),
        raw_subtree_post_state_root: last.raw_post_state_root(),
        represented_row_count,
        leaf_records: records,
        authority_grants_root: commitment(216),
        asset_flows: flows,
        authority_uses: uses,
    })
}

fn one_leaf_subtree() -> SemanticSubtreeV2 {
    let record = leaf_record(0, 0, commitment(101), commitment(102));
    subtree_with_records(vec![record], 1, vec![flow(0, 5, 5, 0, 0)], vec![]).unwrap()
}

fn two_leaf_subtree() -> SemanticSubtreeV2 {
    let first = leaf_record(0, 0, commitment(101), commitment(102));
    let second = leaf_record(1, 1, commitment(102), commitment(103));
    subtree_with_records(vec![first, second], 2, vec![flow(0, 9, 9, 0, 0)], vec![]).unwrap()
}

fn v4_leaf_with_proof_system(proof_system_seed: u8) -> NodeJournalV4 {
    v4_leaf_with_statement(proof_system_seed, 226)
}

fn v4_leaf_with_statement(proof_system_seed: u8, statement_seed: u8) -> NodeJournalV4 {
    NodeJournalV4::new(NodeJournalInputV4 {
        structural: structural_leaf(0, 1),
        semantic_subtree: one_leaf_subtree(),
        application_statement_hash: commitment(statement_seed),
        proof_profile_id: profile(217),
        actual_program_id: program(218),
        proof_system_id: commitment(proof_system_seed),
        receipt_security_profile_id: commitment(220),
        verifier_parameters_root: commitment(221),
        program_manifest_root: commitment(222),
        child_semantic_journal_hashes: vec![],
    })
    .unwrap()
}

fn v4_aggregate() -> NodeJournalV4 {
    let left = structural_leaf(0, 1);
    let right = structural_leaf(1, 11);
    NodeJournalV4::new(NodeJournalInputV4 {
        structural: structural_aggregate(vec![left, right], 41),
        semantic_subtree: two_leaf_subtree(),
        application_statement_hash: commitment(226),
        proof_profile_id: profile(217),
        actual_program_id: program(218),
        proof_system_id: commitment(219),
        receipt_security_profile_id: commitment(220),
        verifier_parameters_root: commitment(221),
        program_manifest_root: commitment(222),
        child_semantic_journal_hashes: vec![commitment(223), commitment(224)],
    })
    .unwrap()
}

fn hex(bytes: [u8; 32]) -> String {
    const ALPHABET: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(64);
    for byte in bytes {
        result.push(char::from(ALPHABET[usize::from(byte >> 4)]));
        result.push(char::from(ALPHABET[usize::from(byte & 0x0f)]));
    }
    result
}

fn mirror_domain(hasher: &mut Sha256, domain: &[u8]) {
    hasher.update((domain.len() as u16).to_be_bytes());
    hasher.update(domain);
}

fn mirror_commitment(hasher: &mut Sha256, value: CommitmentV3) {
    hasher.update(value.as_bytes());
}

fn mirror_v4_verifier_id(journal: &NodeJournalV4) -> CommitmentV3 {
    let mut hasher = Sha256::new();
    mirror_domain(&mut hasher, b"zenodex.zrpf.verifier_id.v4");
    hasher.update(journal.actual_program_id().as_bytes());
    hasher.update(journal.proof_profile_id().as_bytes());
    mirror_commitment(&mut hasher, journal.proof_system_id());
    mirror_commitment(&mut hasher, journal.receipt_security_profile_id());
    mirror_commitment(&mut hasher, journal.verifier_parameters_root());
    hasher.update(NODE_JOURNAL_VERSION_V4.to_be_bytes());
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

fn mirror_v4_statement_hash(journal: &NodeJournalV4) -> CommitmentV3 {
    let mut hasher = Sha256::new();
    mirror_domain(&mut hasher, b"zenodex.zrpf.semantic_statement_hash.v4");
    mirror_commitment(&mut hasher, journal.structural().canonical_hash().unwrap());
    mirror_commitment(
        &mut hasher,
        journal.semantic_subtree().canonical_hash().unwrap(),
    );
    mirror_commitment(&mut hasher, journal.application_statement_hash());
    hasher.update(journal.proof_profile_id().as_bytes());
    hasher.update(journal.actual_program_id().as_bytes());
    for value in [
        journal.proof_system_id(),
        journal.receipt_security_profile_id(),
        journal.verifier_parameters_root(),
        journal.program_manifest_root(),
        journal.child_semantic_journals_root(),
    ] {
        mirror_commitment(&mut hasher, value);
    }
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

fn mirror_v4_journal_hash(journal: &NodeJournalV4) -> CommitmentV3 {
    let mut hasher = Sha256::new();
    mirror_domain(&mut hasher, b"zenodex.zrpf.node_journal_hash.v4");
    hasher.update(NODE_JOURNAL_VERSION_V4.to_be_bytes());
    mirror_commitment(&mut hasher, journal.structural().canonical_hash().unwrap());
    mirror_commitment(
        &mut hasher,
        journal.semantic_subtree().canonical_hash().unwrap(),
    );
    mirror_commitment(&mut hasher, journal.application_statement_hash());
    hasher.update(journal.proof_profile_id().as_bytes());
    hasher.update(journal.actual_program_id().as_bytes());
    for value in [
        journal.proof_system_id(),
        journal.receipt_security_profile_id(),
        journal.verifier_parameters_root(),
        journal.verifier_id(),
        journal.semantic_statement_hash(),
        journal.program_manifest_root(),
    ] {
        mirror_commitment(&mut hasher, value);
    }
    hasher.update((journal.child_semantic_journal_hashes().len() as u32).to_be_bytes());
    for child_hash in journal.child_semantic_journal_hashes() {
        mirror_commitment(&mut hasher, *child_hash);
    }
    mirror_commitment(&mut hasher, journal.child_semantic_journals_root());
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

#[test]
fn semantic_subtree_exact_codec_roundtrips_checked_state_and_flows() {
    let subtree = two_leaf_subtree();
    let bytes = encode_semantic_subtree_v2(&subtree).unwrap();

    assert!(!bytes.is_empty());
    assert!(bytes.len() <= MAX_SEMANTIC_SUBTREE_BYTES_V2);
    assert_eq!(decode_exact_semantic_subtree_v2(&bytes).unwrap(), subtree);
    assert_eq!(subtree.leaf_count(), 2);
    assert_eq!(subtree.represented_row_count(), 2);
    assert_ne!(subtree.canonical_hash().unwrap().into_bytes(), [0; 32]);
}

#[test]
fn subtree_rejects_discontinuous_and_duplicate_leaf_identities() {
    let first = leaf_record(0, 0, commitment(101), commitment(102));
    let discontinuous = leaf_record(1, 1, commitment(104), commitment(105));
    assert_eq!(
        subtree_with_records(
            vec![first.clone(), discontinuous],
            1,
            vec![flow(0, 1, 1, 0, 0)],
            vec![],
        ),
        Err(ValueNodeErrorV4::StateDiscontinuity { ordinal: 1 })
    );

    let mut duplicate =
        serde_json::to_value(leaf_record(1, 1, commitment(102), commitment(103))).unwrap();
    duplicate["source_claim_id"] = serde_json::to_value(first.source_claim_id()).unwrap();
    let duplicate: SemanticValueLeafRecordV2 = serde_json::from_value(duplicate).unwrap();
    assert_eq!(
        subtree_with_records(vec![first, duplicate], 1, vec![flow(0, 1, 1, 0, 0)], vec![],),
        Err(ValueNodeErrorV4::DuplicateSourceClaim)
    );
}

#[test]
fn issued_flow_requires_exact_sorted_authority_uses() {
    let record = leaf_record(0, 0, commitment(101), commitment(102));
    assert_eq!(
        subtree_with_records(vec![record.clone()], 1, vec![flow(0, 0, 5, 5, 0)], vec![],),
        Err(ValueNodeErrorV4::IssuanceUseMismatch)
    );

    let valid = subtree_with_records(
        vec![record.clone()],
        1,
        vec![flow(0, 0, 5, 5, 0)],
        vec![authority_use(&record, 0, 5)],
    )
    .unwrap();
    assert_eq!(valid.authority_uses().len(), 1);

    let second = authority_use(&record, 1, 1);
    let first = authority_use(&record, 0, 5);
    assert_eq!(
        subtree_with_records(
            vec![record],
            2,
            vec![flow(0, 0, 5, 5, 0), flow(1, 0, 1, 1, 0)],
            vec![second, first],
        ),
        Err(ValueNodeErrorV4::NonCanonicalAuthorityUseOrder)
    );
}

#[test]
fn row_flow_and_authority_bounds_fail_closed() {
    let record = leaf_record(0, 0, commitment(101), commitment(102));
    let too_many_flows = (0..=MAX_SEMANTIC_ASSET_FLOWS_V2)
        .map(|index| flow(index, 1, 1, 0, 0))
        .collect();
    assert!(matches!(
        subtree_with_records(vec![record.clone()], 128, too_many_flows, vec![]),
        Err(ValueNodeErrorV4::TooManyAssetFlows { .. })
    ));

    let uses = (0..=MAX_SEMANTIC_AUTHORITY_USES_V2)
        .map(|index| authority_use(&record, index, 1))
        .collect();
    assert!(matches!(
        subtree_with_records(vec![record], 128, vec![flow(0, 0, 1, 1, 0)], uses),
        Err(ValueNodeErrorV4::TooManyAuthorityUses { .. })
    ));
}

#[test]
fn exact_subtree_codec_rejects_trailing_truncated_and_noncanonical_bytes() {
    let bytes = encode_semantic_subtree_v2(&two_leaf_subtree()).unwrap();
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_semantic_subtree_v2(&trailing),
        Err(ValueNodeErrorV4::TrailingBytes)
    );
    for end in 0..bytes.len() {
        assert!(decode_exact_semantic_subtree_v2(&bytes[..end]).is_err());
    }
    let mut nonminimal = vec![0x82, 0x00];
    nonminimal.extend_from_slice(&bytes[1..]);
    assert!(matches!(
        decode_exact_semantic_subtree_v2(&nonminimal),
        Err(ValueNodeErrorV4::PostcardDecode | ValueNodeErrorV4::NonCanonicalEncoding)
    ));
}

#[test]
fn bounded_sequence_decoders_reject_claimed_counts_before_payload_decode() {
    let bytes = encode_semantic_subtree_v2(&two_leaf_subtree()).unwrap();
    const LEAF_RECORD_COUNT_OFFSET: usize = 261;
    assert_eq!(bytes[LEAF_RECORD_COUNT_OFFSET], 2);
    let mut excessive_record_count = Vec::with_capacity(bytes.len() + 1);
    excessive_record_count.extend_from_slice(&bytes[..LEAF_RECORD_COUNT_OFFSET]);
    excessive_record_count.extend_from_slice(&[0x81, 0x01]);
    excessive_record_count.extend_from_slice(&bytes[LEAF_RECORD_COUNT_OFFSET + 1..]);
    assert_eq!(
        decode_exact_semantic_subtree_v2(&excessive_record_count),
        Err(ValueNodeErrorV4::PostcardDecode)
    );

    let mut excessive_flows = serde_json::to_value(two_leaf_subtree()).unwrap();
    let flow_json = serde_json::to_value(flow(0, 1, 1, 0, 0)).unwrap();
    excessive_flows["asset_flows"] =
        serde_json::Value::Array(vec![flow_json; MAX_SEMANTIC_ASSET_FLOWS_V2 + 1]);
    assert!(serde_json::from_value::<SemanticSubtreeV2>(excessive_flows).is_err());

    let mut excessive_children = serde_json::to_value(v4_aggregate()).unwrap();
    let child_hash = serde_json::to_value(commitment(223)).unwrap();
    excessive_children["child_semantic_journal_hashes"] =
        serde_json::Value::Array(vec![child_hash; MAX_IMMEDIATE_CHILDREN_V3 + 1]);
    assert!(serde_json::from_value::<NodeJournalV4>(excessive_children).is_err());
}

#[test]
fn v4_leaf_binds_structural_semantic_and_receipt_security_identity() {
    let journal = v4_leaf_with_proof_system(219);
    let bytes = encode_node_journal_v4(&journal).unwrap();

    assert_eq!(decode_exact_node_journal_v4(&bytes).unwrap(), journal);
    assert!(journal.child_semantic_journal_hashes().is_empty());
    assert_ne!(journal.verifier_id().into_bytes(), [0; 32]);
    assert_ne!(journal.semantic_statement_hash().into_bytes(), [0; 32]);

    let changed_application_statement = v4_leaf_with_statement(219, 227);
    assert_ne!(
        journal.semantic_statement_hash(),
        changed_application_statement.semantic_statement_hash()
    );
    assert_ne!(
        journal.canonical_hash().unwrap(),
        changed_application_statement.canonical_hash().unwrap()
    );

    let changed_system = v4_leaf_with_proof_system(225);
    assert_ne!(journal.verifier_id(), changed_system.verifier_id());
    assert_ne!(
        journal.semantic_statement_hash(),
        changed_system.semantic_statement_hash()
    );
    assert_ne!(
        journal.canonical_hash().unwrap(),
        changed_system.canonical_hash().unwrap()
    );
}

#[test]
fn v4_child_hash_count_and_uniqueness_are_structural_invariants() {
    let leaf = NodeJournalV4::new(NodeJournalInputV4 {
        structural: structural_leaf(0, 1),
        semantic_subtree: one_leaf_subtree(),
        application_statement_hash: commitment(226),
        proof_profile_id: profile(217),
        actual_program_id: program(218),
        proof_system_id: commitment(219),
        receipt_security_profile_id: commitment(220),
        verifier_parameters_root: commitment(221),
        program_manifest_root: commitment(222),
        child_semantic_journal_hashes: vec![commitment(223)],
    });
    assert_eq!(
        leaf,
        Err(ValueNodeErrorV4::InvalidChildSemanticJournalCount {
            actual: 1,
            expected: 0,
        })
    );

    let left = structural_leaf(0, 1);
    let right = structural_leaf(1, 11);
    let duplicate = NodeJournalV4::new(NodeJournalInputV4 {
        structural: structural_aggregate(vec![left, right], 41),
        semantic_subtree: two_leaf_subtree(),
        application_statement_hash: commitment(226),
        proof_profile_id: profile(217),
        actual_program_id: program(218),
        proof_system_id: commitment(219),
        receipt_security_profile_id: commitment(220),
        verifier_parameters_root: commitment(221),
        program_manifest_root: commitment(222),
        child_semantic_journal_hashes: vec![commitment(223), commitment(223)],
    });
    assert_eq!(
        duplicate,
        Err(ValueNodeErrorV4::DuplicateChildSemanticJournal)
    );
}

#[test]
fn v4_rejects_structural_semantic_partition_and_scope_relabeling() {
    let wrong_partition = NodeJournalV4::new(NodeJournalInputV4 {
        structural: structural_leaf(1, 1),
        semantic_subtree: one_leaf_subtree(),
        application_statement_hash: commitment(226),
        proof_profile_id: profile(217),
        actual_program_id: program(218),
        proof_system_id: commitment(219),
        receipt_security_profile_id: commitment(220),
        verifier_parameters_root: commitment(221),
        program_manifest_root: commitment(222),
        child_semantic_journal_hashes: vec![],
    });
    assert_eq!(
        wrong_partition,
        Err(ValueNodeErrorV4::StructuralPartitionMismatch)
    );

    let mut wrong_scope = serde_json::to_value(one_leaf_subtree()).unwrap();
    wrong_scope["scope_hash"] = serde_json::to_value(commitment(199)).unwrap();
    wrong_scope["value_subtree_root"] = serde_json::to_value(commitment(198)).unwrap();
    assert!(serde_json::from_value::<SemanticSubtreeV2>(wrong_scope).is_err());
}

#[test]
fn decoded_v4_cannot_relabel_verifier_statement_or_child_root() {
    let journal = v4_aggregate();
    for field in [
        "verifier_id",
        "semantic_statement_hash",
        "child_semantic_journals_root",
    ] {
        let mut mutated = serde_json::to_value(&journal).unwrap();
        mutated[field] = serde_json::to_value(commitment(199)).unwrap();
        assert!(serde_json::from_value::<NodeJournalV4>(mutated).is_err());
    }

    let mut unknown = serde_json::to_value(journal).unwrap();
    unknown["authority"] = serde_json::Value::Bool(true);
    assert!(serde_json::from_value::<NodeJournalV4>(unknown).is_err());
}

#[test]
fn every_v4_statement_identity_component_is_fail_closed_on_decode() {
    let journal = v4_aggregate();
    for field in [
        "application_statement_hash",
        "proof_profile_id",
        "actual_program_id",
        "proof_system_id",
        "receipt_security_profile_id",
        "verifier_parameters_root",
        "program_manifest_root",
    ] {
        let mut mutated = serde_json::to_value(&journal).unwrap();
        mutated[field] = serde_json::to_value(commitment(199)).unwrap();
        assert!(serde_json::from_value::<NodeJournalV4>(mutated).is_err());
    }
}

#[test]
fn semantic_root_is_topology_independent_while_v4_statement_binds_child_order() {
    let original = v4_aggregate();
    let swapped = NodeJournalV4::new(NodeJournalInputV4 {
        structural: original.structural().clone(),
        semantic_subtree: original.semantic_subtree().clone(),
        application_statement_hash: original.application_statement_hash(),
        proof_profile_id: original.proof_profile_id(),
        actual_program_id: original.actual_program_id(),
        proof_system_id: original.proof_system_id(),
        receipt_security_profile_id: original.receipt_security_profile_id(),
        verifier_parameters_root: original.verifier_parameters_root(),
        program_manifest_root: original.program_manifest_root(),
        child_semantic_journal_hashes: vec![commitment(224), commitment(223)],
    })
    .unwrap();

    assert_eq!(
        original.semantic_subtree().value_subtree_root(),
        swapped.semantic_subtree().value_subtree_root()
    );
    assert_ne!(
        original.child_semantic_journals_root(),
        swapped.child_semantic_journals_root()
    );
    assert_ne!(
        original.semantic_statement_hash(),
        swapped.semantic_statement_hash()
    );
    assert_ne!(
        original.canonical_hash().unwrap(),
        swapped.canonical_hash().unwrap()
    );
}

#[test]
fn exact_v4_codec_rejects_every_truncated_prefix_and_oversize() {
    let bytes = encode_node_journal_v4(&v4_aggregate()).unwrap();
    for end in 0..bytes.len() {
        assert!(decode_exact_node_journal_v4(&bytes[..end]).is_err());
    }
    assert_eq!(
        decode_exact_node_journal_v4(&vec![0; MAX_NODE_JOURNAL_BYTES_V4 + 1]),
        Err(ValueNodeErrorV4::InputTooLarge {
            actual: MAX_NODE_JOURNAL_BYTES_V4 + 1,
            maximum: MAX_NODE_JOURNAL_BYTES_V4,
        })
    );
}

#[test]
fn bounded_byte_mutation_cannot_preserve_the_v4_journal_hash_silently() {
    let journal = v4_aggregate();
    let expected_hash = journal.canonical_hash().unwrap();
    let bytes = encode_node_journal_v4(&journal).unwrap();
    for index in 0..bytes.len() {
        let mut mutated = bytes.clone();
        mutated[index] ^= 1;
        if let Ok(decoded) = decode_exact_node_journal_v4(&mutated) {
            assert_ne!(decoded.canonical_hash().unwrap(), expected_hash);
        }
    }
}

#[test]
fn maximum_semantic_summary_and_v4_journal_fit_the_governed_byte_caps() {
    let records = (0..MAX_SEMANTIC_VALUE_RECORDS_V2)
        .map(|index| {
            leaf_record(
                index as u64,
                index,
                indexed_commitment(100, index),
                indexed_commitment(100, index + 1),
            )
        })
        .collect::<Vec<_>>();
    let flows = (0..MAX_SEMANTIC_ASSET_FLOWS_V2)
        .map(|index| flow(index, u128::MAX, u128::MAX, 1, 0))
        .collect::<Vec<_>>();
    let uses = (0..MAX_SEMANTIC_AUTHORITY_USES_V2)
        .map(|index| authority_use(&records[index % records.len()], index, 1))
        .collect::<Vec<_>>();
    let subtree = subtree_with_records(records, 128, flows, uses).unwrap();
    let subtree_bytes = encode_semantic_subtree_v2(&subtree).unwrap();
    assert!(subtree_bytes.len() <= MAX_SEMANTIC_SUBTREE_BYTES_V2);

    let mut level_one_nodes = Vec::new();
    for group in 0..MAX_IMMEDIATE_CHILDREN_V3 {
        let leaves = (0..MAX_IMMEDIATE_CHILDREN_V3)
            .map(|child| {
                structural_leaf(
                    (group * MAX_IMMEDIATE_CHILDREN_V3 + child) as u64,
                    (group * MAX_IMMEDIATE_CHILDREN_V3 + child + 1) as u8,
                )
            })
            .collect();
        level_one_nodes.push(structural_aggregate(leaves, 70 + group as u8));
    }
    let root = structural_aggregate(level_one_nodes, 90);
    let journal = NodeJournalV4::new(NodeJournalInputV4 {
        structural: root,
        semantic_subtree: subtree,
        application_statement_hash: commitment(226),
        proof_profile_id: profile(217),
        actual_program_id: program(218),
        proof_system_id: commitment(219),
        receipt_security_profile_id: commitment(220),
        verifier_parameters_root: commitment(221),
        program_manifest_root: commitment(222),
        child_semantic_journal_hashes: (0..MAX_IMMEDIATE_CHILDREN_V3)
            .map(|index| indexed_commitment(230, index))
            .collect(),
    })
    .unwrap();
    let journal_bytes = encode_node_journal_v4(&journal).unwrap();
    assert!(journal_bytes.len() <= MAX_NODE_JOURNAL_BYTES_V4);
}

#[test]
fn semantic_subtree_and_v4_journal_hash_vectors_are_stable() {
    let subtree = two_leaf_subtree();
    let journal = v4_aggregate();

    assert_eq!(
        hex(subtree.value_subtree_root().into_bytes()),
        "d95434b68beecb47a87cb1875e4cbd1ba0ae17382ea0a0ed74c290e63794f30a"
    );
    assert_eq!(
        hex(subtree.canonical_hash().unwrap().into_bytes()),
        "918e52100c997049adf8971bf5749a8d4a05dd1be616b71ab84a807e18e71f8f"
    );
    assert_eq!(
        hex(journal.verifier_id().into_bytes()),
        "0d0ffc1ab18d49281d24178730b65efd5bf5e6f4c08098eaa9d2b3e2814422f1"
    );
    assert_eq!(
        hex(journal.semantic_statement_hash().into_bytes()),
        "2e39deccf78b15d00e9a4bb093885d10a230e0fc9aa6b221c6be28de11780d75"
    );
    assert_eq!(
        hex(journal.canonical_hash().unwrap().into_bytes()),
        "210af1ef25c1f027ec0e0823df534fd6a1932cf73e5df959139157b7f1e35028"
    );
    assert_eq!(journal.verifier_id(), mirror_v4_verifier_id(&journal));
    assert_eq!(
        journal.semantic_statement_hash(),
        mirror_v4_statement_hash(&journal)
    );
    assert_eq!(
        journal.canonical_hash().unwrap(),
        mirror_v4_journal_hash(&journal)
    );
}
