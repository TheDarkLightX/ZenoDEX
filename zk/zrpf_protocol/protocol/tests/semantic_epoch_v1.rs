use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_semantic_epoch_proposal_v1, decode_exact_semantic_epoch_proposal_v2,
    encode_semantic_epoch_proposal_v1, encode_semantic_epoch_proposal_v2,
    semantic_epoch_dependency_manifest_root_v2, semantic_epoch_manifest_root_v1,
    semantic_epoch_profile_id_v1, v1_adapter_count_unit_id_v1, v1_adapter_manifest_root_v1,
    v1_adapter_profile_id_v1, v1_adapter_semantic_source_root_v1, v1_adapter_task_set_root_v1,
    ApplicationIdV3, CommitmentV3, DomainIdV3, ExpectedV1AdapterLeafIdentityV1, LeafNodeInputV3,
    NodeCommitmentsInputV3, NodeCommitmentsV3, NodeJournalV3, NodeScopeInputV3, NodeScopeV3,
    PartitionV3, ProfileIdV3, ProgramIdV3, ProposedSemanticEpochV1, ProposedSemanticEpochV2,
    ProposedSemanticLeafV1, SemanticEpochDependencyProgramsInputV1,
    SemanticEpochDependencyProgramsV1, SemanticEpochErrorV1, SemanticEpochErrorV2,
    SemanticEpochProposalInputV1, SemanticEpochProposalInputV2, TaskIdV3,
    V1AdapterSemanticLeafOpeningV1, MAX_LEAF_COUNT_V3, MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1,
    MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2,
};

const PROFILE_ID_DOMAIN: &[u8] = b"zenodex.zrpf.profile_id.v3";
const COUNT_UNIT_ID_DOMAIN: &[u8] = b"zenodex.zrpf.count_unit_id.v3";
const ADAPTER_MANIFEST_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_manifest.v1";
const SEMANTIC_MANIFEST_DOMAIN: &[u8] = b"zenodex.zrpf.semantic_epoch_manifest.v1";
const ADAPTER_NODE_STATEMENT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_node_statement.v1";
const PROVENANCE_ROOT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_provenance_root.v1";
const TASK_SET_ROOT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_task_set_root.v1";
const SEMANTIC_SOURCE_ROOT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_semantic_source_set_root.v1";
const PARTITION_ENTRY_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_partition_entry.v1";
const PARTITION_PLAN_ROOT_DOMAIN: &[u8] = b"zenodex.zrpf.v1_adapter_partition_plan_root.v1";
const RECEIPT_IDS_ROOT_DOMAIN: &[u8] = b"zenodex.risc0.recursive.receipt_ids_root.v1";
const CROSS_SHARD_MESSAGES_ROOT_DOMAIN: &[u8] =
    b"zenodex.risc0.recursive.cross_shard_messages_root.v1";
const MESSAGE_IDS_ROOT_DOMAIN: &[u8] = b"zenodex.risc0.recursive.message_ids_root.v1";

#[derive(Clone, Copy)]
enum LeafFault {
    None,
    Profile,
    Manifest,
    CountUnit,
    Provenance,
    TaskSet,
    SemanticSourceSet,
    PartitionPlan,
    AcceptedReceipts,
    RejectedReceipts,
    Outbox,
    Inbox,
    MessageIds,
    OperationCount,
    Statement,
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed; 32]).unwrap()
}

fn task(seed: u8) -> TaskIdV3 {
    TaskIdV3::new([seed; 32]).unwrap()
}

fn program(seed: u8) -> ProgramIdV3 {
    ProgramIdV3::new([seed; 32]).unwrap()
}

fn profile(seed: u8) -> ProfileIdV3 {
    ProfileIdV3::new([seed; 32]).unwrap()
}

fn hex(bytes: [u8; 32]) -> String {
    let mut output = String::with_capacity(64);
    for byte in bytes {
        output.push_str(&format!("{byte:02x}"));
    }
    output
}

fn scope(seed: u8) -> NodeScopeV3 {
    NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new([seed; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([seed.wrapping_add(1); 32]).unwrap(),
        epoch_start: 7,
        epoch_end: 7,
        public_policy_hash: commitment(seed.wrapping_add(2)),
        feature_suite_hash: commitment(seed.wrapping_add(3)),
        dependency_lock_hash: commitment(seed.wrapping_add(4)),
        toolchain_lock_hash: commitment(seed.wrapping_add(5)),
    })
    .unwrap()
}

fn prefixed_domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn framed_hash(domain: &[u8], fields: &[&[u8]]) -> [u8; 32] {
    let mut hasher = prefixed_domain_hasher(domain);
    for field in fields {
        hasher.update(u32::try_from(field.len()).unwrap().to_be_bytes());
        hasher.update(field);
    }
    hasher.finalize().into()
}

fn fixed_hash(domain: &[u8], fields: &[&[u8]]) -> [u8; 32] {
    let mut hasher = prefixed_domain_hasher(domain);
    for field in fields {
        hasher.update(field);
    }
    hasher.finalize().into()
}

fn singleton_root(domain: &[u8], value: CommitmentV3) -> CommitmentV3 {
    let mut hasher = prefixed_domain_hasher(domain);
    hasher.update(1u32.to_be_bytes());
    hasher.update(value.as_bytes());
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

fn legacy_empty_root(domain: &[u8]) -> CommitmentV3 {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(0u32.to_be_bytes());
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

fn manual_adapter_profile() -> ProfileIdV3 {
    ProfileIdV3::new(framed_hash(
        PROFILE_ID_DOMAIN,
        &[b"zrpf_v1_leaf_adapter_compatibility_v1"],
    ))
    .unwrap()
}

fn manual_semantic_profile() -> ProfileIdV3 {
    ProfileIdV3::new(framed_hash(
        PROFILE_ID_DOMAIN,
        &[b"zrpf_semantic_v1_adapter_compatibility_v1"],
    ))
    .unwrap()
}

fn manual_count_unit() -> CommitmentV3 {
    CommitmentV3::new(framed_hash(
        COUNT_UNIT_ID_DOMAIN,
        &[b"source_transition_receipt"],
    ))
    .unwrap()
}

fn manual_manifest(program_id: ProgramIdV3) -> CommitmentV3 {
    CommitmentV3::new(framed_hash(
        ADAPTER_MANIFEST_DOMAIN,
        &[
            program_id.as_bytes(),
            manual_adapter_profile().as_bytes(),
            b"unreleased_compatibility_manifest",
        ],
    ))
    .unwrap()
}

fn semantic_dependencies() -> SemanticEpochDependencyProgramsV1 {
    SemanticEpochDependencyProgramsV1::new(SemanticEpochDependencyProgramsInputV1 {
        adapter_program_id: program(231),
        level_one_program_id: program(232),
        level_two_program_id: program(233),
    })
}

fn manual_semantic_manifest(
    program_id: ProgramIdV3,
    dependencies: SemanticEpochDependencyProgramsV1,
) -> CommitmentV3 {
    CommitmentV3::new(framed_hash(
        SEMANTIC_MANIFEST_DOMAIN,
        &[
            program_id.as_bytes(),
            manual_semantic_profile().as_bytes(),
            dependencies.adapter_program_id().as_bytes(),
            dependencies.level_one_program_id().as_bytes(),
            dependencies.level_two_program_id().as_bytes(),
            b"unreleased_semantic_epoch_manifest",
        ],
    ))
    .unwrap()
}

fn manual_partition_plan(task_id: TaskIdV3, partition: PartitionV3) -> CommitmentV3 {
    let start = partition.start().to_be_bytes();
    let end = partition.end_exclusive().to_be_bytes();
    let entry = CommitmentV3::new(fixed_hash(
        PARTITION_ENTRY_DOMAIN,
        &[task_id.as_bytes(), &start, &end],
    ))
    .unwrap();
    singleton_root(PARTITION_PLAN_ROOT_DOMAIN, entry)
}

#[allow(clippy::too_many_arguments)]
fn manual_statement(
    adapter_program_id: ProgramIdV3,
    adapter_profile_id: ProfileIdV3,
    adapter_manifest_root: CommitmentV3,
    source_binding_hash: CommitmentV3,
    scope_hash: CommitmentV3,
    task_id: TaskIdV3,
    partition: PartitionV3,
    count_unit_id: CommitmentV3,
    commitments_hash: CommitmentV3,
) -> CommitmentV3 {
    let start = partition.start().to_be_bytes();
    let end = partition.end_exclusive().to_be_bytes();
    let operation_count = 1u64.to_be_bytes();
    CommitmentV3::new(fixed_hash(
        ADAPTER_NODE_STATEMENT_DOMAIN,
        &[
            adapter_program_id.as_bytes(),
            adapter_profile_id.as_bytes(),
            adapter_manifest_root.as_bytes(),
            source_binding_hash.as_bytes(),
            scope_hash.as_bytes(),
            task_id.as_bytes(),
            &start,
            &end,
            &operation_count,
            count_unit_id.as_bytes(),
            commitments_hash.as_bytes(),
        ],
    ))
    .unwrap()
}

fn base_commitments(
    seed: u8,
    source_claim: CommitmentV3,
    semantic_source: CommitmentV3,
    task_id: TaskIdV3,
    partition: PartitionV3,
) -> NodeCommitmentsInputV3 {
    let root = |offset: u8| {
        let mut bytes = [seed; 32];
        bytes[0] = offset;
        CommitmentV3::new(bytes).unwrap()
    };
    let empty_receipts = legacy_empty_root(RECEIPT_IDS_ROOT_DOMAIN);
    let empty_messages = legacy_empty_root(CROSS_SHARD_MESSAGES_ROOT_DOMAIN);
    NodeCommitmentsInputV3 {
        pre_state_vector_root: root(1),
        post_state_vector_root: root(2),
        input_root: source_claim,
        transaction_root: root(4),
        evidence_root: root(5),
        provenance_root: singleton_root(PROVENANCE_ROOT_DOMAIN, semantic_source),
        receipt_root: root(7),
        accepted_receipts_root: empty_receipts,
        rejected_receipts_root: empty_receipts,
        effect_root: root(10),
        write_set_root: root(11),
        asset_delta_root: root(12),
        cross_lane_outbox_root: empty_messages,
        cross_lane_inbox_root: empty_messages,
        cross_lane_message_ids_root: legacy_empty_root(MESSAGE_IDS_ROOT_DOMAIN),
        conflict_schedule_hash: root(16),
        data_availability_root: root(17),
        data_availability_certificate_root: root(18),
        carry_queue_pre_root: root(19),
        carry_queue_post_root: root(20),
        task_set_root: singleton_root(
            TASK_SET_ROOT_DOMAIN,
            CommitmentV3::new(*task_id.as_bytes()).unwrap(),
        ),
        semantic_source_set_root: singleton_root(SEMANTIC_SOURCE_ROOT_DOMAIN, semantic_source),
        partition_plan_root: manual_partition_plan(task_id, partition),
    }
}

#[allow(clippy::too_many_arguments)]
fn leaf_journal(
    start: u64,
    task_seed: u8,
    source_claim_seed: u8,
    semantic_source_seed: u8,
    epoch_scope: NodeScopeV3,
    adapter_program: ProgramIdV3,
    fault: LeafFault,
) -> NodeJournalV3 {
    let task_id = task(task_seed);
    let semantic_source = commitment(semantic_source_seed);
    let partition = PartitionV3::new(start, start + 1).unwrap();
    let mut profile_id = manual_adapter_profile();
    let mut manifest_root = manual_manifest(adapter_program);
    let mut count_unit = manual_count_unit();
    let mut operation_count = 1;
    let mut commitment_input = base_commitments(
        task_seed.wrapping_add(80),
        commitment(source_claim_seed),
        semantic_source,
        task_id,
        partition,
    );
    match fault {
        LeafFault::None | LeafFault::Statement => {}
        LeafFault::Profile => profile_id = profile(170),
        LeafFault::Manifest => manifest_root = commitment(171),
        LeafFault::CountUnit => count_unit = commitment(172),
        LeafFault::Provenance => commitment_input.provenance_root = commitment(173),
        LeafFault::TaskSet => commitment_input.task_set_root = commitment(174),
        LeafFault::SemanticSourceSet => commitment_input.semantic_source_set_root = commitment(175),
        LeafFault::PartitionPlan => commitment_input.partition_plan_root = commitment(176),
        LeafFault::AcceptedReceipts => commitment_input.accepted_receipts_root = commitment(177),
        LeafFault::RejectedReceipts => commitment_input.rejected_receipts_root = commitment(179),
        LeafFault::Outbox => commitment_input.cross_lane_outbox_root = commitment(180),
        LeafFault::Inbox => commitment_input.cross_lane_inbox_root = commitment(181),
        LeafFault::MessageIds => commitment_input.cross_lane_message_ids_root = commitment(182),
        LeafFault::OperationCount => operation_count = 2,
    }
    let commitments = NodeCommitmentsV3::new(commitment_input);
    let mut statement = manual_statement(
        adapter_program,
        profile_id,
        manifest_root,
        semantic_source,
        epoch_scope.canonical_hash().unwrap(),
        task_id,
        partition,
        count_unit,
        commitments.canonical_hash().unwrap(),
    );
    if matches!(fault, LeafFault::Statement) {
        statement = commitment(178);
    }
    NodeJournalV3::new_leaf(LeafNodeInputV3 {
        task_id,
        partition,
        operation_count,
        count_unit_id: count_unit,
        scope: epoch_scope,
        proof_profile_id: profile_id,
        actual_program_id: adapter_program,
        node_statement_hash: statement,
        program_manifest_root: manifest_root,
        commitments,
    })
    .unwrap()
}

fn proposed_leaf(
    start: u64,
    task_seed: u8,
    source_claim_seed: u8,
    semantic_source_seed: u8,
    epoch_scope: NodeScopeV3,
) -> ProposedSemanticLeafV1 {
    proposed_leaf_with_program(
        start,
        task_seed,
        source_claim_seed,
        semantic_source_seed,
        epoch_scope,
        program(231),
    )
}

fn proposed_leaf_with_program(
    start: u64,
    task_seed: u8,
    source_claim_seed: u8,
    semantic_source_seed: u8,
    epoch_scope: NodeScopeV3,
    adapter_program: ProgramIdV3,
) -> ProposedSemanticLeafV1 {
    let journal = leaf_journal(
        start,
        task_seed,
        source_claim_seed,
        semantic_source_seed,
        epoch_scope,
        adapter_program,
        LeafFault::None,
    );
    ProposedSemanticLeafV1::bind_v1_adapter_journal(
        &journal,
        V1AdapterSemanticLeafOpeningV1::new(commitment(semantic_source_seed)),
        &ExpectedV1AdapterLeafIdentityV1::new(adapter_program).unwrap(),
    )
    .unwrap()
}

fn two_leaves() -> Vec<ProposedSemanticLeafV1> {
    let epoch_scope = scope(200);
    vec![
        proposed_leaf(0, 1, 41, 51, epoch_scope.clone()),
        proposed_leaf(1, 2, 42, 52, epoch_scope),
    ]
}

fn proposal_input(
    leaves: Vec<ProposedSemanticLeafV1>,
    proof_tree_seed: u8,
) -> SemanticEpochProposalInputV1 {
    SemanticEpochProposalInputV1 {
        leaves,
        proof_tree_root: commitment(proof_tree_seed),
        scope: scope(200),
        actual_program_id: program(241),
        program_manifest_root: commitment(242),
    }
}

#[test]
fn adapter_hash_mirror_matches_public_profile_helpers_and_legacy_empty_vectors() {
    assert_eq!(
        v1_adapter_profile_id_v1().unwrap(),
        manual_adapter_profile()
    );
    assert_eq!(v1_adapter_count_unit_id_v1().unwrap(), manual_count_unit());
    assert_eq!(
        semantic_epoch_profile_id_v1().unwrap(),
        manual_semantic_profile()
    );
    assert_eq!(
        semantic_epoch_manifest_root_v1(program(241), &semantic_dependencies()).unwrap(),
        manual_semantic_manifest(program(241), semantic_dependencies())
    );
    let swapped = SemanticEpochDependencyProgramsV1::new(SemanticEpochDependencyProgramsInputV1 {
        adapter_program_id: program(231),
        level_one_program_id: program(233),
        level_two_program_id: program(232),
    });
    assert_ne!(
        semantic_epoch_manifest_root_v1(program(241), &semantic_dependencies()).unwrap(),
        semantic_epoch_manifest_root_v1(program(241), &swapped).unwrap()
    );
    assert_eq!(
        v1_adapter_manifest_root_v1(program(231)).unwrap(),
        manual_manifest(program(231))
    );
    assert_eq!(
        v1_adapter_task_set_root_v1(task(1)).unwrap(),
        singleton_root(
            TASK_SET_ROOT_DOMAIN,
            CommitmentV3::new(*task(1).as_bytes()).unwrap()
        )
    );
    assert_eq!(
        v1_adapter_semantic_source_root_v1(commitment(51)).unwrap(),
        singleton_root(SEMANTIC_SOURCE_ROOT_DOMAIN, commitment(51))
    );
    assert_eq!(
        hex(manual_adapter_profile().into_bytes()),
        "8ce3044e0671823f37fd3c6370cb51677fd7d92425d2928700f651451dece421"
    );
    assert_eq!(
        hex(manual_count_unit().into_bytes()),
        "fc3f8bdba6c5e7647d5419a61af0ebd31582850020d88ea5aa8b987de8913a5f"
    );
    assert_eq!(
        hex(legacy_empty_root(RECEIPT_IDS_ROOT_DOMAIN).into_bytes()),
        "0703e0dc50174ed94bfd82b1b1e48e594d0cb155e543ca9f5dee3a5de556d165"
    );
    assert_eq!(
        hex(legacy_empty_root(CROSS_SHARD_MESSAGES_ROOT_DOMAIN).into_bytes()),
        "b0e66f5c5d096c83137c48f97d91a3664aca38c8c653eefa23cb24a89364ba3b"
    );
    assert_eq!(
        hex(legacy_empty_root(MESSAGE_IDS_ROOT_DOMAIN).into_bytes()),
        "6e095bf396e0574ae6af14227162b06d520004600fb53e49d63a82840fc487eb"
    );
}

#[test]
fn valid_semantic_proposal_round_trips_through_exact_bounded_codec() {
    let proposal = ProposedSemanticEpochV1::derive(proposal_input(two_leaves(), 243)).unwrap();
    let encoded = encode_semantic_epoch_proposal_v1(&proposal).unwrap();

    assert!(encoded.len() <= MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1);
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v1(&encoded).unwrap(),
        proposal
    );
    assert_eq!(proposal.partition(), PartitionV3::new(0, 2).unwrap());
    assert_eq!(proposal.leaf_count(), 2);
    assert_eq!(proposal.operation_count(), 2);
    assert_eq!(proposal.scope(), &scope(200));
    assert_eq!(proposal.actual_program_id(), program(241));
    assert_eq!(proposal.program_manifest_root(), commitment(242));
    assert_eq!(
        hex(proposal.semantic_profile_id().into_bytes()),
        "1f85ab429c2fd960e2ba02486b55a1055a735c11b9552e5672d9dee847016d29"
    );
    assert_ne!(proposal.semantic_epoch_root(), proposal.proof_tree_root());
    assert_ne!(
        proposal.commitments().source_claim_ids_root().into_bytes(),
        [0; 32]
    );
    assert_eq!(
        hex(proposal.semantic_epoch_root().into_bytes()),
        "0955053e6305585103d60a7a6429d06a991cc7c1552ed52fd155f807f0d5dff7"
    );
    assert_eq!(
        hex(proposal.proposal_hash().unwrap().into_bytes()),
        "785e4d7882eaa2590f6c21b92209433e92a73fb3ed2074932cc6e55b02b95023"
    );
}

#[test]
fn changing_only_proof_tree_root_preserves_semantic_root_for_identical_leaves() {
    let leaves = two_leaves();
    let left = ProposedSemanticEpochV1::derive(proposal_input(leaves.clone(), 243)).unwrap();
    let right = ProposedSemanticEpochV1::derive(proposal_input(leaves, 244)).unwrap();

    assert_eq!(left.semantic_epoch_root(), right.semantic_epoch_root());
    assert_ne!(left.proof_tree_root(), right.proof_tree_root());
    assert_ne!(
        left.proposal_hash().unwrap(),
        right.proposal_hash().unwrap()
    );
}

#[test]
fn duplicate_profile_bound_identities_reject_across_distinct_partitions() {
    let epoch_scope = scope(200);
    let duplicate_claim = vec![
        proposed_leaf(0, 1, 41, 51, epoch_scope.clone()),
        proposed_leaf(1, 2, 41, 52, epoch_scope.clone()),
    ];
    assert_eq!(
        ProposedSemanticEpochV1::derive(proposal_input(duplicate_claim, 243)),
        Err(SemanticEpochErrorV1::DuplicateSourceClaim)
    );

    let duplicate_source = vec![
        proposed_leaf(0, 1, 41, 51, epoch_scope.clone()),
        proposed_leaf(1, 2, 42, 51, epoch_scope.clone()),
    ];
    assert_eq!(
        ProposedSemanticEpochV1::derive(proposal_input(duplicate_source, 243)),
        Err(SemanticEpochErrorV1::DuplicateSemanticSource)
    );

    let duplicate_task = vec![
        proposed_leaf(0, 1, 41, 51, epoch_scope.clone()),
        proposed_leaf(1, 1, 42, 52, epoch_scope),
    ];
    assert_eq!(
        ProposedSemanticEpochV1::derive(proposal_input(duplicate_task, 243)),
        Err(SemanticEpochErrorV1::DuplicateTask)
    );
}

#[test]
fn dense_zero_origin_scope_and_adapter_program_are_mandatory() {
    let mut reordered = two_leaves();
    reordered.reverse();
    assert_eq!(
        ProposedSemanticEpochV1::derive(proposal_input(reordered, 243)),
        Err(SemanticEpochErrorV1::NonCanonicalLeafOrder)
    );

    let epoch_scope = scope(200);
    let nonzero_origin = vec![proposed_leaf(1, 1, 41, 51, epoch_scope.clone())];
    assert_eq!(
        ProposedSemanticEpochV1::derive(proposal_input(nonzero_origin, 243)),
        Err(SemanticEpochErrorV1::PartitionMustStartAtZero)
    );

    let gapped = vec![
        proposed_leaf(0, 1, 41, 51, epoch_scope.clone()),
        proposed_leaf(2, 2, 42, 52, epoch_scope.clone()),
    ];
    assert_eq!(
        ProposedSemanticEpochV1::derive(proposal_input(gapped, 243)),
        Err(SemanticEpochErrorV1::NonContiguousLeafPartitions)
    );

    let wrong_scope = vec![
        proposed_leaf(0, 1, 41, 51, epoch_scope.clone()),
        proposed_leaf(1, 2, 42, 52, scope(201)),
    ];
    assert_eq!(
        ProposedSemanticEpochV1::derive(proposal_input(wrong_scope, 243)),
        Err(SemanticEpochErrorV1::ScopeMismatch)
    );

    let mixed_programs = vec![
        proposed_leaf_with_program(0, 1, 41, 51, epoch_scope.clone(), program(231)),
        proposed_leaf_with_program(1, 2, 42, 52, epoch_scope, program(232)),
    ];
    assert_eq!(
        ProposedSemanticEpochV1::derive(proposal_input(mixed_programs, 243)),
        Err(SemanticEpochErrorV1::LeafProgramMismatch)
    );
}

#[test]
fn semantic_opening_cannot_relabel_an_adapter_leaf() {
    let journal = leaf_journal(0, 1, 41, 51, scope(200), program(231), LeafFault::None);
    let result = ProposedSemanticLeafV1::bind_v1_adapter_journal(
        &journal,
        V1AdapterSemanticLeafOpeningV1::new(commitment(52)),
        &ExpectedV1AdapterLeafIdentityV1::new(program(231)).unwrap(),
    );
    assert_eq!(
        result,
        Err(SemanticEpochErrorV1::V1AdapterProvenanceMismatch)
    );
}

#[test]
fn profile_bound_leaf_getters_expose_only_checked_journal_identities() {
    let journal = leaf_journal(0, 1, 41, 51, scope(200), program(231), LeafFault::None);
    let leaf = ProposedSemanticLeafV1::bind_v1_adapter_journal(
        &journal,
        V1AdapterSemanticLeafOpeningV1::new(commitment(51)),
        &ExpectedV1AdapterLeafIdentityV1::new(program(231)).unwrap(),
    )
    .unwrap();

    assert_eq!(leaf.source_claim_id().into_commitment(), commitment(41));
    assert_eq!(leaf.semantic_source_id().into_commitment(), commitment(51));
    assert_eq!(leaf.task_id(), task(1));
    assert_eq!(leaf.scope(), &scope(200));
    assert_eq!(leaf.leaf_program_id(), program(231));
    assert_eq!(leaf.leaf_profile_id(), manual_adapter_profile());
    assert_eq!(leaf.leaf_statement_hash(), journal.node_statement_hash());
    assert_eq!(
        leaf.leaf_program_manifest_root(),
        manual_manifest(program(231))
    );
    assert_eq!(leaf.commitments(), journal.commitments());
}

#[test]
fn every_v1_adapter_projection_boundary_fails_closed() {
    let expected = ExpectedV1AdapterLeafIdentityV1::new(program(231)).unwrap();
    let cases = [
        (
            LeafFault::Profile,
            SemanticEpochErrorV1::V1AdapterProfileMismatch,
        ),
        (
            LeafFault::Manifest,
            SemanticEpochErrorV1::V1AdapterManifestMismatch,
        ),
        (
            LeafFault::CountUnit,
            SemanticEpochErrorV1::V1AdapterCountUnitMismatch,
        ),
        (
            LeafFault::Provenance,
            SemanticEpochErrorV1::V1AdapterProvenanceMismatch,
        ),
        (
            LeafFault::TaskSet,
            SemanticEpochErrorV1::V1AdapterTaskSetMismatch,
        ),
        (
            LeafFault::SemanticSourceSet,
            SemanticEpochErrorV1::V1AdapterSemanticSourceMismatch,
        ),
        (
            LeafFault::PartitionPlan,
            SemanticEpochErrorV1::V1AdapterPartitionPlanMismatch,
        ),
        (
            LeafFault::AcceptedReceipts,
            SemanticEpochErrorV1::V1AdapterAuxiliarySetMustBeEmpty("accepted_receipts_root"),
        ),
        (
            LeafFault::RejectedReceipts,
            SemanticEpochErrorV1::V1AdapterAuxiliarySetMustBeEmpty("rejected_receipts_root"),
        ),
        (
            LeafFault::Outbox,
            SemanticEpochErrorV1::V1AdapterAuxiliarySetMustBeEmpty("cross_lane_outbox_root"),
        ),
        (
            LeafFault::Inbox,
            SemanticEpochErrorV1::V1AdapterAuxiliarySetMustBeEmpty("cross_lane_inbox_root"),
        ),
        (
            LeafFault::MessageIds,
            SemanticEpochErrorV1::V1AdapterAuxiliarySetMustBeEmpty("cross_lane_message_ids_root"),
        ),
        (
            LeafFault::OperationCount,
            SemanticEpochErrorV1::InvalidLeafOperationCount,
        ),
        (
            LeafFault::Statement,
            SemanticEpochErrorV1::V1AdapterStatementMismatch,
        ),
    ];
    for (fault, expected_error) in cases {
        let journal = leaf_journal(0, 1, 41, 51, scope(200), program(231), fault);
        assert_eq!(
            ProposedSemanticLeafV1::bind_v1_adapter_journal(
                &journal,
                V1AdapterSemanticLeafOpeningV1::new(commitment(51)),
                &expected,
            ),
            Err(expected_error)
        );
    }

    let journal = leaf_journal(0, 1, 41, 51, scope(200), program(231), LeafFault::None);
    assert_eq!(
        ProposedSemanticLeafV1::bind_v1_adapter_journal(
            &journal,
            V1AdapterSemanticLeafOpeningV1::new(commitment(51)),
            &ExpectedV1AdapterLeafIdentityV1::new(program(232)).unwrap(),
        ),
        Err(SemanticEpochErrorV1::LeafProgramMismatch)
    );
}

#[test]
fn bound_plus_one_leaf_rejects() {
    let epoch_scope = scope(200);
    let leaves = (0..=MAX_LEAF_COUNT_V3)
        .map(|index| {
            proposed_leaf(
                index,
                index as u8 + 1,
                index as u8 + 70,
                index as u8 + 140,
                epoch_scope.clone(),
            )
        })
        .collect();
    assert_eq!(
        ProposedSemanticEpochV1::derive(proposal_input(leaves, 243)),
        Err(SemanticEpochErrorV1::TooManyLeaves {
            actual: MAX_LEAF_COUNT_V3 as usize + 1,
            maximum: MAX_LEAF_COUNT_V3 as usize,
        })
    );
}

#[test]
fn exact_codec_rejects_trailing_bytes_and_root_substitution() {
    let proposal = ProposedSemanticEpochV1::derive(proposal_input(two_leaves(), 243)).unwrap();
    let encoded = encode_semantic_epoch_proposal_v1(&proposal).unwrap();
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v1(&trailing),
        Err(SemanticEpochErrorV1::TrailingBytes)
    );

    let semantic_root = proposal.semantic_epoch_root();
    let offsets = encoded
        .windows(semantic_root.as_bytes().len())
        .enumerate()
        .filter_map(|(offset, window)| (window == semantic_root.as_bytes()).then_some(offset))
        .collect::<Vec<_>>();
    assert_eq!(offsets.len(), 1);
    let mut substituted = encoded;
    substituted[offsets[0]..offsets[0] + 32].copy_from_slice(commitment(99).as_bytes());
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v1(&substituted),
        Err(SemanticEpochErrorV1::SemanticRootMismatch)
    );
}

#[test]
fn exact_codec_rejects_every_truncated_prefix_and_oversize() {
    let proposal = ProposedSemanticEpochV1::derive(proposal_input(two_leaves(), 243)).unwrap();
    let encoded = encode_semantic_epoch_proposal_v1(&proposal).unwrap();
    for length in 0..encoded.len() {
        assert!(decode_exact_semantic_epoch_proposal_v1(&encoded[..length]).is_err());
    }
    let oversized = vec![0_u8; MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1 + 1];
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v1(&oversized),
        Err(SemanticEpochErrorV1::InputTooLarge {
            actual: MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1 + 1,
            maximum: MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1,
        })
    );
}

#[test]
fn bounded_byte_mutation_atlas_cannot_change_semantic_root_silently() {
    let proposal = ProposedSemanticEpochV1::derive(proposal_input(two_leaves(), 243)).unwrap();
    let encoded = encode_semantic_epoch_proposal_v1(&proposal).unwrap();
    let expected_semantic_root = proposal.semantic_epoch_root();
    let mut accepted = Vec::new();
    let mut rejected = 0_usize;

    for index in 0..encoded.len() {
        let mut mutated = encoded.clone();
        mutated[index] ^= 1;
        match decode_exact_semantic_epoch_proposal_v1(&mutated) {
            Ok(value) => {
                assert_eq!(value.semantic_epoch_root(), expected_semantic_root);
                accepted.push(mutated);
            }
            Err(_) => rejected += 1,
        }
    }
    assert!(!accepted.is_empty());
    assert!(rejected > accepted.len());

    for seed in accepted.iter().take(8) {
        for index in 0..seed.len() {
            let mut depth_two = seed.clone();
            depth_two[index] ^= 2;
            if let Ok(value) = decode_exact_semantic_epoch_proposal_v1(&depth_two) {
                assert_eq!(value.semantic_epoch_root(), expected_semantic_root);
            }
        }
    }
}

#[test]
fn v2_removes_runtime_identity_while_preserving_semantic_identity() {
    let leaves = two_leaves();
    let legacy = ProposedSemanticEpochV1::derive(proposal_input(leaves.clone(), 243)).unwrap();
    let dependency_manifest_root =
        semantic_epoch_dependency_manifest_root_v2(&semantic_dependencies()).unwrap();
    let current = ProposedSemanticEpochV2::derive(SemanticEpochProposalInputV2 {
        leaves,
        proof_tree_root: commitment(243),
        scope: scope(200),
        dependency_manifest_root,
    })
    .unwrap();

    assert_eq!(current.proposal_schema_version(), 2);
    assert_eq!(current.semantic_statement_version(), 1);
    assert_eq!(current.semantic_epoch_root(), legacy.semantic_epoch_root());
    assert_eq!(current.proof_tree_root(), legacy.proof_tree_root());
    assert_eq!(current.dependency_manifest_root(), dependency_manifest_root);
    assert_eq!(
        hex(dependency_manifest_root.into_bytes()),
        "d986b7f2ab628cb1fbd0e3ad238fb7d10903e787988c084cafe8d908e671bacd"
    );
    let swapped = SemanticEpochDependencyProgramsV1::new(SemanticEpochDependencyProgramsInputV1 {
        adapter_program_id: program(232),
        level_one_program_id: program(231),
        level_two_program_id: program(233),
    });
    assert_ne!(
        dependency_manifest_root,
        semantic_epoch_dependency_manifest_root_v2(&swapped).unwrap()
    );
}

#[test]
fn v1_and_v2_proposal_codecs_fail_closed_without_compatibility_fallback() {
    let legacy = ProposedSemanticEpochV1::derive(proposal_input(two_leaves(), 243)).unwrap();
    let current = ProposedSemanticEpochV2::derive(SemanticEpochProposalInputV2 {
        leaves: two_leaves(),
        proof_tree_root: commitment(243),
        scope: scope(200),
        dependency_manifest_root: semantic_epoch_dependency_manifest_root_v2(
            &semantic_dependencies(),
        )
        .unwrap(),
    })
    .unwrap();
    let legacy_bytes = encode_semantic_epoch_proposal_v1(&legacy).unwrap();
    let current_bytes = encode_semantic_epoch_proposal_v2(&current).unwrap();

    assert_eq!(
        decode_exact_semantic_epoch_proposal_v2(&legacy_bytes),
        Err(SemanticEpochErrorV2::PostcardDecode)
    );
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v1(&current_bytes),
        Err(SemanticEpochErrorV1::PostcardDecode)
    );
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v2(&current_bytes).unwrap(),
        current
    );
}

#[test]
fn v2_exact_codec_rejects_truncation_trailing_oversize_and_root_substitution() {
    let proposal = ProposedSemanticEpochV2::derive(SemanticEpochProposalInputV2 {
        leaves: two_leaves(),
        proof_tree_root: commitment(243),
        scope: scope(200),
        dependency_manifest_root: semantic_epoch_dependency_manifest_root_v2(
            &semantic_dependencies(),
        )
        .unwrap(),
    })
    .unwrap();
    let encoded = encode_semantic_epoch_proposal_v2(&proposal).unwrap();

    for length in 0..encoded.len() {
        assert!(decode_exact_semantic_epoch_proposal_v2(&encoded[..length]).is_err());
    }

    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v2(&trailing),
        Err(SemanticEpochErrorV2::TrailingBytes)
    );

    let mut noncanonical_schema = Vec::with_capacity(encoded.len() + 1);
    noncanonical_schema.extend_from_slice(&[0x82, 0x00]);
    noncanonical_schema.extend_from_slice(&encoded[1..]);
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v2(&noncanonical_schema),
        Err(SemanticEpochErrorV2::NonCanonicalEncoding)
    );

    let oversized = vec![0_u8; MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2 + 1];
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v2(&oversized),
        Err(SemanticEpochErrorV2::InputTooLarge {
            actual: MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2 + 1,
            maximum: MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2,
        })
    );

    let semantic_root = proposal.semantic_epoch_root();
    let offsets = encoded
        .windows(semantic_root.as_bytes().len())
        .enumerate()
        .filter_map(|(offset, window)| (window == semantic_root.as_bytes()).then_some(offset))
        .collect::<Vec<_>>();
    assert_eq!(offsets.len(), 1);
    let mut substituted = encoded;
    substituted[offsets[0]..offsets[0] + 32].copy_from_slice(commitment(99).as_bytes());
    assert_eq!(
        decode_exact_semantic_epoch_proposal_v2(&substituted),
        Err(SemanticEpochErrorV2::SemanticRootMismatch)
    );
}
