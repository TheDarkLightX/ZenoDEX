use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{
    compose_spot_recursive_leaf_summary_v1, recursive_asset_delta_root_v1,
    recursive_authority_scope_root_v1, recursive_cross_shard_messages_root_v1,
    recursive_lane_state_vector_root_v1, recursive_receipt_ids_root_v1,
    spot_recursive_leaf_asset_delta_rows_v1, ChainBalanceV1, DexBalanceEntryV1, DexStateV1,
    FaucetMintV1, RecursiveAssetDeltaRowV1, RecursiveEffectSummaryV1, SpotRecursiveLeafInputV1,
    StateProofInputV1, TauTxAppOpsV1, TauTxV1, TxIngressFactV1, RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
    RECURSIVE_SPOT_LEAF_PROFILE_V1,
};
use zenodex_zrpf_protocol_v3::{
    decode_exact_semantic_subtree_v2, encode_node_journal_v3, encode_semantic_subtree_v2,
    AggregateNodeInputV3, ApplicationIdV3, CommitmentV3, DomainIdV3,
    ExpectedV1AdapterLeafIdentityV1, NodeJournalInputV4, NodeJournalV3, NodeJournalV4,
    NodeScopeInputV3, NodeScopeV3, ProfileIdV3, ProgramIdV3, ProjectedChildDescriptorV3,
    ProposedSemanticEpochV1, ProposedSemanticLeafV1, SemanticEpochProposalInputV1, TaskIdV3,
    V1AdapterSemanticLeafOpeningV1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    bind_expected_spot_semantic_subtree_v4, canonical_spot_asset_name_v1,
    close_spot_represented_value_epoch_v1, compose_spot_represented_value_v1,
    match_expected_spot_semantic_value_v1, merge_spot_value_subtrees_v2,
    propose_spot_value_subtree_v2, semantic_subtree_v2_from_spot_summary,
    spot_accounting_domain_id_v1, spot_atoms_unit_id_v1, spot_represented_value_profile_id_v1,
    spot_state_root_scheme_id_v1, ExpectedSpotSemanticValueFieldV1,
    ExpectedSpotSemanticValueInputV1, ExpectedSpotSemanticValueV1, SpotMintAuthorityGrantV1,
    SpotRepresentedValuePolicyV1, SpotSemanticValueErrorV1, SpotSemanticValueProjectionV1,
    SpotValueLeafOpeningV1, SpotValueSubtreeSummaryV2, SpotValueWireErrorV4, SpotValueWireFieldV4,
    CANONICAL_SPOT_ASSET_NAME_BYTES_V1, MAX_SPOT_ASSET_ROWS_PER_LEAF_V1, MAX_SPOT_LANE_ID_BYTES_V1,
    MAX_SPOT_MINT_GRANTS_V1, MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2, MAX_SPOT_VALUE_LEAVES_V1,
    MAX_SPOT_VALUE_SUBTREE_LEAVES_V2,
};
use zenodex_zrpf_risc0_shared::{
    project_policy_bound_v1_journal, SourceKindV1, PINNED_SPOT_LEAF_IMAGE_ID_V1,
};

const ADAPTER_IMAGE_ID: [u32; 8] = [31, 32, 33, 34, 35, 36, 37, 38];
const POLICY_HASH: [u8; 32] = [80; 32];
const LANE_ID: &str = "spot-value-lane-0";
const PRE_STATE_VECTOR_DOMAIN_V1: &[u8] = b"zenodex.risc0.recursive.pre_state_vector_root.v1";
const POST_STATE_VECTOR_DOMAIN_V1: &[u8] = b"zenodex.risc0.recursive.post_state_vector_root.v1";

fn root(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn asset(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn ordinary_row(
    asset_id: [u8; 32],
    outflow_atoms: u128,
    inflow_atoms: u128,
) -> RecursiveAssetDeltaRowV1 {
    RecursiveAssetDeltaRowV1 {
        asset_id: canonical_spot_asset_name_v1(asset_id),
        debit_atoms: outflow_atoms,
        credit_atoms: inflow_atoms,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_root: [0; 32],
    }
}

fn mint_row(
    asset_id: [u8; 32],
    atoms: u128,
    public_policy_hash: [u8; 32],
) -> RecursiveAssetDeltaRowV1 {
    let asset_name = canonical_spot_asset_name_v1(asset_id);
    let authority_root = recursive_authority_scope_root_v1(
        public_policy_hash,
        "spot",
        &asset_name,
        RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
    )
    .unwrap();
    RecursiveAssetDeltaRowV1 {
        asset_id: asset_name,
        debit_atoms: 0,
        credit_atoms: atoms,
        authorized_mint_atoms: atoms,
        authorized_burn_atoms: 0,
        authority_root,
    }
}

fn grant(asset_id: [u8; 32], cap: u128) -> SpotMintAuthorityGrantV1 {
    let authority_root = recursive_authority_scope_root_v1(
        POLICY_HASH,
        "spot",
        &canonical_spot_asset_name_v1(asset_id),
        RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
    )
    .unwrap();
    SpotMintAuthorityGrantV1::new(asset_id, authority_root, cap).unwrap()
}

fn policy(grants: Vec<SpotMintAuthorityGrantV1>) -> SpotRepresentedValuePolicyV1 {
    SpotRepresentedValuePolicyV1::new(POLICY_HASH, grants).unwrap()
}

#[derive(Clone)]
struct LeafFixture {
    leaf: ProposedSemanticLeafV1,
    opening: SpotValueLeafOpeningV1,
    structural: NodeJournalV3,
}

struct LeafInput {
    seed: u8,
    ordinal: u64,
    lane_id: &'static str,
    pre_state_root: [u8; 32],
    post_state_root: [u8; 32],
    transaction_root: [u8; 32],
    rows: Vec<RecursiveAssetDeltaRowV1>,
}

fn leaf(input: LeafInput) -> LeafFixture {
    let empty_receipts = recursive_receipt_ids_root_v1(&[]).unwrap();
    let empty_messages = recursive_cross_shard_messages_root_v1(&[]).unwrap();
    let asset_delta_root = recursive_asset_delta_root_v1(&input.rows).unwrap();
    let summary = RecursiveEffectSummaryV1 {
        summary_version: 1,
        lane_id: input.lane_id.to_owned(),
        lane_kind: "spot".to_owned(),
        chain_id: "zenodex-value-test".to_owned(),
        epoch_id: 71,
        proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1.to_owned(),
        risc0_image_id: PINNED_SPOT_LEAF_IMAGE_ID_V1,
        statement_hash: root(input.seed),
        pre_state_root: input.pre_state_root,
        post_state_root: input.post_state_root,
        tx_root: input.transaction_root,
        evidence_root: root(input.seed.wrapping_add(1)),
        receipt_root: root(input.seed.wrapping_add(2)),
        accepted_receipts_root: empty_receipts,
        rejected_receipts_root: empty_receipts,
        asset_delta_root,
        cross_shard_outbox_root: empty_messages,
        cross_shard_inbox_root: empty_messages,
        write_set_root: root(input.seed.wrapping_add(3)),
        public_policy_hash: POLICY_HASH,
        feature_suite_hash: root(81),
        dependency_lock_hash: root(82),
        toolchain_lock_hash: root(83),
    };
    adapt_summary(summary, input.rows, input.ordinal)
}

fn adapt_summary(
    summary: RecursiveEffectSummaryV1,
    rows: Vec<RecursiveAssetDeltaRowV1>,
    ordinal: u64,
) -> LeafFixture {
    let source_bytes = postcard::to_allocvec(&summary).unwrap();
    let projection = project_policy_bound_v1_journal(
        SourceKindV1::Spot,
        &source_bytes,
        ordinal,
        ADAPTER_IMAGE_ID,
    )
    .unwrap();
    let semantic_opening =
        V1AdapterSemanticLeafOpeningV1::new(projection.source_binding.canonical_hash().unwrap());
    let expected =
        ExpectedV1AdapterLeafIdentityV1::new(projection.journal.actual_program_id()).unwrap();
    let structural = projection.journal;
    let semantic_leaf =
        ProposedSemanticLeafV1::bind_v1_adapter_journal(&structural, semantic_opening, &expected)
            .unwrap();
    LeafFixture {
        leaf: semantic_leaf,
        opening: SpotValueLeafOpeningV1::new(
            summary.lane_id,
            summary.pre_state_root,
            summary.post_state_root,
            rows,
        )
        .unwrap(),
        structural,
    }
}

fn empty_real_spot_input() -> SpotRecursiveLeafInputV1 {
    let snapshot = DexStateV1::empty().to_snapshot();
    let app_hash = DexStateV1::from_snapshot(snapshot.clone())
        .unwrap()
        .canonical_app_hash_sha256();
    SpotRecursiveLeafInputV1 {
        chain_id: "zenodex-value-test".to_owned(),
        epoch_id: 71,
        lane_id: LANE_ID.to_owned(),
        risc0_image_id: PINNED_SPOT_LEAF_IMAGE_ID_V1,
        public_policy_hash: POLICY_HASH,
        feature_suite_hash: root(81),
        dependency_lock_hash: root(82),
        toolchain_lock_hash: root(83),
        spot_input: StateProofInputV1 {
            state_hash: app_hash,
            block_timestamp: 1,
            pre_app_hash_present: true,
            pre_app_hash: app_hash,
            pre_state: snapshot,
            txs: Vec::new(),
            pre_nonces: Vec::new(),
            tx_ingress: Vec::new(),
            chain_balances_post: Vec::new(),
            expected_post_app_hash: app_hash,
            protocol_fee_share_bps: 0,
            protocol_fee_recipient_pubkey: None,
            tx_execution_order: Vec::new(),
            route_price_intervals: Vec::new(),
            route_price_interval_authority: None,
            route_price_interval_authority_policy: None,
            route_price_interval_max_width_bps: None,
            shared_pool_frontier_signature_certificates: Vec::new(),
        },
    }
}

fn write_mirror_domain(hasher: &mut Sha256, domain: &[u8]) {
    hasher.update((domain.len() as u16).to_be_bytes());
    hasher.update(domain);
}

fn write_mirror_str(hasher: &mut Sha256, value: &str) {
    hasher.update((value.len() as u32).to_be_bytes());
    hasher.update(value.as_bytes());
}

fn mirror_label(domain: &[u8], label: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    write_mirror_domain(&mut hasher, domain);
    hasher.update((label.len() as u32).to_be_bytes());
    hasher.update(label);
    hasher.finalize().into()
}

fn mirror_value_profile_id() -> [u8; 32] {
    let atoms = mirror_label(
        b"zenodex.zrpf.spot_atoms_unit_id.v1",
        b"spot_raw_u128_atoms",
    );
    let accounting = mirror_label(
        b"zenodex.zrpf.spot_accounting_domain_id.v1",
        b"authenticated_represented_external_effect_rows",
    );
    let mut state_hasher = Sha256::new();
    write_mirror_domain(
        &mut state_hasher,
        b"zenodex.zrpf.spot_state_root_scheme_id.v1",
    );
    for word in PINNED_SPOT_LEAF_IMAGE_ID_V1 {
        state_hasher.update(word.to_le_bytes());
    }
    write_mirror_str(&mut state_hasher, RECURSIVE_SPOT_LEAF_PROFILE_V1);
    let state_scheme: [u8; 32] = state_hasher.finalize().into();

    let mut hasher = Sha256::new();
    write_mirror_domain(
        &mut hasher,
        b"zenodex.zrpf.spot_represented_value_profile_id.v1",
    );
    hasher.update(atoms);
    hasher.update(accounting);
    hasher.update(state_scheme);
    for bound in [
        MAX_SPOT_VALUE_LEAVES_V1,
        MAX_SPOT_VALUE_SUBTREE_LEAVES_V2,
        MAX_SPOT_ASSET_ROWS_PER_LEAF_V1,
        MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2,
        MAX_SPOT_MINT_GRANTS_V1,
        MAX_SPOT_LANE_ID_BYTES_V1,
        CANONICAL_SPOT_ASSET_NAME_BYTES_V1,
    ] {
        hasher.update((bound as u64).to_be_bytes());
    }
    for rule in [
        "asset_codec=lowercase_0x_plus_64_hex",
        "state=single_lane_raw_post_equals_next_raw_pre",
        "flow=outflow_plus_issued_equals_inflow_plus_destroyed",
        "supply=spot_pure_mint_only",
        "grant_cap=per_closed_value_root",
        "transactions=ordered_unique_leaf_transaction_root_commitments",
        "arithmetic=checked_u128",
    ] {
        write_mirror_str(&mut hasher, rule);
    }
    hasher.finalize().into()
}

fn mirror_expected_statement_hash(input: &ExpectedSpotSemanticValueInputV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    write_mirror_domain(&mut hasher, b"zenodex.zrpf.spot_expected_semantic_value.v1");
    hasher.update(input.scope.canonical_hash().unwrap().as_bytes());
    for value in [
        input.lane_id_hash,
        input.value_profile_id,
        input.accounting_domain_id,
        input.atoms_unit_id,
        input.state_root_scheme_id,
        input.ordered_transaction_roots_root,
        input.state_chain_root,
    ] {
        hasher.update(value.as_bytes());
    }
    hasher.update(input.raw_pre_state_root);
    hasher.update(input.raw_post_state_root);
    hasher.update(input.leaf_count.to_be_bytes());
    hasher.update(input.represented_row_count.to_be_bytes());
    for value in [
        input.authority_grants_root,
        input.base_semantic_epoch_root,
        input.semantic_value_root,
    ] {
        hasher.update(value.as_bytes());
    }
    hasher.finalize().into()
}

fn hex32(value: [u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(64);
    for byte in value {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

fn fixture(
    seed: u8,
    ordinal: u64,
    pre: u8,
    post: u8,
    rows: Vec<RecursiveAssetDeltaRowV1>,
) -> LeafFixture {
    leaf(LeafInput {
        seed,
        ordinal,
        lane_id: LANE_ID,
        pre_state_root: root(pre),
        post_state_root: root(post),
        transaction_root: root(seed.wrapping_add(20)),
        rows,
    })
}

fn base_proposal(
    leaves: &[ProposedSemanticLeafV1],
    proof_tree_seed: u8,
) -> ProposedSemanticEpochV1 {
    ProposedSemanticEpochV1::derive(SemanticEpochProposalInputV1 {
        leaves: leaves.to_vec(),
        proof_tree_root: CommitmentV3::new(root(proof_tree_seed)).unwrap(),
        scope: leaves[0].scope().clone(),
        actual_program_id: ProgramIdV3::new(root(90)).unwrap(),
        program_manifest_root: CommitmentV3::new(root(91)).unwrap(),
    })
    .unwrap()
}

fn compose(
    fixtures: &[LeafFixture],
    proof_tree_seed: u8,
    policy: &SpotRepresentedValuePolicyV1,
) -> Result<
    zenodex_zrpf_risc0_semantic_shared::SpotSemanticValueProjectionV1,
    SpotSemanticValueErrorV1,
> {
    let leaves = fixtures
        .iter()
        .map(|fixture| fixture.leaf.clone())
        .collect::<Vec<_>>();
    let openings = fixtures
        .iter()
        .map(|fixture| fixture.opening.clone())
        .collect::<Vec<_>>();
    compose_spot_represented_value_v1(
        &base_proposal(&leaves, proof_tree_seed),
        &leaves,
        &openings,
        policy,
    )
}

fn closed_summary_and_projection(
    fixtures: &[LeafFixture],
    proof_tree_seed: u8,
    policy: &SpotRepresentedValuePolicyV1,
) -> (
    SpotValueSubtreeSummaryV2,
    SpotSemanticValueProjectionV1,
    NodeScopeV3,
) {
    let leaves = fixtures
        .iter()
        .map(|fixture| fixture.leaf.clone())
        .collect::<Vec<_>>();
    let openings = fixtures
        .iter()
        .map(|fixture| fixture.opening.clone())
        .collect::<Vec<_>>();
    let summary = propose_spot_value_subtree_v2(&leaves, &openings, policy).unwrap();
    let proposal = base_proposal(&leaves, proof_tree_seed);
    let scope = proposal.scope().clone();
    let projection = close_spot_represented_value_epoch_v1(&proposal, &summary, policy).unwrap();
    (summary, projection, scope)
}

fn structural_parent(fixtures: &[LeafFixture]) -> NodeJournalV3 {
    let children = fixtures
        .iter()
        .enumerate()
        .map(|(index, fixture)| {
            let bytes = encode_node_journal_v3(&fixture.structural).unwrap();
            ProjectedChildDescriptorV3::project_canonical_journal(
                CommitmentV3::new(root(210 + index as u8)).unwrap(),
                &bytes,
            )
            .unwrap()
        })
        .collect();
    NodeJournalV3::new_aggregate(AggregateNodeInputV3 {
        children,
        task_id: TaskIdV3::new(root(220)).unwrap(),
        count_unit_id: fixtures[0].structural.count_unit_id(),
        scope: fixtures[0].structural.scope().clone(),
        proof_profile_id: ProfileIdV3::new(root(221)).unwrap(),
        actual_program_id: ProgramIdV3::new(root(222)).unwrap(),
        node_statement_hash: CommitmentV3::new(root(223)).unwrap(),
        program_manifest_root: CommitmentV3::new(root(224)).unwrap(),
        commitments: fixtures[0].structural.commitments().clone(),
    })
    .unwrap()
}

fn balanced_projection() -> (SpotSemanticValueProjectionV1, NodeScopeV3) {
    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 10)]),
    ];
    let scope = fixtures[0].leaf.scope().clone();
    (compose(&fixtures, 92, &policy(vec![])).unwrap(), scope)
}

fn expected_input(
    scope: NodeScopeV3,
    projection: &SpotSemanticValueProjectionV1,
) -> ExpectedSpotSemanticValueInputV1 {
    let commitments = projection.commitments();
    ExpectedSpotSemanticValueInputV1 {
        scope,
        lane_id_hash: projection.lane_id_hash(),
        value_profile_id: commitments.value_profile_id(),
        accounting_domain_id: commitments.accounting_domain_id(),
        atoms_unit_id: commitments.atoms_unit_id(),
        state_root_scheme_id: commitments.state_root_scheme_id(),
        ordered_transaction_roots_root: commitments.ordered_transaction_roots_root(),
        state_chain_root: commitments.state_chain_root(),
        raw_pre_state_root: projection.raw_epoch_pre_state_root(),
        raw_post_state_root: projection.raw_epoch_post_state_root(),
        leaf_count: projection.leaf_count(),
        represented_row_count: projection.represented_row_count(),
        authority_grants_root: commitments.authority_grants_root(),
        base_semantic_epoch_root: commitments.base_semantic_epoch_root(),
        semantic_value_root: projection.semantic_value_root(),
    }
}

fn unrelated_scope(epoch_start: u64, epoch_end: u64) -> NodeScopeV3 {
    NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new(root(181)).unwrap(),
        chain_or_domain_id: DomainIdV3::new(root(182)).unwrap(),
        epoch_start,
        epoch_end,
        public_policy_hash: CommitmentV3::new(POLICY_HASH).unwrap(),
        feature_suite_hash: CommitmentV3::new(root(183)).unwrap(),
        dependency_lock_hash: CommitmentV3::new(root(184)).unwrap(),
        toolchain_lock_hash: CommitmentV3::new(root(185)).unwrap(),
    })
    .unwrap()
}

fn assert_expected_mismatch(
    projection: &SpotSemanticValueProjectionV1,
    baseline_hash: CommitmentV3,
    input: ExpectedSpotSemanticValueInputV1,
    field: ExpectedSpotSemanticValueFieldV1,
) {
    let expected = ExpectedSpotSemanticValueV1::new(input).unwrap();
    assert_ne!(expected.statement_hash(), baseline_hash);
    assert_eq!(
        match_expected_spot_semantic_value_v1(projection.clone(), &expected),
        Err(SpotSemanticValueErrorV1::ExpectedProjectionMismatch(field))
    );
}

#[test]
fn sequential_spot_rows_compose_with_raw_state_continuity() {
    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 10)]),
    ];

    let projection = compose(&fixtures, 92, &policy(vec![])).unwrap();

    assert_eq!(projection.leaf_count(), 2);
    assert_eq!(projection.represented_row_count(), 2);
    assert_eq!(projection.raw_epoch_pre_state_root(), root(10));
    assert_eq!(projection.raw_epoch_post_state_root(), root(12));
    assert_eq!(projection.asset_flows().len(), 1);
    assert_eq!(projection.asset_flows()[0].asset_id(), native);
    assert_eq!(projection.asset_flows()[0].outflow_atoms(), 10);
    assert_eq!(projection.asset_flows()[0].inflow_atoms(), 10);
}

#[test]
fn equal_raw_chain_endpoint_uses_distinct_pre_and_post_commitment_domains() {
    let raw = root(11);
    let pre = recursive_lane_state_vector_root_v1(
        PRE_STATE_VECTOR_DOMAIN_V1,
        &[(LANE_ID.to_owned(), raw)],
    )
    .unwrap();
    let post = recursive_lane_state_vector_root_v1(
        POST_STATE_VECTOR_DOMAIN_V1,
        &[(LANE_ID.to_owned(), raw)],
    )
    .unwrap();
    assert_ne!(pre, post);

    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 1, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 1)]),
    ];
    compose(&fixtures, 92, &policy(vec![])).unwrap();
}

#[test]
fn governed_capped_spot_faucet_issuance_composes() {
    let issued_asset = asset(7);
    let fixtures = [fixture(
        1,
        0,
        10,
        11,
        vec![mint_row(issued_asset, 7, POLICY_HASH)],
    )];

    let projection = compose(&fixtures, 92, &policy(vec![grant(issued_asset, 7)])).unwrap();

    assert_eq!(projection.asset_flows()[0].issued_atoms(), 7);
    assert_eq!(projection.asset_flows()[0].inflow_atoms(), 7);
    assert_eq!(projection.authority_uses().len(), 1);
    assert_eq!(projection.authority_uses()[0].asset_id(), issued_asset);
    assert_eq!(projection.authority_uses()[0].atoms(), 7);
}

#[test]
fn topology_changes_preserve_value_root_and_change_proposal_hash() {
    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 4, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 4)]),
    ];
    let governed = policy(vec![]);

    let left = compose(&fixtures, 92, &governed).unwrap();
    let right = compose(&fixtures, 93, &governed).unwrap();

    assert_eq!(left.semantic_value_root(), right.semantic_value_root());
    assert_ne!(left.proposal_hash(), right.proposal_hash());
}

#[test]
fn raw_state_discontinuity_rejects() {
    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 2, 0)]),
        fixture(2, 1, 19, 20, vec![ordinary_row(native, 0, 2)]),
    ];

    assert_eq!(
        compose(&fixtures, 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::StateDiscontinuity { ordinal: 1 })
    );
}

#[test]
fn one_atom_global_imbalance_rejects() {
    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 9)]),
    ];

    assert_eq!(
        compose(&fixtures, 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::AssetImbalance { asset_id: native })
    );
}

#[test]
fn asset_row_mutation_rejects_before_accounting() {
    let native = [0; 32];
    let original = fixture(1, 0, 10, 11, vec![ordinary_row(native, 5, 5)]);
    let mutated = LeafFixture {
        leaf: original.leaf.clone(),
        opening: SpotValueLeafOpeningV1::new(
            LANE_ID.to_owned(),
            root(10),
            root(11),
            vec![ordinary_row(native, 5, 4)],
        )
        .unwrap(),
        structural: original.structural.clone(),
    };

    assert_eq!(
        compose(&[mutated], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::AssetRowsRootMismatch { ordinal: 0 })
    );
}

#[test]
fn noncanonical_asset_alias_rejects_even_when_leaf_root_matches() {
    let mut row = ordinary_row(asset(10), 3, 3);
    row.asset_id = row.asset_id.to_ascii_uppercase().replacen("0X", "0x", 1);
    let fixtures = [fixture(1, 0, 10, 11, vec![row])];

    assert_eq!(
        compose(&fixtures, 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::NonCanonicalAssetId { ordinal: 0, row: 0 })
    );
}

#[test]
fn missing_or_exceeded_mint_grant_rejects() {
    let issued_asset = asset(7);
    let fixtures = [fixture(
        1,
        0,
        10,
        11,
        vec![mint_row(issued_asset, 7, POLICY_HASH)],
    )];

    assert_eq!(
        compose(&fixtures, 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::MissingMintGrant { ordinal: 0, row: 0 })
    );
    assert_eq!(
        compose(&fixtures, 92, &policy(vec![grant(issued_asset, 6)])),
        Err(SpotSemanticValueErrorV1::MintCapExceeded { ordinal: 0, row: 0 })
    );
}

#[test]
fn inverted_mint_and_burn_rows_reject() {
    let issued_asset = asset(7);
    let mut inverted = mint_row(issued_asset, 7, POLICY_HASH);
    inverted.debit_atoms = 7;
    inverted.credit_atoms = 0;
    let mint_fixture = fixture(1, 0, 10, 11, vec![inverted]);
    assert_eq!(
        compose(&[mint_fixture], 92, &policy(vec![grant(issued_asset, 7)])),
        Err(SpotSemanticValueErrorV1::MintRowShapeInvalid { ordinal: 0, row: 0 })
    );

    let mut burn = ordinary_row(issued_asset, 7, 0);
    burn.authorized_burn_atoms = 7;
    burn.authority_root = root(9);
    let burn_fixture = fixture(2, 0, 20, 21, vec![burn]);
    assert_eq!(
        compose(&[burn_fixture], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::BurnUnsupported { ordinal: 0, row: 0 })
    );
}

#[test]
fn duplicate_transaction_and_mixed_lane_reject() {
    let native = [0; 32];
    let repeated_tx = root(44);
    let left = leaf(LeafInput {
        seed: 1,
        ordinal: 0,
        lane_id: LANE_ID,
        pre_state_root: root(10),
        post_state_root: root(11),
        transaction_root: repeated_tx,
        rows: vec![ordinary_row(native, 1, 0)],
    });
    let right = leaf(LeafInput {
        seed: 2,
        ordinal: 1,
        lane_id: LANE_ID,
        pre_state_root: root(11),
        post_state_root: root(12),
        transaction_root: repeated_tx,
        rows: vec![ordinary_row(native, 0, 1)],
    });
    assert_eq!(
        compose(&[left, right], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::DuplicateTransactionRoot { ordinal: 1 })
    );

    let left = fixture(3, 0, 20, 21, vec![ordinary_row(native, 1, 0)]);
    let right = leaf(LeafInput {
        seed: 4,
        ordinal: 1,
        lane_id: "spot-value-lane-1",
        pre_state_root: root(21),
        post_state_root: root(22),
        transaction_root: root(24),
        rows: vec![ordinary_row(native, 0, 1)],
    });
    assert_eq!(
        compose(&[left, right], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::MixedLaneId { ordinal: 1 })
    );
}

#[test]
fn accumulation_overflow_rejects_without_wrapping() {
    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, u128::MAX, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 1, 0)]),
    ];

    assert_eq!(
        compose(&fixtures, 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::ArithmeticOverflow(
            "asset_outflow"
        ))
    );
}

#[test]
fn public_policy_and_grant_order_are_fail_closed() {
    let native = [0; 32];
    let fixtures = [fixture(1, 0, 10, 11, vec![ordinary_row(native, 2, 2)])];
    let wrong_policy = SpotRepresentedValuePolicyV1::new(root(79), vec![]).unwrap();
    assert_eq!(
        compose(&fixtures, 92, &wrong_policy),
        Err(SpotSemanticValueErrorV1::PublicPolicyMismatch)
    );

    assert_eq!(
        SpotRepresentedValuePolicyV1::new(
            POLICY_HASH,
            vec![grant(asset(2), 1), grant(asset(1), 1)]
        ),
        Err(SpotSemanticValueErrorV1::NonCanonicalGrantOrder)
    );

    let wrong_root = SpotMintAuthorityGrantV1::new(asset(3), root(7), 1).unwrap();
    assert_eq!(
        SpotRepresentedValuePolicyV1::new(POLICY_HASH, vec![wrong_root]),
        Err(SpotSemanticValueErrorV1::InvalidGrant)
    );
}

#[test]
fn empty_rows_and_profile_leaf_bound_reject() {
    let empty = fixture(1, 0, 10, 11, vec![]);
    assert_eq!(
        compose(&[empty], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::EmptyRepresentedRows)
    );

    let native = [0; 32];
    let fixtures = (0..=MAX_SPOT_VALUE_LEAVES_V1)
        .map(|ordinal| {
            fixture(
                (ordinal + 1) as u8,
                ordinal as u64,
                (ordinal + 10) as u8,
                (ordinal + 11) as u8,
                vec![ordinary_row(native, 1, 1)],
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        compose(&fixtures, 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::TooManyLeaves {
            actual: MAX_SPOT_VALUE_LEAVES_V1 + 1,
            maximum: MAX_SPOT_VALUE_LEAVES_V1,
        })
    );
}

#[test]
fn state_opening_must_recompose_the_authenticated_commitment() {
    let native = [0; 32];
    let original = fixture(1, 0, 10, 11, vec![ordinary_row(native, 2, 2)]);
    let substituted = LeafFixture {
        leaf: original.leaf,
        opening: SpotValueLeafOpeningV1::new(
            LANE_ID.to_owned(),
            root(9),
            root(11),
            vec![ordinary_row(native, 2, 2)],
        )
        .unwrap(),
        structural: original.structural,
    };

    assert_eq!(
        compose(&[substituted], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::StateCommitmentMismatch {
            ordinal: 0,
            side: "pre",
        })
    );
}

#[test]
fn zero_rows_and_detached_authority_roots_reject() {
    let native = [0; 32];
    let zero = RecursiveAssetDeltaRowV1 {
        asset_id: canonical_spot_asset_name_v1(native),
        debit_atoms: 0,
        credit_atoms: 0,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_root: [0; 32],
    };
    let zero_fixture = fixture(1, 0, 10, 11, vec![zero]);
    assert_eq!(
        compose(&[zero_fixture], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::ZeroAssetRow { ordinal: 0, row: 0 })
    );

    let mut detached = ordinary_row(native, 2, 2);
    detached.authority_root = root(7);
    let detached_fixture = fixture(2, 0, 20, 21, vec![detached]);
    assert_eq!(
        compose(&[detached_fixture], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::OrdinaryRowHasAuthority { ordinal: 0, row: 0 })
    );
}

#[test]
fn combined_mint_and_burn_row_rejects() {
    let issued_asset = asset(7);
    let mut row = mint_row(issued_asset, 5, POLICY_HASH);
    row.authorized_burn_atoms = 1;
    let fixtures = [fixture(1, 0, 10, 11, vec![row])];

    assert_eq!(
        compose(&fixtures, 92, &policy(vec![grant(issued_asset, 5)])),
        Err(SpotSemanticValueErrorV1::SupplyRowCombinesMintAndBurn { ordinal: 0, row: 0 })
    );
}

#[test]
fn mint_cap_accumulates_across_distinct_authenticated_leaves() {
    let issued_asset = asset(7);
    let fixtures = [
        fixture(1, 0, 10, 11, vec![mint_row(issued_asset, 6, POLICY_HASH)]),
        fixture(2, 1, 11, 12, vec![mint_row(issued_asset, 6, POLICY_HASH)]),
    ];

    assert_eq!(
        compose(&fixtures, 92, &policy(vec![grant(issued_asset, 10)])),
        Err(SpotSemanticValueErrorV1::MintCapExceeded { ordinal: 1, row: 0 })
    );
}

#[test]
fn conservation_side_addition_overflow_rejects() {
    let issued_asset = asset(7);
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(issued_asset, u128::MAX, 0)]),
        fixture(2, 1, 11, 12, vec![mint_row(issued_asset, 1, POLICY_HASH)]),
    ];

    assert_eq!(
        compose(&fixtures, 92, &policy(vec![grant(issued_asset, 1)])),
        Err(SpotSemanticValueErrorV1::ArithmeticOverflow("balance_left"))
    );
}

#[test]
fn partial_subtrees_carry_residuals_until_closed_epoch_finalization() {
    let native = [0; 32];
    let left = fixture(1, 0, 10, 11, vec![ordinary_row(native, 10, 0)]);
    let right = fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 10)]);
    let governed = policy(vec![]);

    let left_summary = propose_spot_value_subtree_v2(
        core::slice::from_ref(&left.leaf),
        core::slice::from_ref(&left.opening),
        &governed,
    )
    .unwrap();
    let right_summary = propose_spot_value_subtree_v2(
        core::slice::from_ref(&right.leaf),
        core::slice::from_ref(&right.opening),
        &governed,
    )
    .unwrap();
    assert_eq!(left_summary.partition_start(), 0);
    assert_eq!(right_summary.partition_start(), 1);
    assert_eq!(left_summary.asset_flows()[0].outflow_atoms(), 10);
    assert_eq!(right_summary.asset_flows()[0].inflow_atoms(), 10);

    let left_base = base_proposal(core::slice::from_ref(&left.leaf), 92);
    assert_eq!(
        close_spot_represented_value_epoch_v1(&left_base, &left_summary, &governed),
        Err(SpotSemanticValueErrorV1::AssetImbalance { asset_id: native })
    );
    let full_base = base_proposal(&[left.leaf.clone(), right.leaf.clone()], 93);
    assert_eq!(
        close_spot_represented_value_epoch_v1(&full_base, &right_summary, &governed),
        Err(SpotSemanticValueErrorV1::NonZeroOriginClosedEpoch)
    );

    let merged = merge_spot_value_subtrees_v2(&left_summary, &right_summary, &governed).unwrap();
    let closed = close_spot_represented_value_epoch_v1(&full_base, &merged, &governed).unwrap();
    assert_eq!(merged.partition_start(), 0);
    assert_eq!(merged.partition_end_exclusive(), 2);
    assert_eq!(closed.asset_flows()[0].outflow_atoms(), 10);
    assert_eq!(closed.asset_flows()[0].inflow_atoms(), 10);
}

#[test]
fn subtree_merge_is_associative_over_the_canonical_flattened_summary() {
    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 4, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 6, 0)]),
        fixture(3, 2, 12, 13, vec![ordinary_row(native, 0, 10)]),
    ];
    let governed = policy(vec![]);
    let summaries = fixtures
        .iter()
        .map(|fixture| {
            propose_spot_value_subtree_v2(
                core::slice::from_ref(&fixture.leaf),
                core::slice::from_ref(&fixture.opening),
                &governed,
            )
            .unwrap()
        })
        .collect::<Vec<_>>();

    let left_pair = merge_spot_value_subtrees_v2(&summaries[0], &summaries[1], &governed).unwrap();
    let left_grouped = merge_spot_value_subtrees_v2(&left_pair, &summaries[2], &governed).unwrap();
    let right_pair = merge_spot_value_subtrees_v2(&summaries[1], &summaries[2], &governed).unwrap();
    let right_grouped =
        merge_spot_value_subtrees_v2(&summaries[0], &right_pair, &governed).unwrap();

    assert_eq!(left_grouped, right_grouped);
    assert_eq!(left_grouped.subtree_root(), right_grouped.subtree_root());
    let leaves = fixtures
        .iter()
        .map(|fixture| fixture.leaf.clone())
        .collect::<Vec<_>>();
    let first_base = base_proposal(&leaves, 92);
    let second_base = base_proposal(&leaves, 93);
    let first =
        close_spot_represented_value_epoch_v1(&first_base, &left_grouped, &governed).unwrap();
    let second =
        close_spot_represented_value_epoch_v1(&second_base, &right_grouped, &governed).unwrap();
    assert_eq!(first.semantic_value_root(), second.semantic_value_root());
    assert_ne!(first.proposal_hash(), second.proposal_hash());
}

#[test]
fn discontinuous_subtrees_cannot_merge() {
    let native = [0; 32];
    let left = fixture(1, 0, 10, 11, vec![ordinary_row(native, 1, 0)]);
    let right = fixture(2, 1, 19, 20, vec![ordinary_row(native, 0, 1)]);
    let governed = policy(vec![]);
    let left_summary = propose_spot_value_subtree_v2(
        core::slice::from_ref(&left.leaf),
        core::slice::from_ref(&left.opening),
        &governed,
    )
    .unwrap();
    let right_summary = propose_spot_value_subtree_v2(
        core::slice::from_ref(&right.leaf),
        core::slice::from_ref(&right.opening),
        &governed,
    )
    .unwrap();

    assert_eq!(
        merge_spot_value_subtrees_v2(&left_summary, &right_summary, &governed),
        Err(SpotSemanticValueErrorV1::StateDiscontinuity { ordinal: 1 })
    );
}

#[test]
fn mint_cap_is_explicitly_local_to_each_closed_value_root() {
    let issued_asset = asset(7);
    let governed = policy(vec![grant(issued_asset, 7)]);
    let first = fixture(1, 0, 10, 11, vec![mint_row(issued_asset, 7, POLICY_HASH)]);
    let second = fixture(2, 0, 20, 21, vec![mint_row(issued_asset, 7, POLICY_HASH)]);

    compose(core::slice::from_ref(&first), 92, &governed).unwrap();
    compose(core::slice::from_ref(&second), 93, &governed).unwrap();
}

#[test]
fn subtree_grant_policy_cannot_be_substituted_at_closure() {
    let issued_asset = asset(7);
    let fixture = fixture(1, 0, 10, 11, vec![mint_row(issued_asset, 7, POLICY_HASH)]);
    let exact_policy = policy(vec![grant(issued_asset, 7)]);
    let substituted_policy = policy(vec![grant(issued_asset, 8)]);
    let summary = propose_spot_value_subtree_v2(
        core::slice::from_ref(&fixture.leaf),
        core::slice::from_ref(&fixture.opening),
        &exact_policy,
    )
    .unwrap();
    let base = base_proposal(core::slice::from_ref(&fixture.leaf), 92);

    assert_eq!(
        close_spot_represented_value_epoch_v1(&base, &summary, &substituted_policy),
        Err(SpotSemanticValueErrorV1::AuthorityGrantPolicyMismatch)
    );
}

#[test]
fn unused_grant_policy_cannot_relabel_child_summaries_during_merge() {
    let native = [0; 32];
    let left = fixture(1, 0, 10, 11, vec![ordinary_row(native, 1, 0)]);
    let right = fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 1)]);
    let original_policy = policy(vec![grant(asset(7), 1)]);
    let substituted_policy = policy(vec![]);
    let left_summary = propose_spot_value_subtree_v2(
        core::slice::from_ref(&left.leaf),
        core::slice::from_ref(&left.opening),
        &original_policy,
    )
    .unwrap();
    let right_summary = propose_spot_value_subtree_v2(
        core::slice::from_ref(&right.leaf),
        core::slice::from_ref(&right.opening),
        &original_policy,
    )
    .unwrap();

    assert_eq!(
        merge_spot_value_subtrees_v2(&left_summary, &right_summary, &substituted_policy),
        Err(SpotSemanticValueErrorV1::AuthorityGrantPolicyMismatch)
    );
}

#[test]
fn grant_count_and_asset_identifier_bytes_are_bounded_before_hashing() {
    let grants = (0..=MAX_SPOT_MINT_GRANTS_V1)
        .map(|index| {
            let mut asset_id = [0; 32];
            asset_id[30..].copy_from_slice(&(index as u16 + 1).to_be_bytes());
            grant(asset_id, 1)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        SpotRepresentedValuePolicyV1::new(POLICY_HASH, grants),
        Err(SpotSemanticValueErrorV1::TooManyGrants {
            actual: MAX_SPOT_MINT_GRANTS_V1 + 1,
            maximum: MAX_SPOT_MINT_GRANTS_V1,
        })
    );

    let overlong = RecursiveAssetDeltaRowV1 {
        asset_id: "a".repeat(67),
        debit_atoms: 1,
        credit_atoms: 1,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_root: [0; 32],
    };
    assert_eq!(
        SpotValueLeafOpeningV1::new(LANE_ID.to_owned(), root(1), root(2), vec![overlong]),
        Err(SpotSemanticValueErrorV1::NonCanonicalAssetId { ordinal: 0, row: 0 })
    );
}

#[test]
fn malformed_bounded_asset_identifiers_reject_after_exact_legacy_root_opening() {
    for (seed, malformed) in [
        (1, "native".to_owned()),
        (2, format!("0x{}!", "0".repeat(63))),
        (3, format!("0x{}é", "0".repeat(62))),
    ] {
        let row = RecursiveAssetDeltaRowV1 {
            asset_id: malformed,
            debit_atoms: 1,
            credit_atoms: 1,
            authorized_mint_atoms: 0,
            authorized_burn_atoms: 0,
            authority_root: [0; 32],
        };
        let fixture = fixture(seed, 0, 10, 11, vec![row]);
        assert_eq!(
            compose(&[fixture], 92, &policy(vec![])),
            Err(SpotSemanticValueErrorV1::NonCanonicalAssetId { ordinal: 0, row: 0 })
        );
    }
}

#[test]
fn per_leaf_row_bound_accepts_exact_limit_and_rejects_limit_plus_one() {
    let rows = (0..MAX_SPOT_ASSET_ROWS_PER_LEAF_V1)
        .map(|index| ordinary_row(asset(index as u8), 1, 1))
        .collect::<Vec<_>>();
    compose(&[fixture(1, 0, 10, 11, rows)], 92, &policy(vec![])).unwrap();

    let too_many = (0..=MAX_SPOT_ASSET_ROWS_PER_LEAF_V1)
        .map(|index| ordinary_row(asset(index as u8), 1, 1))
        .collect::<Vec<_>>();
    assert_eq!(
        SpotValueLeafOpeningV1::new(LANE_ID.to_owned(), root(1), root(2), too_many),
        Err(SpotSemanticValueErrorV1::TooManyRows {
            ordinal: 0,
            actual: MAX_SPOT_ASSET_ROWS_PER_LEAF_V1 + 1,
            maximum: MAX_SPOT_ASSET_ROWS_PER_LEAF_V1,
        })
    );
}

#[test]
fn summary_row_bound_accepts_exact_limit_and_rejects_limit_plus_one() {
    let exact = (0..MAX_SPOT_VALUE_LEAVES_V1)
        .map(|ordinal| {
            let rows = (0..MAX_SPOT_ASSET_ROWS_PER_LEAF_V1)
                .map(|index| ordinary_row(asset(index as u8), 1, 1))
                .collect::<Vec<_>>();
            fixture(
                (ordinal + 1) as u8,
                ordinal as u64,
                (ordinal + 10) as u8,
                (ordinal + 11) as u8,
                rows,
            )
        })
        .collect::<Vec<_>>();
    compose(&exact, 92, &policy(vec![])).unwrap();

    let mut over = exact;
    over.push(fixture(
        20,
        MAX_SPOT_VALUE_LEAVES_V1 as u64,
        (MAX_SPOT_VALUE_LEAVES_V1 + 10) as u8,
        (MAX_SPOT_VALUE_LEAVES_V1 + 11) as u8,
        vec![ordinary_row(asset(17), 1, 1)],
    ));
    let leaves = over
        .iter()
        .map(|fixture| fixture.leaf.clone())
        .collect::<Vec<_>>();
    let openings = over
        .iter()
        .map(|fixture| fixture.opening.clone())
        .collect::<Vec<_>>();
    assert_eq!(
        propose_spot_value_subtree_v2(&leaves, &openings, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::TooManyRepresentedRows {
            actual: MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2 + 1,
            maximum: MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2,
        })
    );
}

#[test]
fn subtree_leaf_bound_accepts_exact_limit_and_rejects_limit_plus_one() {
    let fixtures = (0..=MAX_SPOT_VALUE_SUBTREE_LEAVES_V2)
        .map(|ordinal| {
            fixture(
                (ordinal + 1) as u8,
                ordinal as u64,
                (ordinal + 1) as u8,
                (ordinal + 2) as u8,
                vec![],
            )
        })
        .collect::<Vec<_>>();
    let leaves = fixtures
        .iter()
        .map(|fixture| fixture.leaf.clone())
        .collect::<Vec<_>>();
    let openings = fixtures
        .iter()
        .map(|fixture| fixture.opening.clone())
        .collect::<Vec<_>>();
    propose_spot_value_subtree_v2(
        &leaves[..MAX_SPOT_VALUE_SUBTREE_LEAVES_V2],
        &openings[..MAX_SPOT_VALUE_SUBTREE_LEAVES_V2],
        &policy(vec![]),
    )
    .unwrap();
    assert_eq!(
        propose_spot_value_subtree_v2(&leaves, &openings, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::TooManyLeaves {
            actual: MAX_SPOT_VALUE_SUBTREE_LEAVES_V2 + 1,
            maximum: MAX_SPOT_VALUE_SUBTREE_LEAVES_V2,
        })
    );
}

#[test]
fn post_lane_base_and_opening_substitutions_fail_closed() {
    let native = [0; 32];
    let original = fixture(1, 0, 10, 11, vec![ordinary_row(native, 2, 2)]);
    let post_substituted = LeafFixture {
        leaf: original.leaf.clone(),
        opening: SpotValueLeafOpeningV1::new(
            LANE_ID.to_owned(),
            root(10),
            root(12),
            vec![ordinary_row(native, 2, 2)],
        )
        .unwrap(),
        structural: original.structural.clone(),
    };
    assert_eq!(
        compose(&[post_substituted], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::StateCommitmentMismatch {
            ordinal: 0,
            side: "post",
        })
    );

    let lane_substituted = LeafFixture {
        leaf: original.leaf.clone(),
        opening: SpotValueLeafOpeningV1::new(
            "spot-value-lane-1".to_owned(),
            root(10),
            root(11),
            vec![ordinary_row(native, 2, 2)],
        )
        .unwrap(),
        structural: original.structural.clone(),
    };
    assert_eq!(
        compose(&[lane_substituted], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::StateCommitmentMismatch {
            ordinal: 0,
            side: "pre",
        })
    );

    let other = fixture(2, 0, 20, 21, vec![ordinary_row(native, 2, 2)]);
    assert_eq!(
        compose_spot_represented_value_v1(
            &base_proposal(core::slice::from_ref(&original.leaf), 92),
            core::slice::from_ref(&other.leaf),
            core::slice::from_ref(&other.opening),
            &policy(vec![]),
        ),
        Err(SpotSemanticValueErrorV1::BaseProposalMismatch)
    );

    let pair = [
        fixture(3, 0, 30, 31, vec![ordinary_row(native, 1, 0)]),
        fixture(4, 1, 31, 32, vec![ordinary_row(native, 0, 1)]),
    ];
    let swapped_openings = [pair[1].opening.clone(), pair[0].opening.clone()];
    assert_eq!(
        compose_spot_represented_value_v1(
            &base_proposal(&[pair[0].leaf.clone(), pair[1].leaf.clone()], 92),
            &[pair[0].leaf.clone(), pair[1].leaf.clone()],
            &swapped_openings,
            &policy(vec![]),
        ),
        Err(SpotSemanticValueErrorV1::StateCommitmentMismatch {
            ordinal: 0,
            side: "pre",
        })
    );
}

#[test]
fn wrong_mint_authority_and_nonchanging_state_reject() {
    let issued_asset = asset(7);
    let mut wrong_authority = mint_row(issued_asset, 7, POLICY_HASH);
    wrong_authority.authority_root = root(9);
    assert_eq!(
        compose(
            &[fixture(1, 0, 10, 11, vec![wrong_authority])],
            92,
            &policy(vec![grant(issued_asset, 7)]),
        ),
        Err(SpotSemanticValueErrorV1::MintAuthorityMismatch { ordinal: 0, row: 0 })
    );

    let unchanged = fixture(2, 0, 20, 20, vec![ordinary_row([0; 32], 1, 1)]);
    assert_eq!(
        compose(&[unchanged], 92, &policy(vec![])),
        Err(SpotSemanticValueErrorV1::NonChangingValueState { ordinal: 0 })
    );
}

#[test]
fn real_spot_faucet_transition_rows_cross_the_value_composer() {
    let issued_asset = asset(7);
    let asset_name = canonical_spot_asset_name_v1(issued_asset);
    let mut input = empty_real_spot_input();
    input.spot_input.txs = vec![TauTxV1 {
        sender_pubkey: "wallet-a".to_owned(),
        app_ops: TauTxAppOpsV1 {
            has_faucet: true,
            faucet_mint: vec![FaucetMintV1 {
                pubkey: "wallet-a".to_owned(),
                asset: asset_name,
                amount: 7,
            }],
            has_intents: false,
            intents: Vec::new(),
        },
    }];
    input.spot_input.tx_ingress = vec![TxIngressFactV1 {
        sender_pubkey: "wallet-a".to_owned(),
        nonce: 0,
    }];
    let mut post_state = DexStateV1::empty();
    post_state
        .add_balance("wallet-a", &canonical_spot_asset_name_v1(issued_asset), 7)
        .unwrap();
    input.spot_input.expected_post_app_hash = post_state.canonical_app_hash_sha256();
    input.spot_input.state_hash = input.spot_input.expected_post_app_hash;

    let rows = spot_recursive_leaf_asset_delta_rows_v1(&input.spot_input, input.public_policy_hash)
        .unwrap();
    let summary = compose_spot_recursive_leaf_summary_v1(input).unwrap();
    assert_eq!(
        summary.asset_delta_root,
        recursive_asset_delta_root_v1(&rows).unwrap()
    );
    let fixture = adapt_summary(summary, rows, 0);
    let projection = compose(&[fixture], 92, &policy(vec![grant(issued_asset, 7)])).unwrap();
    assert_eq!(projection.asset_flows()[0].issued_atoms(), 7);
    assert_eq!(projection.asset_flows()[0].inflow_atoms(), 7);
}

#[test]
fn real_spot_native_sync_rows_cross_the_value_composer() {
    let native = [0; 32];
    let mut input = empty_real_spot_input();
    input.spot_input.pre_state.balances = vec![DexBalanceEntryV1 {
        pubkey: "wallet-a".to_owned(),
        asset: canonical_spot_asset_name_v1(native),
        amount: 10,
    }];
    input.spot_input.chain_balances_post = vec![
        ChainBalanceV1 {
            pubkey: "wallet-a".to_owned(),
            amount: 4,
        },
        ChainBalanceV1 {
            pubkey: "wallet-b".to_owned(),
            amount: 6,
        },
    ];
    let pre_state = DexStateV1::from_snapshot(input.spot_input.pre_state.clone()).unwrap();
    input.spot_input.pre_app_hash = pre_state.canonical_app_hash_sha256();
    let mut post_state = pre_state;
    post_state.sync_native_balances_post(&input.spot_input.chain_balances_post);
    input.spot_input.expected_post_app_hash = post_state.canonical_app_hash_sha256();
    input.spot_input.state_hash = input.spot_input.expected_post_app_hash;

    let rows = spot_recursive_leaf_asset_delta_rows_v1(&input.spot_input, input.public_policy_hash)
        .unwrap();
    let summary = compose_spot_recursive_leaf_summary_v1(input).unwrap();
    assert_eq!(
        summary.asset_delta_root,
        recursive_asset_delta_root_v1(&rows).unwrap()
    );
    let projection = compose(&[adapt_summary(summary, rows, 0)], 92, &policy(vec![])).unwrap();
    assert_eq!(projection.asset_flows()[0].asset_id(), native);
    assert_eq!(projection.asset_flows()[0].outflow_atoms(), 6);
    assert_eq!(projection.asset_flows()[0].inflow_atoms(), 6);
}

#[test]
fn malformed_real_spot_faucet_transition_rejects_before_value_projection() {
    let mut input = empty_real_spot_input();
    input.spot_input.txs = vec![TauTxV1 {
        sender_pubkey: "wallet-a".to_owned(),
        app_ops: TauTxAppOpsV1 {
            has_faucet: false,
            faucet_mint: vec![FaucetMintV1 {
                pubkey: "wallet-a".to_owned(),
                asset: canonical_spot_asset_name_v1(asset(7)),
                amount: 7,
            }],
            has_intents: false,
            intents: Vec::new(),
        },
    }];
    assert!(
        spot_recursive_leaf_asset_delta_rows_v1(&input.spot_input, input.public_policy_hash)
            .is_err()
    );
    assert!(compose_spot_recursive_leaf_summary_v1(input).is_err());
}

#[test]
fn value_profile_and_closed_root_vectors_are_stable() {
    let profile = spot_represented_value_profile_id_v1().unwrap();
    assert_eq!(*profile.as_bytes(), mirror_value_profile_id());

    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 10)]),
    ];
    let governed = policy(vec![]);
    let leaves = fixtures
        .iter()
        .map(|fixture| fixture.leaf.clone())
        .collect::<Vec<_>>();
    let openings = fixtures
        .iter()
        .map(|fixture| fixture.opening.clone())
        .collect::<Vec<_>>();
    let subtree = propose_spot_value_subtree_v2(&leaves, &openings, &governed).unwrap();
    let projection =
        close_spot_represented_value_epoch_v1(&base_proposal(&leaves, 92), &subtree, &governed)
            .unwrap();

    assert_eq!(
        hex32(*spot_atoms_unit_id_v1().unwrap().as_bytes()),
        "75b2937b0224d9accb8cf6d3c6f43dcf381dce412720afa5da982f797ce264fb"
    );
    assert_eq!(
        hex32(*spot_accounting_domain_id_v1().unwrap().as_bytes()),
        "9486db0738818c3bd2d1009516d64861481d03de5d0e7f0b294b0eb41dcde316"
    );
    assert_eq!(
        hex32(*spot_state_root_scheme_id_v1().unwrap().as_bytes()),
        "b01a20d7e5d1024289330875c2c6521632a57b82295ae7aa2eb3792c8bb7314a"
    );
    assert_eq!(
        hex32(*profile.as_bytes()),
        "20f73c0589af1ff8e8519c4cf522cb423a06589b19173b6deccfe7c386129c6d"
    );
    assert_eq!(
        hex32(*subtree.subtree_root().as_bytes()),
        "144ea9eeab83a4e02b35a1f592dbfec2fe2e7f962dd2fb5288ae096a64d7e856"
    );
    assert_eq!(
        hex32(*projection.semantic_value_root().as_bytes()),
        "827958dcd3ad40edfac0a395db3b3b98a02118e248f4bff54413d920e387d14c"
    );
    assert_eq!(
        hex32(*projection.proposal_hash().as_bytes()),
        "8880d620c7e8763b2ea45ffaed6bb302d9d36bd81743199d8b0134fb5a028fce"
    );
}

#[test]
fn exact_expected_statement_match_is_a_distinct_sealed_transition() {
    let (projection, scope) = balanced_projection();
    let input = expected_input(scope, &projection);
    let mirror_hash = mirror_expected_statement_hash(&input);
    let expected = ExpectedSpotSemanticValueV1::new(input).unwrap();

    assert_eq!(*expected.statement_hash().as_bytes(), mirror_hash);
    let matched = match_expected_spot_semantic_value_v1(projection.clone(), &expected).unwrap();
    assert_eq!(matched.projection(), &projection);
    assert_eq!(matched.expected_statement_hash(), expected.statement_hash());
    assert_eq!(
        hex32(*expected.statement_hash().as_bytes()),
        "2db123542625f35539a98a811091e4aa2140bdcc132f29f1fc48d8c185ea6bca"
    );
}

#[test]
fn ordinary_spot_summary_has_exact_v1_v4_root_and_statement_parity() {
    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 10)]),
    ];
    let (summary, projection, scope) =
        closed_summary_and_projection(&fixtures, 92, &policy(vec![]));
    let subtree = semantic_subtree_v2_from_spot_summary(&summary).unwrap();

    assert_eq!(subtree.value_subtree_root(), summary.subtree_root());
    assert_eq!(
        subtree.value_subtree_root(),
        projection.commitments().value_subtree_root()
    );
    assert_eq!(
        decode_exact_semantic_subtree_v2(&encode_semantic_subtree_v2(&subtree).unwrap()).unwrap(),
        subtree
    );

    let expected = ExpectedSpotSemanticValueV1::new(expected_input(scope, &projection)).unwrap();
    let expected_hash = expected.statement_hash();
    let matched = match_expected_spot_semantic_value_v1(projection, &expected).unwrap();
    let bound = bind_expected_spot_semantic_subtree_v4(&summary, matched).unwrap();
    assert_eq!(bound.semantic_subtree(), &subtree);
    assert_eq!(bound.application_statement_hash(), expected_hash);
    assert_eq!(bound.semantic_value_root(), expected.semantic_value_root());
}

#[test]
fn sealed_spot_match_supplies_the_v4_application_statement_hash() {
    let native = [0; 32];
    let fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 10)]),
    ];
    let (summary, projection, scope) =
        closed_summary_and_projection(&fixtures, 92, &policy(vec![]));
    let expected = ExpectedSpotSemanticValueV1::new(expected_input(scope, &projection)).unwrap();
    let expected_hash = expected.statement_hash();
    let matched = match_expected_spot_semantic_value_v1(projection, &expected).unwrap();
    let bound = bind_expected_spot_semantic_subtree_v4(&summary, matched).unwrap();

    let journal = NodeJournalV4::new(NodeJournalInputV4 {
        structural: structural_parent(&fixtures),
        semantic_subtree: bound.semantic_subtree().clone(),
        application_statement_hash: bound.application_statement_hash(),
        proof_profile_id: ProfileIdV3::new(root(225)).unwrap(),
        actual_program_id: ProgramIdV3::new(root(226)).unwrap(),
        proof_system_id: CommitmentV3::new(root(227)).unwrap(),
        receipt_security_profile_id: CommitmentV3::new(root(228)).unwrap(),
        verifier_parameters_root: CommitmentV3::new(root(229)).unwrap(),
        program_manifest_root: CommitmentV3::new(root(230)).unwrap(),
        child_semantic_journal_hashes: vec![
            CommitmentV3::new(root(231)).unwrap(),
            CommitmentV3::new(root(232)).unwrap(),
        ],
    })
    .unwrap();

    assert_eq!(journal.application_statement_hash(), expected_hash);
    assert_eq!(journal.semantic_subtree(), bound.semantic_subtree());
    assert_ne!(journal.semantic_statement_hash(), expected_hash);
}

#[test]
fn governed_spot_mint_has_exact_v1_v4_flow_and_authority_parity() {
    let minted_asset = asset(7);
    let fixtures = [fixture(
        5,
        0,
        30,
        31,
        vec![mint_row(minted_asset, 25, POLICY_HASH)],
    )];
    let governed = policy(vec![grant(minted_asset, 25)]);
    let (summary, projection, scope) = closed_summary_and_projection(&fixtures, 93, &governed);
    let expected = ExpectedSpotSemanticValueV1::new(expected_input(scope, &projection)).unwrap();
    let matched = match_expected_spot_semantic_value_v1(projection, &expected).unwrap();
    let bound = bind_expected_spot_semantic_subtree_v4(&summary, matched).unwrap();
    let subtree = bound.semantic_subtree();

    assert_eq!(subtree.value_subtree_root(), summary.subtree_root());
    assert_eq!(subtree.asset_flows().len(), 1);
    assert_eq!(subtree.asset_flows()[0].asset_id(), minted_asset);
    assert_eq!(subtree.asset_flows()[0].issued_atoms(), 25);
    assert_eq!(subtree.authority_uses().len(), 1);
    assert_eq!(subtree.authority_uses()[0].asset_id(), minted_asset);
    assert_eq!(subtree.authority_uses()[0].atoms(), 25);
}

#[test]
fn v4_subtree_rejects_a_valid_summary_from_an_unmatched_projection() {
    let native = [0; 32];
    let expected_fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 10)]),
    ];
    let substituted_fixtures = [
        fixture(3, 0, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(4, 1, 11, 12, vec![ordinary_row(native, 0, 10)]),
    ];
    let governed = policy(vec![]);
    let (_, projection, scope) = closed_summary_and_projection(&expected_fixtures, 92, &governed);
    let (substituted_summary, _, _) =
        closed_summary_and_projection(&substituted_fixtures, 93, &governed);
    let expected = ExpectedSpotSemanticValueV1::new(expected_input(scope, &projection)).unwrap();
    let matched = match_expected_spot_semantic_value_v1(projection, &expected).unwrap();

    assert_eq!(
        bind_expected_spot_semantic_subtree_v4(&substituted_summary, matched),
        Err(SpotValueWireErrorV4::ExpectedProjectionMismatch(
            SpotValueWireFieldV4::SemanticLeafRecordsRoot,
        ))
    );
}

#[test]
fn expected_spot_projection_rejects_an_off_origin_v4_subtree() {
    let native = [0; 32];
    let expected_fixtures = [
        fixture(1, 0, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(2, 1, 11, 12, vec![ordinary_row(native, 0, 10)]),
    ];
    let off_origin_fixtures = [
        fixture(3, 2, 10, 11, vec![ordinary_row(native, 10, 0)]),
        fixture(4, 3, 11, 12, vec![ordinary_row(native, 0, 10)]),
    ];
    let governed = policy(vec![]);
    let (_, projection, scope) = closed_summary_and_projection(&expected_fixtures, 92, &governed);
    let off_origin_leaves = off_origin_fixtures
        .iter()
        .map(|fixture| fixture.leaf.clone())
        .collect::<Vec<_>>();
    let off_origin_openings = off_origin_fixtures
        .iter()
        .map(|fixture| fixture.opening.clone())
        .collect::<Vec<_>>();
    let off_origin_summary =
        propose_spot_value_subtree_v2(&off_origin_leaves, &off_origin_openings, &governed).unwrap();
    let expected = ExpectedSpotSemanticValueV1::new(expected_input(scope, &projection)).unwrap();
    let matched = match_expected_spot_semantic_value_v1(projection, &expected).unwrap();

    assert_eq!(
        bind_expected_spot_semantic_subtree_v4(&off_origin_summary, matched),
        Err(SpotValueWireErrorV4::ExpectedProjectionMismatch(
            SpotValueWireFieldV4::Partition,
        ))
    );
}

#[test]
fn expected_scope_lane_and_ordering_reject_independent_substitution() {
    let (projection, scope) = balanced_projection();
    let baseline = expected_input(scope, &projection);
    let baseline_hash = ExpectedSpotSemanticValueV1::new(baseline.clone())
        .unwrap()
        .statement_hash();

    let mut input = baseline.clone();
    input.scope = unrelated_scope(71, 71);
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::ScopeHash,
    );

    let mut input = baseline.clone();
    input.lane_id_hash = CommitmentV3::new(root(190)).unwrap();
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::LaneIdHash,
    );

    let mut input = baseline.clone();
    input.ordered_transaction_roots_root = CommitmentV3::new(root(191)).unwrap();
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::OrderedTransactionRootsRoot,
    );

    let mut input = baseline.clone();
    input.state_chain_root = CommitmentV3::new(root(192)).unwrap();
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::StateChainRoot,
    );
}

#[test]
fn expected_endpoints_and_counts_reject_independent_substitution() {
    let (projection, scope) = balanced_projection();
    let baseline = expected_input(scope, &projection);
    let baseline_hash = ExpectedSpotSemanticValueV1::new(baseline.clone())
        .unwrap()
        .statement_hash();

    let mut input = baseline.clone();
    input.raw_pre_state_root = root(193);
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::RawPreStateRoot,
    );

    let mut input = baseline.clone();
    input.raw_post_state_root = root(194);
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::RawPostStateRoot,
    );

    let mut input = baseline.clone();
    input.leaf_count += 1;
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::LeafCount,
    );

    let mut input = baseline.clone();
    input.represented_row_count += 1;
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::RepresentedRowCount,
    );
}

#[test]
fn expected_policy_and_terminal_roots_reject_independent_substitution() {
    let (projection, scope) = balanced_projection();
    let baseline = expected_input(scope, &projection);
    let baseline_hash = ExpectedSpotSemanticValueV1::new(baseline.clone())
        .unwrap()
        .statement_hash();

    let mut input = baseline.clone();
    input.authority_grants_root = CommitmentV3::new(root(195)).unwrap();
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::AuthorityGrantsRoot,
    );

    let mut input = baseline.clone();
    input.base_semantic_epoch_root = CommitmentV3::new(root(196)).unwrap();
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::BaseSemanticEpochRoot,
    );

    let mut input = baseline;
    input.semantic_value_root = CommitmentV3::new(root(197)).unwrap();
    assert_expected_mismatch(
        &projection,
        baseline_hash,
        input,
        ExpectedSpotSemanticValueFieldV1::SemanticValueRoot,
    );
}

#[test]
fn expected_statement_rejects_profile_relabeling_before_matching() {
    let (projection, scope) = balanced_projection();
    let baseline = expected_input(scope, &projection);

    let mut input = baseline.clone();
    input.value_profile_id = CommitmentV3::new(root(200)).unwrap();
    assert_eq!(
        ExpectedSpotSemanticValueV1::new(input),
        Err(SpotSemanticValueErrorV1::ExpectedProfileMismatch(
            ExpectedSpotSemanticValueFieldV1::ValueProfileId
        ))
    );

    let mut input = baseline.clone();
    input.accounting_domain_id = CommitmentV3::new(root(201)).unwrap();
    assert_eq!(
        ExpectedSpotSemanticValueV1::new(input),
        Err(SpotSemanticValueErrorV1::ExpectedProfileMismatch(
            ExpectedSpotSemanticValueFieldV1::AccountingDomainId
        ))
    );

    let mut input = baseline.clone();
    input.atoms_unit_id = CommitmentV3::new(root(202)).unwrap();
    assert_eq!(
        ExpectedSpotSemanticValueV1::new(input),
        Err(SpotSemanticValueErrorV1::ExpectedProfileMismatch(
            ExpectedSpotSemanticValueFieldV1::AtomsUnitId
        ))
    );

    let mut input = baseline;
    input.state_root_scheme_id = CommitmentV3::new(root(203)).unwrap();
    assert_eq!(
        ExpectedSpotSemanticValueV1::new(input),
        Err(SpotSemanticValueErrorV1::ExpectedProfileMismatch(
            ExpectedSpotSemanticValueFieldV1::StateRootSchemeId
        ))
    );
}

#[test]
fn expected_statement_shape_is_bounded_and_single_epoch() {
    let (projection, scope) = balanced_projection();
    let baseline = expected_input(scope, &projection);

    let mut input = baseline.clone();
    input.raw_pre_state_root = [0; 32];
    assert_eq!(
        ExpectedSpotSemanticValueV1::new(input),
        Err(SpotSemanticValueErrorV1::ExpectedStatementShape(
            ExpectedSpotSemanticValueFieldV1::RawPreStateRoot
        ))
    );

    let mut input = baseline.clone();
    input.raw_post_state_root = [0; 32];
    assert_eq!(
        ExpectedSpotSemanticValueV1::new(input),
        Err(SpotSemanticValueErrorV1::ExpectedStatementShape(
            ExpectedSpotSemanticValueFieldV1::RawPostStateRoot
        ))
    );

    for leaf_count in [0, MAX_SPOT_VALUE_LEAVES_V1 as u64 + 1] {
        let mut input = baseline.clone();
        input.leaf_count = leaf_count;
        assert_eq!(
            ExpectedSpotSemanticValueV1::new(input),
            Err(SpotSemanticValueErrorV1::ExpectedStatementShape(
                ExpectedSpotSemanticValueFieldV1::LeafCount
            ))
        );
    }

    for represented_row_count in [0, MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2 as u64 + 1] {
        let mut input = baseline.clone();
        input.represented_row_count = represented_row_count;
        assert_eq!(
            ExpectedSpotSemanticValueV1::new(input),
            Err(SpotSemanticValueErrorV1::ExpectedStatementShape(
                ExpectedSpotSemanticValueFieldV1::RepresentedRowCount
            ))
        );
    }

    let mut input = baseline;
    input.scope = unrelated_scope(70, 71);
    assert_eq!(
        ExpectedSpotSemanticValueV1::new(input),
        Err(SpotSemanticValueErrorV1::EpochRangeUnsupported)
    );
}
