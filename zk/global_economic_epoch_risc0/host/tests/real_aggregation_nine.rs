use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_epoch_test_methods::{
    ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF, ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID,
};
use zenodex_global_economic_epoch_risc0_host::{
    prove_aggregated_economic_epoch_succinct_v1, prove_command_aggregation_succinct_v1,
    prove_economic_epoch_succinct_v1,
};
use zenodex_global_economic_epoch_risc0_methods::ZENODEX_ECONOMIC_EPOCH_GUEST_ID;
use zenodex_global_economic_epoch_risc0_shared::{
    canonical_json_bytes_v1, derive_route_composition_assumption_root_v1, image_id_root_v1,
    sha256_root_v1, AggregatedEconomicEpochGuestInputV1, CommandAggregationGuestInputV1,
    CommandAggregationJournalV1, CommandAggregationReceiptClaimV1, EconomicEpochGuestInputV1,
    GlobalEconomicEpochJournalV1, RootV1, RouteCompositionAssumptionInputV1,
    RouteCompositionJournalV1, RouteReceiptClaimV1, COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1,
    GLOBAL_SETTLEMENT_ABI_V1, MAX_DIRECT_ROUTE_ASSUMPTIONS_V1, MAX_EPOCH_COMMANDS_V1,
};

struct BoundedCommandTopologyV1 {
    command_count: usize,
    groups: Vec<CommandAggregationGuestInputV1>,
    aggregated_epoch: AggregatedEconomicEpochGuestInputV1,
}

struct RouteRowV1 {
    pre_state_root: RootV1,
    post_state_root: RootV1,
    receipt_claim: RouteReceiptClaimV1,
    occurrence_id: RootV1,
    journal_root: RootV1,
    assumption_root: RootV1,
}

struct RouteChainV1 {
    profile_root: RootV1,
    deployment_root: RootV1,
    pre_state_root: RootV1,
    post_state_root: RootV1,
    rows: Vec<RouteRowV1>,
}

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "real bounded-command root",
        false,
    )
    .unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(
        "0x0000000000000000000000000000000000000000000000000000000000000000",
        "real bounded-command zero root",
        true,
    )
    .unwrap()
}

fn route_row(
    index: u64,
    profile_root: &RootV1,
    deployment_root: &RootV1,
    pre_state_root: RootV1,
) -> RouteRowV1 {
    let post_state_root = root(100 + index);
    let route = RouteCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-real-bounded-command-test".to_owned(),
        deployment_root: deployment_root.clone(),
        profile_root: profile_root.clone(),
        writer_epoch: 7,
        route_release_id: root(200),
        command_occurrence_id: root(300 + index),
        ordered_lane_journal_roots: vec![root(400 + index)],
        pre_state_root: pre_state_root.clone(),
        post_state_root: post_state_root.clone(),
        effect_plan_root: root(500 + index),
        terminal_obligations_root: zero_root(),
    };
    let journal_bytes = canonical_json_bytes_v1(&route, "real bounded route journal").unwrap();
    let journal_root = route.journal_root().unwrap();
    let journal_digest = sha256_root_v1(&journal_bytes);
    let route_image_root = image_id_root_v1(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID).unwrap();
    let assumption_root =
        derive_route_composition_assumption_root_v1(&RouteCompositionAssumptionInputV1 {
            profile_id: profile_root,
            route_release_id: &route.route_release_id,
            command_occurrence_id: &route.command_occurrence_id,
            writer_epoch: 7,
            route_journal_root: &journal_root,
            route_journal_digest: &journal_digest,
            expected_image_id: &route_image_root,
        })
        .unwrap();
    RouteRowV1 {
        pre_state_root,
        post_state_root,
        receipt_claim: RouteReceiptClaimV1 {
            image_id: ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID,
            journal_bytes,
        },
        occurrence_id: route.command_occurrence_id,
        journal_root,
        assumption_root,
    }
}

fn route_chain(command_count: usize) -> RouteChainV1 {
    assert!((1..=MAX_EPOCH_COMMANDS_V1).contains(&command_count));
    let profile_root = root(10);
    let deployment_root = root(11);
    let pre_state_root = root(12);
    let mut current_root = pre_state_root.clone();
    let mut rows = Vec::with_capacity(command_count);
    for index in 0..u64::try_from(command_count).unwrap() {
        let row = route_row(index, &profile_root, &deployment_root, current_root);
        current_root = row.post_state_root.clone();
        rows.push(row);
    }
    RouteChainV1 {
        profile_root,
        deployment_root,
        pre_state_root,
        post_state_root: current_root,
        rows,
    }
}

fn epoch_certificate(chain: &RouteChainV1) -> GlobalEconomicEpochJournalV1 {
    let command_count = chain.rows.len();
    GlobalEconomicEpochJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-real-bounded-command-test".to_owned(),
        deployment_root: chain.deployment_root.clone(),
        profile_root: chain.profile_root.clone(),
        writer_epoch: 7,
        height: 42,
        pre_state_root: chain.pre_state_root.clone(),
        post_state_root: chain.post_state_root.clone(),
        ordered_occurrence_ids: chain
            .rows
            .iter()
            .map(|row| row.occurrence_id.clone())
            .collect(),
        ordered_route_journal_roots: chain
            .rows
            .iter()
            .map(|row| row.journal_root.clone())
            .collect(),
        ordered_route_assumption_roots: chain
            .rows
            .iter()
            .map(|row| row.assumption_root.clone())
            .collect(),
        module_leaf_occurrences: u64::try_from(command_count).unwrap(),
        aggregation_fanout: 8,
        aggregation_levels: u64::from(command_count > MAX_DIRECT_ROUTE_ASSUMPTIONS_V1),
        effect_plan_root: root(600),
        terminal_obligations_root: zero_root(),
        body_commitment: root(601),
        data_availability_root: root(602),
        finality_root: root(603),
        source_manifest_root: root(604),
        toolchain_manifest_root: root(605),
        root_image_id: image_id_root_v1(ZENODEX_ECONOMIC_EPOCH_GUEST_ID).unwrap(),
    }
}

fn command_group(
    group_index: usize,
    start: usize,
    certificate: &GlobalEconomicEpochJournalV1,
    chain: &RouteChainV1,
) -> (
    CommandAggregationGuestInputV1,
    CommandAggregationReceiptClaimV1,
) {
    let end = core::cmp::min(start + MAX_DIRECT_ROUTE_ASSUMPTIONS_V1, chain.rows.len());
    let journal = CommandAggregationJournalV1 {
        schema: COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1.to_owned(),
        settlement_abi: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: certificate.chain_id.clone(),
        deployment_root: certificate.deployment_root.clone(),
        profile_root: certificate.profile_root.clone(),
        writer_epoch: certificate.writer_epoch,
        epoch_height: certificate.height,
        group_index: group_index as u64,
        first_command_index: start as u64,
        ordered_occurrence_ids: certificate.ordered_occurrence_ids[start..end].to_vec(),
        ordered_route_journal_roots: certificate.ordered_route_journal_roots[start..end].to_vec(),
        ordered_route_assumption_roots: certificate.ordered_route_assumption_roots[start..end]
            .to_vec(),
        pre_state_root: chain.rows[start].pre_state_root.clone(),
        post_state_root: chain.rows[end - 1].post_state_root.clone(),
        module_leaf_occurrences: (end - start) as u64,
    };
    let journal_bytes = journal.canonical_bytes().unwrap();
    (
        CommandAggregationGuestInputV1 {
            aggregation_journal_bytes: journal_bytes.clone(),
            route_receipts: chain.rows[start..end]
                .iter()
                .map(|row| row.receipt_claim.clone())
                .collect(),
        },
        CommandAggregationReceiptClaimV1 {
            image_id: ZENODEX_ECONOMIC_EPOCH_GUEST_ID,
            journal_bytes,
        },
    )
}

fn aggregated_command_topology(command_count: usize) -> BoundedCommandTopologyV1 {
    assert_ne!(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID, [0; 8]);
    assert_ne!(ZENODEX_ECONOMIC_EPOCH_GUEST_ID, [0; 8]);
    assert!((MAX_DIRECT_ROUTE_ASSUMPTIONS_V1 + 1..=MAX_EPOCH_COMMANDS_V1).contains(&command_count));
    let chain = route_chain(command_count);
    let certificate = epoch_certificate(&chain);

    let group_count = command_count.div_ceil(MAX_DIRECT_ROUTE_ASSUMPTIONS_V1);
    let mut groups = Vec::with_capacity(group_count);
    let mut aggregation_claims = Vec::with_capacity(group_count);
    for (group_index, start) in (0..command_count)
        .step_by(MAX_DIRECT_ROUTE_ASSUMPTIONS_V1)
        .enumerate()
    {
        let (group, claim) = command_group(group_index, start, &certificate, &chain);
        groups.push(group);
        aggregation_claims.push(claim);
    }
    BoundedCommandTopologyV1 {
        command_count,
        groups,
        aggregated_epoch: AggregatedEconomicEpochGuestInputV1 {
            certificate_journal_bytes: canonical_json_bytes_v1(
                &certificate,
                "real bounded-command certificate",
            )
            .unwrap(),
            command_aggregation_receipts: aggregation_claims,
        },
    }
}

fn prove_structural_route(claim: &RouteReceiptClaimV1) -> Receipt {
    let journal_len = u32::try_from(claim.journal_bytes.len()).unwrap();
    let env = ExecutorEnv::builder()
        .write_slice(&[journal_len])
        .write_slice(&claim.journal_bytes)
        .build()
        .unwrap();
    let receipt = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF,
            &ProverOpts::succinct(),
        )
        .unwrap()
        .receipt;
    assert!(matches!(&receipt.inner, InnerReceipt::Succinct(_)));
    receipt
        .verify(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID)
        .unwrap();
    assert_eq!(receipt.journal.bytes, claim.journal_bytes);
    receipt
}

fn prove_direct_epoch(command_count: usize) {
    // Arrange
    assert!((1..=MAX_DIRECT_ROUTE_ASSUMPTIONS_V1).contains(&command_count));
    let chain = route_chain(command_count);
    let certificate = epoch_certificate(&chain);
    let input = EconomicEpochGuestInputV1 {
        certificate_journal_bytes: canonical_json_bytes_v1(
            &certificate,
            "real direct bounded-command certificate",
        )
        .unwrap(),
        route_receipts: chain
            .rows
            .iter()
            .map(|row| row.receipt_claim.clone())
            .collect(),
    };
    let mut route_receipts = Vec::with_capacity(command_count);

    // Act
    for claim in &input.route_receipts {
        route_receipts.push(prove_structural_route(claim));
        eprintln!(
            "proved direct structural route {}/{}",
            route_receipts.len(),
            command_count
        );
    }
    let root_receipt = prove_economic_epoch_succinct_v1(&input, route_receipts).unwrap();

    // Assert
    assert!(matches!(&root_receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(root_receipt.journal.bytes, input.certificate_journal_bytes);
    root_receipt
        .verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID)
        .unwrap();
}

fn prove_aggregated_epoch(command_count: usize) {
    // Arrange
    let topology = aggregated_command_topology(command_count);
    let group_count = topology.groups.len();
    let mut aggregation_receipts = Vec::with_capacity(group_count);
    let mut proved_route_count = 0usize;

    // Act
    for (group_index, group) in topology.groups.iter().enumerate() {
        let mut route_receipts = Vec::with_capacity(group.route_receipts.len());
        for claim in &group.route_receipts {
            route_receipts.push(prove_structural_route(claim));
            proved_route_count += 1;
            eprintln!(
                "proved structural route {}/{}",
                proved_route_count, topology.command_count
            );
        }
        let receipt = prove_command_aggregation_succinct_v1(group, route_receipts).unwrap();
        assert!(matches!(&receipt.inner, InnerReceipt::Succinct(_)));
        assert_eq!(receipt.journal.bytes, group.aggregation_journal_bytes);
        receipt.verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID).unwrap();
        aggregation_receipts.push(receipt);
        eprintln!(
            "proved command aggregation {}/{}",
            group_index + 1,
            group_count
        );
    }
    let root_receipt = prove_aggregated_economic_epoch_succinct_v1(
        &topology.aggregated_epoch,
        aggregation_receipts,
    )
    .unwrap();

    // Assert
    assert!(matches!(&root_receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(
        root_receipt.journal.bytes,
        topology.aggregated_epoch.certificate_journal_bytes
    );
    root_receipt
        .verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID)
        .unwrap();
}

#[test]
#[ignore = "generates nine real RISC0 Succinct receipts; run as release evidence"]
fn eight_routes_compose_directly_into_one_exact_epoch_root() {
    prove_direct_epoch(MAX_DIRECT_ROUTE_ASSUMPTIONS_V1);
}

#[test]
#[ignore = "generates twelve real RISC0 Succinct receipts; run as release evidence"]
fn nine_routes_compose_through_two_groups_into_one_exact_epoch_root() {
    prove_aggregated_epoch(MAX_DIRECT_ROUTE_ASSUMPTIONS_V1 + 1);
}

#[test]
#[ignore = "generates seventy-three real RISC0 Succinct receipts; run as release evidence"]
fn sixty_four_routes_compose_through_eight_groups_into_one_exact_epoch_root() {
    prove_aggregated_epoch(MAX_EPOCH_COMMANDS_V1);
}
