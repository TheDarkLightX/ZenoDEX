use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_epoch_test_methods::{
    ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF, ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID,
};
use zenodex_global_economic_epoch_risc0_host::{
    build_economic_epoch_executor_env_v1, prove_command_aggregation_succinct_v1,
    prove_economic_epoch_succinct_v1, EconomicEpochHostErrorV1,
};
use zenodex_global_economic_epoch_risc0_methods::ZENODEX_ECONOMIC_EPOCH_GUEST_ID;
use zenodex_global_economic_epoch_risc0_shared::{
    canonical_json_bytes_v1, derive_route_composition_assumption_root_v1, image_id_root_v1,
    sha256_root_v1, CommandAggregationGuestInputV1, CommandAggregationJournalV1,
    EconomicEpochGuestInputV1, GlobalEconomicEpochJournalV1, RootV1,
    RouteCompositionAssumptionInputV1, RouteCompositionJournalV1, RouteReceiptClaimV1,
    COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1, GLOBAL_SETTLEMENT_ABI_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "real proof test root", false).unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(
        "0x0000000000000000000000000000000000000000000000000000000000000000",
        "real proof zero root",
        true,
    )
    .unwrap()
}

fn real_proof_input() -> EconomicEpochGuestInputV1 {
    assert_ne!(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID, [0; 8]);
    assert_ne!(ZENODEX_ECONOMIC_EPOCH_GUEST_ID, [0; 8]);
    let profile_root = root(10);
    let deployment_root = root(11);
    let pre_state_root = root(12);
    let post_state_root = root(13);
    let route_image_root = image_id_root_v1(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID).unwrap();
    let route_journal = RouteCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-real-composition-test".to_owned(),
        deployment_root: deployment_root.clone(),
        profile_root: profile_root.clone(),
        writer_epoch: 7,
        route_release_id: root(14),
        command_occurrence_id: root(15),
        ordered_lane_journal_roots: vec![root(16)],
        pre_state_root: pre_state_root.clone(),
        post_state_root: post_state_root.clone(),
        effect_plan_root: root(17),
        terminal_obligations_root: zero_root(),
    };
    let route_journal_bytes =
        canonical_json_bytes_v1(&route_journal, "real proof route journal").unwrap();
    let route_journal_root = route_journal.journal_root().unwrap();
    let route_journal_digest = sha256_root_v1(&route_journal_bytes);
    let route_assumption_root =
        derive_route_composition_assumption_root_v1(&RouteCompositionAssumptionInputV1 {
            profile_id: &profile_root,
            route_release_id: &route_journal.route_release_id,
            command_occurrence_id: &route_journal.command_occurrence_id,
            writer_epoch: 7,
            route_journal_root: &route_journal_root,
            route_journal_digest: &route_journal_digest,
            expected_image_id: &route_image_root,
        })
        .unwrap();
    let certificate = GlobalEconomicEpochJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: route_journal.chain_id.clone(),
        deployment_root,
        profile_root,
        writer_epoch: 7,
        height: 42,
        pre_state_root,
        post_state_root,
        ordered_occurrence_ids: vec![route_journal.command_occurrence_id.clone()],
        ordered_route_journal_roots: vec![route_journal_root],
        ordered_route_assumption_roots: vec![route_assumption_root],
        module_leaf_occurrences: 1,
        aggregation_fanout: 8,
        aggregation_levels: 0,
        effect_plan_root: route_journal.effect_plan_root,
        terminal_obligations_root: zero_root(),
        body_commitment: root(18),
        data_availability_root: root(19),
        finality_root: root(20),
        source_manifest_root: root(21),
        toolchain_manifest_root: root(22),
        root_image_id: image_id_root_v1(ZENODEX_ECONOMIC_EPOCH_GUEST_ID).unwrap(),
    };
    EconomicEpochGuestInputV1 {
        certificate_journal_bytes: canonical_json_bytes_v1(
            &certificate,
            "real proof epoch certificate",
        )
        .unwrap(),
        route_receipts: vec![RouteReceiptClaimV1 {
            image_id: ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID,
            journal_bytes: route_journal_bytes,
        }],
    }
}

fn prove_structural_test_leaf(input: &EconomicEpochGuestInputV1) -> Receipt {
    assert!(!ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF.is_empty());
    let journal_bytes = &input.route_receipts[0].journal_bytes;
    let journal_len = u32::try_from(journal_bytes.len()).unwrap();
    let env = ExecutorEnv::builder()
        .write_slice(&[journal_len])
        .write_slice(journal_bytes)
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
    assert_eq!(receipt.journal.bytes, *journal_bytes);
    receipt
}

fn command_aggregation_input(direct: &EconomicEpochGuestInputV1) -> CommandAggregationGuestInputV1 {
    let certificate: GlobalEconomicEpochJournalV1 =
        serde_json::from_slice(&direct.certificate_journal_bytes).unwrap();
    let journal = CommandAggregationJournalV1 {
        schema: COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1.to_owned(),
        settlement_abi: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: certificate.chain_id,
        deployment_root: certificate.deployment_root,
        profile_root: certificate.profile_root,
        writer_epoch: certificate.writer_epoch,
        epoch_height: certificate.height,
        group_index: 0,
        first_command_index: 0,
        ordered_occurrence_ids: certificate.ordered_occurrence_ids,
        ordered_route_journal_roots: certificate.ordered_route_journal_roots,
        ordered_route_assumption_roots: certificate.ordered_route_assumption_roots,
        pre_state_root: certificate.pre_state_root,
        post_state_root: certificate.post_state_root,
        module_leaf_occurrences: certificate.module_leaf_occurrences,
    };
    CommandAggregationGuestInputV1 {
        aggregation_journal_bytes: journal.canonical_bytes().unwrap(),
        route_receipts: direct.route_receipts.clone(),
    }
}

#[test]
#[ignore = "generates three real RISC0 Succinct receipts; run as release evidence"]
fn real_succinct_child_assumption_resolves_into_exact_epoch_journal() {
    // Arrange
    let input = real_proof_input();
    let child_receipt = prove_structural_test_leaf(&input);
    let aggregation_input = command_aggregation_input(&input);
    assert!(matches!(
        build_economic_epoch_executor_env_v1(&input, vec![]),
        Err(EconomicEpochHostErrorV1::ReceiptCount)
    ));
    let mut wrong_journal = child_receipt.clone();
    wrong_journal.journal.bytes.push(b'\n');
    assert!(matches!(
        build_economic_epoch_executor_env_v1(&input, vec![wrong_journal]),
        Err(EconomicEpochHostErrorV1::ReceiptJournal)
    ));
    let mut foreign_method_input = input.clone();
    let mut foreign_certificate: GlobalEconomicEpochJournalV1 =
        serde_json::from_slice(&foreign_method_input.certificate_journal_bytes).unwrap();
    foreign_certificate.root_image_id = root(99_999);
    foreign_method_input.certificate_journal_bytes =
        canonical_json_bytes_v1(&foreign_certificate, "foreign method certificate").unwrap();
    assert!(matches!(
        prove_economic_epoch_succinct_v1(&foreign_method_input, vec![]),
        Err(EconomicEpochHostErrorV1::MethodBinding)
    ));

    // Act
    let aggregation_receipt =
        prove_command_aggregation_succinct_v1(&aggregation_input, vec![child_receipt.clone()])
            .unwrap();
    let root_receipt = prove_economic_epoch_succinct_v1(&input, vec![child_receipt]).unwrap();

    // Assert
    assert!(matches!(
        &aggregation_receipt.inner,
        InnerReceipt::Succinct(_)
    ));
    assert_eq!(
        aggregation_receipt.journal.bytes,
        aggregation_input.aggregation_journal_bytes
    );
    aggregation_receipt
        .verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID)
        .unwrap();
    assert!(matches!(&root_receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(root_receipt.journal.bytes, input.certificate_journal_bytes);
    root_receipt
        .verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID)
        .unwrap();
}
