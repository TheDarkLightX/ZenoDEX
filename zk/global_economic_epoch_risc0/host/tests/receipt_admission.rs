use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use zenodex_global_economic_epoch_risc0_host::{
    build_aggregated_economic_epoch_executor_env_v1, build_command_aggregation_executor_env_v1,
    build_economic_epoch_executor_env_v1, EconomicEpochHostErrorV1,
};
use zenodex_global_economic_epoch_risc0_shared::{
    canonical_json_bytes_v1, derive_route_composition_assumption_root_v1, image_id_root_v1,
    sha256_root_v1, AggregatedEconomicEpochGuestInputV1, CommandAggregationGuestInputV1,
    CommandAggregationJournalV1, CommandAggregationReceiptClaimV1, EconomicEpochGuestInputV1,
    GlobalEconomicEpochJournalV1, RootV1, RouteCompositionAssumptionInputV1,
    RouteCompositionJournalV1, RouteReceiptClaimV1, COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1,
    GLOBAL_SETTLEMENT_ABI_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "host admission test root", false).unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(
        "0x0000000000000000000000000000000000000000000000000000000000000000",
        "host admission zero root",
        true,
    )
    .unwrap()
}

fn direct_input() -> EconomicEpochGuestInputV1 {
    let route_image_id = [1, 2, 3, 4, 5, 6, 7, 8];
    let route_image_root = image_id_root_v1(route_image_id).unwrap();
    let route = RouteCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-host-admission-test".to_owned(),
        deployment_root: root(10),
        profile_root: root(11),
        writer_epoch: 7,
        route_release_id: root(12),
        command_occurrence_id: root(13),
        ordered_lane_journal_roots: vec![root(14)],
        pre_state_root: root(15),
        post_state_root: root(16),
        effect_plan_root: root(17),
        terminal_obligations_root: zero_root(),
    };
    let route_journal_bytes =
        canonical_json_bytes_v1(&route, "host admission route journal").unwrap();
    let route_journal_root = route.journal_root().unwrap();
    let route_journal_digest = sha256_root_v1(&route_journal_bytes);
    let route_assumption_root =
        derive_route_composition_assumption_root_v1(&RouteCompositionAssumptionInputV1 {
            profile_id: &route.profile_root,
            route_release_id: &route.route_release_id,
            command_occurrence_id: &route.command_occurrence_id,
            writer_epoch: route.writer_epoch,
            route_journal_root: &route_journal_root,
            route_journal_digest: &route_journal_digest,
            expected_image_id: &route_image_root,
        })
        .unwrap();
    let certificate = GlobalEconomicEpochJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: route.chain_id.clone(),
        deployment_root: route.deployment_root.clone(),
        profile_root: route.profile_root.clone(),
        writer_epoch: route.writer_epoch,
        height: 42,
        pre_state_root: route.pre_state_root.clone(),
        post_state_root: route.post_state_root.clone(),
        ordered_occurrence_ids: vec![route.command_occurrence_id.clone()],
        ordered_route_journal_roots: vec![route_journal_root],
        ordered_route_assumption_roots: vec![route_assumption_root],
        module_leaf_occurrences: 1,
        aggregation_fanout: 8,
        aggregation_levels: 0,
        effect_plan_root: route.effect_plan_root,
        terminal_obligations_root: zero_root(),
        body_commitment: root(18),
        data_availability_root: root(19),
        finality_root: root(20),
        source_manifest_root: root(21),
        toolchain_manifest_root: root(22),
        root_image_id: root(23),
    };
    EconomicEpochGuestInputV1 {
        certificate_journal_bytes: canonical_json_bytes_v1(
            &certificate,
            "host admission certificate",
        )
        .unwrap(),
        route_receipts: vec![RouteReceiptClaimV1 {
            image_id: route_image_id,
            journal_bytes: route_journal_bytes,
        }],
    }
}

fn command_aggregation_input() -> CommandAggregationGuestInputV1 {
    let direct = direct_input();
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
        route_receipts: direct.route_receipts,
    }
}

fn aggregated_epoch_input() -> AggregatedEconomicEpochGuestInputV1 {
    let recursive_image_id = [9, 10, 11, 12, 13, 14, 15, 16];
    let recursive_image_root = image_id_root_v1(recursive_image_id).unwrap();
    let occurrence_ids: Vec<_> = (0..9).map(|index| root(100 + index)).collect();
    let route_journal_roots: Vec<_> = (0..9).map(|index| root(200 + index)).collect();
    let route_assumption_roots: Vec<_> = (0..9).map(|index| root(300 + index)).collect();
    let certificate = GlobalEconomicEpochJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-host-aggregate-admission-test".to_owned(),
        deployment_root: root(30),
        profile_root: root(31),
        writer_epoch: 7,
        height: 42,
        pre_state_root: root(32),
        post_state_root: root(34),
        ordered_occurrence_ids: occurrence_ids,
        ordered_route_journal_roots: route_journal_roots,
        ordered_route_assumption_roots: route_assumption_roots,
        module_leaf_occurrences: 9,
        aggregation_fanout: 8,
        aggregation_levels: 1,
        effect_plan_root: root(35),
        terminal_obligations_root: zero_root(),
        body_commitment: root(36),
        data_availability_root: root(37),
        finality_root: root(38),
        source_manifest_root: root(39),
        toolchain_manifest_root: root(40),
        root_image_id: recursive_image_root,
    };
    let group_roots = [certificate.pre_state_root.clone(), root(33)];
    let group_posts = [root(33), certificate.post_state_root.clone()];
    let mut claims = Vec::new();
    for group_index in 0..2 {
        let start = group_index * 8;
        let end = core::cmp::min(start + 8, 9);
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
            ordered_route_journal_roots: certificate.ordered_route_journal_roots[start..end]
                .to_vec(),
            ordered_route_assumption_roots: certificate.ordered_route_assumption_roots[start..end]
                .to_vec(),
            pre_state_root: group_roots[group_index].clone(),
            post_state_root: group_posts[group_index].clone(),
            module_leaf_occurrences: (end - start) as u64,
        };
        claims.push(CommandAggregationReceiptClaimV1 {
            image_id: recursive_image_id,
            journal_bytes: journal.canonical_bytes().unwrap(),
        });
    }
    AggregatedEconomicEpochGuestInputV1 {
        certificate_journal_bytes: canonical_json_bytes_v1(
            &certificate,
            "host aggregated admission certificate",
        )
        .unwrap(),
        command_aggregation_receipts: claims,
    }
}

#[test]
fn fake_route_receipt_rejects_before_assumption_installation() {
    // Arrange
    let input = direct_input();
    let claim = &input.route_receipts[0];
    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        claim.image_id,
        claim.journal_bytes.clone(),
    ))
    .try_into()
    .unwrap();

    // Act
    let result = build_economic_epoch_executor_env_v1(&input, vec![fake]);

    // Assert
    assert!(matches!(result, Err(EconomicEpochHostErrorV1::ReceiptKind)));
}

#[test]
fn fake_route_receipt_cannot_enter_command_aggregation() {
    // Arrange
    let input = command_aggregation_input();
    let claim = &input.route_receipts[0];
    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        claim.image_id,
        claim.journal_bytes.clone(),
    ))
    .try_into()
    .unwrap();

    // Act
    let result = build_command_aggregation_executor_env_v1(&input, vec![fake]);

    // Assert
    assert!(matches!(result, Err(EconomicEpochHostErrorV1::ReceiptKind)));
}

#[test]
fn fake_command_aggregation_receipt_cannot_enter_epoch_root() {
    // Arrange
    let input = aggregated_epoch_input();
    let fake_receipts = input
        .command_aggregation_receipts
        .iter()
        .map(|claim| {
            FakeReceipt::new(ReceiptClaim::ok(
                claim.image_id,
                claim.journal_bytes.clone(),
            ))
            .try_into()
            .unwrap()
        })
        .collect();

    // Act
    let result = build_aggregated_economic_epoch_executor_env_v1(&input, fake_receipts);

    // Assert
    assert!(matches!(result, Err(EconomicEpochHostErrorV1::ReceiptKind)));
}
