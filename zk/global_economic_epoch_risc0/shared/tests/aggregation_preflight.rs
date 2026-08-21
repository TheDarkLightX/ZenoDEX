use zenodex_global_economic_epoch_risc0_shared::{
    canonical_json_bytes_v1, derive_route_composition_assumption_root_v1,
    preflight_aggregated_economic_epoch_guest_input_v1,
    preflight_command_aggregation_guest_input_v1, AggregatedEconomicEpochGuestInputV1,
    CommandAggregationGuestInputV1, CommandAggregationJournalV1, CommandAggregationReceiptClaimV1,
    EconomicEpochGuestErrorV1, GlobalEconomicEpochJournalV1, RootV1,
    RouteCompositionAssumptionInputV1, RouteCompositionJournalV1, RouteReceiptClaimV1,
    COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1, GLOBAL_SETTLEMENT_ABI_V1,
};

struct AggregationTopologyFixtureV1 {
    certificate: GlobalEconomicEpochJournalV1,
    groups: Vec<CommandAggregationGuestInputV1>,
    aggregated_epoch: AggregatedEconomicEpochGuestInputV1,
}

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "aggregation test root", false).unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(
        "0x0000000000000000000000000000000000000000000000000000000000000000",
        "aggregation test zero root",
        true,
    )
    .unwrap()
}

fn image_words_from_root(root: &RootV1) -> [u32; 8] {
    let bytes = hex::decode(&root.as_str()[2..]).unwrap();
    let mut words = [0u32; 8];
    for (word, chunk) in words.iter_mut().zip(bytes.chunks_exact(4)) {
        *word = u32::from_le_bytes(chunk.try_into().unwrap());
    }
    words
}

fn aggregation_topology(count: usize) -> AggregationTopologyFixtureV1 {
    assert!((1..=64).contains(&count));
    let profile_root = root(10);
    let deployment_root = root(11);
    let route_image_root = root(12);
    let route_image_id = image_words_from_root(&route_image_root);
    let recursive_image_root = root(13);
    let recursive_image_id = image_words_from_root(&recursive_image_root);
    let pre_state_root = root(14);
    let mut current_root = pre_state_root.clone();
    let mut route_receipts = Vec::with_capacity(count);
    let mut route_pre_roots = Vec::with_capacity(count);
    let mut route_post_roots = Vec::with_capacity(count);
    let mut occurrence_ids = Vec::with_capacity(count);
    let mut route_journal_roots = Vec::with_capacity(count);
    let mut route_assumption_roots = Vec::with_capacity(count);

    for index in 0..count {
        let post_state_root = root(1_000 + index as u64);
        let route = RouteCompositionJournalV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            chain_id: "zeno-aggregation-test".to_owned(),
            deployment_root: deployment_root.clone(),
            profile_root: profile_root.clone(),
            writer_epoch: 7,
            route_release_id: root(2_000),
            command_occurrence_id: root(3_000 + index as u64),
            ordered_lane_journal_roots: vec![root(4_000 + index as u64)],
            pre_state_root: current_root.clone(),
            post_state_root: post_state_root.clone(),
            effect_plan_root: root(5_000 + index as u64),
            terminal_obligations_root: zero_root(),
        };
        let journal_bytes = canonical_json_bytes_v1(&route, "aggregation test route").unwrap();
        let journal_root = route.journal_root().unwrap();
        let journal_digest =
            zenodex_global_economic_epoch_risc0_shared::sha256_root_v1(&journal_bytes);
        let assumption_root =
            derive_route_composition_assumption_root_v1(&RouteCompositionAssumptionInputV1 {
                profile_id: &profile_root,
                route_release_id: &route.route_release_id,
                command_occurrence_id: &route.command_occurrence_id,
                writer_epoch: 7,
                route_journal_root: &journal_root,
                route_journal_digest: &journal_digest,
                expected_image_id: &route_image_root,
            })
            .unwrap();
        route_pre_roots.push(current_root);
        route_post_roots.push(post_state_root.clone());
        occurrence_ids.push(route.command_occurrence_id);
        route_journal_roots.push(journal_root);
        route_assumption_roots.push(assumption_root);
        route_receipts.push(RouteReceiptClaimV1 {
            image_id: route_image_id,
            journal_bytes,
        });
        current_root = post_state_root;
    }

    let certificate = GlobalEconomicEpochJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-aggregation-test".to_owned(),
        deployment_root,
        profile_root,
        writer_epoch: 7,
        height: 42,
        pre_state_root,
        post_state_root: current_root,
        ordered_occurrence_ids: occurrence_ids,
        ordered_route_journal_roots: route_journal_roots,
        ordered_route_assumption_roots: route_assumption_roots,
        module_leaf_occurrences: count as u64,
        aggregation_fanout: 8,
        aggregation_levels: u64::from(count > 8),
        effect_plan_root: root(20),
        terminal_obligations_root: zero_root(),
        body_commitment: root(21),
        data_availability_root: root(22),
        finality_root: root(23),
        source_manifest_root: root(24),
        toolchain_manifest_root: root(25),
        root_image_id: recursive_image_root,
    };

    let mut groups = Vec::new();
    let mut aggregation_receipts = Vec::new();
    for (group_index, start) in (0..count).step_by(8).enumerate() {
        let end = core::cmp::min(start + 8, count);
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
            pre_state_root: route_pre_roots[start].clone(),
            post_state_root: route_post_roots[end - 1].clone(),
            module_leaf_occurrences: (end - start) as u64,
        };
        let journal_bytes = journal.canonical_bytes().unwrap();
        groups.push(CommandAggregationGuestInputV1 {
            aggregation_journal_bytes: journal_bytes.clone(),
            route_receipts: route_receipts[start..end].to_vec(),
        });
        aggregation_receipts.push(CommandAggregationReceiptClaimV1 {
            image_id: recursive_image_id,
            journal_bytes,
        });
    }
    AggregationTopologyFixtureV1 {
        certificate: certificate.clone(),
        groups,
        aggregated_epoch: AggregatedEconomicEpochGuestInputV1 {
            certificate_journal_bytes: canonical_json_bytes_v1(
                &certificate,
                "aggregation test certificate",
            )
            .unwrap(),
            command_aggregation_receipts: aggregation_receipts,
        },
    }
}

#[test]
fn command_aggregation_bva_accepts_one_and_eight_then_rejects_zero_and_nine() {
    // Arrange / Act / Assert: canonical lower and upper fanout boundaries.
    let fixture = aggregation_topology(9);
    for (group, expected_count) in fixture.groups.iter().zip([8, 1]) {
        let prepared = preflight_command_aggregation_guest_input_v1(group).unwrap();
        assert_eq!(prepared.route_claims.len(), expected_count);
    }

    // Arrange: preserve all non-cardinality fields while constructing zero commands.
    let mut zero = fixture.groups[0].clone();
    let mut zero_journal: CommandAggregationJournalV1 =
        serde_json::from_slice(&zero.aggregation_journal_bytes).unwrap();
    zero_journal.ordered_occurrence_ids.clear();
    zero_journal.ordered_route_journal_roots.clear();
    zero_journal.ordered_route_assumption_roots.clear();
    zero_journal.post_state_root = zero_journal.pre_state_root.clone();
    zero_journal.module_leaf_occurrences = 0;
    zero.aggregation_journal_bytes =
        canonical_json_bytes_v1(&zero_journal, "zero-command aggregation journal").unwrap();
    zero.route_receipts.clear();

    // Act
    let zero_result = preflight_command_aggregation_guest_input_v1(&zero);

    // Assert
    assert!(matches!(
        zero_result,
        Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "command aggregation route count"
        ))
    ));

    // Arrange: a nine-command journal paired with exactly nine route receipts.
    let full = aggregation_topology(9);
    let nine_journal = CommandAggregationJournalV1 {
        schema: COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1.to_owned(),
        settlement_abi: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: full.certificate.chain_id.clone(),
        deployment_root: full.certificate.deployment_root.clone(),
        profile_root: full.certificate.profile_root.clone(),
        writer_epoch: full.certificate.writer_epoch,
        epoch_height: full.certificate.height,
        group_index: 0,
        first_command_index: 0,
        ordered_occurrence_ids: full.certificate.ordered_occurrence_ids.clone(),
        ordered_route_journal_roots: full.certificate.ordered_route_journal_roots.clone(),
        ordered_route_assumption_roots: full.certificate.ordered_route_assumption_roots.clone(),
        pre_state_root: full.certificate.pre_state_root.clone(),
        post_state_root: full.certificate.post_state_root.clone(),
        module_leaf_occurrences: 9,
    };
    let mut nine_route_receipts = full.groups[0].route_receipts.clone();
    nine_route_receipts.extend(full.groups[1].route_receipts.clone());
    let nine = CommandAggregationGuestInputV1 {
        aggregation_journal_bytes: canonical_json_bytes_v1(
            &nine_journal,
            "nine-command aggregation journal",
        )
        .unwrap(),
        route_receipts: nine_route_receipts,
    };

    // Act
    let nine_result = preflight_command_aggregation_guest_input_v1(&nine);

    // Assert
    assert!(matches!(
        nine_result,
        Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "command aggregation route count"
        ))
    ));
}

#[test]
fn aggregated_epoch_bva_accepts_nine_and_sixty_four_then_rejects_eight_and_sixty_five() {
    // Arrange / Act / Assert: first recursive boundary and maximum epoch.
    for count in [9, 64] {
        let fixture = aggregation_topology(count);
        let prepared =
            preflight_aggregated_economic_epoch_guest_input_v1(&fixture.aggregated_epoch).unwrap();
        assert_eq!(prepared.command_aggregation_claims.len(), count.div_ceil(8));
    }

    // Arrange: mark the certificate as aggregated so only the lower count fails.
    let mut eight = aggregation_topology(8);
    eight.certificate.aggregation_levels = 1;
    eight.aggregated_epoch.certificate_journal_bytes =
        canonical_json_bytes_v1(&eight.certificate, "eight-command aggregated certificate")
            .unwrap();

    // Act
    let eight_result = preflight_aggregated_economic_epoch_guest_input_v1(&eight.aggregated_epoch);

    // Assert
    assert!(matches!(
        eight_result,
        Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "aggregated epoch shape"
        ))
    ));

    let mut sixty_five = aggregation_topology(64).aggregated_epoch;
    let mut certificate: GlobalEconomicEpochJournalV1 =
        serde_json::from_slice(&sixty_five.certificate_journal_bytes).unwrap();
    certificate.ordered_occurrence_ids.push(root(90_001));
    certificate.ordered_route_journal_roots.push(root(90_002));
    certificate
        .ordered_route_assumption_roots
        .push(root(90_003));
    certificate.module_leaf_occurrences = 65;
    sixty_five.certificate_journal_bytes =
        canonical_json_bytes_v1(&certificate, "65-command certificate").unwrap();
    assert!(matches!(
        preflight_aggregated_economic_epoch_guest_input_v1(&sixty_five),
        Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "epoch command count"
        ))
    ));
}

#[test]
fn reordered_split_wrong_image_and_leaf_count_mutants_fail_closed() {
    // Arrange
    let exact = aggregation_topology(9).aggregated_epoch;
    let mut reordered = exact.clone();
    reordered.command_aggregation_receipts.swap(0, 1);

    let mut split = exact.clone();
    let mut short_first: CommandAggregationJournalV1 =
        serde_json::from_slice(&split.command_aggregation_receipts[0].journal_bytes).unwrap();
    short_first.ordered_occurrence_ids.pop();
    short_first.ordered_route_journal_roots.pop();
    short_first.ordered_route_assumption_roots.pop();
    short_first.module_leaf_occurrences -= 1;
    split.command_aggregation_receipts[0].journal_bytes = short_first.canonical_bytes().unwrap();

    let mut wrong_image = exact.clone();
    wrong_image.command_aggregation_receipts[0].image_id[0] ^= 1;

    let mut wrong_leaf_count = exact;
    let mut inflated: CommandAggregationJournalV1 =
        serde_json::from_slice(&wrong_leaf_count.command_aggregation_receipts[1].journal_bytes)
            .unwrap();
    inflated.module_leaf_occurrences += 1;
    wrong_leaf_count.command_aggregation_receipts[1].journal_bytes =
        inflated.canonical_bytes().unwrap();

    // Act / Assert
    for mutant in [reordered, split, wrong_image, wrong_leaf_count] {
        assert!(preflight_aggregated_economic_epoch_guest_input_v1(&mutant).is_err());
    }
}

#[test]
fn command_aggregation_rejects_reordered_routes_and_module_leaf_drift() {
    // Arrange
    let mut topology = aggregation_topology(9);
    let exact = topology.groups.remove(0);
    let mut reordered = exact.clone();
    reordered.route_receipts.swap(0, 1);

    let mut leaf_drift = exact;
    let mut journal: CommandAggregationJournalV1 =
        serde_json::from_slice(&leaf_drift.aggregation_journal_bytes).unwrap();
    journal.module_leaf_occurrences += 1;
    leaf_drift.aggregation_journal_bytes = journal.canonical_bytes().unwrap();

    // Act / Assert
    assert!(matches!(
        preflight_command_aggregation_guest_input_v1(&reordered),
        Err(EconomicEpochGuestErrorV1::InvalidOrder(
            "epoch route receipt sequence"
        ))
    ));
    assert!(matches!(
        preflight_command_aggregation_guest_input_v1(&leaf_drift),
        Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "command aggregation terminal binding"
        ))
    ));
}
