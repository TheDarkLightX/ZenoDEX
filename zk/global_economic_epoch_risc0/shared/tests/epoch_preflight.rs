use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_economic_epoch_risc0_shared::{
    canonical_json_bytes_v1, derive_route_composition_assumption_root_v1, image_id_root_v1,
    preflight_command_aggregation_guest_input_v1, preflight_economic_epoch_guest_input_v1,
    sha256_root_v1, CommandAggregationGuestInputV1, CommandAggregationJournalV1,
    EconomicEpochGuestErrorV1, EconomicEpochGuestInputV1, GlobalEconomicEpochJournalV1, RootV1,
    RouteCompositionAssumptionInputV1, RouteCompositionJournalV1, RouteReceiptClaimV1,
    GLOBAL_SETTLEMENT_ABI_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).unwrap()
}

fn image_words_from_root(root: &RootV1) -> [u32; 8] {
    let bytes = hex::decode(&root.as_str()[2..]).unwrap();
    let mut words = [0u32; 8];
    for (word, chunk) in words.iter_mut().zip(bytes.chunks_exact(4)) {
        *word = u32::from_le_bytes(chunk.try_into().unwrap());
    }
    words
}

fn route_journal(
    index: usize,
    profile_root: &RootV1,
    deployment_root: &RootV1,
    pre_state_root: RootV1,
    post_state_root: RootV1,
) -> RouteCompositionJournalV1 {
    RouteCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-epoch-guest-test".to_owned(),
        deployment_root: deployment_root.clone(),
        profile_root: profile_root.clone(),
        writer_epoch: 7,
        route_release_id: root(2_000),
        command_occurrence_id: root(3_000 + index as u64),
        ordered_lane_journal_roots: vec![root(4_000 + index as u64)],
        pre_state_root,
        post_state_root,
        effect_plan_root: root(5_000 + index as u64),
        terminal_obligations_root: RootV1::parse(
            "0x0000000000000000000000000000000000000000000000000000000000000000",
            "zero terminal root",
            true,
        )
        .unwrap(),
    }
}

fn input_fixture(count: usize) -> EconomicEpochGuestInputV1 {
    assert!((1..=64).contains(&count));
    let profile_root = root(10);
    let deployment_root = root(11);
    let route_image_root = root(12);
    let route_image_id = image_words_from_root(&route_image_root);
    assert_eq!(image_id_root_v1(route_image_id).unwrap(), route_image_root);
    let pre_state_root = root(13);
    let mut current_root = pre_state_root.clone();
    let mut route_receipts = Vec::with_capacity(count);
    let mut occurrence_ids = Vec::with_capacity(count);
    let mut route_journal_roots = Vec::with_capacity(count);
    let mut route_assumption_roots = Vec::with_capacity(count);

    for index in 0..count {
        let next_root = root(100 + index as u64);
        let journal = route_journal(
            index,
            &profile_root,
            &deployment_root,
            current_root,
            next_root.clone(),
        );
        let journal_bytes = canonical_json_bytes_v1(&journal, "test route journal").unwrap();
        let journal_root = journal.journal_root().unwrap();
        let journal_digest = sha256_root_v1(&journal_bytes);
        let assumption_root =
            derive_route_composition_assumption_root_v1(&RouteCompositionAssumptionInputV1 {
                profile_id: &profile_root,
                route_release_id: &journal.route_release_id,
                command_occurrence_id: &journal.command_occurrence_id,
                writer_epoch: 7,
                route_journal_root: &journal_root,
                route_journal_digest: &journal_digest,
                expected_image_id: &route_image_root,
            })
            .unwrap();
        occurrence_ids.push(journal.command_occurrence_id.clone());
        route_journal_roots.push(journal_root);
        route_assumption_roots.push(assumption_root);
        route_receipts.push(RouteReceiptClaimV1 {
            image_id: route_image_id,
            journal_bytes,
        });
        current_root = next_root;
    }

    let certificate = GlobalEconomicEpochJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-epoch-guest-test".to_owned(),
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
        terminal_obligations_root: RootV1::parse(
            "0x0000000000000000000000000000000000000000000000000000000000000000",
            "zero terminal root",
            true,
        )
        .unwrap(),
        body_commitment: root(21),
        data_availability_root: root(22),
        finality_root: root(23),
        source_manifest_root: root(24),
        toolchain_manifest_root: root(25),
        root_image_id: root(26),
    };
    EconomicEpochGuestInputV1 {
        certificate_journal_bytes: canonical_json_bytes_v1(&certificate, "test epoch certificate")
            .unwrap(),
        route_receipts,
    }
}

fn golden_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("tests/data/global_settlement_abi_v1_golden.json")
}

#[test]
fn direct_epoch_bva_accepts_one_and_eight_then_rejects_isolated_zero_nine_and_sixty_four() {
    for count in [1, 8] {
        // Arrange
        let input = input_fixture(count);

        // Act
        let prepared = preflight_economic_epoch_guest_input_v1(&input).unwrap();

        // Assert
        assert_eq!(prepared.route_claims.len(), count);
        assert_eq!(
            prepared.certificate_journal_bytes,
            input.certificate_journal_bytes
        );
    }

    // Arrange: a structurally coherent empty certificate and no route receipts.
    let mut zero = input_fixture(1);
    let mut zero_certificate: GlobalEconomicEpochJournalV1 =
        serde_json::from_slice(&zero.certificate_journal_bytes).unwrap();
    zero_certificate.ordered_occurrence_ids.clear();
    zero_certificate.ordered_route_journal_roots.clear();
    zero_certificate.ordered_route_assumption_roots.clear();
    zero_certificate.module_leaf_occurrences = 0;
    zero_certificate.post_state_root = zero_certificate.pre_state_root.clone();
    zero_certificate.aggregation_levels = 0;
    zero.certificate_journal_bytes =
        canonical_json_bytes_v1(&zero_certificate, "zero-command certificate").unwrap();
    zero.route_receipts.clear();

    // Act
    let zero_result = preflight_economic_epoch_guest_input_v1(&zero);

    // Assert: command count is the first and exact failed obligation.
    assert!(matches!(
        zero_result,
        Err(EconomicEpochGuestErrorV1::InvalidBounds(
            "epoch command count"
        ))
    ));

    for count in [9, 64] {
        // Arrange: preserve direct-mode metadata so only the upper count fails.
        let mut input = input_fixture(count);
        let mut certificate: GlobalEconomicEpochJournalV1 =
            serde_json::from_slice(&input.certificate_journal_bytes).unwrap();
        certificate.aggregation_levels = 0;
        input.certificate_journal_bytes =
            canonical_json_bytes_v1(&certificate, "direct upper-bound certificate").unwrap();

        // Act
        let result = preflight_economic_epoch_guest_input_v1(&input);

        // Assert
        assert!(matches!(
            result,
            Err(EconomicEpochGuestErrorV1::InvalidBounds(
                "direct epoch aggregation shape"
            ))
        ));
    }
}

#[test]
fn missing_reordered_wrong_image_and_noncanonical_route_claims_fail_closed() {
    // Arrange
    let exact = input_fixture(2);

    let mut missing = exact.clone();
    missing.route_receipts.pop();

    let mut reordered = exact.clone();
    reordered.route_receipts.swap(0, 1);

    let mut wrong_image = exact.clone();
    wrong_image.route_receipts[0].image_id[0] ^= 1;

    let mut noncanonical = exact;
    noncanonical.route_receipts[0].journal_bytes.push(b'\n');

    // Act / Assert
    assert!(matches!(
        preflight_economic_epoch_guest_input_v1(&missing),
        Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "epoch route receipt count"
        ))
    ));
    assert!(matches!(
        preflight_economic_epoch_guest_input_v1(&reordered),
        Err(EconomicEpochGuestErrorV1::InvalidOrder(
            "epoch route receipt sequence"
        ))
    ));
    assert!(matches!(
        preflight_economic_epoch_guest_input_v1(&wrong_image),
        Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "epoch route assumption root"
        ))
    ));
    assert!(matches!(
        preflight_economic_epoch_guest_input_v1(&noncanonical),
        Err(EconomicEpochGuestErrorV1::NonCanonical(
            "route receipt journal"
        ))
    ));
}

#[test]
fn direct_epoch_rejects_module_leaf_occurrence_drift() {
    // Arrange
    let mut input = input_fixture(2);
    let mut certificate: GlobalEconomicEpochJournalV1 =
        serde_json::from_slice(&input.certificate_journal_bytes).unwrap();
    certificate.module_leaf_occurrences += 1;
    input.certificate_journal_bytes =
        canonical_json_bytes_v1(&certificate, "module leaf drift certificate").unwrap();

    // Act
    let result = preflight_economic_epoch_guest_input_v1(&input);

    // Assert
    assert!(matches!(
        result,
        Err(EconomicEpochGuestErrorV1::InvalidBinding(
            "epoch module leaf occurrences"
        ))
    ));
}

#[test]
fn risc0_image_words_have_one_explicit_little_endian_root_encoding() {
    // Arrange
    let image_id = [
        0x0102_0304,
        0x1112_1314,
        0x2122_2324,
        0x3132_3334,
        0x4142_4344,
        0x5152_5354,
        0x6162_6364,
        0x7172_7374,
    ];

    // Act
    let root = image_id_root_v1(image_id).unwrap();

    // Assert
    assert_eq!(
        root.as_str(),
        "0x0403020114131211242322213433323144434241545352516463626174737271"
    );
}

#[test]
fn guest_preflight_replays_the_python_rust_golden_epoch_and_assumption() {
    // Arrange
    let fixture: Value = serde_json::from_slice(&fs::read(golden_path()).unwrap()).unwrap();
    let epoch = &fixture["vectors"]["epoch_certificate"];
    let route = &fixture["vectors"]["route_journal"];
    let assumption = &fixture["vectors"]["route_assumption"];
    let aggregation = &fixture["vectors"]["command_aggregation_journal"];
    let certificate_journal_bytes = serde_json::to_vec(&epoch["journal_canonical"]).unwrap();
    let route_journal_bytes = serde_json::to_vec(&route["canonical"]).unwrap();
    let expected_image = RootV1::parse(
        assumption["canonical"]["expected_image_id"]
            .as_str()
            .unwrap()
            .to_owned(),
        "golden route image",
        false,
    )
    .unwrap();
    let input = EconomicEpochGuestInputV1 {
        certificate_journal_bytes,
        route_receipts: vec![RouteReceiptClaimV1 {
            image_id: image_words_from_root(&expected_image),
            journal_bytes: route_journal_bytes.clone(),
        }],
    };
    let aggregation_journal: CommandAggregationJournalV1 =
        serde_json::from_value(aggregation["canonical"].clone()).unwrap();
    let aggregation_input = CommandAggregationGuestInputV1 {
        aggregation_journal_bytes: serde_json::to_vec(&aggregation["canonical"]).unwrap(),
        route_receipts: vec![RouteReceiptClaimV1 {
            image_id: image_words_from_root(&expected_image),
            journal_bytes: route_journal_bytes,
        }],
    };

    // Act
    let prepared = preflight_economic_epoch_guest_input_v1(&input).unwrap();
    let prepared_aggregation =
        preflight_command_aggregation_guest_input_v1(&aggregation_input).unwrap();

    // Assert
    assert_eq!(prepared.route_claims.len(), 1);
    assert_eq!(prepared_aggregation.route_claims.len(), 1);
    assert_eq!(
        aggregation_journal.journal_root().unwrap().as_str(),
        aggregation["expected_root"].as_str().unwrap()
    );
    assert_eq!(
        sha256_root_v1(
            &canonical_json_bytes_v1(&assumption["canonical"], "golden assumption",).unwrap()
        )
        .as_str(),
        format!(
            "0x{}",
            assumption["canonical_bytes_sha256"].as_str().unwrap()
        )
    );
}
