use risc0_zkvm::InnerReceipt;

#[path = "support/mod.rs"]
mod support;

use support::route_input;
use zenodex_global_economic_epoch_risc0_host::prove_economic_epoch_succinct_v1;
use zenodex_global_economic_epoch_risc0_methods::ZENODEX_ECONOMIC_EPOCH_GUEST_ID;
use zenodex_global_economic_epoch_risc0_shared::{
    canonical_json_bytes_v1, derive_route_composition_assumption_root_v1, image_id_root_v1,
    sha256_root_v1, EconomicEpochGuestInputV1, GlobalEconomicEpochJournalV1, RootV1 as EpochRootV1,
    RouteCompositionAssumptionInputV1, RouteCompositionJournalV1 as EpochRouteCompositionJournalV1,
    RouteReceiptClaimV1, GLOBAL_SETTLEMENT_ABI_V1,
};
use zenodex_perps_margin_lane_coordinator_risc0_host::prove_perps_margin_lane_coordinator_succinct_v1;
use zenodex_perps_margin_module_risc0_host::prove_perps_margin_module_succinct_v1;
use zenodex_perps_margin_route_composer_risc0_host::{
    build_perps_margin_route_composer_executor_env_v1,
    prove_perps_margin_route_composer_succinct_v1, verify_perps_margin_route_composer_receipt_v1,
    PerpsMarginRouteComposerHostErrorV1,
};
use zenodex_perps_margin_route_composer_risc0_methods::{
    ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ELF, ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ID,
};
use zenodex_perps_margin_route_composer_risc0_shared::prepare_perps_margin_route_composer_v1;

fn epoch_root(value: u64) -> EpochRootV1 {
    EpochRootV1::parse(
        format!("0x{value:064x}"),
        "perps route epoch test root",
        false,
    )
    .unwrap()
}

fn epoch_input(
    route_journal_bytes: Vec<u8>,
    route_image_id: [u32; 8],
    root_image_id: [u32; 8],
) -> EconomicEpochGuestInputV1 {
    let route_journal: EpochRouteCompositionJournalV1 =
        serde_json::from_slice(&route_journal_bytes).unwrap();
    let route_image_root = image_id_root_v1(route_image_id).unwrap();
    let route_journal_root = route_journal.journal_root().unwrap();
    let route_journal_digest = sha256_root_v1(&route_journal_bytes);
    let route_assumption_root =
        derive_route_composition_assumption_root_v1(&RouteCompositionAssumptionInputV1 {
            profile_id: &route_journal.profile_root,
            route_release_id: &route_journal.route_release_id,
            command_occurrence_id: &route_journal.command_occurrence_id,
            writer_epoch: route_journal.writer_epoch,
            route_journal_root: &route_journal_root,
            route_journal_digest: &route_journal_digest,
            expected_image_id: &route_image_root,
        })
        .unwrap();
    let certificate = GlobalEconomicEpochJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: route_journal.chain_id.clone(),
        deployment_root: route_journal.deployment_root.clone(),
        profile_root: route_journal.profile_root.clone(),
        writer_epoch: route_journal.writer_epoch,
        height: 42,
        pre_state_root: route_journal.pre_state_root.clone(),
        post_state_root: route_journal.post_state_root.clone(),
        ordered_occurrence_ids: vec![route_journal.command_occurrence_id.clone()],
        ordered_route_journal_roots: vec![route_journal_root],
        ordered_route_assumption_roots: vec![route_assumption_root],
        module_leaf_occurrences: 1,
        aggregation_fanout: 8,
        aggregation_levels: 0,
        effect_plan_root: route_journal.effect_plan_root.clone(),
        terminal_obligations_root: route_journal.terminal_obligations_root.clone(),
        body_commitment: epoch_root(30),
        data_availability_root: epoch_root(31),
        finality_root: epoch_root(32),
        source_manifest_root: epoch_root(33),
        toolchain_manifest_root: epoch_root(34),
        root_image_id: image_id_root_v1(root_image_id).unwrap(),
    };
    EconomicEpochGuestInputV1 {
        certificate_journal_bytes: canonical_json_bytes_v1(
            &certificate,
            "perps route epoch certificate",
        )
        .unwrap(),
        route_receipts: vec![RouteReceiptClaimV1 {
            image_id: route_image_id,
            journal_bytes: route_journal_bytes,
        }],
    }
}

#[test]
fn epoch_certificate_exactly_binds_the_structural_route_journal() {
    // Arrange.
    let prepared = prepare_perps_margin_route_composer_v1(route_input(100)).unwrap();

    // Act.
    let input = epoch_input(prepared.route_journal_bytes.clone(), [51; 8], [52; 8]);
    let certificate: GlobalEconomicEpochJournalV1 =
        serde_json::from_slice(&input.certificate_journal_bytes).unwrap();
    let route: EpochRouteCompositionJournalV1 =
        serde_json::from_slice(&prepared.route_journal_bytes).unwrap();

    // Assert.
    assert_eq!(
        input.route_receipts[0].journal_bytes,
        prepared.route_journal_bytes
    );
    assert_eq!(
        certificate.ordered_route_journal_roots,
        vec![route.journal_root().unwrap()]
    );
    assert_eq!(certificate.pre_state_root, route.pre_state_root);
    assert_eq!(certificate.post_state_root, route.post_state_root);
    assert_eq!(certificate.effect_plan_root, route.effect_plan_root);
    assert_eq!(
        certificate.terminal_obligations_root,
        route.terminal_obligations_root
    );
}

#[test]
#[ignore = "generates four real RISC0 Succinct receipts; run on the proof benchmark host"]
fn real_perps_module_lane_route_and_epoch_composition_is_exact() {
    // Arrange.
    assert!(!ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ELF.is_empty());
    assert_ne!(ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ID, [0; 8]);
    let input = route_input(100);
    let prepared = prepare_perps_margin_route_composer_v1(input.clone()).unwrap();
    let module_receipt =
        prove_perps_margin_module_succinct_v1(&input.lane_input.module_input).unwrap();
    let lane_receipt =
        prove_perps_margin_lane_coordinator_succinct_v1(&input.lane_input, module_receipt).unwrap();

    // A receipt for one disclosed transition cannot authenticate another.
    assert!(matches!(
        build_perps_margin_route_composer_executor_env_v1(&route_input(101), lane_receipt.clone()),
        Err(PerpsMarginRouteComposerHostErrorV1::LaneReceiptJournal)
    ));

    // Act.
    let route_receipt =
        prove_perps_margin_route_composer_succinct_v1(&input, lane_receipt).unwrap();
    let epoch_input = epoch_input(
        prepared.route_journal_bytes.clone(),
        ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ID,
        ZENODEX_ECONOMIC_EPOCH_GUEST_ID,
    );
    let epoch_receipt =
        prove_economic_epoch_succinct_v1(&epoch_input, vec![route_receipt.clone()]).unwrap();

    // Assert.
    assert!(matches!(&route_receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(route_receipt.journal.bytes, prepared.route_journal_bytes);
    verify_perps_margin_route_composer_receipt_v1(&route_receipt, &prepared.route_journal_bytes)
        .unwrap();
    assert!(matches!(&epoch_receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(
        epoch_receipt.journal.bytes,
        epoch_input.certificate_journal_bytes
    );
    epoch_receipt
        .verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID)
        .unwrap();
}
