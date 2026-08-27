use std::time::{Duration, Instant};

use risc0_zkvm::{InnerReceipt, Receipt};
use sha2::{Digest, Sha256};

#[path = "support/mod.rs"]
mod support;

use support::{release_aware_asset_lane_fixture_v1, ReleaseAwareAssetLaneFixtureV1};
use zenodex_asset_lane_coordinator_risc0_host::{
    asset_lane_coordinator_image_root_v1, encode_asset_lane_coordinator_receipt_v1,
    prove_asset_lane_coordinator_succinct_v1, verify_asset_lane_coordinator_receipt_v1,
    AssetLaneCoordinatorHostErrorV1, PinnedAssetLaneCoordinatorReceiptVerifierV1,
};
use zenodex_asset_lane_coordinator_risc0_methods::{
    ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF, ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID,
};
use zenodex_asset_lane_coordinator_risc0_shared::{
    prepare_asset_lane_coordinator_v1, PreparedAssetLaneCoordinatorV1,
    ASSET_TRANSFER_MODULE_IMAGE_ID_V1,
};
use zenodex_asset_transfer_module_risc0_host::{
    asset_transfer_module_image_root_v1, encode_asset_transfer_module_receipt_v1,
    prove_asset_transfer_module_succinct_v1, AssetTransferModuleHostErrorV1,
    PinnedAssetTransferModuleReceiptVerifierV1,
};
use zenodex_asset_transfer_module_risc0_methods::ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID;
use zenodex_global_settlement_abi_v1::{
    bind_asset_transfer_lane_output_to_release_route_v1,
    compose_receipt_backed_asset_lane_single_v1, verify_asset_lane_composition_receipt_v1,
    verify_asset_transfer_lane_module_receipt_v1, AssetTransferLaneModuleReceiptCandidateV1,
    AssetTransferReleaseRouteBindingCandidateV1, LaneCompositionReceiptCandidateV1,
    LaneCompositionReceiptEnvelopeV1, LaneCompositionSuccinctReceiptVerifierV1, LaneIdV1,
    LaneModuleReceiptEnvelopeV1, ReceiptBackedAssetLaneCompositionCandidateV1,
    ReceiptBackedAssetLaneCompositionV1, ReceiptKindV1, ReleaseRouteBoundLaneTransitionV1, RootV1,
    VerifiedLaneCompositionV1,
};

struct ReleaseAwareLaneProofV1 {
    fixture: ReleaseAwareAssetLaneFixtureV1,
    prepared: PreparedAssetLaneCoordinatorV1,
    structural: ReceiptBackedAssetLaneCompositionV1,
    lane_receipt: Receipt,
    lane_receipt_bytes: Vec<u8>,
    verified_lane: VerifiedLaneCompositionV1,
    lane_image_root: RootV1,
    module_elapsed: Duration,
    total_elapsed: Duration,
}

fn arrange_release_aware_lane_v1() -> (
    ReleaseAwareAssetLaneFixtureV1,
    PreparedAssetLaneCoordinatorV1,
    RootV1,
) {
    assert!(!ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF.is_empty());
    assert_ne!(ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID, [0; 8]);
    assert_eq!(
        ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID,
        ASSET_TRANSFER_MODULE_IMAGE_ID_V1
    );
    let module_image_root = asset_transfer_module_image_root_v1().unwrap();
    let lane_image_root = asset_lane_coordinator_image_root_v1().unwrap();
    let fixture = release_aware_asset_lane_fixture_v1(module_image_root, lane_image_root.clone());
    let prepared = prepare_asset_lane_coordinator_v1(fixture.guest_input.clone()).unwrap();
    (fixture, prepared, lane_image_root)
}

fn bind_release_route_v1(
    fixture: &ReleaseAwareAssetLaneFixtureV1,
    prepared: &PreparedAssetLaneCoordinatorV1,
) -> ReleaseRouteBoundLaneTransitionV1 {
    bind_asset_transfer_lane_output_to_release_route_v1(
        AssetTransferReleaseRouteBindingCandidateV1 {
            profile: &fixture.profile,
            policy_registry: &fixture.policy_registry,
            asset_policy_registry: &fixture.asset_policy_registry,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            module_input: &fixture.guest_input.module_input,
            accepted: &prepared.module_accepted,
        },
    )
    .unwrap()
}

fn verify_module_and_compose_v1(
    fixture: &ReleaseAwareAssetLaneFixtureV1,
    prepared: &PreparedAssetLaneCoordinatorV1,
    binding: &ReleaseRouteBoundLaneTransitionV1,
    module_receipt: &Receipt,
) -> ReceiptBackedAssetLaneCompositionV1 {
    let receipt_bytes = encode_asset_transfer_module_receipt_v1(module_receipt).unwrap();
    let verified_module = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &fixture.profile,
            policy_registry: &fixture.policy_registry,
            asset_policy_registry: &fixture.asset_policy_registry,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            authenticated_command: &fixture.authenticated_command,
            module_input: &fixture.guest_input.module_input,
            accepted: &prepared.module_accepted,
            release_route_binding: binding,
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: &receipt_bytes,
            },
        },
        &PinnedAssetTransferModuleReceiptVerifierV1,
    )
    .unwrap();
    compose_receipt_backed_asset_lane_single_v1(ReceiptBackedAssetLaneCompositionCandidateV1 {
        profile: &fixture.profile,
        lanes: &fixture.lanes,
        coordinators: &fixture.coordinators,
        routes: &fixture.routes,
        occurrence: &fixture.occurrence,
        coordinator_context: &fixture.guest_input.coordinator_context,
        module_journal: &prepared.module_accepted.module_journal,
        private_port: &prepared.module_accepted.private_port,
        module_effects: &prepared.module_accepted.effects,
        verified_module: &verified_module,
    })
    .unwrap()
}

fn verify_lane_v1(
    fixture: &ReleaseAwareAssetLaneFixtureV1,
    prepared: &PreparedAssetLaneCoordinatorV1,
    structural: &ReceiptBackedAssetLaneCompositionV1,
    receipt_bytes: &[u8],
) -> VerifiedLaneCompositionV1 {
    verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            structural_composition: structural,
            lane_journal: &prepared.lane_accepted.lane_journal,
            receipt: LaneCompositionReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes,
            },
        },
        &PinnedAssetLaneCoordinatorReceiptVerifierV1,
    )
    .unwrap()
}

fn prove_release_aware_lane_v1() -> ReleaseAwareLaneProofV1 {
    let (fixture, prepared, lane_image_root) = arrange_release_aware_lane_v1();
    let binding = bind_release_route_v1(&fixture, &prepared);
    let started = Instant::now();
    let module_receipt =
        prove_asset_transfer_module_succinct_v1(&fixture.guest_input.module_input).unwrap();
    let module_elapsed = started.elapsed();
    let structural = verify_module_and_compose_v1(&fixture, &prepared, &binding, &module_receipt);
    let lane_receipt =
        prove_asset_lane_coordinator_succinct_v1(&fixture.guest_input, module_receipt).unwrap();
    let total_elapsed = started.elapsed();
    let lane_receipt_bytes = encode_asset_lane_coordinator_receipt_v1(&lane_receipt).unwrap();
    let verified_lane = verify_lane_v1(&fixture, &prepared, &structural, &lane_receipt_bytes);
    ReleaseAwareLaneProofV1 {
        fixture,
        prepared,
        structural,
        lane_receipt,
        lane_receipt_bytes,
        verified_lane,
        lane_image_root,
        module_elapsed,
        total_elapsed,
    }
}

fn assert_release_and_journal_bindings(proof: &ReleaseAwareLaneProofV1) {
    assert!(matches!(
        &proof.lane_receipt.inner,
        InnerReceipt::Succinct(_)
    ));
    assert_eq!(
        proof.lane_receipt.journal.bytes,
        proof.prepared.lane_journal_bytes
    );
    assert_eq!(
        proof.verified_lane.profile_id(),
        &proof.fixture.profile.profile_id
    );
    assert_eq!(proof.verified_lane.lane_id(), LaneIdV1::ASSET_TRANSFER);
    assert_eq!(
        proof.verified_lane.expected_image_id(),
        &proof.lane_image_root
    );
    assert_eq!(
        proof.verified_lane.lane_journal_root(),
        proof.structural.lane_journal_root()
    );
    PinnedAssetLaneCoordinatorReceiptVerifierV1
        .verify_succinct_receipt(
            &proof.lane_receipt_bytes,
            &proof.lane_image_root,
            &proof.prepared.lane_journal_bytes,
        )
        .unwrap();
}

fn assert_mutated_bindings_reject(proof: &ReleaseAwareLaneProofV1) {
    let mut wrong_journal = proof.prepared.lane_journal_bytes.clone();
    wrong_journal[0] ^= 1;
    assert!(matches!(
        verify_asset_lane_coordinator_receipt_v1(&proof.lane_receipt, &wrong_journal),
        Err(AssetLaneCoordinatorHostErrorV1::LaneReceiptJournal)
    ));
    assert!(PinnedAssetLaneCoordinatorReceiptVerifierV1
        .verify_succinct_receipt(
            &proof.lane_receipt_bytes,
            &support::root(99),
            &proof.prepared.lane_journal_bytes,
        )
        .is_err());
}

fn report_proof_artifacts(proof: &ReleaseAwareLaneProofV1) {
    let elf_digest = hex::encode(Sha256::digest(ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF));
    println!("asset lane coordinator image words: {ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID:?}");
    println!(
        "asset lane coordinator image root: {}",
        proof.lane_image_root
    );
    println!("asset lane coordinator embedded method sha256: {elf_digest}");
    println!(
        "release-aware verified lane binding root: {}",
        proof.verified_lane.binding_root().unwrap()
    );
    println!(
        "asset transfer module proof elapsed: {:?}",
        proof.module_elapsed
    );
    println!(
        "asset lane recursive proof total elapsed: {:?}",
        proof.total_elapsed
    );
}

#[test]
#[ignore = "generates a real module receipt and recursively verifies it in one lane receipt"]
fn real_module_receipt_composes_into_the_exact_lane_journal() {
    // Arrange and Act
    let proof = prove_release_aware_lane_v1();

    // Assert
    assert_release_and_journal_bindings(&proof);
    assert_mutated_bindings_reject(&proof);
    report_proof_artifacts(&proof);
}

#[test]
fn governed_fixture_binds_the_exact_authenticated_command_occurrence() {
    // Arrange
    let (module_image_root, lane_image_root) = match (
        asset_transfer_module_image_root_v1(),
        asset_lane_coordinator_image_root_v1(),
    ) {
        (Ok(module), Ok(lane)) => (module, lane),
        (
            Err(AssetTransferModuleHostErrorV1::PlaceholderMethod),
            Err(AssetLaneCoordinatorHostErrorV1::PlaceholderMethod),
        ) => return,
        _ => panic!("module and lane methods must both be real or both be placeholders"),
    };

    // Act
    let fixture = release_aware_asset_lane_fixture_v1(module_image_root, lane_image_root);

    // Assert
    assert_eq!(
        fixture.authenticated_command.occurrence(),
        &fixture.occurrence
    );
    assert_eq!(
        fixture.authenticated_command.occurrence_id(),
        &fixture.occurrence.occurrence_id().unwrap()
    );
    assert_eq!(
        fixture.occurrence.command_body_hash,
        fixture
            .guest_input
            .module_input
            .command
            .command_body_hash()
            .unwrap()
    );
}
