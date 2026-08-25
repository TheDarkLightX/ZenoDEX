use std::time::Instant;

use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts};
use sha2::{Digest, Sha256};

#[path = "support/mod.rs"]
mod support;

use support::{coordinator_input, root};
use zenodex_global_settlement_abi_v1::LaneCompositionSuccinctReceiptVerifierV1;
use zenodex_perps_margin_lane_coordinator_risc0_host::{
    build_perps_margin_lane_coordinator_executor_env_v1,
    decode_canonical_perps_margin_lane_coordinator_receipt_v1,
    encode_perps_margin_lane_coordinator_receipt_v1, perps_margin_lane_coordinator_image_root_v1,
    prove_perps_margin_lane_coordinator_succinct_v1,
    verify_perps_margin_lane_coordinator_receipt_v1, PerpsMarginLaneCoordinatorHostErrorV1,
    PinnedPerpsMarginLaneCoordinatorReceiptVerifierV1, MAX_PERPS_MARGIN_LANE_COORDINATOR_CYCLES_V1,
};
use zenodex_perps_margin_lane_coordinator_risc0_methods::{
    ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF, ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID,
};
use zenodex_perps_margin_lane_coordinator_risc0_shared::{
    canonical_perps_margin_lane_coordinator_guest_input_bytes_v1,
    prepare_perps_margin_lane_coordinator_v1, PERPS_MARGIN_MODULE_IMAGE_ID_V1,
};
use zenodex_perps_margin_module_risc0_host::prove_perps_margin_module_succinct_v1;
use zenodex_perps_margin_module_risc0_methods::ZENODEX_PERPS_MARGIN_MODULE_GUEST_ID;

#[test]
#[ignore = "generates a real module receipt and recursively verifies it in one perps lane receipt"]
fn real_module_receipt_composes_into_exact_perps_margin_lane_journal() {
    // Arrange.
    assert!(!ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF.is_empty());
    assert_ne!(ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID, [0; 8]);
    assert_eq!(
        ZENODEX_PERPS_MARGIN_MODULE_GUEST_ID,
        PERPS_MARGIN_MODULE_IMAGE_ID_V1
    );
    let input = coordinator_input(100);
    let prepared = prepare_perps_margin_lane_coordinator_v1(input.clone()).unwrap();

    // Act.
    let started = Instant::now();
    let module_receipt = prove_perps_margin_module_succinct_v1(&input.module_input).unwrap();
    let module_elapsed = started.elapsed();

    // Assert the host rejects a valid child receipt for a different exact journal.
    assert!(matches!(
        build_perps_margin_lane_coordinator_executor_env_v1(
            &coordinator_input(101),
            module_receipt.clone(),
        ),
        Err(PerpsMarginLaneCoordinatorHostErrorV1::ModuleReceiptJournal)
    ));

    let lane_receipt =
        prove_perps_margin_lane_coordinator_succinct_v1(&input, module_receipt).unwrap();
    let total_elapsed = started.elapsed();

    // Assert.
    assert!(matches!(lane_receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(lane_receipt.journal.bytes, prepared.lane_journal_bytes);
    verify_perps_margin_lane_coordinator_receipt_v1(&lane_receipt, &prepared.lane_journal_bytes)
        .unwrap();

    let lane_image_root = perps_margin_lane_coordinator_image_root_v1().unwrap();
    let receipt_bytes = encode_perps_margin_lane_coordinator_receipt_v1(&lane_receipt).unwrap();
    PinnedPerpsMarginLaneCoordinatorReceiptVerifierV1
        .verify_succinct_receipt(
            &receipt_bytes,
            &lane_image_root,
            &prepared.lane_journal_bytes,
        )
        .unwrap();

    let mut wrong_journal = prepared.lane_journal_bytes.clone();
    wrong_journal[0] ^= 1;
    assert!(matches!(
        verify_perps_margin_lane_coordinator_receipt_v1(&lane_receipt, &wrong_journal),
        Err(PerpsMarginLaneCoordinatorHostErrorV1::LaneReceiptJournal)
    ));
    assert!(PinnedPerpsMarginLaneCoordinatorReceiptVerifierV1
        .verify_succinct_receipt(&receipt_bytes, &root(99), &prepared.lane_journal_bytes)
        .is_err());
    let pretty_receipt = serde_json::to_vec_pretty(&lane_receipt).unwrap();
    assert!(matches!(
        decode_canonical_perps_margin_lane_coordinator_receipt_v1(&pretty_receipt),
        Err(PerpsMarginLaneCoordinatorHostErrorV1::ReceiptNonCanonical)
    ));

    let elf_digest = hex::encode(Sha256::digest(
        ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF,
    ));
    println!(
        "perps margin lane coordinator image words: {ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID:?}"
    );
    println!("perps margin lane coordinator image root: {lane_image_root}");
    println!("perps margin lane coordinator embedded method sha256: {elf_digest}");
    println!("perps margin module proof elapsed: {module_elapsed:?}");
    println!("perps margin recursive lane proof total elapsed: {total_elapsed:?}");
}

#[test]
#[ignore = "executes the real coordinator guest and proves the child assumption is mandatory"]
fn missing_child_assumption_cannot_produce_a_perps_lane_receipt() {
    // Arrange.
    assert!(!ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF.is_empty());
    let input = coordinator_input(100);
    let input_bytes = canonical_perps_margin_lane_coordinator_guest_input_bytes_v1(&input).unwrap();
    let input_len = u32::try_from(input_bytes.len()).unwrap();
    let mut builder = ExecutorEnv::builder();
    builder.session_limit(Some(MAX_PERPS_MARGIN_LANE_COORDINATOR_CYCLES_V1));
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    let env = builder.build().unwrap();

    // Act.
    let proof = default_prover().prove_with_opts(
        env,
        ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF,
        &ProverOpts::succinct(),
    );

    // Assert.
    assert!(proof.is_err());
}
