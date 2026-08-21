#[path = "../../shared/tests/support/mod.rs"]
mod support;

use std::time::Instant;

use risc0_zkvm::{default_prover, InnerReceipt, ProverOpts, ReceiptClaim};
use sha2::{Digest, Sha256};
use support::{fixture, root};
use zenodex_global_settlement_abi_v1::ZDEXLaneSuccinctReceiptVerifierV1;
use zenodex_zdex_hyperdeflation_burn_risc0_host::{
    prove_zdex_hyperdeflation_burn_succinct_v1, zdex_hyperdeflation_burn_image_root_v1,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_host::{
    build_zdex_tokenomics_lane_coordinator_executor_env_v1,
    encode_zdex_tokenomics_lane_coordinator_receipt_v1,
    prove_zdex_tokenomics_lane_coordinator_succinct_v1, verify_child_burn_receipt_v1,
    verify_zdex_tokenomics_lane_coordinator_receipt_v1,
    zdex_tokenomics_lane_coordinator_image_root_v1,
    PinnedZDEXTokenomicsLaneCoordinatorReceiptVerifierV1, ZDEXTokenomicsLaneCoordinatorHostErrorV1,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_methods::{
    ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ELF,
    ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ID,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_shared::{
    canonical_zdex_tokenomics_lane_coordinator_guest_input_bytes_v1,
    prepare_zdex_tokenomics_lane_coordinator_v1,
};

#[test]
#[ignore = "generates real child and recursive coordinator Succinct receipts"]
fn real_recursive_coordinator_proves_the_exact_complete_lane_journal() {
    // Arrange
    assert!(!ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ELF.is_empty());
    assert_ne!(ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ID, [0; 8]);
    let child_image = zdex_hyperdeflation_burn_image_root_v1().unwrap();
    let fixture = fixture(child_image.clone());
    let prepared =
        prepare_zdex_tokenomics_lane_coordinator_v1(fixture.coordinator_input.clone()).unwrap();
    let child_receipt = prove_zdex_hyperdeflation_burn_succinct_v1(&fixture.child_input).unwrap();
    let started = Instant::now();

    // Act
    let receipt = prove_zdex_tokenomics_lane_coordinator_succinct_v1(
        &fixture.coordinator_input,
        &child_receipt,
    )
    .unwrap();
    let elapsed = started.elapsed();
    let image_root = zdex_tokenomics_lane_coordinator_image_root_v1().unwrap();
    let receipt_bytes = encode_zdex_tokenomics_lane_coordinator_receipt_v1(&receipt).unwrap();

    // Assert
    assert!(matches!(&child_receipt.inner, InnerReceipt::Succinct(_)));
    assert!(matches!(&receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(child_receipt.journal.bytes, prepared.burn_journal_bytes);
    assert_eq!(receipt.journal.bytes, prepared.lane_journal_bytes);
    PinnedZDEXTokenomicsLaneCoordinatorReceiptVerifierV1
        .verify_succinct_receipt(&receipt_bytes, &image_root, &prepared.lane_journal_bytes)
        .unwrap();

    let mut wrong_child_journal = prepared.burn_journal_bytes.clone();
    wrong_child_journal[0] ^= 1;
    assert!(matches!(
        verify_child_burn_receipt_v1(&child_receipt, &child_image, &wrong_child_journal),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptJournal)
    ));
    assert!(matches!(
        verify_child_burn_receipt_v1(&child_receipt, &root(99), &prepared.burn_journal_bytes,),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptVerification)
    ));
    let mut wrong_lane_journal = prepared.lane_journal_bytes.clone();
    wrong_lane_journal[0] ^= 1;
    assert!(matches!(
        verify_zdex_tokenomics_lane_coordinator_receipt_v1(&receipt, &wrong_lane_journal),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptJournal)
    ));

    // A direct execution without the admitted child assumption must fail to prove.
    let input_bytes =
        canonical_zdex_tokenomics_lane_coordinator_guest_input_bytes_v1(&fixture.coordinator_input)
            .unwrap();
    let input_len = u32::try_from(input_bytes.len()).unwrap();
    let mut no_assumption_builder = risc0_zkvm::ExecutorEnv::builder();
    no_assumption_builder.write_slice(&[input_len]);
    no_assumption_builder.write_slice(&input_bytes);
    let no_assumption_env = no_assumption_builder.build().unwrap();
    assert!(default_prover()
        .prove_with_opts(
            no_assumption_env,
            ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .is_err());

    // A claim-only assumption can produce a conditional root, which admission rejects.
    let mut conditional_builder = risc0_zkvm::ExecutorEnv::builder();
    conditional_builder.write_slice(&[input_len]);
    conditional_builder.write_slice(&input_bytes);
    let child_claim: ReceiptClaim = child_receipt.claim().unwrap().as_value().unwrap().clone();
    conditional_builder.add_assumption(child_claim);
    let conditional_env = conditional_builder.build().unwrap();
    let conditional_receipt = default_prover()
        .prove_with_opts(
            conditional_env,
            ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .unwrap()
        .receipt;
    assert!(matches!(
        verify_zdex_tokenomics_lane_coordinator_receipt_v1(
            &conditional_receipt,
            &prepared.lane_journal_bytes,
        ),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptVerification)
    ));

    // The public builder accepted the real child and therefore supplied the exact assumption.
    assert!(build_zdex_tokenomics_lane_coordinator_executor_env_v1(
        &fixture.coordinator_input,
        &child_receipt,
    )
    .is_ok());

    let embedded_method_sha256 = hex::encode(Sha256::digest(
        ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ELF,
    ));
    println!(
        "ZDEX tokenomics coordinator image words: {:?}",
        ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ID
    );
    println!("ZDEX tokenomics coordinator image root: {image_root}");
    println!("ZDEX tokenomics coordinator embedded method sha256: {embedded_method_sha256}");
    println!("ZDEX tokenomics coordinator real proof elapsed: {elapsed:?}");
}
