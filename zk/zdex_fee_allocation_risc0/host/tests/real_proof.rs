use std::time::Instant;

use risc0_zkvm::InnerReceipt;
use sha2::{Digest, Sha256};
use zenodex_global_settlement_abi_v1::{
    candidate_zdex_fee_allocation_policy_v1, RootV1, ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1, ZDEXFeeDestinationAmountV1, ZDEXFeeStateV1,
    ZDEXLaneSuccinctReceiptVerifierV1, ZDEX_FEE_DESTINATIONS_V1,
};
use zenodex_zdex_fee_allocation_risc0_host::{
    encode_zdex_fee_allocation_receipt_v1, prove_zdex_fee_allocation_succinct_v1,
    verify_zdex_fee_allocation_receipt_v1, zdex_fee_allocation_image_root_v1,
    PinnedZDEXFeeAllocationReceiptVerifierV1, ZDEXFeeAllocationHostErrorV1,
};
use zenodex_zdex_fee_allocation_risc0_methods::{
    ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ELF, ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ID,
};
use zenodex_zdex_fee_allocation_risc0_shared::{
    prepare_zdex_fee_allocation_v1, ZDEXFeeAllocationGuestInputV1,
    ZDEX_FEE_ALLOCATION_GUEST_INPUT_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "real ZDEX fee-allocation proof root",
        false,
    )
    .unwrap()
}

fn guest_input() -> ZDEXFeeAllocationGuestInputV1 {
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let policy_root = policy.policy_root().unwrap();
    ZDEXFeeAllocationGuestInputV1 {
        schema: ZDEX_FEE_ALLOCATION_GUEST_INPUT_SCHEMA_V1.to_owned(),
        context: ZDEXFeeAllocationContextV1 {
            chain_id: "zenodex-real-fee-allocation-proof".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 11,
            allocation_route_release_id: root(3),
            authorized_buyback_route_release_id: root(4),
            tokenomics_module_release_id: root(5),
            command_occurrence_id: root(6),
            policy_root: policy_root.clone(),
        },
        pre_state: ZDEXFeeStateV1 {
            fee_asset_id: root(40),
            policy_root,
            fee_ingress_atoms: 50_000,
            unallocated_reserve_atoms: 700,
            destination_balances: ZDEX_FEE_DESTINATIONS_V1
                .into_iter()
                .zip([10, 20, 30, 40, 50, 60])
                .map(
                    |(destination, allocation_atoms)| ZDEXFeeDestinationAmountV1 {
                        destination,
                        allocation_atoms,
                    },
                )
                .collect(),
            owned_and_custodied_atoms: 1_000_000,
            supply_atoms: 1_000_000,
        },
        policy,
        command: ZDEXFeeAllocationCommandV1 {
            fee_charged_atoms: 10_003,
        },
    }
}

#[test]
#[ignore = "generates one real ZDEX fee-allocation RISC0 Succinct receipt"]
fn real_zdex_fee_allocation_proves_the_exact_occurrence_journal() {
    // Arrange
    assert!(!ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ELF.is_empty());
    assert_ne!(ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ID, [0; 8]);
    let input = guest_input();
    let prepared = prepare_zdex_fee_allocation_v1(input.clone()).unwrap();
    let started = Instant::now();

    // Act
    let receipt = prove_zdex_fee_allocation_succinct_v1(&input).unwrap();
    let elapsed = started.elapsed();
    let image_root = zdex_fee_allocation_image_root_v1().unwrap();
    let receipt_bytes = encode_zdex_fee_allocation_receipt_v1(&receipt).unwrap();

    // Assert
    assert!(matches!(&receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(receipt.journal.bytes, prepared.journal_bytes);
    PinnedZDEXFeeAllocationReceiptVerifierV1
        .verify_succinct_receipt(&receipt_bytes, &image_root, &prepared.journal_bytes)
        .unwrap();
    let mut wrong_journal = prepared.journal_bytes.clone();
    wrong_journal[0] ^= 1;
    assert!(matches!(
        verify_zdex_fee_allocation_receipt_v1(&receipt, &wrong_journal),
        Err(ZDEXFeeAllocationHostErrorV1::ReceiptJournal)
    ));
    assert!(PinnedZDEXFeeAllocationReceiptVerifierV1
        .verify_succinct_receipt(&receipt_bytes, &root(99), &prepared.journal_bytes)
        .is_err());

    let embedded_method_sha256 = hex::encode(Sha256::digest(ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ELF));
    println!("ZDEX fee-allocation guest image words: {ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ID:?}");
    println!("ZDEX fee-allocation guest image root: {image_root}");
    println!("ZDEX fee-allocation embedded method sha256: {embedded_method_sha256}");
    println!("ZDEX fee-allocation real proof elapsed: {elapsed:?}");
}
