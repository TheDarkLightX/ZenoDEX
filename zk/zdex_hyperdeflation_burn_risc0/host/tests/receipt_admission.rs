mod support;

use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use support::{guest_input, root};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, ZDEXBurnRejectCodeV1, ZDEXLaneSuccinctReceiptVerifierV1, MAX_JOURNAL_BYTES_V1,
};
use zenodex_zdex_hyperdeflation_burn_risc0_host::{
    build_zdex_hyperdeflation_burn_executor_env_v1,
    decode_canonical_zdex_hyperdeflation_burn_receipt_v1,
    encode_zdex_hyperdeflation_burn_receipt_v1, prove_zdex_hyperdeflation_burn_succinct_v1,
    require_zdex_hyperdeflation_burn_receipt_bytes_len_v1,
    verify_zdex_hyperdeflation_burn_receipt_v1, PinnedZDEXHyperdeflationBurnReceiptVerifierV1,
    ZDEXHyperdeflationBurnHostErrorV1, MAX_ZDEX_HYPERDEFLATION_BURN_RECEIPT_BYTES_V1,
};
use zenodex_zdex_hyperdeflation_burn_risc0_shared::ZDEXHyperdeflationBurnGuestErrorV1;

#[test]
fn host_preflight_uses_the_same_transition_and_rejects_economic_denial() {
    // Arrange
    let accepted_input = guest_input(100);
    let mut rejected_input = guest_input(100);
    rejected_input.route_context.purchased_zdex_atoms = 101;
    rejected_input.command.purchased_zdex_atoms = 101;

    // Act
    let (_, accepted) = build_zdex_hyperdeflation_burn_executor_env_v1(&accepted_input).unwrap();
    let rejected = build_zdex_hyperdeflation_burn_executor_env_v1(&rejected_input);

    // Assert
    assert_eq!(accepted.projection.journal().burned_zdex_atoms, 100);
    assert_eq!(accepted.projection.journal().burn_bucket_post_atoms, 0);
    assert!(matches!(
        rejected,
        Err(ZDEXHyperdeflationBurnHostErrorV1::Guest(
            ZDEXHyperdeflationBurnGuestErrorV1::Rejected(
                ZDEXBurnRejectCodeV1::PURCHASE_EXCEEDS_BURN_CAPACITY
            )
        ))
    ));
}

#[test]
fn placeholder_method_and_fake_receipt_fail_before_authority() {
    // Arrange
    let (_, prepared) = build_zdex_hyperdeflation_burn_executor_env_v1(&guest_input(100)).unwrap();
    let fake: Receipt =
        FakeReceipt::new(ReceiptClaim::ok([1_u32; 8], prepared.journal_bytes.clone()))
            .try_into()
            .unwrap();

    // Act / Assert
    assert!(matches!(
        prove_zdex_hyperdeflation_burn_succinct_v1(&guest_input(100)),
        Err(ZDEXHyperdeflationBurnHostErrorV1::PlaceholderMethod)
    ));
    assert!(matches!(
        verify_zdex_hyperdeflation_burn_receipt_v1(&fake, &prepared.journal_bytes),
        Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptKind)
    ));
}

#[test]
fn receipt_json_must_be_the_exact_canonical_host_encoding() {
    // Arrange
    let (_, prepared) = build_zdex_hyperdeflation_burn_executor_env_v1(&guest_input(100)).unwrap();
    let fake: Receipt =
        FakeReceipt::new(ReceiptClaim::ok([1_u32; 8], prepared.journal_bytes.clone()))
            .try_into()
            .unwrap();
    let canonical = encode_zdex_hyperdeflation_burn_receipt_v1(&fake).unwrap();
    let mut padded = Vec::with_capacity(canonical.len() + 1);
    padded.push(b' ');
    padded.extend_from_slice(&canonical);

    // Act / Assert
    assert!(decode_canonical_zdex_hyperdeflation_burn_receipt_v1(&canonical).is_ok());
    assert!(matches!(
        decode_canonical_zdex_hyperdeflation_burn_receipt_v1(b"{}"),
        Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptEncoding)
    ));
    assert!(matches!(
        decode_canonical_zdex_hyperdeflation_burn_receipt_v1(&padded),
        Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptNonCanonical)
    ));
}

#[test]
fn receipt_and_expected_journal_bounds_fail_closed() {
    // Arrange / Act / Assert: BVA around both untrusted byte ceilings.
    assert!(matches!(
        require_zdex_hyperdeflation_burn_receipt_bytes_len_v1(0),
        Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptSize)
    ));
    assert!(require_zdex_hyperdeflation_burn_receipt_bytes_len_v1(
        MAX_ZDEX_HYPERDEFLATION_BURN_RECEIPT_BYTES_V1
    )
    .is_ok());
    assert!(matches!(
        require_zdex_hyperdeflation_burn_receipt_bytes_len_v1(
            MAX_ZDEX_HYPERDEFLATION_BURN_RECEIPT_BYTES_V1 + 1
        ),
        Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptSize)
    ));

    let (_, prepared) = build_zdex_hyperdeflation_burn_executor_env_v1(&guest_input(100)).unwrap();
    let fake: Receipt =
        FakeReceipt::new(ReceiptClaim::ok([1_u32; 8], prepared.journal_bytes.clone()))
            .try_into()
            .unwrap();
    assert!(matches!(
        verify_zdex_hyperdeflation_burn_receipt_v1(&fake, &[]),
        Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptJournal)
    ));
    let oversized_journal = vec![0_u8; usize::try_from(MAX_JOURNAL_BYTES_V1).unwrap() + 1];
    assert!(matches!(
        verify_zdex_hyperdeflation_burn_receipt_v1(&fake, &oversized_journal),
        Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptJournal)
    ));

    let verifier = PinnedZDEXHyperdeflationBurnReceiptVerifierV1;
    assert!(matches!(
        verifier.verify_succinct_receipt(&[], &root(91), &prepared.journal_bytes),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
    let oversized_receipt = vec![0_u8; MAX_ZDEX_HYPERDEFLATION_BURN_RECEIPT_BYTES_V1 + 1];
    assert!(matches!(
        verifier.verify_succinct_receipt(&oversized_receipt, &root(91), &prepared.journal_bytes),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
}
