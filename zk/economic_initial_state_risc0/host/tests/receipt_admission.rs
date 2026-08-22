mod support;

use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use support::{guest_input, root};
use zenodex_economic_initial_state_risc0_host::{
    build_economic_initial_state_executor_env_v1, certify_economic_initial_state_receipt_v1,
    decode_canonical_economic_initial_state_receipt_v1, encode_economic_initial_state_receipt_v1,
    prove_economic_initial_state_succinct_v1, require_economic_initial_state_receipt_bytes_len_v1,
    verify_economic_initial_state_receipt_v1, EconomicInitialStateHostErrorV1,
    MAX_ECONOMIC_INITIAL_STATE_RECEIPT_BYTES_V1,
};
use zenodex_global_settlement_abi_v1::{MAX_CYCLE_BUDGET_V1, MAX_JOURNAL_BYTES_V1};

fn prepared_and_fake_receipt() -> (
    zenodex_economic_initial_state_risc0_shared::PreparedEconomicInitialStateV1,
    Receipt,
) {
    let (_, prepared) =
        build_economic_initial_state_executor_env_v1(&guest_input(root(91))).unwrap();
    let fake = FakeReceipt::new(ReceiptClaim::ok(
        [1_u32; 8],
        prepared.journal_bytes().to_vec(),
    ))
    .try_into()
    .unwrap();
    (prepared, fake)
}

#[test]
fn placeholder_method_and_fake_receipt_fail_before_authority() {
    // Arrange
    let (prepared, fake) = prepared_and_fake_receipt();

    // Act / Assert
    assert!(matches!(
        prove_economic_initial_state_succinct_v1(&guest_input(root(91))),
        Err(EconomicInitialStateHostErrorV1::PlaceholderMethod)
    ));
    assert!(matches!(
        verify_economic_initial_state_receipt_v1(&fake, prepared.journal_bytes()),
        Err(EconomicInitialStateHostErrorV1::ReceiptKind)
    ));
}

#[test]
fn receipt_json_must_be_the_exact_canonical_host_encoding() {
    // Arrange
    let (_, fake) = prepared_and_fake_receipt();
    let canonical = encode_economic_initial_state_receipt_v1(&fake).unwrap();
    let mut padded = Vec::with_capacity(canonical.len() + 1);
    padded.push(b' ');
    padded.extend_from_slice(&canonical);

    // Act / Assert
    assert!(decode_canonical_economic_initial_state_receipt_v1(&canonical).is_ok());
    assert!(matches!(
        decode_canonical_economic_initial_state_receipt_v1(b"{}"),
        Err(EconomicInitialStateHostErrorV1::ReceiptEncoding)
    ));
    assert!(matches!(
        decode_canonical_economic_initial_state_receipt_v1(&padded),
        Err(EconomicInitialStateHostErrorV1::ReceiptNonCanonical)
    ));
}

#[test]
fn receipt_and_expected_journal_byte_bounds_have_exact_neighbors() {
    // Arrange / Act / Assert
    assert!(matches!(
        require_economic_initial_state_receipt_bytes_len_v1(0),
        Err(EconomicInitialStateHostErrorV1::ReceiptSize)
    ));
    assert!(require_economic_initial_state_receipt_bytes_len_v1(1).is_ok());
    assert!(require_economic_initial_state_receipt_bytes_len_v1(
        MAX_ECONOMIC_INITIAL_STATE_RECEIPT_BYTES_V1 - 1
    )
    .is_ok());
    assert!(require_economic_initial_state_receipt_bytes_len_v1(
        MAX_ECONOMIC_INITIAL_STATE_RECEIPT_BYTES_V1
    )
    .is_ok());
    assert!(matches!(
        require_economic_initial_state_receipt_bytes_len_v1(
            MAX_ECONOMIC_INITIAL_STATE_RECEIPT_BYTES_V1 + 1
        ),
        Err(EconomicInitialStateHostErrorV1::ReceiptSize)
    ));

    let (_, fake) = prepared_and_fake_receipt();
    assert!(matches!(
        verify_economic_initial_state_receipt_v1(&fake, &[]),
        Err(EconomicInitialStateHostErrorV1::ReceiptJournal)
    ));
    assert!(matches!(
        verify_economic_initial_state_receipt_v1(&fake, &[b'0']),
        Err(EconomicInitialStateHostErrorV1::ReceiptKind)
    ));
    let below_limit = vec![b'0'; usize::try_from(MAX_JOURNAL_BYTES_V1).unwrap() - 1];
    assert!(matches!(
        verify_economic_initial_state_receipt_v1(&fake, &below_limit),
        Err(EconomicInitialStateHostErrorV1::ReceiptKind)
    ));
    let at_limit = vec![b'0'; usize::try_from(MAX_JOURNAL_BYTES_V1).unwrap()];
    assert!(matches!(
        verify_economic_initial_state_receipt_v1(&fake, &at_limit),
        Err(EconomicInitialStateHostErrorV1::ReceiptKind)
    ));
    let over_limit = vec![b'0'; usize::try_from(MAX_JOURNAL_BYTES_V1).unwrap() + 1];
    assert!(matches!(
        verify_economic_initial_state_receipt_v1(&fake, &over_limit),
        Err(EconomicInitialStateHostErrorV1::ReceiptJournal)
    ));
}

#[test]
fn certificate_cycle_budget_rejects_zero_and_global_maximum_plus_one_first() {
    // Arrange
    let (prepared, fake) = prepared_and_fake_receipt();

    // Act / Assert
    assert!(matches!(
        certify_economic_initial_state_receipt_v1(&prepared, &fake, 0),
        Err(EconomicInitialStateHostErrorV1::Certificate)
    ));
    assert!(matches!(
        certify_economic_initial_state_receipt_v1(&prepared, &fake, 1),
        Err(EconomicInitialStateHostErrorV1::ReceiptKind)
    ));
    assert!(matches!(
        certify_economic_initial_state_receipt_v1(&prepared, &fake, MAX_CYCLE_BUDGET_V1 - 1,),
        Err(EconomicInitialStateHostErrorV1::ReceiptKind)
    ));
    assert!(matches!(
        certify_economic_initial_state_receipt_v1(&prepared, &fake, MAX_CYCLE_BUDGET_V1 + 1,),
        Err(EconomicInitialStateHostErrorV1::Certificate)
    ));
    assert!(matches!(
        certify_economic_initial_state_receipt_v1(&prepared, &fake, MAX_CYCLE_BUDGET_V1,),
        Err(EconomicInitialStateHostErrorV1::ReceiptKind)
    ));
}
