use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};

#[path = "support/mod.rs"]
mod support;

use support::{module_input, root};
use zenodex_global_settlement_abi_v1::{AbiErrorV1, LaneModuleSuccinctReceiptVerifierV1};
use zenodex_perps_margin_module_risc0_host::{
    build_perps_margin_module_executor_env_v1, decode_canonical_perps_margin_module_receipt_v1,
    encode_perps_margin_module_receipt_v1, prove_perps_margin_module_succinct_v1,
    require_perps_margin_module_receipt_bytes_len_v1, verify_perps_margin_module_receipt_v1,
    PerpsMarginModuleHostErrorV1, PinnedPerpsMarginModuleReceiptVerifierV1,
    MAX_PERPS_MARGIN_MODULE_RECEIPT_BYTES_V1,
};

#[test]
fn host_preflight_recomputes_transition_and_rejects_economic_denial() {
    // Arrange and act.
    let (_, accepted) = build_perps_margin_module_executor_env_v1(&module_input(100)).unwrap();
    let rejected = build_perps_margin_module_executor_env_v1(&module_input(0));

    // Assert.
    assert_eq!(
        accepted.accepted.post_state.accounts[0].collateral_atoms,
        100
    );
    assert!(matches!(
        rejected,
        Err(PerpsMarginModuleHostErrorV1::Guest(
            zenodex_perps_margin_module_risc0_shared::PerpsMarginModuleGuestErrorV1::Rejected(
                zenodex_global_settlement_abi_v1::PerpsMarginRejectCodeV1::ZERO_AMOUNT
            )
        ))
    ));
}

#[test]
fn placeholder_method_and_fake_receipt_fail_before_authority() {
    // Arrange.
    let (_, prepared) = build_perps_margin_module_executor_env_v1(&module_input(100)).unwrap();
    let fake: Receipt =
        FakeReceipt::new(ReceiptClaim::ok([1_u32; 8], prepared.journal_bytes.clone()))
            .try_into()
            .unwrap();

    // Act and assert.
    assert!(matches!(
        prove_perps_margin_module_succinct_v1(&module_input(100)),
        Err(PerpsMarginModuleHostErrorV1::PlaceholderMethod)
    ));
    assert!(matches!(
        verify_perps_margin_module_receipt_v1(&fake, &prepared.journal_bytes),
        Err(PerpsMarginModuleHostErrorV1::ReceiptKind)
    ));
    let encoded = encode_perps_margin_module_receipt_v1(&fake).unwrap();
    assert!(matches!(
        PinnedPerpsMarginModuleReceiptVerifierV1.verify_succinct_receipt(
            &encoded,
            &root(91),
            &prepared.journal_bytes,
        ),
        Err(AbiErrorV1::InvalidBinding("perps margin RISC0 method"))
    ));
}

#[test]
fn receipt_byte_and_expected_journal_bva_reject_before_decoding() {
    // Arrange, act, and assert.
    assert!(matches!(
        require_perps_margin_module_receipt_bytes_len_v1(0),
        Err(PerpsMarginModuleHostErrorV1::ReceiptSize)
    ));
    assert!(require_perps_margin_module_receipt_bytes_len_v1(
        MAX_PERPS_MARGIN_MODULE_RECEIPT_BYTES_V1
    )
    .is_ok());
    assert!(matches!(
        require_perps_margin_module_receipt_bytes_len_v1(
            MAX_PERPS_MARGIN_MODULE_RECEIPT_BYTES_V1 + 1
        ),
        Err(PerpsMarginModuleHostErrorV1::ReceiptSize)
    ));

    let verifier = PinnedPerpsMarginModuleReceiptVerifierV1;
    assert!(matches!(
        verifier.verify_succinct_receipt(&[], &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
    let oversized = vec![0_u8; MAX_PERPS_MARGIN_MODULE_RECEIPT_BYTES_V1 + 1];
    assert!(matches!(
        verifier.verify_succinct_receipt(&oversized, &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
}

#[test]
fn receipt_codec_accepts_exact_bytes_and_rejects_equivalent_pretty_json() {
    // Arrange.
    let (_, prepared) = build_perps_margin_module_executor_env_v1(&module_input(100)).unwrap();
    let fake: Receipt =
        FakeReceipt::new(ReceiptClaim::ok([1_u32; 8], prepared.journal_bytes.clone()))
            .try_into()
            .unwrap();
    let canonical = encode_perps_margin_module_receipt_v1(&fake).unwrap();
    let noncanonical = serde_json::to_vec_pretty(&fake).unwrap();

    // Act and assert.
    let decoded = decode_canonical_perps_margin_module_receipt_v1(&canonical).unwrap();
    assert_eq!(
        encode_perps_margin_module_receipt_v1(&decoded).unwrap(),
        canonical
    );
    assert!(matches!(
        decode_canonical_perps_margin_module_receipt_v1(&noncanonical),
        Err(PerpsMarginModuleHostErrorV1::ReceiptNonCanonical)
    ));
}
