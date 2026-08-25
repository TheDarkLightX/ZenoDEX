use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};

#[path = "support/mod.rs"]
mod support;

use support::{root, route_input};
use zenodex_global_settlement_abi_v1::{AbiErrorV1, RouteCompositionSuccinctReceiptVerifierV1};
use zenodex_perps_margin_route_composer_risc0_host::{
    build_perps_margin_route_composer_executor_env_v1,
    decode_canonical_perps_margin_route_composer_receipt_v1,
    prove_perps_margin_route_composer_succinct_v1,
    require_perps_margin_route_composer_receipt_bytes_len_v1, verify_perps_margin_lane_receipt_v1,
    PerpsMarginRouteComposerHostErrorV1, PinnedPerpsMarginRouteComposerReceiptVerifierV1,
    MAX_PERPS_MARGIN_ROUTE_COMPOSER_RECEIPT_BYTES_V1,
};
use zenodex_perps_margin_route_composer_risc0_methods::ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ELF;
use zenodex_perps_margin_route_composer_risc0_shared::{
    prepare_perps_margin_route_composer_v1, PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1,
};

#[test]
fn fake_lane_receipt_and_placeholder_route_method_fail_closed() {
    // Arrange.
    let input = route_input(100);
    let prepared = prepare_perps_margin_route_composer_v1(input.clone()).unwrap();
    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1,
        prepared.lane_journal_bytes.clone(),
    ))
    .try_into()
    .unwrap();

    // Act and assert.
    assert!(matches!(
        verify_perps_margin_lane_receipt_v1(&fake, &prepared.lane_journal_bytes),
        Err(PerpsMarginRouteComposerHostErrorV1::LaneReceiptKind)
    ));
    assert!(matches!(
        build_perps_margin_route_composer_executor_env_v1(&input, fake.clone()),
        Err(PerpsMarginRouteComposerHostErrorV1::LaneReceiptKind)
    ));
    let error = prove_perps_margin_route_composer_succinct_v1(&input, fake).unwrap_err();
    if ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ELF.is_empty() {
        assert_eq!(
            error,
            PerpsMarginRouteComposerHostErrorV1::PlaceholderMethod
        );
    } else {
        assert_eq!(error, PerpsMarginRouteComposerHostErrorV1::LaneReceiptKind);
    }
}

#[test]
fn receipt_and_expected_journal_boundaries_reject_before_authority() {
    // Arrange, act, and assert.
    assert!(matches!(
        require_perps_margin_route_composer_receipt_bytes_len_v1(0),
        Err(PerpsMarginRouteComposerHostErrorV1::ReceiptSize)
    ));
    assert!(require_perps_margin_route_composer_receipt_bytes_len_v1(
        MAX_PERPS_MARGIN_ROUTE_COMPOSER_RECEIPT_BYTES_V1
    )
    .is_ok());
    assert!(matches!(
        require_perps_margin_route_composer_receipt_bytes_len_v1(
            MAX_PERPS_MARGIN_ROUTE_COMPOSER_RECEIPT_BYTES_V1 + 1
        ),
        Err(PerpsMarginRouteComposerHostErrorV1::ReceiptSize)
    ));

    let verifier = PinnedPerpsMarginRouteComposerReceiptVerifierV1;
    assert!(matches!(
        verifier.verify_succinct_receipt(&[], &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
    let oversized = vec![0_u8; MAX_PERPS_MARGIN_ROUTE_COMPOSER_RECEIPT_BYTES_V1 + 1];
    assert!(matches!(
        verifier.verify_succinct_receipt(&oversized, &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
}

#[test]
fn receipt_codec_rejects_equivalent_noncanonical_json() {
    // Arrange.
    let prepared = prepare_perps_margin_route_composer_v1(route_input(100)).unwrap();
    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1,
        prepared.route_journal_bytes,
    ))
    .try_into()
    .unwrap();
    let canonical = serde_json::to_vec(&fake).unwrap();
    let pretty = serde_json::to_vec_pretty(&fake).unwrap();

    // Act and assert.
    assert!(decode_canonical_perps_margin_route_composer_receipt_v1(&canonical).is_ok());
    assert!(matches!(
        decode_canonical_perps_margin_route_composer_receipt_v1(&pretty),
        Err(PerpsMarginRouteComposerHostErrorV1::ReceiptNonCanonical)
    ));
}
