use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};

#[path = "support/mod.rs"]
mod support;

use support::{coordinator_input, root};
use zenodex_global_settlement_abi_v1::{AbiErrorV1, LaneCompositionSuccinctReceiptVerifierV1};
use zenodex_perps_margin_lane_coordinator_risc0_host::{
    build_perps_margin_lane_coordinator_executor_env_v1,
    decode_canonical_perps_margin_lane_coordinator_receipt_v1,
    prove_perps_margin_lane_coordinator_succinct_v1,
    require_perps_margin_lane_coordinator_receipt_bytes_len_v1,
    PerpsMarginLaneCoordinatorHostErrorV1, PinnedPerpsMarginLaneCoordinatorReceiptVerifierV1,
    MAX_PERPS_MARGIN_LANE_COORDINATOR_RECEIPT_BYTES_V1,
};
use zenodex_perps_margin_lane_coordinator_risc0_methods::ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF;
use zenodex_perps_margin_lane_coordinator_risc0_shared::{
    prepare_perps_margin_lane_coordinator_v1, PERPS_MARGIN_MODULE_IMAGE_ID_V1,
};

#[test]
fn fake_module_receipt_and_any_placeholder_lane_method_reject_before_authority() {
    // Arrange.
    let input = coordinator_input(100);
    let prepared = prepare_perps_margin_lane_coordinator_v1(input.clone()).unwrap();
    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        PERPS_MARGIN_MODULE_IMAGE_ID_V1,
        prepared.module_journal_bytes,
    ))
    .try_into()
    .unwrap();

    // Act and assert.
    assert!(matches!(
        build_perps_margin_lane_coordinator_executor_env_v1(&input, fake.clone()),
        Err(PerpsMarginLaneCoordinatorHostErrorV1::ModuleReceiptKind)
    ));
    let prove_error = prove_perps_margin_lane_coordinator_succinct_v1(&input, fake).unwrap_err();
    if ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF.is_empty() {
        assert_eq!(
            prove_error,
            PerpsMarginLaneCoordinatorHostErrorV1::PlaceholderMethod
        );
    } else {
        assert_eq!(
            prove_error,
            PerpsMarginLaneCoordinatorHostErrorV1::ModuleReceiptKind
        );
    }
}

#[test]
fn receipt_byte_ceiling_rejects_zero_and_maximum_plus_one_before_decoding() {
    // Arrange, act, and assert: BVA around the resource-admission ceiling.
    assert!(matches!(
        require_perps_margin_lane_coordinator_receipt_bytes_len_v1(0),
        Err(PerpsMarginLaneCoordinatorHostErrorV1::ReceiptSize)
    ));
    assert!(require_perps_margin_lane_coordinator_receipt_bytes_len_v1(
        MAX_PERPS_MARGIN_LANE_COORDINATOR_RECEIPT_BYTES_V1
    )
    .is_ok());
    assert!(matches!(
        require_perps_margin_lane_coordinator_receipt_bytes_len_v1(
            MAX_PERPS_MARGIN_LANE_COORDINATOR_RECEIPT_BYTES_V1 + 1
        ),
        Err(PerpsMarginLaneCoordinatorHostErrorV1::ReceiptSize)
    ));

    let verifier = PinnedPerpsMarginLaneCoordinatorReceiptVerifierV1;
    assert!(matches!(
        verifier.verify_succinct_receipt(&[], &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
    let oversized = vec![0_u8; MAX_PERPS_MARGIN_LANE_COORDINATOR_RECEIPT_BYTES_V1 + 1];
    assert!(matches!(
        verifier.verify_succinct_receipt(&oversized, &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
}

#[test]
fn receipt_codec_accepts_exact_bytes_and_rejects_equivalent_pretty_json() {
    // Arrange.
    let prepared = prepare_perps_margin_lane_coordinator_v1(coordinator_input(100)).unwrap();
    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        PERPS_MARGIN_MODULE_IMAGE_ID_V1,
        prepared.lane_journal_bytes,
    ))
    .try_into()
    .unwrap();
    let canonical = serde_json::to_vec(&fake).unwrap();
    let pretty = serde_json::to_vec_pretty(&fake).unwrap();

    // Act and assert.
    assert!(decode_canonical_perps_margin_lane_coordinator_receipt_v1(&canonical).is_ok());
    assert!(matches!(
        decode_canonical_perps_margin_lane_coordinator_receipt_v1(&pretty),
        Err(PerpsMarginLaneCoordinatorHostErrorV1::ReceiptNonCanonical)
    ));
}
