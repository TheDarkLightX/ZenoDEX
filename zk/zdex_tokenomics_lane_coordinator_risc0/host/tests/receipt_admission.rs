#[path = "../../shared/tests/support/mod.rs"]
mod support;

use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use support::{fee_fixture, fixture, root};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, ZDEXLaneSuccinctReceiptVerifierV1, MAX_JOURNAL_BYTES_V1,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_host::{
    build_zdex_tokenomics_fee_lane_coordinator_executor_env_v1,
    build_zdex_tokenomics_lane_coordinator_executor_env_v1,
    decode_canonical_zdex_tokenomics_lane_coordinator_receipt_v1,
    encode_zdex_tokenomics_lane_coordinator_receipt_v1,
    prove_zdex_tokenomics_fee_lane_coordinator_succinct_v1,
    prove_zdex_tokenomics_lane_coordinator_succinct_v1,
    require_zdex_tokenomics_lane_coordinator_receipt_bytes_len_v1, verify_child_burn_receipt_v1,
    verify_zdex_tokenomics_lane_coordinator_receipt_v1,
    PinnedZDEXTokenomicsLaneCoordinatorReceiptVerifierV1, ZDEXTokenomicsLaneCoordinatorHostErrorV1,
    MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_RECEIPT_BYTES_V1,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_shared::{
    prepare_zdex_tokenomics_fee_lane_coordinator_v1, prepare_zdex_tokenomics_lane_coordinator_v1,
};

fn fake_receipt(image: [u32; 8], journal: Vec<u8>) -> Receipt {
    FakeReceipt::new(ReceiptClaim::ok(image, journal))
        .try_into()
        .unwrap()
}

#[test]
fn host_preflight_recomputes_the_complete_lane_before_receipt_admission() {
    // Arrange
    let fixture = fixture(root(101));
    let prepared =
        prepare_zdex_tokenomics_lane_coordinator_v1(fixture.coordinator_input.clone()).unwrap();
    let fake = fake_receipt([1_u32; 8], prepared.burn_journal_bytes.clone());

    // Act
    let result =
        build_zdex_tokenomics_lane_coordinator_executor_env_v1(&fixture.coordinator_input, &fake);

    // Assert
    assert!(matches!(
        result,
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptKind)
    ));
    assert_eq!(
        prepared.accepted.post_state,
        fixture.coordinator_input.post_state
    );
}

#[test]
fn fee_host_preflight_recomputes_the_complete_lane_before_receipt_admission() {
    // Arrange
    let fixture = fee_fixture(root(201));
    let prepared =
        prepare_zdex_tokenomics_fee_lane_coordinator_v1(fixture.coordinator_input.clone()).unwrap();
    let fake = fake_receipt([1_u32; 8], prepared.child_journal_bytes.clone());

    // Act
    let result = build_zdex_tokenomics_fee_lane_coordinator_executor_env_v1(
        &fixture.coordinator_input,
        &fake,
    );

    // Assert
    assert!(matches!(
        result,
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptKind)
    ));
    assert_eq!(
        prepared.accepted.post_state,
        fixture.coordinator_input.post_state
    );
    assert!(matches!(
        prove_zdex_tokenomics_fee_lane_coordinator_succinct_v1(&fixture.coordinator_input, &fake,),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::PlaceholderMethod)
    ));
}

#[test]
fn placeholder_coordinator_and_fake_receipts_fail_before_authority() {
    // Arrange
    let fixture = fixture(root(101));
    let prepared =
        prepare_zdex_tokenomics_lane_coordinator_v1(fixture.coordinator_input.clone()).unwrap();
    let fake_child = fake_receipt([1_u32; 8], prepared.burn_journal_bytes.clone());
    let fake_coordinator = fake_receipt([2_u32; 8], prepared.lane_journal_bytes.clone());

    // Act / Assert
    assert!(matches!(
        prove_zdex_tokenomics_lane_coordinator_succinct_v1(&fixture.coordinator_input, &fake_child),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::PlaceholderMethod)
    ));
    assert!(matches!(
        verify_child_burn_receipt_v1(
            &fake_child,
            &fixture.coordinator_input.module_release.guest_image_id,
            &prepared.burn_journal_bytes,
        ),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptKind)
    ));
    assert!(matches!(
        verify_zdex_tokenomics_lane_coordinator_receipt_v1(
            &fake_coordinator,
            &prepared.lane_journal_bytes,
        ),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptKind)
    ));
}

#[test]
fn receipt_json_requires_the_exact_canonical_host_encoding() {
    // Arrange
    let fake = fake_receipt([1_u32; 8], b"coordinator-journal".to_vec());
    let canonical = encode_zdex_tokenomics_lane_coordinator_receipt_v1(&fake).unwrap();
    let mut padded = Vec::with_capacity(canonical.len() + 1);
    padded.push(b' ');
    padded.extend_from_slice(&canonical);

    // Act / Assert
    assert!(decode_canonical_zdex_tokenomics_lane_coordinator_receipt_v1(&canonical).is_ok());
    assert!(matches!(
        decode_canonical_zdex_tokenomics_lane_coordinator_receipt_v1(b"{}"),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptEncoding)
    ));
    assert!(matches!(
        decode_canonical_zdex_tokenomics_lane_coordinator_receipt_v1(&padded),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptNonCanonical)
    ));
}

#[test]
fn receipt_and_expected_journal_bounds_fail_closed() {
    // Arrange / Act / Assert
    assert!(matches!(
        require_zdex_tokenomics_lane_coordinator_receipt_bytes_len_v1(0),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptSize)
    ));
    assert!(
        require_zdex_tokenomics_lane_coordinator_receipt_bytes_len_v1(
            MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_RECEIPT_BYTES_V1
        )
        .is_ok()
    );
    assert!(matches!(
        require_zdex_tokenomics_lane_coordinator_receipt_bytes_len_v1(
            MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_RECEIPT_BYTES_V1 + 1
        ),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptSize)
    ));

    let fixture = fixture(root(101));
    let prepared =
        prepare_zdex_tokenomics_lane_coordinator_v1(fixture.coordinator_input.clone()).unwrap();
    let fake = fake_receipt([1_u32; 8], prepared.lane_journal_bytes.clone());
    assert!(matches!(
        verify_zdex_tokenomics_lane_coordinator_receipt_v1(&fake, &[]),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptJournal)
    ));
    let oversized_journal = vec![0_u8; usize::try_from(MAX_JOURNAL_BYTES_V1).unwrap() + 1];
    assert!(matches!(
        verify_child_burn_receipt_v1(
            &fake,
            &fixture.coordinator_input.module_release.guest_image_id,
            &oversized_journal,
        ),
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptJournal)
    ));

    let verifier = PinnedZDEXTokenomicsLaneCoordinatorReceiptVerifierV1;
    assert!(matches!(
        verifier.verify_succinct_receipt(&[], &root(91), &prepared.lane_journal_bytes),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
    let oversized_receipt = vec![0_u8; MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_RECEIPT_BYTES_V1 + 1];
    assert!(matches!(
        verifier.verify_succinct_receipt(
            &oversized_receipt,
            &root(91),
            &prepared.lane_journal_bytes,
        ),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
}
