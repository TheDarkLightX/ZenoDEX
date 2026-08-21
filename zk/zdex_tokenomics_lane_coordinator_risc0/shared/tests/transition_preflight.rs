mod support;

use support::{fixture, rebind_release_id, root};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, LaneIdV1, ReleaseStatusV1, RootV1,
    ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_shared::{
    canonical_zdex_tokenomics_lane_coordinator_guest_input_bytes_v1,
    prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1,
    prepare_zdex_tokenomics_lane_coordinator_v1, risc0_digest_bytes_from_root_v1,
    ZDEXTokenomicsLaneCoordinatorGuestErrorV1,
    MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1,
};

#[test]
fn exact_complete_lane_composition_emits_both_canonical_journals() {
    // Arrange
    let fixture = fixture(root(101));
    let input_bytes =
        canonical_zdex_tokenomics_lane_coordinator_guest_input_bytes_v1(&fixture.coordinator_input)
            .unwrap();

    // Act
    let first =
        prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(&input_bytes).unwrap();
    let second =
        prepare_zdex_tokenomics_lane_coordinator_v1(fixture.coordinator_input.clone()).unwrap();

    // Assert
    assert_eq!(first, second);
    assert_eq!(
        first.burn_journal_bytes,
        canonical_bytes_v1(&first.input.burn_journal).unwrap()
    );
    assert_eq!(
        first.lane_journal_bytes,
        canonical_bytes_v1(first.lane_journal()).unwrap()
    );
    assert_eq!(first.accepted.post_state, first.input.post_state);
    assert_eq!(
        first.lane_journal().ordered_module_journal_roots,
        vec![first.input.module_journal.journal_root().unwrap()]
    );
    assert!(!first.input.private_port.terminal_obligations_root.is_zero());
    assert!(!first
        .input
        .module_journal
        .terminal_obligations_root
        .is_zero());
    assert!(first.lane_journal().terminal_obligations_root.is_zero());
}

#[test]
fn rejected_composition_produces_no_prepared_journal() {
    // Arrange
    let mut input = fixture(root(101)).coordinator_input;
    input.post_state.host_claims_state_root = root(9_001);

    // Act
    let result = prepare_zdex_tokenomics_lane_coordinator_v1(input);

    // Assert
    assert!(matches!(
        result,
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Rejected(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::UNRELATED_STATE_MUTATION
        ))
    ));
}

#[test]
fn module_release_is_content_derived_shadow_tokenomics_and_command_bound() {
    // Arrange
    let baseline = fixture(root(101)).coordinator_input;
    let mut stale_id = baseline.clone();
    stale_id.module_release.release_id = root(9_100);
    let mut candidate = baseline.clone();
    candidate.module_release.status = ReleaseStatusV1::CANDIDATE;
    let mut wrong_lane = baseline.clone();
    wrong_lane.module_release.lane_id = LaneIdV1::SPOT_LIQUIDITY;
    rebind_release_id(&mut wrong_lane.module_release);
    let mut missing_command = baseline;
    missing_command.module_release.command_variants = vec!["other_command".to_owned()];
    rebind_release_id(&mut missing_command.module_release);

    // Act / Assert
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_v1(stale_id),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)
    ));
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_v1(candidate),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ModuleRelease)
    ));
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_v1(wrong_lane),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ModuleRelease)
    ));
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_v1(missing_command),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ModuleRelease)
    ));
}

#[test]
fn post_construction_release_and_occurrence_substitutions_are_revalidated() {
    // Arrange
    let baseline = fixture(root(101)).coordinator_input;
    let mut release_substitution = baseline.clone();
    release_substitution.context.tokenomics_module_release_id = root(9_200);
    let mut occurrence_substitution = baseline;
    occurrence_substitution.context.command_occurrence_id = root(9_201);

    // Act / Assert
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_v1(release_substitution),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ModuleReleaseBinding)
    ));
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_v1(occurrence_substitution),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Rejected(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::OCCURRENCE_MISMATCH
        ))
    ));
}

#[test]
fn canonical_decode_and_input_byte_ceiling_fail_closed() {
    // Arrange
    let canonical = canonical_zdex_tokenomics_lane_coordinator_guest_input_bytes_v1(
        &fixture(root(101)).coordinator_input,
    )
    .unwrap();
    let mut trailing = canonical.clone();
    trailing.push(b'\n');
    let mut unknown: serde_json::Value = serde_json::from_slice(&canonical).unwrap();
    unknown
        .as_object_mut()
        .unwrap()
        .insert("unexpected".to_owned(), serde_json::Value::Bool(true));
    let unknown = serde_json::to_vec(&unknown).unwrap();
    let at_limit = vec![b' '; MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1];
    let oversized = vec![0_u8; MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1 + 1];

    // Act / Assert
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(&[]),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::EmptyInput)
    ));
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(b"{"),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(&at_limit),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(&oversized),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::InputTooLarge)
    ));
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(&unknown),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(&trailing),
        Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::NonCanonicalInput)
    ));
}

#[test]
fn selected_module_image_root_has_exact_risc0_digest_bytes() {
    // Arrange
    let image = RootV1::parse(
        "0x0123456789abcdef1020304050607080a0b0c0d0e0f00102030405060708090a",
        "ZDEX tokenomics image test",
        false,
    )
    .unwrap();

    // Act
    let bytes = risc0_digest_bytes_from_root_v1(&image).unwrap();

    // Assert
    assert_eq!(
        bytes,
        [
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60,
            0x70, 0x80, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
            0x07, 0x08, 0x09, 0x0a,
        ]
    );
}
