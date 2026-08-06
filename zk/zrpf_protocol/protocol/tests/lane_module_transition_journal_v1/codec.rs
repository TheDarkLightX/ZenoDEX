use super::support::*;
use zenodex_zrpf_protocol_v3::MAX_LANE_MODULE_TRANSITION_JOURNAL_BYTES_V1;

#[test]
fn accepted_journal_codec_round_trips_exactly() {
    // Arrange
    let fixture = accepted_fixture(1);
    let encoded = encode_lane_module_transition_journal_v1(&fixture.journal).unwrap();

    // Act
    let decoded = decode_exact_lane_module_transition_journal_v1(&encoded).unwrap();

    // Assert
    assert_eq!(decoded, fixture.journal);
    assert_eq!(
        decoded.canonical_journal_hash().unwrap(),
        fixture.journal.canonical_journal_hash().unwrap()
    );
}

#[test]
fn journal_codec_rejects_zero_trailing_excess_and_mutated_version_inputs() {
    // Arrange
    let fixture = accepted_fixture(1);
    let encoded = encode_lane_module_transition_journal_v1(&fixture.journal).unwrap();
    let mut trailing = encoded.clone();
    trailing.push(0);
    let mut version = encoded;
    version[0] = 2;
    let excess = vec![0; MAX_LANE_MODULE_TRANSITION_JOURNAL_BYTES_V1 + 1];

    // Act / Assert
    assert_eq!(
        decode_exact_lane_module_transition_journal_v1(&[]),
        Err(LaneModuleTransitionJournalErrorV1::EmptyInput)
    );
    assert_eq!(
        decode_exact_lane_module_transition_journal_v1(&trailing),
        Err(LaneModuleTransitionJournalErrorV1::TrailingBytes)
    );
    assert!(decode_exact_lane_module_transition_journal_v1(&version).is_err());
    assert_eq!(
        decode_exact_lane_module_transition_journal_v1(&excess),
        Err(LaneModuleTransitionJournalErrorV1::InputTooLarge {
            actual: MAX_LANE_MODULE_TRANSITION_JOURNAL_BYTES_V1 + 1,
            maximum: MAX_LANE_MODULE_TRANSITION_JOURNAL_BYTES_V1,
        })
    );
}

#[test]
fn zero_is_not_a_rejection_code() {
    // Arrange / Act
    let result = LaneModuleRejectCodeV1::new(0);

    // Assert
    assert_eq!(
        result,
        Err(LaneModuleTransitionJournalErrorV1::ZeroRejectCode)
    );
}

#[test]
fn accepted_journal_requires_a_changing_global_state_root() {
    // Arrange
    let fixture = accepted_fixture(1);
    let LaneModuleTransitionOutcomeV1::Accepted(accepted) = fixture.journal.outcome() else {
        panic!("accepted fixture must be accepted");
    };
    let invalid = LaneModuleAcceptedTransitionV1::new(LaneModuleAcceptedTransitionInputV1 {
        global_post_state_root: fixture.state.state_root(),
        global_effect_plan_commitment: accepted.global_effect_plan_commitment(),
        lane_post_state_root: accepted.lane_post_state_root(),
        lane_effect_rows_root: accepted.lane_effect_rows_root(),
        state_transition_root: accepted.state_transition_root(),
        private_input_ports_root: accepted.private_input_ports_root(),
        private_output_ports_root: accepted.private_output_ports_root(),
        terminal_obligations_root: accepted.terminal_obligations_root(),
    });

    // Act
    let result = LaneModuleTransitionJournalV1::new(journal_input(
        &fixture.registries,
        &fixture.state,
        &fixture.occurrence,
        LaneModuleTransitionOutcomeV1::Accepted(invalid),
    ));

    // Assert
    assert_eq!(
        result,
        Err(LaneModuleTransitionJournalErrorV1::PreAndPostGlobalStateMatch)
    );
}

#[test]
fn every_accepted_public_root_changes_the_canonical_journal_hash() {
    // Arrange
    let fixture = accepted_fixture(1);
    let LaneModuleTransitionOutcomeV1::Accepted(accepted) = fixture.journal.outcome() else {
        panic!("accepted fixture must be accepted");
    };
    let mutated = LaneModuleAcceptedTransitionV1::new(LaneModuleAcceptedTransitionInputV1 {
        global_post_state_root: accepted.global_post_state_root(),
        global_effect_plan_commitment: accepted.global_effect_plan_commitment(),
        lane_post_state_root: accepted.lane_post_state_root(),
        lane_effect_rows_root: accepted.lane_effect_rows_root(),
        state_transition_root: accepted.state_transition_root(),
        private_input_ports_root: root(999),
        private_output_ports_root: accepted.private_output_ports_root(),
        terminal_obligations_root: accepted.terminal_obligations_root(),
    });
    let mutated_journal = LaneModuleTransitionJournalV1::new(journal_input(
        &fixture.registries,
        &fixture.state,
        &fixture.occurrence,
        LaneModuleTransitionOutcomeV1::Accepted(mutated),
    ))
    .unwrap();

    // Act
    let original_hash = fixture.journal.canonical_journal_hash().unwrap();
    let mutated_hash = mutated_journal.canonical_journal_hash().unwrap();

    // Assert
    assert_ne!(original_hash, mutated_hash);
}

#[test]
fn rejected_journal_codec_preserves_the_typed_code() {
    // Arrange
    let fixture = accepted_fixture(1);
    let journal = rejected_journal(&fixture);
    let encoded = encode_lane_module_transition_journal_v1(&journal).unwrap();

    // Act
    let decoded = decode_exact_lane_module_transition_journal_v1(&encoded).unwrap();

    // Assert
    assert_eq!(decoded, journal);
    assert!(matches!(
        decoded.outcome(),
        LaneModuleTransitionOutcomeV1::Rejected(code) if code.get() == 41
    ));
}
