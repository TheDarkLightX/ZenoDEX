use super::support::*;
use zenodex_zrpf_protocol_v3::MAX_LANE_STATE_OPENING_WITNESSES_V1;

#[test]
fn one_and_maximum_same_action_openings_are_accepted() {
    // Arrange
    let action_id = crate::sparse_support::action(0x55);
    let one = same_action_witnesses(1, action_id);
    let maximum = same_action_witnesses(MAX_LANE_STATE_OPENING_WITNESSES_V1, action_id);

    // Act
    let one_batch = opening_batch(one).unwrap();
    let maximum_batch = opening_batch(maximum).unwrap();

    // Assert
    assert_eq!(one_batch.witnesses().len(), 1);
    assert_eq!(
        maximum_batch.witnesses().len(),
        MAX_LANE_STATE_OPENING_WITNESSES_V1
    );
    assert_ne!(one_batch.openings_root(), maximum_batch.openings_root());
}

#[test]
fn zero_and_maximum_plus_one_openings_fail_closed() {
    // Arrange
    let action_id = crate::sparse_support::action(0x55);
    let empty = LaneStateOpeningBatchInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        economic_action_id: action_id,
        witnesses: vec![],
        lane_pre_state_root: root(1),
        lane_post_state_root: root(2),
    };
    let excess_witnesses =
        same_action_witnesses(MAX_LANE_STATE_OPENING_WITNESSES_V1 + 1, action_id);
    let excess = LaneStateOpeningBatchInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        economic_action_id: action_id,
        lane_pre_state_root: excess_witnesses[0].claimed_pre_root(),
        lane_post_state_root: excess_witnesses.last().unwrap().claimed_post_root(),
        witnesses: excess_witnesses,
    };

    // Act
    let empty_error = rejection(LaneStateOpeningBatchV1::new(empty));
    let excess_error = rejection(LaneStateOpeningBatchV1::new(excess));

    // Assert
    assert_eq!(empty_error, LaneStateTransitionErrorV1::EmptyWitnesses);
    assert_eq!(
        excess_error,
        LaneStateTransitionErrorV1::TooManyWitnesses {
            actual: MAX_LANE_STATE_OPENING_WITNESSES_V1 + 1,
            maximum: MAX_LANE_STATE_OPENING_WITNESSES_V1,
        }
    );
}

#[test]
fn every_opening_must_bind_the_same_economic_action() {
    // Arrange
    let action_id = crate::sparse_support::action(0x55);
    let mut witnesses = same_action_witnesses(2, action_id);
    witnesses[1] = witness_for_action(&witnesses[1], crate::sparse_support::action(0x56));
    let input = LaneStateOpeningBatchInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        economic_action_id: action_id,
        lane_pre_state_root: witnesses[0].claimed_pre_root(),
        lane_post_state_root: witnesses[1].claimed_post_root(),
        witnesses,
    };

    // Act
    let error = rejection(LaneStateOpeningBatchV1::new(input));

    // Assert
    assert_eq!(
        error,
        LaneStateTransitionErrorV1::EconomicActionMismatch { index: 1 }
    );
}

#[test]
fn duplicate_and_reordered_cell_keys_are_typed_rejections() {
    // Arrange
    let action_id = crate::sparse_support::action(0x55);
    let witnesses = same_action_witnesses(2, action_id);
    let canonical_pre_root = witnesses[0].claimed_pre_root();
    let canonical_post_root = witnesses[1].claimed_post_root();
    let duplicate = vec![witnesses[0].clone(), witnesses[0].clone()];
    let reordered = vec![witnesses[1].clone(), witnesses[0].clone()];
    let input_for =
        |values: Vec<SparseMerkleCellTransitionWitnessV1>| LaneStateOpeningBatchInputV1 {
            lane_id: EconomicLaneIdV1::AssetTransfer,
            economic_action_id: action_id,
            lane_pre_state_root: canonical_pre_root,
            lane_post_state_root: canonical_post_root,
            witnesses: values,
        };

    // Act
    let duplicate_error = rejection(LaneStateOpeningBatchV1::new(input_for(duplicate)));
    let reordered_error = rejection(LaneStateOpeningBatchV1::new(input_for(reordered)));

    // Assert
    assert_eq!(
        duplicate_error,
        LaneStateTransitionErrorV1::DuplicateCellKey
    );
    assert_eq!(
        reordered_error,
        LaneStateTransitionErrorV1::NonCanonicalCellKeyOrder
    );
}

#[test]
fn skipped_opening_breaks_the_authenticated_root_chain() {
    // Arrange
    let action_id = crate::sparse_support::action(0x55);
    let witnesses = same_action_witnesses(3, action_id);
    let skipped = vec![witnesses[0].clone(), witnesses[2].clone()];
    let input = LaneStateOpeningBatchInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        economic_action_id: action_id,
        lane_pre_state_root: skipped[0].claimed_pre_root(),
        lane_post_state_root: skipped[1].claimed_post_root(),
        witnesses: skipped,
    };

    // Act
    let error = rejection(LaneStateOpeningBatchV1::new(input));

    // Assert
    assert_eq!(
        error,
        LaneStateTransitionErrorV1::RootChainDiscontinuity { index: 1 }
    );
}

#[test]
fn a_changed_batch_cannot_claim_an_unchanged_lane_root() {
    // Arrange
    let action_id = crate::sparse_support::action(0x55);
    let witnesses = same_action_witnesses(1, action_id);
    let pre_root = witnesses[0].claimed_pre_root();
    let input = LaneStateOpeningBatchInputV1 {
        lane_id: EconomicLaneIdV1::AssetTransfer,
        economic_action_id: action_id,
        lane_pre_state_root: pre_root,
        lane_post_state_root: pre_root,
        witnesses,
    };

    // Act
    let error = rejection(LaneStateOpeningBatchV1::new(input));

    // Assert
    assert_eq!(error, LaneStateTransitionErrorV1::UnchangedBatchRoot);
}

#[test]
fn state_transition_codec_is_exact_bounded_and_canonical() {
    // Arrange
    let action_id = crate::sparse_support::action(0x55);
    let transition = LaneStateTransitionWitnessV1::changed(
        opening_batch(same_action_witnesses(2, action_id)).unwrap(),
    )
    .unwrap();
    let encoded = encode_lane_state_transition_witness_v1(&transition).unwrap();
    let mut trailing = encoded.clone();
    trailing.push(0);

    // Act
    let decoded = decode_exact_lane_state_transition_witness_v1(&encoded).unwrap();

    // Assert
    assert_eq!(decoded, transition);
    assert_eq!(
        decoded.canonical_commitment().unwrap(),
        transition.canonical_commitment().unwrap()
    );
    assert_eq!(
        decode_exact_lane_state_transition_witness_v1(&[]),
        Err(LaneStateTransitionErrorV1::EmptyInput)
    );
    assert_eq!(
        decode_exact_lane_state_transition_witness_v1(&trailing),
        Err(LaneStateTransitionErrorV1::TrailingBytes)
    );
}

#[test]
fn unchanged_transition_has_exact_identity_roots_and_a_distinct_commitment() {
    // Arrange
    let action_id = crate::sparse_support::action(0x55);
    let unchanged = LaneStateTransitionWitnessV1::unchanged(
        EconomicLaneIdV1::AssetTransfer,
        action_id,
        root(77),
    );
    let changed = LaneStateTransitionWitnessV1::changed(
        opening_batch(same_action_witnesses(1, action_id)).unwrap(),
    )
    .unwrap();

    // Act
    let unchanged_commitment = unchanged.canonical_commitment().unwrap();
    let changed_commitment = changed.canonical_commitment().unwrap();

    // Assert
    assert_eq!(unchanged.lane_pre_state_root(), root(77));
    assert_eq!(unchanged.lane_post_state_root(), root(77));
    assert_ne!(unchanged_commitment, changed_commitment);
}
