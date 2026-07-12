#[path = "support/spot_certificate_fixture.rs"]
mod fixture;
#[path = "support/spot_certificate_state_v2_fixture.rs"]
mod state_fixture;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    encode_settlement_effect_plan_v2, encode_sparse_merkle_cell_transition_witness_v1,
    encode_value_aggregate_proposal_v5, EconomicActionIdV1, ValueHashV2,
    MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2, MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
    MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};
use zenodex_zrpf_risc0_semantic_shared::{
    decode_exact_ordinary_spot_settlement_replay_data_v2,
    derive_spot_settlement_state_projection_v2, encode_ordinary_spot_settlement_replay_data_v2,
    ordinary_spot_settlement_replay_data_schema_id_v2, OrdinarySpotSettlementReplayDataErrorV2,
    OrdinarySpotSettlementReplayDataV2, SpotSettlementAuthorizationInputV1,
    MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2,
    ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V2,
};

use fixture::{authorization, authorization_with, commitment, proposal, FixtureConfig};
use state_fixture::{witness, witness_with, WitnessOverridesV2};

#[test]
fn replay_v2_exactly_frames_every_replay_sufficient_component() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let projection =
        derive_spot_settlement_state_projection_v2(&proposal, authorization, witness.clone())
            .unwrap();
    let replay =
        OrdinarySpotSettlementReplayDataV2::recompose(&proposal, authorization, &witness).unwrap();
    let proposal_bytes = encode_value_aggregate_proposal_v5(&proposal).unwrap();
    let witness_bytes = encode_sparse_merkle_cell_transition_witness_v1(&witness).unwrap();
    let plan_bytes = encode_settlement_effect_plan_v2(projection.settlement_plan()).unwrap();
    let encoded = encode_ordinary_spot_settlement_replay_data_v2(&replay).unwrap();

    assert_eq!(replay.proposal_bytes(), proposal_bytes);
    assert_eq!(replay.authorization(), authorization);
    assert_eq!(replay.witness(), &witness);
    assert_eq!(replay.settlement_effect_plan_bytes(), plan_bytes);
    assert_eq!(
        encoded,
        independent_frame(&proposal_bytes, authorization, &witness_bytes, &plan_bytes)
    );
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&encoded).unwrap(),
        replay
    );
    assert_eq!(
        projection
            .settlement_plan()
            .economic_action_batch()
            .pre_state_root(),
        witness.claimed_pre_root()
    );
    assert_eq!(
        projection.settlement_plan().post_state_root(),
        witness.claimed_post_root()
    );
}

#[test]
fn replay_v2_schema_and_complete_blob_match_fixed_independent_preimages() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let replay =
        OrdinarySpotSettlementReplayDataV2::recompose(&proposal, authorization, &witness).unwrap();
    let encoded = encode_ordinary_spot_settlement_replay_data_v2(&replay).unwrap();
    let schema = independent_schema_id();

    assert_eq!(
        ordinary_spot_settlement_replay_data_schema_id_v2()
            .unwrap()
            .into_bytes(),
        schema
    );
    assert_eq!(
        schema,
        [
            143, 5, 160, 135, 141, 59, 233, 194, 2, 81, 49, 213, 207, 138, 52, 123, 120, 233, 205,
            153, 229, 50, 112, 184, 192, 55, 190, 85, 202, 231, 60, 252,
        ]
    );
    assert_eq!(
        Sha256::digest(&encoded).to_vec(),
        vec![
            246, 9, 248, 203, 23, 7, 79, 147, 92, 7, 41, 78, 0, 84, 113, 220, 118, 8, 65, 143, 169,
            166, 46, 159, 152, 184, 232, 102, 64, 17, 71, 42,
        ]
    );
    assert_eq!(encoded.len(), 12_423);
}

#[test]
fn replay_v2_rejects_truncation_trailing_versions_and_all_length_boundaries() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let replay =
        OrdinarySpotSettlementReplayDataV2::recompose(&proposal, authorization, &witness).unwrap();
    let encoded = encode_ordinary_spot_settlement_replay_data_v2(&replay).unwrap();

    for end in 0..encoded.len() {
        assert!(decode_exact_ordinary_spot_settlement_replay_data_v2(&encoded[..end]).is_err());
    }
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&trailing),
        Err(OrdinarySpotSettlementReplayDataErrorV2::TrailingBytes)
    );
    assert_declared_length_rejects(&encoded);
    assert!(matches!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&vec![
            0;
            MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2
                + 1
        ]),
        Err(OrdinarySpotSettlementReplayDataErrorV2::InputTooLarge { .. })
    ));
}

#[test]
fn replay_v2_rederivation_rejects_proposal_and_every_authorization_substitution() {
    let baseline_proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&baseline_proposal, authorization);
    let projection = derive_spot_settlement_state_projection_v2(
        &baseline_proposal,
        authorization,
        witness.clone(),
    )
    .unwrap();
    let proposal_bytes = encode_value_aggregate_proposal_v5(&baseline_proposal).unwrap();
    let witness_bytes = encode_sparse_merkle_cell_transition_witness_v1(&witness).unwrap();
    let plan_bytes = encode_settlement_effect_plan_v2(projection.settlement_plan()).unwrap();

    let changed_proposal = proposal(FixtureConfig {
        flow_amount: 18,
        ..FixtureConfig::default()
    });
    assert!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&independent_frame(
            &encode_value_aggregate_proposal_v5(&changed_proposal).unwrap(),
            authorization,
            &witness_bytes,
            &plan_bytes,
        ))
        .is_err()
    );
    for changed_authorization in [
        authorization_with(53, 51, 7, 52),
        authorization_with(50, 54, 7, 52),
        authorization_with(50, 51, 8, 52),
        authorization_with(50, 51, 7, 55),
    ] {
        assert!(
            decode_exact_ordinary_spot_settlement_replay_data_v2(&independent_frame(
                &proposal_bytes,
                changed_authorization,
                &witness_bytes,
                &plan_bytes,
            ))
            .is_err()
        );
    }
}

#[test]
fn replay_v2_rederivation_rejects_every_sparse_witness_field_substitution() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let baseline_witness = witness(&proposal, authorization);
    let projection = derive_spot_settlement_state_projection_v2(
        &proposal,
        authorization,
        baseline_witness.clone(),
    )
    .unwrap();
    let proposal_bytes = encode_value_aggregate_proposal_v5(&proposal).unwrap();
    let plan_bytes = encode_settlement_effect_plan_v2(projection.settlement_plan()).unwrap();
    let mutations = [
        WitnessOverridesV2 {
            economic_action_id: Some(EconomicActionIdV1::new([91; 32]).unwrap()),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            cell_key: Some(commitment(92)),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            pre_value_hash: Some(ValueHashV2::new([93; 32])),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            post_value_hash: Some(ValueHashV2::new([94; 32])),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            sibling_seed: 95,
            ..WitnessOverridesV2::default()
        },
    ];
    for overrides in mutations {
        let changed_witness = witness_with(&proposal, authorization, overrides);
        let changed_witness_bytes =
            encode_sparse_merkle_cell_transition_witness_v1(&changed_witness).unwrap();
        assert!(
            decode_exact_ordinary_spot_settlement_replay_data_v2(&independent_frame(
                &proposal_bytes,
                authorization,
                &changed_witness_bytes,
                &plan_bytes,
            ))
            .is_err()
        );
    }
}

#[test]
fn replay_v2_rederivation_rejects_valid_plan_substitution() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let baseline_witness = witness(&proposal, authorization);
    let changed_witness = witness_with(
        &proposal,
        authorization,
        WitnessOverridesV2 {
            sibling_seed: 91,
            ..WitnessOverridesV2::default()
        },
    );
    let changed_projection =
        derive_spot_settlement_state_projection_v2(&proposal, authorization, changed_witness)
            .unwrap();
    let substituted = independent_frame(
        &encode_value_aggregate_proposal_v5(&proposal).unwrap(),
        authorization,
        &encode_sparse_merkle_cell_transition_witness_v1(&baseline_witness).unwrap(),
        &encode_settlement_effect_plan_v2(changed_projection.settlement_plan()).unwrap(),
    );
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&substituted),
        Err(OrdinarySpotSettlementReplayDataErrorV2::RecomposedPlanMismatch)
    );
}

fn assert_declared_length_rejects(encoded: &[u8]) {
    let mut stale = encoded.to_vec();
    stale[..2]
        .copy_from_slice(&(ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V2 + 1).to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&stale),
        Err(OrdinarySpotSettlementReplayDataErrorV2::InvalidVersion(3))
    );

    let mut empty_proposal = encoded.to_vec();
    empty_proposal[2..6].copy_from_slice(&0_u32.to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&empty_proposal),
        Err(OrdinarySpotSettlementReplayDataErrorV2::EmptyProposalBytes)
    );
    let mut large_proposal = encoded.to_vec();
    large_proposal[2..6].copy_from_slice(
        &u32::try_from(MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert!(matches!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&large_proposal),
        Err(OrdinarySpotSettlementReplayDataErrorV2::ProposalBytesTooLarge { .. })
    ));

    let proposal_length =
        usize::try_from(u32::from_be_bytes(encoded[2..6].try_into().unwrap())).unwrap();
    let witness_length_offset = 6 + proposal_length + 104;
    let witness_length = usize::try_from(u32::from_be_bytes(
        encoded[witness_length_offset..witness_length_offset + 4]
            .try_into()
            .unwrap(),
    ))
    .unwrap();
    assert_component_length_rejects(encoded, witness_length_offset, witness_length);
}

fn assert_component_length_rejects(
    encoded: &[u8],
    witness_length_offset: usize,
    witness_length: usize,
) {
    let mut empty_witness = encoded.to_vec();
    empty_witness[witness_length_offset..witness_length_offset + 4]
        .copy_from_slice(&0_u32.to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&empty_witness),
        Err(OrdinarySpotSettlementReplayDataErrorV2::EmptyWitnessBytes)
    );
    let mut large_witness = encoded.to_vec();
    large_witness[witness_length_offset..witness_length_offset + 4].copy_from_slice(
        &u32::try_from(MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert!(matches!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&large_witness),
        Err(OrdinarySpotSettlementReplayDataErrorV2::WitnessBytesTooLarge { .. })
    ));

    let plan_length_offset = witness_length_offset + 4 + witness_length;
    let mut empty_plan = encoded.to_vec();
    empty_plan[plan_length_offset..plan_length_offset + 4].copy_from_slice(&0_u32.to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&empty_plan),
        Err(OrdinarySpotSettlementReplayDataErrorV2::EmptyPlanBytes)
    );
    let mut large_plan = encoded.to_vec();
    large_plan[plan_length_offset..plan_length_offset + 4].copy_from_slice(
        &u32::try_from(MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert!(matches!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(&large_plan),
        Err(OrdinarySpotSettlementReplayDataErrorV2::PlanBytesTooLarge { .. })
    ));

    assert_combined_length_rejects(
        encoded,
        witness_length_offset,
        witness_length,
        plan_length_offset,
    );
}

fn assert_combined_length_rejects(
    encoded: &[u8],
    witness_length_offset: usize,
    witness_length: usize,
    plan_length_offset: usize,
) {
    let proposal_length = witness_length_offset - 6 - 104;
    let oversized_total =
        118 + proposal_length + witness_length + MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2;
    let mut legal_components_with_oversized_total = encoded.to_vec();
    legal_components_with_oversized_total[plan_length_offset..plan_length_offset + 4]
        .copy_from_slice(
            &u32::try_from(MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2)
                .unwrap()
                .to_be_bytes(),
        );
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v2(
            &legal_components_with_oversized_total
        ),
        Err(OrdinarySpotSettlementReplayDataErrorV2::InputTooLarge {
            actual: oversized_total,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2,
        })
    );
}

fn independent_frame(
    proposal_bytes: &[u8],
    authorization: SpotSettlementAuthorizationInputV1,
    witness_bytes: &[u8],
    plan_bytes: &[u8],
) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V2.to_be_bytes());
    bytes.extend_from_slice(&u32::try_from(proposal_bytes.len()).unwrap().to_be_bytes());
    bytes.extend_from_slice(proposal_bytes);
    bytes.extend_from_slice(authorization.authorization_subject_id.as_bytes());
    bytes.extend_from_slice(authorization.authorization_scope_id.as_bytes());
    bytes.extend_from_slice(&authorization.authorization_nonce.to_be_bytes());
    bytes.extend_from_slice(authorization.authorization_grant_id.as_bytes());
    bytes.extend_from_slice(&u32::try_from(witness_bytes.len()).unwrap().to_be_bytes());
    bytes.extend_from_slice(witness_bytes);
    bytes.extend_from_slice(&u32::try_from(plan_bytes.len()).unwrap().to_be_bytes());
    bytes.extend_from_slice(plan_bytes);
    bytes
}

fn independent_schema_id() -> [u8; 32] {
    let domain = b"zenodex.zrpf.ordinary_spot_settlement_replay_data.schema.v2";
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher.finalize().into()
}
