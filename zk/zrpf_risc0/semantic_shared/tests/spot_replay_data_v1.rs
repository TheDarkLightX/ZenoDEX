#[path = "support/spot_certificate_fixture.rs"]
mod fixture;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    encode_settlement_effect_plan_v2, encode_value_aggregate_proposal_v5,
    MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};
use zenodex_zrpf_risc0_semantic_shared::{
    decode_exact_ordinary_spot_settlement_replay_data_v1, derive_spot_settlement_projection_v1,
    encode_ordinary_spot_settlement_replay_data_v1,
    ordinary_spot_settlement_replay_data_schema_id_v1, OrdinarySpotSettlementReplayDataErrorV1,
    OrdinarySpotSettlementReplayDataV1, MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1,
    ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V1,
};

use fixture::{authorization, proposal, FixtureConfig};

#[test]
fn replay_data_contains_exact_canonical_proposal_and_recomposed_plan_bytes() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let projection = derive_spot_settlement_projection_v1(&proposal, authorization).unwrap();
    let expected_proposal = encode_value_aggregate_proposal_v5(&proposal).unwrap();
    let expected_plan = encode_settlement_effect_plan_v2(projection.settlement_plan()).unwrap();
    let replay = OrdinarySpotSettlementReplayDataV1::recompose(&proposal, authorization).unwrap();

    assert_eq!(replay.proposal_bytes(), expected_proposal);
    assert_eq!(replay.settlement_effect_plan_bytes(), expected_plan);
    let encoded = encode_ordinary_spot_settlement_replay_data_v1(&replay).unwrap();
    assert_eq!(
        encoded,
        independent_frame(&expected_proposal, &expected_plan)
    );
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&encoded).unwrap(),
        replay
    );
}

#[test]
fn schema_and_complete_replay_blob_match_fixed_independent_preimages() {
    let proposal = proposal(FixtureConfig::default());
    let replay = OrdinarySpotSettlementReplayDataV1::recompose(&proposal, authorization()).unwrap();
    let encoded = encode_ordinary_spot_settlement_replay_data_v1(&replay).unwrap();
    let schema = independent_schema_id();

    assert_eq!(
        ordinary_spot_settlement_replay_data_schema_id_v1()
            .unwrap()
            .into_bytes(),
        schema
    );
    assert_eq!(
        schema,
        [
            250, 130, 240, 0, 198, 86, 149, 52, 60, 187, 82, 20, 67, 188, 216, 169, 249, 129, 141,
            222, 147, 84, 45, 79, 121, 235, 185, 136, 249, 94, 29, 63,
        ]
    );
    assert_eq!(
        Sha256::digest(&encoded).to_vec(),
        vec![
            207, 198, 189, 209, 229, 77, 66, 50, 110, 7, 158, 38, 94, 198, 254, 51, 34, 25, 217,
            93, 94, 81, 51, 222, 72, 127, 162, 190, 99, 212, 39, 111,
        ]
    );
    assert_eq!(encoded.len(), 3_930);
}

#[test]
fn exact_codec_rejects_truncation_trailing_stale_and_declared_bounds() {
    let proposal = proposal(FixtureConfig::default());
    let replay = OrdinarySpotSettlementReplayDataV1::recompose(&proposal, authorization()).unwrap();
    let encoded = encode_ordinary_spot_settlement_replay_data_v1(&replay).unwrap();

    for end in 0..encoded.len() {
        assert!(decode_exact_ordinary_spot_settlement_replay_data_v1(&encoded[..end]).is_err());
    }
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&trailing),
        Err(OrdinarySpotSettlementReplayDataErrorV1::TrailingBytes)
    );
    assert_reject_precedence(&encoded);
    assert!(matches!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&vec![
            0;
            MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1
                + 1
        ]),
        Err(OrdinarySpotSettlementReplayDataErrorV1::InputTooLarge { .. })
    ));
}

fn assert_reject_precedence(encoded: &[u8]) {
    let mut stale_with_trailing = encoded.to_vec();
    stale_with_trailing[..2]
        .copy_from_slice(&(ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V1 + 1).to_be_bytes());
    stale_with_trailing.push(0);
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&stale_with_trailing),
        Err(OrdinarySpotSettlementReplayDataErrorV1::InvalidVersion(2))
    );

    let mut empty_proposal = encoded.to_vec();
    empty_proposal[2..6].copy_from_slice(&0_u32.to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&empty_proposal),
        Err(OrdinarySpotSettlementReplayDataErrorV1::EmptyProposalBytes)
    );

    let mut large_proposal = encoded.to_vec();
    large_proposal[2..6].copy_from_slice(
        &u32::try_from(MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert!(matches!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&large_proposal),
        Err(OrdinarySpotSettlementReplayDataErrorV1::ProposalBytesTooLarge { .. })
    ));

    let proposal_length =
        usize::try_from(u32::from_be_bytes(encoded[2..6].try_into().unwrap())).unwrap();
    let plan_length_offset = 6 + proposal_length;
    let mut empty_plan = encoded.to_vec();
    empty_plan[plan_length_offset..plan_length_offset + 4].copy_from_slice(&0_u32.to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&empty_plan),
        Err(OrdinarySpotSettlementReplayDataErrorV1::EmptyPlanBytes)
    );

    let mut large_plan = encoded.to_vec();
    large_plan[plan_length_offset..plan_length_offset + 4].copy_from_slice(
        &u32::try_from(MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert!(matches!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&large_plan),
        Err(OrdinarySpotSettlementReplayDataErrorV1::PlanBytesTooLarge { .. })
    ));

    assert_combined_bound(encoded, proposal_length, plan_length_offset);
}

fn assert_combined_bound(encoded: &[u8], proposal_length: usize, plan_length_offset: usize) {
    let mut combined_oversize = encoded[..plan_length_offset + 4].to_vec();
    combined_oversize[plan_length_offset..plan_length_offset + 4].copy_from_slice(
        &u32::try_from(MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2)
            .unwrap()
            .to_be_bytes(),
    );
    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&combined_oversize),
        Err(OrdinarySpotSettlementReplayDataErrorV1::InputTooLarge {
            actual: 10 + proposal_length + MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1,
        })
    );
}

#[test]
fn canonical_plan_from_a_different_proposal_rejects_after_inner_decode() {
    let first = proposal(FixtureConfig::default());
    let changed = FixtureConfig {
        flow_amount: 18,
        ..FixtureConfig::default()
    };
    let second = proposal(changed);
    let second_projection = derive_spot_settlement_projection_v1(&second, authorization()).unwrap();
    let mismatched = independent_frame(
        &encode_value_aggregate_proposal_v5(&first).unwrap(),
        &encode_settlement_effect_plan_v2(second_projection.settlement_plan()).unwrap(),
    );

    assert_eq!(
        decode_exact_ordinary_spot_settlement_replay_data_v1(&mismatched),
        Err(OrdinarySpotSettlementReplayDataErrorV1::RecomposedPlanMismatch)
    );
}

fn independent_frame(proposal_bytes: &[u8], plan_bytes: &[u8]) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V1.to_be_bytes());
    bytes.extend_from_slice(&u32::try_from(proposal_bytes.len()).unwrap().to_be_bytes());
    bytes.extend_from_slice(proposal_bytes);
    bytes.extend_from_slice(&u32::try_from(plan_bytes.len()).unwrap().to_be_bytes());
    bytes.extend_from_slice(plan_bytes);
    bytes
}

fn independent_schema_id() -> [u8; 32] {
    let domain = b"zenodex.zrpf.ordinary_spot_settlement_replay_data.schema.v1";
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher.finalize().into()
}
