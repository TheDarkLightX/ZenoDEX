#[path = "support/spot_certificate_fixture.rs"]
mod fixture;
#[path = "support/spot_certificate_state_v2_fixture.rs"]
mod state_fixture;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_epoch_certificate_v1, decode_exact_value_aggregate_proposal_v5,
    encode_settlement_epoch_certificate_v1, encode_value_aggregate_proposal_v5,
};
use zenodex_zrpf_risc0_semantic_shared::{
    bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2,
    compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2,
    compose_ordinary_spot_settlement_guest_output_after_l2_verification_v2,
    decode_exact_ordinary_spot_settlement_guest_envelope_v2,
    decode_exact_ordinary_spot_settlement_guest_input_v2,
    encode_ordinary_spot_settlement_guest_input_v2, OrdinarySpotSettlementGuestInputErrorV2,
    OrdinarySpotSettlementGuestInputV2,
};
use zenodex_zrpf_risc0_shared::derive_risc0_verified_claim_binding_v1;

use fixture::{authorization, proposal, FixtureConfig};
use state_fixture::{matching_da_certificate, replay_blob, witness};

const RECORDED_L2_IMAGE_ID: [u32; 8] = [
    3_310_209_353,
    2_187_234_401,
    3_429_179_959,
    3_497_520_757,
    2_979_683_736,
    4_028_871_351,
    2_266_228_022,
    4_165_101_325,
];

#[test]
fn proposal_opaque_envelope_defers_v5_interpretation_until_receipt_binding() {
    let input = baseline_input();
    let encoded = encode_ordinary_spot_settlement_guest_input_v2(&input).unwrap();
    let envelope = decode_exact_ordinary_spot_settlement_guest_envelope_v2(&encoded).unwrap();

    assert_eq!(envelope.proposal_bytes(), input.proposal_bytes());
    let bound =
        bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2(envelope)
            .unwrap();
    assert_eq!(bound, input);
    assert_eq!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&encoded).unwrap(),
        input
    );

    let mut malformed = encoded;
    let proposal_length =
        usize::try_from(u32::from_be_bytes(malformed[2..6].try_into().unwrap())).unwrap();
    malformed[6..6 + proposal_length].fill(0);
    let opaque = decode_exact_ordinary_spot_settlement_guest_envelope_v2(&malformed).unwrap();
    assert!(matches!(
        bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2(opaque),
        Err(OrdinarySpotSettlementGuestInputErrorV2::ValueAggregate(_))
    ));
}

#[test]
fn executable_host_boundary_matches_direct_t17_composition_and_canonical_output() {
    let input = baseline_input();
    let claim_binding =
        derive_risc0_verified_claim_binding_v1(RECORDED_L2_IMAGE_ID, input.proposal_bytes())
            .unwrap();
    let output = compose_ordinary_spot_settlement_guest_output_after_l2_verification_v2(
        &input,
        claim_binding,
    )
    .unwrap();
    let proposal = decode_exact_value_aggregate_proposal_v5(input.proposal_bytes()).unwrap();
    let direct = compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2(
        &proposal,
        input.authorization(),
        input.witness().clone(),
        claim_binding,
        input.data_availability_certificate(),
    )
    .unwrap();
    let decoded = decode_exact_settlement_epoch_certificate_v1(&output).unwrap();

    assert_eq!(decoded, direct);
    assert_eq!(
        output,
        encode_settlement_epoch_certificate_v1(&direct).unwrap()
    );
    assert_eq!(
        Sha256::digest(&output).to_vec(),
        vec![
            123, 137, 185, 130, 193, 205, 107, 17, 44, 82, 39, 124, 167, 64, 89, 207, 154, 53, 231,
            121, 63, 86, 220, 177, 67, 172, 101, 227, 90, 6, 247, 211,
        ]
    );
    assert_eq!(output.len(), 803);
}

#[test]
fn verified_claim_binding_changes_with_l2_image_or_exact_proposal_bytes() {
    let input = baseline_input();
    let baseline =
        derive_risc0_verified_claim_binding_v1(RECORDED_L2_IMAGE_ID, input.proposal_bytes())
            .unwrap();
    let mut changed_image = RECORDED_L2_IMAGE_ID;
    changed_image[0] ^= 1;
    let image_substitution =
        derive_risc0_verified_claim_binding_v1(changed_image, input.proposal_bytes()).unwrap();
    let mut changed_proposal = input.proposal_bytes().to_vec();
    changed_proposal.push(0);
    let proposal_substitution =
        derive_risc0_verified_claim_binding_v1(RECORDED_L2_IMAGE_ID, &changed_proposal).unwrap();

    assert_ne!(baseline, image_substitution);
    assert_ne!(baseline, proposal_substitution);
}

fn baseline_input() -> OrdinarySpotSettlementGuestInputV2 {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let replay = replay_blob(&proposal, authorization, &witness);
    let certificate = matching_da_certificate(&proposal, &replay);
    OrdinarySpotSettlementGuestInputV2::new(
        encode_value_aggregate_proposal_v5(&proposal).unwrap(),
        authorization,
        witness,
        certificate,
    )
    .unwrap()
}
