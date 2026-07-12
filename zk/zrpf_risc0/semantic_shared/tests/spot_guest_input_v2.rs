#[path = "support/spot_certificate_fixture.rs"]
mod fixture;
#[path = "support/spot_certificate_state_v2_fixture.rs"]
mod state_fixture;
#[path = "support/spot_guest_input_v2_wire.rs"]
mod wire_fixture;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    encode_full_blob_da_certificate_v1, encode_sparse_merkle_cell_transition_witness_v1,
    encode_value_aggregate_proposal_v5, ApplicationIdV3, AuthorizationGrantIdV1,
    AuthorizationScopeIdV1, AuthorizationSubjectIdV1, DomainIdV3, EconomicActionErrorV1,
    EconomicActionIdV1, ValueHashV2, MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
    MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};
use zenodex_zrpf_risc0_semantic_shared::{
    decode_exact_ordinary_spot_settlement_guest_input_v2,
    encode_ordinary_spot_settlement_guest_input_v2, OrdinarySpotSettlementGuestInputErrorV2,
    OrdinarySpotSettlementGuestInputV2, SpotSettlementAuthorizationInputV1,
    MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
    ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V2,
};

use fixture::{authorization, authorization_with, commitment, proposal, FixtureConfig};
use state_fixture::{
    da_certificate, matching_da_certificate, replay_blob, witness, witness_with,
    DaCertificateMetadataV2, WitnessOverridesV2,
};
use wire_fixture::{independent_frame, read_length};

#[test]
fn guest_input_v2_exactly_frames_only_proof_neutral_components() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let certificate =
        matching_da_certificate(&proposal, &replay_blob(&proposal, authorization, &witness));
    let proposal_bytes = encode_value_aggregate_proposal_v5(&proposal).unwrap();
    let witness_bytes = encode_sparse_merkle_cell_transition_witness_v1(&witness).unwrap();
    let certificate_bytes = encode_full_blob_da_certificate_v1(&certificate).unwrap();
    let input = OrdinarySpotSettlementGuestInputV2::new(
        proposal_bytes.clone(),
        authorization,
        witness.clone(),
        certificate.clone(),
    )
    .unwrap();
    let encoded = encode_ordinary_spot_settlement_guest_input_v2(&input).unwrap();

    assert_eq!(input.proposal_bytes(), proposal_bytes);
    assert_eq!(input.authorization(), authorization);
    assert_eq!(input.witness(), &witness);
    assert_eq!(input.data_availability_certificate(), &certificate);
    assert_eq!(
        encoded,
        independent_frame(
            &proposal_bytes,
            authorization,
            &witness_bytes,
            &certificate_bytes,
        )
    );
    assert_eq!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&encoded).unwrap(),
        input
    );
}

#[test]
fn guest_input_v2_matches_fixed_independent_blob_preimage() {
    let input = baseline_input();
    let encoded = encode_ordinary_spot_settlement_guest_input_v2(&input).unwrap();

    assert_eq!(
        Sha256::digest(&encoded).to_vec(),
        vec![
            163, 51, 78, 152, 119, 129, 183, 106, 60, 186, 132, 144, 106, 188, 114, 189, 92, 219,
            123, 5, 73, 178, 12, 164, 255, 19, 105, 165, 225, 113, 255, 67,
        ]
    );
    assert_eq!(encoded.len(), 11_547);
    assert_eq!(MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2, 74_678);
}

#[test]
fn authorization_identifier_constructors_reject_zero_before_guest_construction() {
    for error in [
        AuthorizationSubjectIdV1::new([0; 32]).unwrap_err(),
        AuthorizationScopeIdV1::new([0; 32]).unwrap_err(),
        AuthorizationGrantIdV1::new([0; 32]).unwrap_err(),
    ] {
        assert!(matches!(error, EconomicActionErrorV1::ZeroIdentifier(_)));
    }
}

#[test]
fn guest_input_v2_rejects_each_encoded_zero_authorization_identifier() {
    let encoded = encode_ordinary_spot_settlement_guest_input_v2(&baseline_input()).unwrap();
    assert_zero_authorization_ids(&encoded);
}

#[test]
fn guest_input_v2_rejects_every_prefix_trailing_version_and_component_bound() {
    let encoded = encode_ordinary_spot_settlement_guest_input_v2(&baseline_input()).unwrap();
    for end in 0..encoded.len() {
        assert!(decode_exact_ordinary_spot_settlement_guest_input_v2(&encoded[..end]).is_err());
    }
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&trailing),
        Err(OrdinarySpotSettlementGuestInputErrorV2::TrailingBytes)
    );
    assert_guest_declared_bounds(&encoded);
    assert_eq!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&vec![
            0;
            MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2
                + 1
        ]),
        Err(OrdinarySpotSettlementGuestInputErrorV2::InputTooLarge {
            actual: MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2 + 1,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
        })
    );
}

#[test]
fn guest_input_v2_every_component_field_mutation_changes_exact_bytes() {
    let baseline_proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&baseline_proposal, authorization);
    let replay = replay_blob(&baseline_proposal, authorization, &witness);
    let certificate = matching_da_certificate(&baseline_proposal, &replay);
    let baseline = OrdinarySpotSettlementGuestInputV2::new(
        encode_value_aggregate_proposal_v5(&baseline_proposal).unwrap(),
        authorization,
        witness.clone(),
        certificate.clone(),
    )
    .unwrap();
    let baseline_bytes = encode_ordinary_spot_settlement_guest_input_v2(&baseline).unwrap();

    let changed_proposal = proposal(FixtureConfig {
        flow_amount: 18,
        ..FixtureConfig::default()
    });
    let proposals = [encode_value_aggregate_proposal_v5(&changed_proposal).unwrap()];
    for proposal_bytes in proposals {
        assert_distinct_roundtrip(
            &baseline_bytes,
            OrdinarySpotSettlementGuestInputV2::new(
                proposal_bytes,
                authorization,
                witness.clone(),
                certificate.clone(),
            )
            .unwrap(),
        );
    }

    for changed_authorization in [
        authorization_with(53, 51, 7, 52),
        authorization_with(50, 54, 7, 52),
        authorization_with(50, 51, 8, 52),
        authorization_with(50, 51, 7, 55),
    ] {
        assert_distinct_roundtrip(
            &baseline_bytes,
            OrdinarySpotSettlementGuestInputV2::new(
                baseline.proposal_bytes().to_vec(),
                changed_authorization,
                witness.clone(),
                certificate.clone(),
            )
            .unwrap(),
        );
    }

    assert_witness_field_mutations(
        &baseline,
        &baseline_bytes,
        &baseline_proposal,
        authorization,
    );
    assert_certificate_field_mutations(&baseline, &baseline_bytes, &baseline_proposal, &replay);
}

fn assert_witness_field_mutations(
    baseline: &OrdinarySpotSettlementGuestInputV2,
    baseline_bytes: &[u8],
    proposal: &zenodex_zrpf_protocol_v3::ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
) {
    let mutations = [
        WitnessOverridesV2 {
            economic_action_id: Some(EconomicActionIdV1::new([71; 32]).unwrap()),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            cell_key: Some(commitment(72)),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            pre_value_hash: Some(ValueHashV2::new([73; 32])),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            post_value_hash: Some(ValueHashV2::new([74; 32])),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            sibling_seed: 75,
            ..WitnessOverridesV2::default()
        },
    ];
    for overrides in mutations {
        let changed_witness = witness_with(proposal, authorization, overrides);
        assert_distinct_roundtrip(
            baseline_bytes,
            OrdinarySpotSettlementGuestInputV2::new(
                baseline.proposal_bytes().to_vec(),
                authorization,
                changed_witness,
                baseline.data_availability_certificate().clone(),
            )
            .unwrap(),
        );
    }
}

fn assert_certificate_field_mutations(
    baseline: &OrdinarySpotSettlementGuestInputV2,
    baseline_bytes: &[u8],
    proposal: &zenodex_zrpf_protocol_v3::ProposedValueAggregateV5,
    replay: &[u8],
) {
    assert_certificate_metadata_field_mutations(baseline, baseline_bytes, proposal, replay);
    assert_certificate_content_mutation(baseline, baseline_bytes, proposal, replay);
}

fn assert_certificate_metadata_field_mutations(
    baseline: &OrdinarySpotSettlementGuestInputV2,
    baseline_bytes: &[u8],
    proposal: &zenodex_zrpf_protocol_v3::ProposedValueAggregateV5,
    replay: &[u8],
) {
    let matching = DaCertificateMetadataV2::matching(proposal);
    let metadata = [
        DaCertificateMetadataV2 {
            application_id: ApplicationIdV3::new([81; 32]).unwrap(),
            ..matching
        },
        DaCertificateMetadataV2 {
            chain_or_domain_id: DomainIdV3::new([82; 32]).unwrap(),
            ..matching
        },
        DaCertificateMetadataV2 {
            epoch_id: matching.epoch_id + 1,
            retention_through_epoch: matching.retention_through_epoch + 1,
            ..matching
        },
        DaCertificateMetadataV2 {
            data_schema_id: commitment(83),
            ..matching
        },
        DaCertificateMetadataV2 {
            retention_through_epoch: matching.retention_through_epoch + 1,
            ..matching
        },
        DaCertificateMetadataV2 {
            storage_policy_hash: commitment(84),
            ..matching
        },
    ];
    for changed_metadata in metadata {
        let changed_certificate = da_certificate(replay, changed_metadata);
        assert_distinct_roundtrip(
            baseline_bytes,
            OrdinarySpotSettlementGuestInputV2::new(
                baseline.proposal_bytes().to_vec(),
                baseline.authorization(),
                baseline.witness().clone(),
                changed_certificate,
            )
            .unwrap(),
        );
    }
}

fn assert_certificate_content_mutation(
    baseline: &OrdinarySpotSettlementGuestInputV2,
    baseline_bytes: &[u8],
    proposal: &zenodex_zrpf_protocol_v3::ProposedValueAggregateV5,
    replay: &[u8],
) {
    let matching = DaCertificateMetadataV2::matching(proposal);
    let mut changed_blob = replay.to_vec();
    changed_blob.push(0);
    let changed_certificate = da_certificate(&changed_blob, matching);
    assert_distinct_roundtrip(
        baseline_bytes,
        OrdinarySpotSettlementGuestInputV2::new(
            baseline.proposal_bytes().to_vec(),
            baseline.authorization(),
            baseline.witness().clone(),
            changed_certificate,
        )
        .unwrap(),
    );
}

fn assert_distinct_roundtrip(baseline_bytes: &[u8], input: OrdinarySpotSettlementGuestInputV2) {
    let changed = encode_ordinary_spot_settlement_guest_input_v2(&input).unwrap();
    assert_ne!(changed, baseline_bytes);
    assert_eq!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&changed).unwrap(),
        input
    );
}

fn assert_guest_declared_bounds(encoded: &[u8]) {
    let mut stale = encoded.to_vec();
    stale[..2]
        .copy_from_slice(&(ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V2 + 1).to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&stale),
        Err(OrdinarySpotSettlementGuestInputErrorV2::InvalidVersion(3))
    );
    assert_component_bounds(encoded);
}

fn assert_component_bounds(encoded: &[u8]) {
    let mut empty_proposal = encoded.to_vec();
    empty_proposal[2..6].copy_from_slice(&0_u32.to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&empty_proposal),
        Err(OrdinarySpotSettlementGuestInputErrorV2::EmptyProposalBytes)
    );
    let mut large_proposal = encoded.to_vec();
    large_proposal[2..6].copy_from_slice(
        &u32::try_from(MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert!(matches!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&large_proposal),
        Err(OrdinarySpotSettlementGuestInputErrorV2::ProposalBytesTooLarge { .. })
    ));

    let proposal_length = read_length(encoded, 2);
    let witness_offset = 6 + proposal_length + 104;
    assert_one_component_bound(
        encoded,
        witness_offset,
        ComponentBoundExpectation {
            maximum: MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
            empty_error: OrdinarySpotSettlementGuestInputErrorV2::EmptyWitnessBytes,
            large_error: OrdinarySpotSettlementGuestInputErrorV2::WitnessBytesTooLarge {
                actual: MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1 + 1,
                maximum: MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
            },
        },
    );
    let witness_length = read_length(encoded, witness_offset);
    let certificate_offset = witness_offset + 4 + witness_length;
    assert_one_component_bound(
        encoded,
        certificate_offset,
        ComponentBoundExpectation {
            maximum: MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
            empty_error: OrdinarySpotSettlementGuestInputErrorV2::EmptyCertificateBytes,
            large_error: OrdinarySpotSettlementGuestInputErrorV2::CertificateBytesTooLarge {
                actual: MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1 + 1,
                maximum: MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
            },
        },
    );
}

struct ComponentBoundExpectation {
    maximum: usize,
    empty_error: OrdinarySpotSettlementGuestInputErrorV2,
    large_error: OrdinarySpotSettlementGuestInputErrorV2,
}

fn assert_one_component_bound(encoded: &[u8], offset: usize, expected: ComponentBoundExpectation) {
    let mut empty = encoded.to_vec();
    empty[offset..offset + 4].copy_from_slice(&0_u32.to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&empty),
        Err(expected.empty_error)
    );
    let mut large = encoded.to_vec();
    large[offset..offset + 4]
        .copy_from_slice(&u32::try_from(expected.maximum + 1).unwrap().to_be_bytes());
    assert_eq!(
        decode_exact_ordinary_spot_settlement_guest_input_v2(&large),
        Err(expected.large_error)
    );
}

fn assert_zero_authorization_ids(encoded: &[u8]) {
    let proposal_length = read_length(encoded, 2);
    let authorization_offset = 6 + proposal_length;
    for (relative, field) in [
        (0, "authorization_subject_id"),
        (32, "authorization_scope_id"),
        (72, "authorization_grant_id"),
    ] {
        let mut changed = encoded.to_vec();
        changed[authorization_offset + relative..authorization_offset + relative + 32].fill(0);
        assert_eq!(
            decode_exact_ordinary_spot_settlement_guest_input_v2(&changed),
            Err(OrdinarySpotSettlementGuestInputErrorV2::InvalidAuthorization(field))
        );
    }
}

fn baseline_input() -> OrdinarySpotSettlementGuestInputV2 {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let certificate =
        matching_da_certificate(&proposal, &replay_blob(&proposal, authorization, &witness));
    OrdinarySpotSettlementGuestInputV2::new(
        encode_value_aggregate_proposal_v5(&proposal).unwrap(),
        authorization,
        witness,
        certificate,
    )
    .unwrap()
}
