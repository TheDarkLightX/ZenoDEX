use super::support::*;
use serde::Serialize;

#[test]
fn state_exact_codec_round_trips_and_rejects_boundary_malformations() {
    // Arrange.
    let state =
        GlobalEconomicStateV1::new(state_content_with_lanes(lane_state_roots(100)).unwrap())
            .unwrap();
    let bytes = encode_global_economic_state_v1(&state).unwrap();
    let mut trailing = bytes.clone();
    trailing.push(0);
    let mut nonminimal = vec![0x81, 0x00];
    nonminimal.extend_from_slice(&bytes[1..]);

    // Act / Assert.
    assert_eq!(
        decode_exact_global_economic_state_v1(&bytes).unwrap(),
        state
    );
    assert_eq!(
        decode_exact_global_economic_state_v1(&[]).unwrap_err(),
        GlobalEconomicStateErrorV1::EmptyInput
    );
    assert_eq!(
        decode_exact_global_economic_state_v1(&[0]).unwrap_err(),
        GlobalEconomicStateErrorV1::PostcardDecode
    );
    assert_eq!(
        decode_exact_global_economic_state_v1(&trailing).unwrap_err(),
        GlobalEconomicStateErrorV1::TrailingBytes
    );
    assert_eq!(
        decode_exact_global_economic_state_v1(&nonminimal).unwrap_err(),
        GlobalEconomicStateErrorV1::NonCanonicalEncoding
    );
    let oversized = vec![0; MAX_GLOBAL_ECONOMIC_STATE_BYTES_V1 + 1];
    assert_eq!(
        decode_exact_global_economic_state_v1(&oversized).unwrap_err(),
        GlobalEconomicStateErrorV1::InputTooLarge {
            actual: MAX_GLOBAL_ECONOMIC_STATE_BYTES_V1 + 1,
            maximum: MAX_GLOBAL_ECONOMIC_STATE_BYTES_V1,
        }
    );
}

#[derive(Serialize)]
struct RawStateV1<'a> {
    state_version: u16,
    state_root: [u8; 32],
    content: &'a GlobalEconomicStateContentV1,
}

#[derive(Serialize)]
struct RawStateContentV1<'a> {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    height: u64,
    writer_epoch: u64,
    profile_id: zenodex_zrpf_protocol_v3::EconomicProfileIdV1,
    lane_state_roots: &'a [GlobalEconomicLaneStateRootV1],
    partition_roots: GlobalEconomicPartitionRootsV1,
}

#[derive(Serialize)]
struct RawStateWithRawContentV1<'a> {
    state_version: u16,
    state_root: [u8; 32],
    content: RawStateContentV1<'a>,
}

#[derive(Serialize)]
struct RawPinV1 {
    pin_version: u16,
    object_id: CommitmentV3,
    lane_id: EconomicLaneIdV1,
    creating_release_id: LaneModuleReleaseIdV1,
}

#[derive(Serialize)]
struct RawPinProofV1<'a> {
    pin: RawPinV1,
    sibling_commitments: &'a SparseMerkleSiblingPathV1,
}

#[test]
fn state_decoder_rejects_wrong_version_counterfeit_root_and_unknown_fields() {
    // Arrange.
    let state =
        GlobalEconomicStateV1::new(state_content_with_lanes(lane_state_roots(100)).unwrap())
            .unwrap();
    let wrong_version = postcard::to_allocvec(&RawStateV1 {
        state_version: 2,
        state_root: state.state_root().into_bytes(),
        content: state.content(),
    })
    .unwrap();
    let counterfeit = postcard::to_allocvec(&RawStateV1 {
        state_version: GLOBAL_ECONOMIC_STATE_VERSION_V1,
        state_root: [77; 32],
        content: state.content(),
    })
    .unwrap();
    let mut excess_lanes = state.content().lane_state_roots().to_vec();
    excess_lanes.push(GlobalEconomicLaneStateRootV1::new(
        EconomicLaneIdV1::GovernanceMigration,
        root(999),
    ));
    let excessive_lane_count = postcard::to_allocvec(&RawStateWithRawContentV1 {
        state_version: GLOBAL_ECONOMIC_STATE_VERSION_V1,
        state_root: state.state_root().into_bytes(),
        content: RawStateContentV1 {
            application_id: state.content().application_id(),
            chain_or_domain_id: state.content().chain_or_domain_id(),
            height: state.content().height(),
            writer_epoch: state.content().writer_epoch(),
            profile_id: state.content().profile_id(),
            lane_state_roots: &excess_lanes,
            partition_roots: state.content().partition_roots(),
        },
    })
    .unwrap();
    let mut unknown = serde_json::to_value(&state).unwrap();
    unknown
        .as_object_mut()
        .unwrap()
        .insert("unknown".into(), serde_json::json!(1));
    let mut unknown_content = serde_json::to_value(&state).unwrap();
    unknown_content["content"]
        .as_object_mut()
        .unwrap()
        .insert("unknown".into(), serde_json::json!(1));
    let mut unknown_partition = serde_json::to_value(&state).unwrap();
    unknown_partition["content"]["partition_roots"]
        .as_object_mut()
        .unwrap()
        .insert("unknown".into(), serde_json::json!(1));
    let mut unknown_lane_root = serde_json::to_value(&state).unwrap();
    unknown_lane_root["content"]["lane_state_roots"][0]
        .as_object_mut()
        .unwrap()
        .insert("unknown".into(), serde_json::json!(1));

    // Act / Assert.
    assert_eq!(
        decode_exact_global_economic_state_v1(&wrong_version).unwrap_err(),
        GlobalEconomicStateErrorV1::InvalidStateVersion(2)
    );
    assert_eq!(
        decode_exact_global_economic_state_v1(&counterfeit).unwrap_err(),
        GlobalEconomicStateErrorV1::CounterfeitStateRoot
    );
    assert_eq!(
        decode_exact_global_economic_state_v1(&excessive_lane_count).unwrap_err(),
        GlobalEconomicStateErrorV1::PostcardDecode
    );
    assert!(serde_json::from_value::<GlobalEconomicStateV1>(unknown).is_err());
    assert!(serde_json::from_value::<GlobalEconomicStateV1>(unknown_content).is_err());
    assert!(serde_json::from_value::<GlobalEconomicStateV1>(unknown_partition).is_err());
    assert!(serde_json::from_value::<GlobalEconomicStateV1>(unknown_lane_root).is_err());
}

#[test]
fn pin_proof_codec_is_exact_bounded_and_rejects_unknown_fields() {
    // Arrange.
    let proof = object_pin_proof(
        root(800),
        EconomicLaneIdV1::AssetTransfer,
        lane_release_id(801),
        700,
    );
    let bytes = encode_economic_object_release_pin_proof_v1(&proof).unwrap();
    let mut trailing = bytes.clone();
    trailing.push(0);
    let mut nonminimal = vec![0x81, 0x00];
    nonminimal.extend_from_slice(&bytes[1..]);
    let stale_version = postcard::to_allocvec(&RawPinProofV1 {
        pin: RawPinV1 {
            pin_version: 2,
            object_id: proof.pin().object_id(),
            lane_id: proof.pin().lane_id(),
            creating_release_id: proof.pin().creating_release_id(),
        },
        sibling_commitments: proof.sibling_commitments(),
    })
    .unwrap();
    let oversized = vec![0; MAX_ECONOMIC_OBJECT_RELEASE_PIN_PROOF_BYTES_V1 + 1];
    let mut unknown = serde_json::to_value(&proof).unwrap();
    unknown
        .as_object_mut()
        .unwrap()
        .insert("unknown".into(), serde_json::json!(1));
    let mut unknown_pin = serde_json::to_value(&proof).unwrap();
    unknown_pin["pin"]
        .as_object_mut()
        .unwrap()
        .insert("unknown".into(), serde_json::json!(1));

    // Act / Assert.
    assert_eq!(
        decode_exact_economic_object_release_pin_proof_v1(&bytes).unwrap(),
        proof
    );
    assert_eq!(
        decode_exact_economic_object_release_pin_proof_v1(&[]).unwrap_err(),
        GlobalEconomicStateErrorV1::EmptyInput
    );
    assert_eq!(
        decode_exact_economic_object_release_pin_proof_v1(&[0]).unwrap_err(),
        GlobalEconomicStateErrorV1::PostcardDecode
    );
    assert_eq!(
        decode_exact_economic_object_release_pin_proof_v1(&trailing).unwrap_err(),
        GlobalEconomicStateErrorV1::TrailingBytes
    );
    assert_eq!(
        decode_exact_economic_object_release_pin_proof_v1(&nonminimal).unwrap_err(),
        GlobalEconomicStateErrorV1::NonCanonicalEncoding
    );
    assert_eq!(
        decode_exact_economic_object_release_pin_proof_v1(&stale_version).unwrap_err(),
        GlobalEconomicStateErrorV1::InvalidObjectReleasePinVersion(2)
    );
    assert_eq!(
        decode_exact_economic_object_release_pin_proof_v1(&oversized).unwrap_err(),
        GlobalEconomicStateErrorV1::InputTooLarge {
            actual: MAX_ECONOMIC_OBJECT_RELEASE_PIN_PROOF_BYTES_V1 + 1,
            maximum: MAX_ECONOMIC_OBJECT_RELEASE_PIN_PROOF_BYTES_V1,
        }
    );
    assert!(serde_json::from_value::<EconomicObjectReleasePinProofV1>(unknown).is_err());
    assert!(serde_json::from_value::<EconomicObjectReleasePinProofV1>(unknown_pin).is_err());
}

#[test]
fn state_and_pin_proof_have_fixed_cross_implementation_digests() {
    // Arrange.
    let state =
        GlobalEconomicStateV1::new(state_content_with_lanes(lane_state_roots(100)).unwrap())
            .unwrap();
    let proof = object_pin_proof(
        root(800),
        EconomicLaneIdV1::AssetTransfer,
        lane_release_id(801),
        700,
    );

    // Act.
    let state_digest: [u8; 32] =
        Sha256::digest(encode_global_economic_state_v1(&state).unwrap()).into();
    let proof_digest: [u8; 32] =
        Sha256::digest(encode_economic_object_release_pin_proof_v1(&proof).unwrap()).into();

    // Assert. Filled from the independent canonical encodings after the red test.
    assert_eq!(
        state_digest,
        [
            218, 29, 65, 55, 233, 23, 237, 233, 176, 180, 208, 102, 98, 166, 9, 8, 68, 26, 150, 96,
            64, 49, 55, 34, 153, 108, 241, 178, 235, 246, 160, 97,
        ]
    );
    assert_eq!(
        proof_digest,
        [
            56, 229, 52, 59, 15, 68, 194, 231, 128, 105, 218, 65, 72, 126, 113, 37, 64, 143, 104,
            1, 82, 98, 195, 110, 131, 99, 210, 156, 190, 155, 182, 94,
        ]
    );
}
