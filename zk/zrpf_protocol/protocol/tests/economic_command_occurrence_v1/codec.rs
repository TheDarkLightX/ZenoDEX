use super::support::*;

#[test]
fn exact_codec_round_trips_and_rejects_empty_trailing_and_oversized_bytes() {
    // Arrange.
    let governed_route = route(root(20), 21);
    let route_registry = RouteReleaseRegistryV1::new(vec![governed_route.clone()]).unwrap();
    let active_profile = profile(&route_registry, 9);
    let occurrence = occurrence(&active_profile, &governed_route);
    let bytes = encode_economic_command_occurrence_v1(&occurrence).unwrap();

    // Act / Assert.
    assert_eq!(
        decode_exact_economic_command_occurrence_v1(&bytes).unwrap(),
        occurrence
    );
    assert_eq!(
        decode_exact_economic_command_occurrence_v1(&[]).unwrap_err(),
        EconomicCommandOccurrenceErrorV1::EmptyInput
    );
    let mut trailing = bytes.clone();
    trailing.push(0);
    let mut nonminimal = vec![0x81, 0x00];
    nonminimal.extend_from_slice(&bytes[1..]);
    assert_eq!(
        decode_exact_economic_command_occurrence_v1(&trailing).unwrap_err(),
        EconomicCommandOccurrenceErrorV1::TrailingBytes
    );
    assert_eq!(
        decode_exact_economic_command_occurrence_v1(&nonminimal).unwrap_err(),
        EconomicCommandOccurrenceErrorV1::NonCanonicalEncoding
    );
    let oversized = vec![0; MAX_ECONOMIC_COMMAND_OCCURRENCE_BYTES_V1 + 1];
    assert_eq!(
        decode_exact_economic_command_occurrence_v1(&oversized).unwrap_err(),
        EconomicCommandOccurrenceErrorV1::InputTooLarge {
            actual: MAX_ECONOMIC_COMMAND_OCCURRENCE_BYTES_V1 + 1,
            maximum: MAX_ECONOMIC_COMMAND_OCCURRENCE_BYTES_V1,
        }
    );
}

#[test]
fn wire_rejects_unknown_fields_and_counterfeit_occurrence_identity() {
    // Arrange.
    let governed_route = route(root(20), 21);
    let route_registry = RouteReleaseRegistryV1::new(vec![governed_route.clone()]).unwrap();
    let active_profile = profile(&route_registry, 9);
    let occurrence = occurrence(&active_profile, &governed_route);
    let canonical = serde_json::to_value(&occurrence).unwrap();

    // Act / Assert.
    for pointer in [
        "",
        "/content",
        "/content/position",
        "/content/authorized_action",
    ] {
        let mut value = canonical.clone();
        value
            .pointer_mut(pointer)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert("unknown".into(), serde_json::json!(1));
        assert!(serde_json::from_value::<EconomicCommandOccurrenceV1>(value).is_err());
    }
    let mut counterfeit = serde_json::to_value(&occurrence).unwrap();
    counterfeit["occurrence_id"] = serde_json::to_value([77u8; 32]).unwrap();
    assert!(serde_json::from_value::<EconomicCommandOccurrenceV1>(counterfeit).is_err());
}

#[derive(Serialize)]
struct RawOccurrenceV1<'a> {
    occurrence_version: u16,
    occurrence_id: [u8; 32],
    content: &'a EconomicCommandOccurrenceContentV1,
}

#[test]
fn exact_decoder_rejects_noncanonical_version_and_counterfeit_id_without_a_witness() {
    // Arrange.
    let governed_route = route(root(20), 21);
    let route_registry = RouteReleaseRegistryV1::new(vec![governed_route.clone()]).unwrap();
    let active_profile = profile(&route_registry, 9);
    let occurrence = occurrence(&active_profile, &governed_route);
    let wrong_version = postcard::to_allocvec(&RawOccurrenceV1 {
        occurrence_version: 2,
        occurrence_id: occurrence.occurrence_id().into_bytes(),
        content: occurrence.content(),
    })
    .unwrap();
    let counterfeit = postcard::to_allocvec(&RawOccurrenceV1 {
        occurrence_version: 1,
        occurrence_id: [77; 32],
        content: occurrence.content(),
    })
    .unwrap();

    // Act / Assert.
    assert_eq!(
        decode_exact_economic_command_occurrence_v1(&wrong_version).unwrap_err(),
        EconomicCommandOccurrenceErrorV1::InvalidOccurrenceVersion(2)
    );
    assert_eq!(
        decode_exact_economic_command_occurrence_v1(&counterfeit).unwrap_err(),
        EconomicCommandOccurrenceErrorV1::CounterfeitOccurrenceId
    );
}

#[test]
fn encoded_occurrence_has_a_pinned_digest_for_cross_implementation_parity() {
    // Arrange.
    let governed_route = route(root(20), 21);
    let route_registry = RouteReleaseRegistryV1::new(vec![governed_route.clone()]).unwrap();
    let active_profile = profile(&route_registry, 9);
    let occurrence = occurrence(&active_profile, &governed_route);

    // Act.
    let bytes = encode_economic_command_occurrence_v1(&occurrence).unwrap();
    let digest: [u8; 32] = Sha256::digest(bytes).into();

    // Assert.
    assert_eq!(
        digest,
        [
            132, 99, 88, 72, 15, 160, 104, 182, 184, 101, 181, 192, 171, 231, 0, 241, 34, 123, 98,
            3, 56, 101, 9, 159, 38, 146, 151, 247, 227, 109, 82, 150,
        ]
    );
}

#[test]
fn occurrence_id_type_rejects_zero_at_the_construction_boundary() {
    // Arrange / Act.
    let result = EconomicCommandOccurrenceIdV1::new([0; 32]);

    // Assert.
    assert!(result.is_err());
}
