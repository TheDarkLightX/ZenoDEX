use zenodex_zrpf_risc0_spot_settlement_v7_shared::{
    decode_exact_spot_settlement_v7_guest_envelope_v1, encode_spot_settlement_v7_guest_envelope_v1,
    ProposedSpotSettlementV7EnvelopeV1, SpotSettlementV7ErrorV1,
    MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1,
};

fn proposal() -> ProposedSpotSettlementV7EnvelopeV1 {
    ProposedSpotSettlementV7EnvelopeV1::new(vec![1, 2, 3], vec![4, 5], vec![6, 7, 8, 9], vec![10])
        .unwrap()
}

#[test]
fn envelope_round_trip_is_exact_and_deterministic() {
    let proposal = proposal();
    let first = encode_spot_settlement_v7_guest_envelope_v1(&proposal).unwrap();
    let second = encode_spot_settlement_v7_guest_envelope_v1(&proposal).unwrap();
    assert_eq!(first, second);
    assert_eq!(
        decode_exact_spot_settlement_v7_guest_envelope_v1(&first).unwrap(),
        proposal
    );
}

#[test]
fn envelope_rejects_every_truncation_and_trailing_byte() {
    let bytes = encode_spot_settlement_v7_guest_envelope_v1(&proposal()).unwrap();
    for end in 0..bytes.len() {
        assert!(decode_exact_spot_settlement_v7_guest_envelope_v1(&bytes[..end]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_spot_settlement_v7_guest_envelope_v1(&trailing).unwrap_err(),
        SpotSettlementV7ErrorV1::TrailingBytes
    );
}

#[test]
fn empty_components_and_oversized_envelopes_fail_closed() {
    assert!(matches!(
        ProposedSpotSettlementV7EnvelopeV1::new(vec![], vec![1], vec![1], vec![1]),
        Err(SpotSettlementV7ErrorV1::EmptyComponent(
            "source child journal"
        ))
    ));
    let oversized = vec![0; MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1 + 1];
    assert!(matches!(
        decode_exact_spot_settlement_v7_guest_envelope_v1(&oversized),
        Err(SpotSettlementV7ErrorV1::InputTooLarge { .. })
    ));
}
