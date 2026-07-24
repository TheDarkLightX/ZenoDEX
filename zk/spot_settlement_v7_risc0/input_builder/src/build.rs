use zenodex_zrpf_protocol_v3::{
    decode_exact_full_blob_da_certificate_v1, decode_exact_settlement_admission_journal_v1,
    encode_full_blob_da_certificate_v1, encode_settlement_admission_journal_v1,
};
use zenodex_zrpf_risc0_spot_settlement_v6_shared::{
    decode_exact_source_opened_spot_settlement_replay_v3,
    encode_source_opened_spot_settlement_replay_v3,
};
use zenodex_zrpf_risc0_spot_settlement_v7_shared::{
    decode_exact_spot_settlement_v7_guest_envelope_v1, encode_spot_settlement_v7_guest_envelope_v1,
    ProposedSpotSettlementV7EnvelopeV1,
};
use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::{
    decode_exact_bounded_spot_state_root_v7_host_input_v1,
    encode_bounded_spot_state_root_v7_host_input_v1,
};

use crate::SpotSettlementV7InputBuilderErrorV1;

pub fn build_canonical_spot_settlement_v7_guest_input_v1(
    source_child_journal_bytes: &[u8],
    data_availability_certificate_bytes: &[u8],
    replay_bytes: &[u8],
    state_root_host_input_bytes: &[u8],
) -> Result<Vec<u8>, SpotSettlementV7InputBuilderErrorV1> {
    require_canonical_source_journal(source_child_journal_bytes)?;
    require_canonical_da_certificate(data_availability_certificate_bytes)?;
    require_canonical_replay(replay_bytes)?;
    require_canonical_state_root_host_input(state_root_host_input_bytes)?;

    let envelope = ProposedSpotSettlementV7EnvelopeV1::new(
        source_child_journal_bytes.to_vec(),
        data_availability_certificate_bytes.to_vec(),
        replay_bytes.to_vec(),
        state_root_host_input_bytes.to_vec(),
    )
    .map_err(|_| SpotSettlementV7InputBuilderErrorV1::EnvelopeConstruction)?;
    let encoded = encode_spot_settlement_v7_guest_envelope_v1(&envelope)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::EnvelopeEncoding)?;
    let decoded = decode_exact_spot_settlement_v7_guest_envelope_v1(&encoded)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::EnvelopeRoundTrip)?;
    let reencoded = encode_spot_settlement_v7_guest_envelope_v1(&decoded)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::EnvelopeRoundTrip)?;
    if reencoded != encoded {
        return Err(SpotSettlementV7InputBuilderErrorV1::EnvelopeRoundTrip);
    }
    Ok(encoded)
}

fn require_canonical_source_journal(
    bytes: &[u8],
) -> Result<(), SpotSettlementV7InputBuilderErrorV1> {
    let value = decode_exact_settlement_admission_journal_v1(bytes).map_err(|_| {
        SpotSettlementV7InputBuilderErrorV1::ComponentDecode("source child journal")
    })?;
    let canonical = encode_settlement_admission_journal_v1(&value).map_err(|_| {
        SpotSettlementV7InputBuilderErrorV1::ComponentEncode("source child journal")
    })?;
    require_exact_component("source child journal", bytes, &canonical)
}

fn require_canonical_da_certificate(
    bytes: &[u8],
) -> Result<(), SpotSettlementV7InputBuilderErrorV1> {
    let value = decode_exact_full_blob_da_certificate_v1(bytes).map_err(|_| {
        SpotSettlementV7InputBuilderErrorV1::ComponentDecode("data availability certificate")
    })?;
    let canonical = encode_full_blob_da_certificate_v1(&value).map_err(|_| {
        SpotSettlementV7InputBuilderErrorV1::ComponentEncode("data availability certificate")
    })?;
    require_exact_component("data availability certificate", bytes, &canonical)
}

fn require_canonical_replay(bytes: &[u8]) -> Result<(), SpotSettlementV7InputBuilderErrorV1> {
    let value = decode_exact_source_opened_spot_settlement_replay_v3(bytes)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::ComponentDecode("source replay"))?;
    let canonical = encode_source_opened_spot_settlement_replay_v3(value.base(), value.source())
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::ComponentEncode("source replay"))?;
    require_exact_component("source replay", bytes, &canonical)
}

fn require_canonical_state_root_host_input(
    bytes: &[u8],
) -> Result<(), SpotSettlementV7InputBuilderErrorV1> {
    let value = decode_exact_bounded_spot_state_root_v7_host_input_v1(bytes).map_err(|_| {
        SpotSettlementV7InputBuilderErrorV1::ComponentDecode("state-root host input")
    })?;
    let canonical = encode_bounded_spot_state_root_v7_host_input_v1(&value).map_err(|_| {
        SpotSettlementV7InputBuilderErrorV1::ComponentEncode("state-root host input")
    })?;
    require_exact_component("state-root host input", bytes, &canonical)
}

fn require_exact_component(
    component: &'static str,
    proposed: &[u8],
    canonical: &[u8],
) -> Result<(), SpotSettlementV7InputBuilderErrorV1> {
    if proposed != canonical {
        return Err(SpotSettlementV7InputBuilderErrorV1::ComponentNonCanonical(
            component,
        ));
    }
    Ok(())
}
