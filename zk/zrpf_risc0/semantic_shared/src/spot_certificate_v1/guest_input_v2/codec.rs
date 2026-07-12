use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    decode_exact_full_blob_da_certificate_v1,
    decode_exact_sparse_merkle_cell_transition_witness_v1, encode_full_blob_da_certificate_v1,
    encode_sparse_merkle_cell_transition_witness_v1, MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
    MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};

use super::{
    OrdinarySpotSettlementGuestEnvelopeV2, OrdinarySpotSettlementGuestInputErrorV2,
    OrdinarySpotSettlementGuestInputV2, ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V2,
};
use crate::spot_certificate_v1::wire_v2::{
    read_authorization_v2, write_authorization_v2, ExactCursorV2, AUTHORIZATION_BYTES_V2,
};

const FIXED_HEADER_BYTES_V2: usize = 2 + 4 + AUTHORIZATION_BYTES_V2 + 4 + 4;

pub const MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2: usize = FIXED_HEADER_BYTES_V2
    + MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5
    + MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1
    + MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1;

const _: () = assert!(MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2 == 74_678);

pub fn encode_ordinary_spot_settlement_guest_input_v2(
    input: &OrdinarySpotSettlementGuestInputV2,
) -> Result<Vec<u8>, OrdinarySpotSettlementGuestInputErrorV2> {
    input.validate_self_consistency()?;
    encode_parts(
        input.proposal_bytes(),
        input.authorization(),
        input.witness(),
        input.data_availability_certificate(),
    )
}

pub fn decode_exact_ordinary_spot_settlement_guest_envelope_v2(
    bytes: &[u8],
) -> Result<OrdinarySpotSettlementGuestEnvelopeV2, OrdinarySpotSettlementGuestInputErrorV2> {
    let envelope = decode_envelope_parts(bytes)?;
    if encode_envelope(&envelope)?.as_slice() != bytes {
        return Err(OrdinarySpotSettlementGuestInputErrorV2::NonCanonicalEncoding);
    }
    Ok(envelope)
}

pub fn decode_exact_ordinary_spot_settlement_guest_input_v2(
    bytes: &[u8],
) -> Result<OrdinarySpotSettlementGuestInputV2, OrdinarySpotSettlementGuestInputErrorV2> {
    let envelope = decode_exact_ordinary_spot_settlement_guest_envelope_v2(bytes)?;
    envelope.into_validated()
}

fn encode_envelope(
    envelope: &OrdinarySpotSettlementGuestEnvelopeV2,
) -> Result<Vec<u8>, OrdinarySpotSettlementGuestInputErrorV2> {
    envelope.validate_without_proposal_interpretation()?;
    encode_parts(
        envelope.proposal_bytes(),
        envelope.authorization(),
        envelope.witness(),
        envelope.data_availability_certificate(),
    )
}

fn encode_parts(
    proposal_bytes: &[u8],
    authorization: crate::SpotSettlementAuthorizationInputV1,
    witness: &zenodex_zrpf_protocol_v3::SparseMerkleCellTransitionWitnessV1,
    certificate: &zenodex_zrpf_protocol_v3::FullBlobDataAvailabilityCertificateV1,
) -> Result<Vec<u8>, OrdinarySpotSettlementGuestInputErrorV2> {
    let witness_bytes = encode_sparse_merkle_cell_transition_witness_v1(witness)?;
    let certificate_bytes = encode_full_blob_da_certificate_v1(certificate)?;
    let total = require_part_lengths(
        proposal_bytes.len(),
        witness_bytes.len(),
        certificate_bytes.len(),
    )?;
    let proposal_length = length_to_u32(proposal_bytes.len(), "proposal_length")?;
    let witness_length = length_to_u32(witness_bytes.len(), "witness_length")?;
    let certificate_length = length_to_u32(certificate_bytes.len(), "certificate_length")?;
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V2.to_be_bytes());
    bytes.extend_from_slice(&proposal_length.to_be_bytes());
    bytes.extend_from_slice(proposal_bytes);
    write_authorization_v2(&mut bytes, authorization)?;
    bytes.extend_from_slice(&witness_length.to_be_bytes());
    bytes.extend_from_slice(&witness_bytes);
    bytes.extend_from_slice(&certificate_length.to_be_bytes());
    bytes.extend_from_slice(&certificate_bytes);
    Ok(bytes)
}

fn decode_envelope_parts(
    bytes: &[u8],
) -> Result<OrdinarySpotSettlementGuestEnvelopeV2, OrdinarySpotSettlementGuestInputErrorV2> {
    require_input_size(bytes.len())?;
    let mut cursor = ExactCursorV2::new(bytes);
    let version = cursor.read_u16("guest_input_version")?;
    if version != ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V2 {
        return Err(OrdinarySpotSettlementGuestInputErrorV2::InvalidVersion(
            version,
        ));
    }
    let proposal_length = cursor.read_u32_length("proposal_length")?;
    require_proposal_length(proposal_length)?;
    let proposal_bytes = cursor.read_bytes(proposal_length, "proposal_bytes")?;
    let authorization = read_authorization_v2(&mut cursor)?;
    let witness_length = cursor.read_u32_length("witness_length")?;
    require_witness_length(witness_length)?;
    let witness_bytes = cursor.read_bytes(witness_length, "witness_bytes")?;
    let certificate_length = cursor.read_u32_length("certificate_length")?;
    require_certificate_length(certificate_length)?;
    require_total(proposal_length, witness_length, certificate_length)?;
    let certificate_bytes = cursor.read_bytes(certificate_length, "certificate_bytes")?;
    if !cursor.is_finished() {
        return Err(OrdinarySpotSettlementGuestInputErrorV2::TrailingBytes);
    }
    let witness = decode_exact_sparse_merkle_cell_transition_witness_v1(witness_bytes)?;
    let certificate = decode_exact_full_blob_da_certificate_v1(certificate_bytes)?;
    OrdinarySpotSettlementGuestEnvelopeV2::from_parts(
        proposal_bytes.to_vec(),
        authorization,
        witness,
        certificate,
    )
}

pub(super) fn require_part_lengths(
    proposal_length: usize,
    witness_length: usize,
    certificate_length: usize,
) -> Result<usize, OrdinarySpotSettlementGuestInputErrorV2> {
    require_proposal_length(proposal_length)?;
    require_witness_length(witness_length)?;
    require_certificate_length(certificate_length)?;
    require_total(proposal_length, witness_length, certificate_length)
}

fn require_input_size(size: usize) -> Result<(), OrdinarySpotSettlementGuestInputErrorV2> {
    if size == 0 {
        return Err(OrdinarySpotSettlementGuestInputErrorV2::EmptyInput);
    }
    if size > MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2 {
        return Err(OrdinarySpotSettlementGuestInputErrorV2::InputTooLarge {
            actual: size,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
        });
    }
    Ok(())
}

fn require_proposal_length(length: usize) -> Result<(), OrdinarySpotSettlementGuestInputErrorV2> {
    if length == 0 {
        return Err(OrdinarySpotSettlementGuestInputErrorV2::EmptyProposalBytes);
    }
    if length > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 {
        return Err(
            OrdinarySpotSettlementGuestInputErrorV2::ProposalBytesTooLarge {
                actual: length,
                maximum: MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
            },
        );
    }
    Ok(())
}

fn require_witness_length(length: usize) -> Result<(), OrdinarySpotSettlementGuestInputErrorV2> {
    if length == 0 {
        return Err(OrdinarySpotSettlementGuestInputErrorV2::EmptyWitnessBytes);
    }
    if length > MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1 {
        return Err(
            OrdinarySpotSettlementGuestInputErrorV2::WitnessBytesTooLarge {
                actual: length,
                maximum: MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
            },
        );
    }
    Ok(())
}

fn require_certificate_length(
    length: usize,
) -> Result<(), OrdinarySpotSettlementGuestInputErrorV2> {
    if length == 0 {
        return Err(OrdinarySpotSettlementGuestInputErrorV2::EmptyCertificateBytes);
    }
    if length > MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1 {
        return Err(
            OrdinarySpotSettlementGuestInputErrorV2::CertificateBytesTooLarge {
                actual: length,
                maximum: MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
            },
        );
    }
    Ok(())
}

fn require_total(
    proposal_length: usize,
    witness_length: usize,
    certificate_length: usize,
) -> Result<usize, OrdinarySpotSettlementGuestInputErrorV2> {
    let total = FIXED_HEADER_BYTES_V2
        .checked_add(proposal_length)
        .and_then(|value| value.checked_add(witness_length))
        .and_then(|value| value.checked_add(certificate_length))
        .ok_or(OrdinarySpotSettlementGuestInputErrorV2::ArithmeticOverflow(
            "encoded_length",
        ))?;
    if total > MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2 {
        return Err(OrdinarySpotSettlementGuestInputErrorV2::InputTooLarge {
            actual: total,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
        });
    }
    Ok(total)
}

fn length_to_u32(
    length: usize,
    field: &'static str,
) -> Result<u32, OrdinarySpotSettlementGuestInputErrorV2> {
    u32::try_from(length)
        .map_err(|_| OrdinarySpotSettlementGuestInputErrorV2::ArithmeticOverflow(field))
}
