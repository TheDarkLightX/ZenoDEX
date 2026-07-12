use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    decode_exact_value_aggregate_proposal_v5, encode_full_blob_da_certificate_v1,
    encode_sparse_merkle_cell_transition_witness_v1, FullBlobDataAvailabilityCertificateV1,
    SparseMerkleCellTransitionWitnessV1,
};

mod codec;
mod composition;
mod error;

pub use codec::{
    decode_exact_ordinary_spot_settlement_guest_envelope_v2,
    decode_exact_ordinary_spot_settlement_guest_input_v2,
    encode_ordinary_spot_settlement_guest_input_v2,
    MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
};
pub use composition::{
    compose_ordinary_spot_settlement_guest_output_after_l2_verification_v2,
    OrdinarySpotSettlementGuestCompositionErrorV2,
};
pub use error::OrdinarySpotSettlementGuestInputErrorV2;

use super::wire_v2::validate_authorization_v2;
use codec::require_part_lengths;

use crate::SpotSettlementAuthorizationInputV1;

pub const ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V2: u16 = 2;

/// Bounded settlement input whose V5 proposal remains uninterpreted.
///
/// Exact framing, authorization, sparse witness, and DA certificate are
/// validated during construction. Proposal decoding is deliberately deferred
/// until an enclosing guest verifies the exact proposal bytes as a RISC0
/// assumption. Only those proposal bytes are publicly exposed.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::OrdinarySpotSettlementGuestEnvelopeV2;
/// let _ = OrdinarySpotSettlementGuestEnvelopeV2 {
///     proposal_bytes: vec![],
///     authorization: unimplemented!(),
///     witness: unimplemented!(),
///     data_availability_certificate: unimplemented!(),
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrdinarySpotSettlementGuestEnvelopeV2 {
    proposal_bytes: Vec<u8>,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: SparseMerkleCellTransitionWitnessV1,
    data_availability_certificate: FullBlobDataAvailabilityCertificateV1,
}

impl OrdinarySpotSettlementGuestEnvelopeV2 {
    pub fn proposal_bytes(&self) -> &[u8] {
        &self.proposal_bytes
    }

    pub(super) fn from_parts(
        proposal_bytes: Vec<u8>,
        authorization: SpotSettlementAuthorizationInputV1,
        witness: SparseMerkleCellTransitionWitnessV1,
        data_availability_certificate: FullBlobDataAvailabilityCertificateV1,
    ) -> Result<Self, OrdinarySpotSettlementGuestInputErrorV2> {
        let envelope = Self {
            proposal_bytes,
            authorization,
            witness,
            data_availability_certificate,
        };
        envelope.validate_without_proposal_interpretation()?;
        Ok(envelope)
    }

    pub(super) fn validate_without_proposal_interpretation(
        &self,
    ) -> Result<(), OrdinarySpotSettlementGuestInputErrorV2> {
        validate_components(
            self.proposal_bytes.len(),
            self.authorization,
            &self.witness,
            &self.data_availability_certificate,
        )
    }

    pub(super) const fn authorization(&self) -> SpotSettlementAuthorizationInputV1 {
        self.authorization
    }

    pub(super) const fn witness(&self) -> &SparseMerkleCellTransitionWitnessV1 {
        &self.witness
    }

    pub(super) const fn data_availability_certificate(
        &self,
    ) -> &FullBlobDataAvailabilityCertificateV1 {
        &self.data_availability_certificate
    }

    pub(super) fn into_validated(
        self,
    ) -> Result<OrdinarySpotSettlementGuestInputV2, OrdinarySpotSettlementGuestInputErrorV2> {
        OrdinarySpotSettlementGuestInputV2::new(
            self.proposal_bytes,
            self.authorization,
            self.witness,
            self.data_availability_certificate,
        )
    }
}

/// Interpret the exact proposal only after the caller verifies its L2 receipt.
///
/// The name records a caller precondition. This proof-neutral function carries
/// no receipt, image policy, verifier verdict, or settlement authority.
pub fn bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2(
    envelope: OrdinarySpotSettlementGuestEnvelopeV2,
) -> Result<OrdinarySpotSettlementGuestInputV2, OrdinarySpotSettlementGuestInputErrorV2> {
    envelope.into_validated()
}

/// Exact proof-neutral input validated after authenticating its L2 proposal.
///
/// Canonical L2 proposal bytes, authorization, sparse witness, and external DA
/// certificate are the complete surface. This value carries no proof verdict,
/// image identity, claim binding, receipt, or settlement authority.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::OrdinarySpotSettlementGuestInputV2;
/// let input: OrdinarySpotSettlementGuestInputV2 = unimplemented!();
/// let _ = input.receipt_valid();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::OrdinarySpotSettlementGuestInputV2;
/// let input: OrdinarySpotSettlementGuestInputV2 = unimplemented!();
/// let _ = input.expected_self_image_id();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::OrdinarySpotSettlementGuestInputV2;
/// let input: OrdinarySpotSettlementGuestInputV2 = unimplemented!();
/// let _ = input.semantic_claim_binding();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::OrdinarySpotSettlementGuestInputV2;
/// let _ = OrdinarySpotSettlementGuestInputV2 {
///     proposal_bytes: vec![],
///     authorization: unimplemented!(),
///     witness: unimplemented!(),
///     data_availability_certificate: unimplemented!(),
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrdinarySpotSettlementGuestInputV2 {
    proposal_bytes: Vec<u8>,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: SparseMerkleCellTransitionWitnessV1,
    data_availability_certificate: FullBlobDataAvailabilityCertificateV1,
}

impl OrdinarySpotSettlementGuestInputV2 {
    pub fn new(
        proposal_bytes: Vec<u8>,
        authorization: SpotSettlementAuthorizationInputV1,
        witness: SparseMerkleCellTransitionWitnessV1,
        data_availability_certificate: FullBlobDataAvailabilityCertificateV1,
    ) -> Result<Self, OrdinarySpotSettlementGuestInputErrorV2> {
        let input = Self {
            proposal_bytes,
            authorization,
            witness,
            data_availability_certificate,
        };
        input.validate_self_consistency()?;
        Ok(input)
    }

    pub fn validate_self_consistency(&self) -> Result<(), OrdinarySpotSettlementGuestInputErrorV2> {
        validate_components(
            self.proposal_bytes.len(),
            self.authorization,
            &self.witness,
            &self.data_availability_certificate,
        )?;
        decode_exact_value_aggregate_proposal_v5(&self.proposal_bytes)?;
        Ok(())
    }

    pub fn proposal_bytes(&self) -> &[u8] {
        &self.proposal_bytes
    }

    pub const fn authorization(&self) -> SpotSettlementAuthorizationInputV1 {
        self.authorization
    }

    pub const fn witness(&self) -> &SparseMerkleCellTransitionWitnessV1 {
        &self.witness
    }

    pub const fn data_availability_certificate(&self) -> &FullBlobDataAvailabilityCertificateV1 {
        &self.data_availability_certificate
    }
}

fn validate_components(
    proposal_length: usize,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: &SparseMerkleCellTransitionWitnessV1,
    data_availability_certificate: &FullBlobDataAvailabilityCertificateV1,
) -> Result<(), OrdinarySpotSettlementGuestInputErrorV2> {
    validate_authorization_v2(authorization)?;
    let witness_bytes = encode_sparse_merkle_cell_transition_witness_v1(witness)?;
    let certificate_bytes = encode_full_blob_da_certificate_v1(data_availability_certificate)?;
    require_part_lengths(
        proposal_length,
        witness_bytes.len(),
        certificate_bytes.len(),
    )?;
    Ok(())
}
