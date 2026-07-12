use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    decode_exact_value_aggregate_proposal_v5, encode_full_blob_da_certificate_v1,
    encode_sparse_merkle_cell_transition_witness_v1, FullBlobDataAvailabilityCertificateV1,
    SparseMerkleCellTransitionWitnessV1,
};

mod codec;
mod error;

pub use codec::{
    decode_exact_ordinary_spot_settlement_guest_input_v2,
    encode_ordinary_spot_settlement_guest_input_v2,
    MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
};
pub use error::OrdinarySpotSettlementGuestInputErrorV2;

use super::wire_v2::validate_authorization_v2;
use codec::require_part_lengths;

use crate::SpotSettlementAuthorizationInputV1;

pub const ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V2: u16 = 2;

/// Exact proof-neutral input reserved for a future state-bound settlement guest.
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
        validate_authorization_v2(self.authorization)?;
        decode_exact_value_aggregate_proposal_v5(&self.proposal_bytes)?;
        let witness_bytes = encode_sparse_merkle_cell_transition_witness_v1(&self.witness)?;
        let certificate_bytes =
            encode_full_blob_da_certificate_v1(&self.data_availability_certificate)?;
        require_part_lengths(
            self.proposal_bytes.len(),
            witness_bytes.len(),
            certificate_bytes.len(),
        )?;
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
