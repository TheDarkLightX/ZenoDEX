use core::fmt;

use alloc::vec::Vec;
use zenodex_zrpf_protocol_v3::{
    decode_exact_value_aggregate_proposal_v5, encode_settlement_epoch_certificate_v1, CommitmentV3,
    SettlementEpochCertificateErrorV1, ValueAggregateErrorV5,
};

use super::OrdinarySpotSettlementGuestInputV2;
use crate::{
    compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2,
    OrdinarySpotSettlementCertificateErrorV1,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrdinarySpotSettlementGuestCompositionErrorV2 {
    Proposal(ValueAggregateErrorV5),
    Certificate(OrdinarySpotSettlementCertificateErrorV1),
    Output(SettlementEpochCertificateErrorV1),
}

impl fmt::Display for OrdinarySpotSettlementGuestCompositionErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Proposal(error) => write!(formatter, "settlement proposal rejected: {error}"),
            Self::Certificate(error) => {
                write!(formatter, "settlement certificate rejected: {error}")
            }
            Self::Output(error) => write!(formatter, "settlement output rejected: {error}"),
        }
    }
}

/// Compose canonical settlement output after exact L2 receipt verification.
///
/// The name records a caller precondition. This deterministic function carries
/// no receipt, image policy, verdict, persistence effect, or settlement
/// authority. The caller supplies the claim binding derived from the verified
/// L2 image and these exact proposal bytes.
pub fn compose_ordinary_spot_settlement_guest_output_after_l2_verification_v2(
    input: &OrdinarySpotSettlementGuestInputV2,
    semantic_claim_binding: CommitmentV3,
) -> Result<Vec<u8>, OrdinarySpotSettlementGuestCompositionErrorV2> {
    let proposal = decode_exact_value_aggregate_proposal_v5(input.proposal_bytes())
        .map_err(OrdinarySpotSettlementGuestCompositionErrorV2::Proposal)?;
    let certificate = compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2(
        &proposal,
        input.authorization(),
        input.witness().clone(),
        semantic_claim_binding,
        input.data_availability_certificate(),
    )
    .map_err(OrdinarySpotSettlementGuestCompositionErrorV2::Certificate)?;
    encode_settlement_epoch_certificate_v1(&certificate)
        .map_err(OrdinarySpotSettlementGuestCompositionErrorV2::Output)
}
