use alloc::vec::Vec;

use crate::{PerpsSourceFinalityReferenceErrorV1, ProposedPerpsCollateralRowsV1};

pub const MAX_PROPOSED_PERPS_COLLATERAL_ROWS_BYTES_V1: usize = 262_144;

pub fn encode_proposed_perps_collateral_rows_v1(
    proposal: &ProposedPerpsCollateralRowsV1,
) -> Result<Vec<u8>, PerpsSourceFinalityReferenceErrorV1> {
    proposal.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(proposal)
        .map_err(|_| PerpsSourceFinalityReferenceErrorV1::PostcardDecode)?;
    require_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_proposed_perps_collateral_rows_v1(
    bytes: &[u8],
) -> Result<ProposedPerpsCollateralRowsV1, PerpsSourceFinalityReferenceErrorV1> {
    require_size(bytes.len())?;
    let (proposal, remainder) = postcard::take_from_bytes::<ProposedPerpsCollateralRowsV1>(bytes)
        .map_err(|_| PerpsSourceFinalityReferenceErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(PerpsSourceFinalityReferenceErrorV1::TrailingBytes);
    }
    if postcard::to_allocvec(&proposal)
        .map_err(|_| PerpsSourceFinalityReferenceErrorV1::PostcardDecode)?
        .as_slice()
        != bytes
    {
        return Err(PerpsSourceFinalityReferenceErrorV1::NonCanonicalEncoding);
    }
    Ok(proposal)
}

fn require_size(size: usize) -> Result<(), PerpsSourceFinalityReferenceErrorV1> {
    if size == 0 {
        return Err(PerpsSourceFinalityReferenceErrorV1::EmptyInput);
    }
    if size > MAX_PROPOSED_PERPS_COLLATERAL_ROWS_BYTES_V1 {
        return Err(PerpsSourceFinalityReferenceErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_PROPOSED_PERPS_COLLATERAL_ROWS_BYTES_V1,
        });
    }
    Ok(())
}
