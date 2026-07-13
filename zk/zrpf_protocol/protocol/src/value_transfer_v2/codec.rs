use alloc::vec::Vec;

use super::{
    ValueTransferErrorV2, ValueTransferSetV2, ValueTransferV2, MAX_VALUE_TRANSFER_BYTES_V2,
    MAX_VALUE_TRANSFER_SET_BYTES_V2,
};

pub fn encode_value_transfer_v2(
    transfer: &ValueTransferV2,
) -> Result<Vec<u8>, ValueTransferErrorV2> {
    transfer.validate_self_consistency()?;
    let bytes =
        postcard::to_allocvec(transfer).map_err(|_| ValueTransferErrorV2::PostcardDecode)?;
    require_input_size(bytes.len(), MAX_VALUE_TRANSFER_BYTES_V2)?;
    Ok(bytes)
}

pub fn decode_exact_value_transfer_v2(
    bytes: &[u8],
) -> Result<ValueTransferV2, ValueTransferErrorV2> {
    require_input_size(bytes.len(), MAX_VALUE_TRANSFER_BYTES_V2)?;
    let (transfer, remainder) = postcard::take_from_bytes::<ValueTransferV2>(bytes)
        .map_err(|_| ValueTransferErrorV2::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ValueTransferErrorV2::TrailingBytes);
    }
    if encode_value_transfer_v2(&transfer)?.as_slice() != bytes {
        return Err(ValueTransferErrorV2::NonCanonicalEncoding);
    }
    Ok(transfer)
}

pub fn encode_value_transfer_set_v2(
    set: &ValueTransferSetV2,
) -> Result<Vec<u8>, ValueTransferErrorV2> {
    set.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(set).map_err(|_| ValueTransferErrorV2::PostcardDecode)?;
    require_input_size(bytes.len(), MAX_VALUE_TRANSFER_SET_BYTES_V2)?;
    Ok(bytes)
}

pub fn decode_exact_value_transfer_set_v2(
    bytes: &[u8],
) -> Result<ValueTransferSetV2, ValueTransferErrorV2> {
    require_input_size(bytes.len(), MAX_VALUE_TRANSFER_SET_BYTES_V2)?;
    let (set, remainder) = postcard::take_from_bytes::<ValueTransferSetV2>(bytes)
        .map_err(|_| ValueTransferErrorV2::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ValueTransferErrorV2::TrailingBytes);
    }
    if encode_value_transfer_set_v2(&set)?.as_slice() != bytes {
        return Err(ValueTransferErrorV2::NonCanonicalEncoding);
    }
    Ok(set)
}

fn require_input_size(size: usize, maximum: usize) -> Result<(), ValueTransferErrorV2> {
    if size == 0 {
        return Err(ValueTransferErrorV2::EmptyInput);
    }
    if size > maximum {
        return Err(ValueTransferErrorV2::InputTooLarge {
            actual: size,
            maximum,
        });
    }
    Ok(())
}
