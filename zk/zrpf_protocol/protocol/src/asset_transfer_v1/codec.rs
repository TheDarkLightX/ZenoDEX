use alloc::vec::Vec;

use super::{
    AssetTransferErrorV1, AssetTransferLeafInputV1, MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1,
};

pub fn encode_asset_transfer_leaf_input_v1(
    input: &AssetTransferLeafInputV1,
) -> Result<Vec<u8>, AssetTransferErrorV1> {
    input.command().canonical_hash()?;
    let bytes = postcard::to_allocvec(input).map_err(|_| AssetTransferErrorV1::PostcardEncode)?;
    if bytes.len() > MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1 {
        return Err(AssetTransferErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_asset_transfer_leaf_input_v1(
    bytes: &[u8],
) -> Result<AssetTransferLeafInputV1, AssetTransferErrorV1> {
    if bytes.is_empty() {
        return Err(AssetTransferErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1 {
        return Err(AssetTransferErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1,
        });
    }
    let (input, remainder): (AssetTransferLeafInputV1, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|_| AssetTransferErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(AssetTransferErrorV1::TrailingBytes);
    }
    if encode_asset_transfer_leaf_input_v1(&input)?.as_slice() != bytes {
        return Err(AssetTransferErrorV1::NonCanonicalEncoding);
    }
    Ok(input)
}
