use alloc::vec::Vec;

use super::SemanticSubtreeV2;
use crate::value_node_v4::{ValueNodeErrorV4, MAX_SEMANTIC_SUBTREE_BYTES_V2};

pub fn encode_semantic_subtree_v2(
    subtree: &SemanticSubtreeV2,
) -> Result<Vec<u8>, ValueNodeErrorV4> {
    subtree.validate()?;
    let bytes = postcard::to_allocvec(subtree).map_err(|_| ValueNodeErrorV4::PostcardDecode)?;
    if bytes.len() > MAX_SEMANTIC_SUBTREE_BYTES_V2 {
        return Err(ValueNodeErrorV4::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SEMANTIC_SUBTREE_BYTES_V2,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_semantic_subtree_v2(
    bytes: &[u8],
) -> Result<SemanticSubtreeV2, ValueNodeErrorV4> {
    if bytes.is_empty() {
        return Err(ValueNodeErrorV4::EmptyInput);
    }
    if bytes.len() > MAX_SEMANTIC_SUBTREE_BYTES_V2 {
        return Err(ValueNodeErrorV4::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SEMANTIC_SUBTREE_BYTES_V2,
        });
    }
    let (subtree, remainder): (SemanticSubtreeV2, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|_| ValueNodeErrorV4::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ValueNodeErrorV4::TrailingBytes);
    }
    subtree.validate()?;
    let canonical =
        postcard::to_allocvec(&subtree).map_err(|_| ValueNodeErrorV4::PostcardDecode)?;
    if canonical != bytes {
        return Err(ValueNodeErrorV4::NonCanonicalEncoding);
    }
    Ok(subtree)
}
