use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, ZrpfErrorV3};

use crate::risc0_image_words_to_bytes;

const VERIFIED_CLAIM_BINDING_DOMAIN_V1: &[u8] = b"zenodex.zrpf.risc0_verified_claim_binding.v1";

/// Derives a protocol claim binding after the caller has verified the exact
/// RISC0 claim. Physical receipt and seal encodings are intentionally absent.
pub fn derive_risc0_verified_claim_binding_v1(
    image_id: [u32; 8],
    exact_journal_bytes: &[u8],
) -> Result<CommitmentV3, ZrpfErrorV3> {
    let domain_length = u16::try_from(VERIFIED_CLAIM_BINDING_DOMAIN_V1.len())
        .map_err(|_| ZrpfErrorV3::ArithmeticOverflow("verified_claim_domain_length"))?;
    let journal_length = u32::try_from(exact_journal_bytes.len())
        .map_err(|_| ZrpfErrorV3::ArithmeticOverflow("verified_claim_journal_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_length.to_be_bytes());
    hasher.update(VERIFIED_CLAIM_BINDING_DOMAIN_V1);
    hasher.update(risc0_image_words_to_bytes(image_id));
    hasher.update(journal_length.to_be_bytes());
    hasher.update(exact_journal_bytes);
    CommitmentV3::new(hasher.finalize().into())
}
