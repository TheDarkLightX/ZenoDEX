//! Deterministic canonical encoding primitives.
//!
//! These mirror, byte-for-byte, the authoritative Python encoder in
//! `src/state/canonical.py`. Cross-language agreement on these primitives is
//! what makes Python/Rust state-root and receipt-hash equality possible.
//!
//! Conventions:
//! * `encode_uvarint` — unsigned LEB128 (little-endian base-128).
//! * `encode_bytes` — `uvarint(len)` length prefix, then the raw bytes.
//! * `domain_sep_bytes` — `b"zenodex:" + label + b":v" + version + b"\x00"`,
//!   an ASCII, NUL-terminated domain-separation prefix.
//! * `sha256_hex` — lowercase SHA-256, `0x`-prefixed.

use sha2::{Digest, Sha256};

/// Unsigned LEB128 encoding of `value`.
pub fn encode_uvarint(mut value: u128) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            out.push(byte | 0x80);
        } else {
            out.push(byte);
            break;
        }
    }
    out
}

/// Length-prefixed byte string: `uvarint(len)` followed by `value`.
pub fn encode_bytes(value: &[u8]) -> Vec<u8> {
    let mut out = encode_uvarint(value.len() as u128);
    out.extend_from_slice(value);
    out
}

/// Domain-separation prefix: `b"zenodex:" + label + b":v" + version + b"\x00"`.
///
/// `label` is expected to be non-empty ASCII without a NUL byte (all call sites
/// use compile-time constants that satisfy this).
pub fn domain_sep_bytes(label: &str, version: u32) -> Vec<u8> {
    debug_assert!(!label.is_empty(), "domain-sep label must be non-empty");
    debug_assert!(label.is_ascii(), "domain-sep label must be ASCII");
    debug_assert!(
        !label.contains('\u{0}'),
        "domain-sep label must not contain NUL"
    );
    debug_assert!(version > 0, "domain-sep version must be positive");
    let mut out = Vec::new();
    out.extend_from_slice(b"zenodex:");
    out.extend_from_slice(label.as_bytes());
    out.extend_from_slice(b":v");
    out.extend_from_slice(version.to_string().as_bytes());
    out.push(0x00);
    out
}

/// Lowercase SHA-256 of `data`, `0x`-prefixed.
pub fn sha256_hex(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    format!("0x{}", hex::encode(hasher.finalize()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uvarint_known_vectors() {
        assert_eq!(encode_uvarint(0), vec![0x00]);
        assert_eq!(encode_uvarint(1), vec![0x01]);
        assert_eq!(encode_uvarint(127), vec![0x7f]);
        assert_eq!(encode_uvarint(128), vec![0x80, 0x01]);
        assert_eq!(encode_uvarint(300), vec![0xac, 0x02]);
        assert_eq!(encode_uvarint(16_384), vec![0x80, 0x80, 0x01]);
    }

    #[test]
    fn encode_bytes_prefixes_length() {
        assert_eq!(encode_bytes(b""), vec![0x00]);
        assert_eq!(encode_bytes(b"ab"), vec![0x02, b'a', b'b']);
    }

    #[test]
    fn domain_sep_matches_python() {
        assert_eq!(
            domain_sep_bytes("fee_receipt", 1),
            b"zenodex:fee_receipt:v1\x00".to_vec()
        );
        assert_eq!(
            domain_sep_bytes("fee_accumulator", 1),
            b"zenodex:fee_accumulator:v1\x00".to_vec()
        );
    }

    #[test]
    fn sha256_hex_empty_vector() {
        // Matches hashlib.sha256(b"").hexdigest() with the 0x prefix.
        assert_eq!(
            sha256_hex(b""),
            "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }
}
