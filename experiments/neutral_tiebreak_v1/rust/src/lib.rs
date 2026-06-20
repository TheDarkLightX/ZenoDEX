//! Rust shadow of the grinding-resistant tie-break primitive.
//!
//! Byte-identical to the Python prototype `neutral_tiebreak.py`. Parity is
//! enforced by `tests/parity.rs`, which recomputes the Python-generated golden
//! vectors in `../parity_vectors.tsv` and asserts equality.
//!
//! Construction (collision-free, length-prefixed framing):
//!
//! ```text
//! framed(x)          = u64_be(len(x)) || x
//! tiebreak_key(s, id) = sha256( framed(domain_sep) || framed(s) || framed(id) )
//! ```
//!
//! Pure function; no I/O, no global state. See the Python module for the
//! load-bearing COMPOSITION REQUIREMENT (the seed must be unpredictable until
//! identifiers are locked AND unbiasable at production -- not solved here).

use sha2::{Digest, Sha256};

pub const DOMAIN_SEP: &str = "zenodex.neutral_tiebreak/v1";

/// `u64_be(len(field)) || field` -- collision-free framing.
fn framed(field: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + field.len());
    // Checked conversion (CBC: no unchecked casts). usize<=u64 on supported
    // targets, so this never fails; explicit for proof-friendliness.
    let len = u64::try_from(field.len()).expect("field length fits u64");
    out.extend_from_slice(&len.to_be_bytes());
    out.extend_from_slice(field);
    out
}

/// Grinding-resistant tie-break key with the default domain separator.
pub fn committed_seed_tiebreak_key(seed: &[u8], identifier: &str) -> [u8; 32] {
    committed_seed_tiebreak_key_with_domain(seed, identifier, DOMAIN_SEP)
}

/// Grinding-resistant tie-break key with an explicit domain separator.
pub fn committed_seed_tiebreak_key_with_domain(
    seed: &[u8],
    identifier: &str,
    domain_sep: &str,
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(framed(domain_sep.as_bytes()));
    h.update(framed(seed));
    h.update(framed(identifier.as_bytes()));
    h.finalize().into()
}

// --- Seed source (commit-reveal-with-punishment) parity surface ----------
// Byte-identical to seed_source.py. Parity in tests/seed_parity.rs.

pub const SEED_COMMIT_DOMAIN: &str = "zenodex.seed_commit/v1";
pub const SEED_DOMAIN: &str = "zenodex.seed/v1";

/// Binding commitment: `sha256(framed(domain) || framed(value) || framed(nonce))`.
pub fn seed_commit(value: &[u8], nonce: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(framed(SEED_COMMIT_DOMAIN.as_bytes()));
    h.update(framed(value));
    h.update(framed(nonce));
    h.finalize().into()
}

/// Seed over (participant_id, value) pairs, sorted by id UTF-8 bytes.
pub fn seed_from_pairs(pairs: &[(&str, &[u8])]) -> [u8; 32] {
    let mut items: Vec<(&[u8], &[u8])> = pairs.iter().map(|(id, v)| (id.as_bytes(), *v)).collect();
    items.sort_by(|a, b| a.0.cmp(b.0)); // by id UTF-8 bytes (matches Python)
    let mut h = Sha256::new();
    h.update(framed(SEED_DOMAIN.as_bytes()));
    for (id_bytes, value) in items {
        h.update(framed(id_bytes));
        h.update(framed(value));
    }
    h.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn framing_is_collision_free() {
        // The exact pair that collided under the old `|| 0x00 ||` framing.
        let a = committed_seed_tiebreak_key(b"a\x00b", "c");
        let b = committed_seed_tiebreak_key(b"a", "b\x00c");
        assert_ne!(a, b, "length-prefixed framing must not collide");
    }

    #[test]
    fn is_deterministic() {
        let a = committed_seed_tiebreak_key(b"seed", "intent-0001");
        let b = committed_seed_tiebreak_key(b"seed", "intent-0001");
        assert_eq!(a, b);
    }
}
