//! Replay / idempotency guard — strict-sequential per-sender nonce policy.
//!
//! Rust shadow of the authoritative Python reference (`src/core/replay_guard.py`),
//! itself the single-transition form of `src/state/nonces.py`. A sender's nonces
//! must be `1, 2, 3, …` with no gaps; any nonce at or below the last accepted one
//! is rejected (duplicate / replay). State is keyed per sender, so one sender's
//! stream can never advance or block another's.

use std::collections::BTreeMap;

use thiserror::Error;

use crate::canonical::{domain_sep_bytes, encode_bytes, encode_uvarint, sha256_hex};

/// Largest admissible nonce (u32 range, matching `src/state/nonces.py`).
pub const U32_MAX: u64 = 0xFFFF_FFFF;
const SENDER_NBYTES: usize = 48;
const STATE_LABEL: &str = "replay_guard_state";
const RECEIPT_LABEL: &str = "replay_admission";
const STATE_VERSION: u32 = 1;
const RECEIPT_VERSION: u32 = 1;

/// Why an admission was rejected. Stable `code()` matches the Python reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum ReplayRejectedReason {
    #[error("invalid sender")]
    InvalidSender,
    #[error("invalid nonce")]
    InvalidNonce,
    #[error("duplicate nonce")]
    DuplicateNonce,
    #[error("stale nonce")]
    StaleNonce,
    #[error("nonce gap")]
    NonceGap,
}

impl ReplayRejectedReason {
    pub fn code(self) -> &'static str {
        match self {
            ReplayRejectedReason::InvalidSender => "invalid_sender",
            ReplayRejectedReason::InvalidNonce => "invalid_nonce",
            ReplayRejectedReason::DuplicateNonce => "duplicate_nonce",
            ReplayRejectedReason::StaleNonce => "stale_nonce",
            ReplayRejectedReason::NonceGap => "nonce_gap",
        }
    }

    pub fn reason_str(self) -> String {
        self.code().to_string()
    }
}

/// Canonicalize a sender: raw or `0x`-prefixed 96 hex chars -> lowercase
/// `0x`-prefixed form, else `None`. This matches `src.state.nonces.NonceTable`.
pub fn canonical_sender(sender: &str) -> Option<String> {
    let body = sender
        .strip_prefix("0x")
        .or_else(|| sender.strip_prefix("0X"))
        .unwrap_or(sender);
    if body.len() != SENDER_NBYTES * 2 {
        return None;
    }
    if !body.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    Some(format!("0x{}", body.to_ascii_lowercase()))
}

fn sender_bytes(canonical: &str) -> Vec<u8> {
    // `canonical` is always a validated `0x` + 96 lowercase-hex string.
    hex::decode(&canonical[2..]).expect("validated canonical sender hex")
}

/// Per-sender last-accepted-nonce table.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReplayGuardState {
    last: BTreeMap<String, u64>,
}

impl ReplayGuardState {
    /// Last accepted nonce for `sender` (0 if never seen / invalid).
    pub fn last_for(&self, sender: &str) -> u64 {
        match canonical_sender(sender) {
            Some(c) => *self.last.get(&c).unwrap_or(&0),
            None => 0,
        }
    }

    fn with_last(&self, canonical: &str, nonce: u64) -> ReplayGuardState {
        let mut last = self.last.clone();
        last.insert(canonical.to_string(), nonce);
        ReplayGuardState { last }
    }

    /// Canonical state root (`0x`-prefixed SHA-256). BTreeMap iterates senders in
    /// sorted (== raw-byte) order, matching the Python encoder.
    pub fn state_root(&self) -> String {
        let mut buf = domain_sep_bytes(STATE_LABEL, STATE_VERSION);
        buf.extend(encode_uvarint(self.last.len() as u128));
        for (sender, last_nonce) in &self.last {
            buf.extend(sender_bytes(sender));
            buf.extend(encode_uvarint(*last_nonce as u128));
        }
        sha256_hex(&buf)
    }
}

/// Receipt for an admitted (sender, nonce).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmissionReceipt {
    pub sender: String,
    pub sequence: u64,
    pub prev_sequence: u64,
}

impl AdmissionReceipt {
    pub fn receipt_hash(&self) -> String {
        let mut buf = domain_sep_bytes(RECEIPT_LABEL, RECEIPT_VERSION);
        buf.extend_from_slice(b"SND");
        buf.extend(encode_bytes(&sender_bytes(&self.sender)));
        buf.extend_from_slice(b"NON");
        buf.extend(encode_uvarint(self.sequence as u128));
        buf.extend_from_slice(b"PRV");
        buf.extend(encode_uvarint(self.prev_sequence as u128));
        sha256_hex(&buf)
    }
}

/// Successful admission: a receipt plus the next state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmitAccepted {
    pub receipt: AdmissionReceipt,
    pub state: ReplayGuardState,
}

/// Admit `(sender, nonce)` under the strict-sequential per-sender policy.
///
/// Validation order (mirrors the Python reference exactly): sender format, then
/// nonce range, then duplicate / stale / gap / accept.
pub fn admit(
    state: &ReplayGuardState,
    sender: &str,
    sequence: u64,
) -> Result<AdmitAccepted, ReplayRejectedReason> {
    let canonical = canonical_sender(sender).ok_or(ReplayRejectedReason::InvalidSender)?;
    if !(1..=U32_MAX).contains(&sequence) {
        return Err(ReplayRejectedReason::InvalidNonce);
    }

    let last = *state.last.get(&canonical).unwrap_or(&0);
    if sequence == last {
        return Err(ReplayRejectedReason::DuplicateNonce);
    }
    if sequence < last {
        return Err(ReplayRejectedReason::StaleNonce);
    }
    if sequence > last + 1 {
        return Err(ReplayRejectedReason::NonceGap);
    }

    let new_state = state.with_last(&canonical, sequence);
    Ok(AdmitAccepted {
        receipt: AdmissionReceipt {
            sender: canonical,
            sequence,
            prev_sequence: last,
        },
        state: new_state,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn sender(tag: u8) -> String {
        format!("0x{}", hex::encode([tag; SENDER_NBYTES]))
    }

    fn sequence_values() -> impl Iterator<Item = u64> {
        1u64..=8u64
    }

    #[test]
    fn sequential_accepts_then_duplicate_and_gap_reject() {
        let a = sender(0x11);
        let mut state = ReplayGuardState::default();
        for n in sequence_values().take(4) {
            let acc = admit(&state, &a, n).unwrap();
            assert_eq!(acc.receipt.sequence, n);
            assert_eq!(acc.receipt.prev_sequence, n - 1);
            state = acc.state;
        }
        let mut seqs = sequence_values();
        let stale = seqs.next().unwrap();
        let older_stale = seqs.next().unwrap();
        let just_accepted = seqs.nth(1).unwrap();
        let next = seqs.next().unwrap();
        let gap = seqs.nth(1).unwrap();
        assert_eq!(
            admit(&state, &a, just_accepted),
            Err(ReplayRejectedReason::DuplicateNonce)
        );
        assert_eq!(
            admit(&state, &a, older_stale),
            Err(ReplayRejectedReason::StaleNonce)
        );
        assert_eq!(admit(&state, &a, next).unwrap().receipt.sequence, next);
        assert_eq!(admit(&state, &a, gap), Err(ReplayRejectedReason::NonceGap));
        assert_eq!(stale, 1);
    }

    #[test]
    fn invalid_inputs_rejected() {
        let st = ReplayGuardState::default();
        let mut seqs = sequence_values();
        let first = seqs.next().unwrap();
        let zero = first - 1;
        assert_eq!(
            admit(&st, "0xzz", first),
            Err(ReplayRejectedReason::InvalidSender)
        );
        assert_eq!(
            admit(&st, &sender(1), zero),
            Err(ReplayRejectedReason::InvalidNonce)
        );
        assert_eq!(
            admit(&st, &sender(1), U32_MAX + 1),
            Err(ReplayRejectedReason::InvalidNonce)
        );
        // Bad sender is reported before a bad nonce.
        assert_eq!(
            admit(&st, "0xzz", zero),
            Err(ReplayRejectedReason::InvalidSender)
        );
    }

    #[test]
    fn raw_hex_sender_matches_nonce_table_canonicalization() {
        let prefixed = sender(0x11);
        let raw = prefixed.strip_prefix("0x").unwrap();
        let first = sequence_values().next().unwrap();
        let a = admit(&ReplayGuardState::default(), &prefixed, first).unwrap();
        let b = admit(&ReplayGuardState::default(), raw, first).unwrap();
        assert_eq!(b.receipt.sender, prefixed);
        assert_eq!(a.receipt.receipt_hash(), b.receipt.receipt_hash());
        assert_eq!(a.state.state_root(), b.state.state_root());
    }

    #[test]
    fn senders_are_independent_unit() {
        let (a, b) = (sender(0x11), sender(0x22));
        let mut state = ReplayGuardState::default();
        let mut seqs = sequence_values();
        let first = seqs.next().unwrap();
        let second = seqs.next().unwrap();
        let third = seqs.next().unwrap();
        state = admit(&state, &a, first).unwrap().state;
        state = admit(&state, &a, second).unwrap().state;
        assert!(admit(&state, &b, first).is_ok());
        assert_eq!(
            admit(&state, &b, third),
            Err(ReplayRejectedReason::NonceGap)
        );
    }

    // --- Semantic-invariant property tests (independent of the differential) ---

    proptest! {
        // INVARIANT: a sender's accepted nonces are exactly 1, 2, 3, … and any
        // nonce <= the last accepted is rejected (monotonic + anti-replay).
        #[test]
        fn monotonic_and_anti_replay(ops in proptest::collection::vec(1u64..=6, 0..40)) {
            let s = sender(0x11);
            let mut state = ReplayGuardState::default();
            let mut expected_next = 1u64;
            for nonce in ops {
                let before = state.last_for(&s);
                match admit(&state, &s, nonce) {
                    Ok(acc) => {
                        prop_assert_eq!(nonce, expected_next);
                        prop_assert_eq!(acc.receipt.prev_sequence, before);
                        state = acc.state;
                        expected_next += 1;
                    }
                    Err(_) => {
                        // Rejection never advances state.
                        prop_assert_eq!(state.last_for(&s), before);
                        // Anything <= last is a replay/duplicate; only last+1 would accept.
                        prop_assert!(nonce != before + 1);
                    }
                }
            }
            prop_assert_eq!(state.last_for(&s), expected_next - 1);
        }

        // INVARIANT: per-sender isolation. Replaying a sender's own sub-sequence
        // in isolation yields the same accept/reject decisions as in a mixed run.
        #[test]
        fn no_cross_sender_interference(
            ops in proptest::collection::vec((0u8..3, 1u64..=5), 0..40)
        ) {
            let senders = [sender(0xA0), sender(0xB0), sender(0xC0)];

            // Mixed run: record (sender_idx, nonce, accepted).
            let mut state = ReplayGuardState::default();
            let mut mixed: Vec<(u8, u64, bool)> = Vec::new();
            for (idx, nonce) in &ops {
                let accepted = match admit(&state, &senders[*idx as usize], *nonce) {
                    Ok(acc) => { state = acc.state; true }
                    Err(_) => false,
                };
                mixed.push((*idx, *nonce, accepted));
            }

            // Per-sender isolated runs.
            for target in 0u8..3 {
                let mut iso = ReplayGuardState::default();
                let mut k = 0usize;
                for (idx, nonce) in &ops {
                    if *idx != target { continue; }
                    let accepted = match admit(&iso, &senders[target as usize], *nonce) {
                        Ok(acc) => { iso = acc.state; true }
                        Err(_) => false,
                    };
                    // Find the k-th mixed decision for this sender.
                    let mixed_decision = mixed.iter().filter(|(i, _, _)| *i == target).nth(k).unwrap();
                    prop_assert_eq!(accepted, mixed_decision.2);
                    k += 1;
                }
            }
        }
    }
}
