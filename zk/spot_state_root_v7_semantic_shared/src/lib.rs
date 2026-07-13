#![no_std]

//! Proof-neutral preparation ABI for a future source-authenticated Spot V7 guest.
//!
//! The raw host input contains only one bounded canonical post-snapshot and two
//! proposed ZenoLedger state-root-v5 commitments. A future guest must verify
//! the V6 settlement receipt, authenticate the exact full-blob replay opening
//! against that receipt's journal, and derive the pre-snapshot, sender, ingress
//! nonce, and four legacy commitments from that opening before calling this
//! kernel. Receipt verification alone does not reveal a child guest's input.
//!
//! This crate verifies no receipt and contains no image ID. Its journal grants
//! no source-authentication, receipt, ledger, release, or settlement authority.

extern crate alloc;
#[cfg(test)]
extern crate std;

mod compose;
mod error;
mod host_input;
mod journal;

pub use compose::*;
pub use error::*;
pub use host_input::*;
pub use journal::*;

/// Machine-readable non-claim retained until an actual V7 guest verifies its
/// governed source child.
pub const SPOT_STATE_ROOT_V7_SOURCE_AUTHENTICATION_VERIFIED: bool = false;

/// Machine-readable non-claim retained until a pinned verifier authenticates a
/// fresh V7 receipt.
pub const SPOT_STATE_ROOT_V7_RECEIPT_AUTHORITY: bool = false;

/// Machine-readable non-claim retained until atomic ledger admission binds the
/// authenticated V7 journal.
pub const SPOT_STATE_ROOT_V7_SETTLEMENT_AUTHORITY: bool = false;
