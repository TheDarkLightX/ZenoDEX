#![no_std]

//! Typed, proof-neutral binding between one restricted Spot swap, its exact
//! state-root-v5 transition, and one canonical settlement effect plan.
//!
//! The kernel reopens the complete bounded pre/post Spot snapshots under the
//! existing V7 state journal, derives four typed balance/reserve changes, and
//! constructs the exact V7 plan from those changes and authenticated V6 Plan A
//! lineage. It accepts no host-proposed V7 Plan B. It verifies no receipt and
//! performs no persistence or finality check. A future V7 guest must run this
//! kernel after authenticating its source child and must commit the returned
//! binding journal.

extern crate alloc;
#[cfg(test)]
extern crate std;

mod binding;
mod error;
mod journal;
mod opening;

pub use binding::*;
pub use error::*;
pub use journal::*;
pub use opening::*;

/// Remains false until a governed V7 guest receipt authenticates this exact
/// relation and atomic application-state admission consumes it.
pub const SPOT_SETTLEMENT_V7_EFFECT_BINDING_SETTLEMENT_AUTHORITY: bool = false;

/// This crate verifies the proof-neutral relation only. It never authenticates
/// the V7 journal supplied by its caller.
pub const SPOT_SETTLEMENT_V7_EFFECT_BINDING_RECEIPT_AUTHORITY: bool = false;
