#![no_std]

//! Canonical proof-neutral kernel for the Spot settlement V7 recursive lane.
//!
//! The kernel consumes exact bytes only after a receipt-bearing caller has
//! authenticated the V6 child journal. It validates the child-bound full-blob
//! replay, re-executes the source transition, derives the state-root V7
//! journal, and derives the exact typed settlement plan from full pre/post
//! state openings. This crate performs no receipt verification or persistence.

extern crate alloc;
#[cfg(test)]
extern crate std;

mod compose;
mod envelope;
mod error;
mod journal;
mod source_opening;

pub use compose::*;
pub use envelope::*;
pub use error::*;
pub use journal::*;
pub use source_opening::*;

pub const SPOT_SETTLEMENT_V7_RECEIPT_AUTHORITY: bool = false;
pub const SPOT_SETTLEMENT_V7_SETTLEMENT_AUTHORITY: bool = false;
pub const SPOT_SETTLEMENT_V7_PRODUCTION_AUTHORITY: bool = false;
