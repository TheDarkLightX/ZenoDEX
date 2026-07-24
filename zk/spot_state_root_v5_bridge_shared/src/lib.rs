#![no_std]

//! Restricted legacy-Spot to ZenoLedger state-root-v5 compatibility bridge for V7.
//!
//! This crate is proof-neutral and guest-safe. It derives the exact v5 roots
//! for one deliberately narrow legacy state domain. It does not authenticate a
//! receipt, authorize settlement, or prove that an external ledger state has
//! empty LP duration-risk metadata. A future guest must authenticate the source
//! opening and require the derived roots to equal the governed header roots.

extern crate alloc;
#[cfg(test)]
extern crate std;

mod bridge;
mod error;
mod profile;
mod root_v5;

pub use bridge::*;
pub use error::*;
pub use profile::*;
