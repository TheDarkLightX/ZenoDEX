#![no_std]

//! Source-opened ordinary Spot V6 settlement profile.
//!
//! The profile reopens one canonical V6 source transition after an enclosing
//! guest verifies the exact V5 L2 receipt. It requires singleton two-level
//! semantic and operational equality, binds source data into full-blob replay,
//! and delegates state-bound certificate construction to the proof-neutral
//! settlement kernel. Receipt and ledger authority remain separate.

extern crate alloc;
#[cfg(test)]
extern crate std;

mod codec;
mod composition;
mod error;
mod relation;
mod replay;

pub use codec::*;
pub use composition::*;
pub use error::*;
pub use relation::*;
pub use replay::*;
