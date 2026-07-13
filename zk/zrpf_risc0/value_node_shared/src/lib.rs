#![no_std]

//! Historical V4 Spot value-leaf construction used by retained evidence.
//!
//! The V4 wire includes a host-declared self image. Its exact sealed host
//! verifier compares that declaration with the image used to authenticate the
//! receipt. A consumer that only verifies a receipt and decodes `NodeJournalV4`
//! has not established the claimed runtime identity. This crate therefore
//! supplies experimental replay compatibility, not generic ledger authority.
//! New authority-bearing code must use a proof-neutral successor that attaches
//! runtime identity after receipt verification.

extern crate alloc;
#[cfg(test)]
extern crate std;

mod cursor;
mod error;
mod leaf;
mod leaf_codec;
mod profile;

pub use error::*;
pub use leaf::*;
pub use leaf_codec::*;
pub use profile::*;
