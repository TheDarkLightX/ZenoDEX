#![no_std]

//! Source-opened ordinary Spot value-leaf V6.
//!
//! The raw envelope exposes only the exact adapter journal before receipt
//! authentication. After that boundary, the core re-executes a tightly scoped
//! single-swap source transition, requires exact source-journal and adapter-
//! projection equality, and derives a proof-neutral V6 statement. The V6
//! guest's own image identity is absent from both input and statement.

extern crate alloc;
#[cfg(test)]
extern crate std;

mod compose;
mod error;
mod input;
mod statement;

pub use compose::*;
pub use error::*;
pub use input::*;
pub use statement::*;

/// Current adapter-successor image used only as the verified child identity.
///
/// This does not identify the V6 guest. Historical V4 policy remains unchanged.
pub const PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID: [u32; 8] = [
    2_694_491_980,
    521_072_033,
    1_228_264_456,
    621_804_986,
    626_124_706,
    3_822_529_670,
    2_780_814_110,
    1_619_512_608,
];
