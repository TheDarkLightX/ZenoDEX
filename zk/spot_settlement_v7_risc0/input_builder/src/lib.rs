//! Authority-neutral construction of canonical Spot settlement V7 guest input.
//!
//! This crate validates and frames proposal bytes. It verifies no receipt,
//! data-availability fact, state transition, release, or settlement authority.

mod artifact_io;
mod build;
mod cli;
mod error;

pub use build::*;
pub use cli::*;
pub use error::*;

pub const SPOT_SETTLEMENT_V7_INPUT_BUILDER_RECEIPT_AUTHORITY: bool = false;
pub const SPOT_SETTLEMENT_V7_INPUT_BUILDER_SETTLEMENT_AUTHORITY: bool = false;
pub const SPOT_SETTLEMENT_V7_INPUT_BUILDER_PRODUCTION_AUTHORITY: bool = false;
