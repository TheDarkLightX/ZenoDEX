#![forbid(unsafe_code)]
//! `zenodex-runtime-core` — deterministic, integer-only runtime kernels.
//!
//! This crate is the **production candidate** for ZenoDEX's runtime-critical
//! transitions. It currently owns one surface: the protocol [`fee_router`]. It
//! is built as a *shadow* of the authoritative Python runtime
//! (`src/core/fee_router.py`) and must agree with it bit-for-bit on every
//! golden trace (see `docs/runtime/`).
//!
//! Design rules enforced here (see the migration "Hard Rules"):
//!
//! * `#![forbid(unsafe_code)]` — no `unsafe` anywhere in this crate.
//! * No floating point in any transition path.
//! * No wall-clock, randomness, network, filesystem, or environment reads.
//! * Fixed-width integers (`u128`) and **explicit checked arithmetic**
//!   ([`arith`]).
//! * No panics in public transition functions: every transition returns
//!   `Result<Accepted, RejectedReason>` and never falls back silently.
//! * Canonical output is built from explicit, ordered byte encodings
//!   ([`canonical`]) — never from unordered map iteration.

pub mod arith;
pub mod canonical;
pub mod error;
pub mod fee_router;

pub use error::{DomainConstraint, RejectedReason};
pub use fee_router::{
    canonical_split_table, route_fee, Accepted, Domain, FeeAccumulator, FeeReceipt, FeeSplitTable,
    BPS_DENOM, MAX_FEE_AMOUNT,
};
