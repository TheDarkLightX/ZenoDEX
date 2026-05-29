#![forbid(unsafe_code)]
//! `zenodex-runtime-core` — deterministic, integer-only runtime kernels.
//!
//! This crate is the **production candidate** for ZenoDEX's runtime-critical
//! transitions. It currently owns three surfaces: the protocol [`fee_router`],
//! the [`replay_guard`] (idempotency / nonce), and the [`balance_kernel`]
//! (multi-asset ledger). Each is built as a *shadow* of an authoritative Python
//! runtime (`src/core/*.py`) and must agree with it bit-for-bit on every golden
//! trace (see `docs/runtime/`).
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
pub mod balance_kernel;
pub mod burn_receipts;
pub mod canonical;
pub mod cpmm_swap;
pub mod error;
pub mod fee_router;
pub mod replay_guard;
pub mod state_root;
pub mod zusd;

pub use balance_kernel::{
    credit, transfer, BalanceAccepted, BalanceReceipt, BalanceRejectedReason, BalanceState,
    MAX_BALANCE,
};
pub use burn_receipts::{rail_receipt_hash, verify_rails, RailInputs};
pub use cpmm_swap::{init_pool, swap_exact_in, swap_exact_out, Pool, SwapReceipt};
pub use error::{DomainConstraint, RejectedReason};
pub use fee_router::{
    canonical_split_table, route_fee, Accepted, Domain, FeeAccumulator, FeeReceipt, FeeSplitTable,
    BPS_DENOM, MAX_FEE_AMOUNT,
};
pub use replay_guard::{
    admit, AdmissionReceipt, AdmitAccepted, ReplayGuardState, ReplayRejectedReason,
};
pub use zusd::{step as zusd_step, ZusdAccepted, ZusdCommand, ZusdState};
