#![no_std]

//! Proof-neutral perps collateral source-finality row reference.
//!
//! This crate authenticates no source receipt. It validates canonical proposed
//! transfer bytes, derives the one-sided rows that separate perps accounting
//! from its external counterparty, and fails closed unless every value-moving
//! action has exactly one matching transfer; external-chain finality remains
//! unestablished until separate governed source and destination guests verify
//! the relevant receipt claims and derive the same transfer identities.
//! In concise form: external-chain finality remains unestablished.
//!
//! This layer provides no source guest, receipt verification, transfer
//! finality, durable admission, settlement authority, release authority,
//! privacy, production authority, or complete perps lifecycle coverage.

extern crate alloc;

mod codec;
mod derive;
mod error;
mod model;

pub use codec::{
    decode_exact_proposed_perps_collateral_rows_v1, encode_proposed_perps_collateral_rows_v1,
    MAX_PROPOSED_PERPS_COLLATERAL_ROWS_BYTES_V1,
};
pub use derive::{
    derive_proposed_perps_collateral_rows_v1, perps_counterparty_actor_scope_v1,
    proposed_transfer_input_for_perps_action_v1,
};
pub use error::PerpsSourceFinalityReferenceErrorV1;
pub use model::{
    PerpsCollateralReferenceContextV1, PerpsCollateralTransferRowV1, ProposedPerpsCollateralRowsV1,
    ProposedSourceEvidenceV1, MAX_PERPS_COLLATERAL_ROWS_V1,
    PROPOSED_PERPS_COLLATERAL_ROWS_VERSION_V1,
};
