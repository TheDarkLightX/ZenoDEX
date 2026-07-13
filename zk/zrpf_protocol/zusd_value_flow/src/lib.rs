#![no_std]

//! Proof-neutral zUSD lifecycle value-flow reference.
//!
//! This crate authenticates no receipt. It derives exact integer rows for the
//! bounded zUSD lifecycle from typed host proposals.
//! Oracle truth remains unestablished.
//! External collateral finality remains unestablished.
//! It supplies no source guest, image binding, state-continuity proof, data
//! availability, or durable admission, settlement authority, release
//! authority, privacy, throughput, or production authority.

extern crate alloc;

mod bounded;
mod codec;
mod context;
mod derive;
mod error;
mod hash;
mod operation;
mod proposal;
mod row;

pub use codec::{
    decode_exact_proposed_zusd_value_flow_v1, encode_proposed_zusd_value_flow_v1,
    MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1,
};
pub use context::{
    ProposedZusdSourceEvidenceV1, ZusdValueFlowContextInputV1, ZusdValueFlowContextV1,
};
pub use error::ZusdValueFlowErrorV1;
pub use operation::{
    ZusdValueOperationInputV1, ZusdValueOperationKindV1, ZusdValueOperationV1,
    MAX_ZUSD_AMOUNT_ATOMS_V1, MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1, ZUSD_BPS_SCALE_V1,
    ZUSD_VALUE_OPERATION_VERSION_V1,
};
pub use proposal::{ProposedZusdValueFlowV1, PROPOSED_ZUSD_VALUE_FLOW_VERSION_V1};
pub use row::{
    ZusdValueEffectKindV1, ZusdValueFlowRowV1, MAX_ZUSD_VALUE_FLOW_ROWS_V1,
    ZUSD_VALUE_FLOW_ROW_VERSION_V1,
};
