//! Compatibility path for the retained protocol-only test command.

#[path = "../../../risc0_receipt_verifier_v1/protocol.rs"]
mod shared_protocol;
pub use shared_protocol::*;
