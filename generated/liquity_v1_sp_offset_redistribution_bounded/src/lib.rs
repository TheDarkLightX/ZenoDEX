//! ESSO-generated kernel crate.
//!
//! Model: sha256:7b505df182da9fbff843b199366d6bcb6dd63736d573a9fe5e243f3d70db2fec
//! Generator: esso-codegen v2.1.0
///
/// ## Sealing (compile-fail)
///
/// ```compile_fail
/// use liquity_v1_sp_offset_redistribution_bounded::gen::State;
/// let _ = State::default();
/// ```
///
/// ```compile_fail
/// use liquity_v1_sp_offset_redistribution_bounded::kernel::TySvBranch;
/// let _ = TySvBranch { value: 0 };
/// ```
mod gen;
pub(crate) mod manual;

/// Public, sealed kernel API.
pub mod kernel {
    pub use crate::gen::*;
}

pub use kernel::{step, Command, Effects, State, StepError};
