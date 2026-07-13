use super::{
    CheckpointCursorProposalV2, DerivedCheckpointCursorV2, SuppliedCheckpointFinalityBindingV2,
};
use crate::CommitmentV3;

/// Opaque result of the complete proof-neutral V2 policy and continuity check.
///
/// The private constructor prevents a caller from manufacturing a checked
/// transition through the public API. This type does not authenticate external
/// finality or provide durable, settlement, release, or production authority.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::CheckedCheckpointFinalityTransitionV2;
///
/// let _forged = CheckedCheckpointFinalityTransitionV2 {};
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[must_use = "a checked checkpoint transition must be atomically consumed or explicitly discarded"]
pub struct CheckedCheckpointFinalityTransitionV2 {
    policy_root: CommitmentV3,
    certificate_root: CommitmentV3,
    supplied_binding: SuppliedCheckpointFinalityBindingV2,
    prior_cursor_proposal: CheckpointCursorProposalV2,
    derived_next_cursor: DerivedCheckpointCursorV2,
}

impl CheckedCheckpointFinalityTransitionV2 {
    pub(super) const fn from_checked(
        policy_root: CommitmentV3,
        certificate_root: CommitmentV3,
        supplied_binding: SuppliedCheckpointFinalityBindingV2,
        prior_cursor_proposal: CheckpointCursorProposalV2,
        derived_next_cursor: DerivedCheckpointCursorV2,
    ) -> Self {
        Self {
            policy_root,
            certificate_root,
            supplied_binding,
            prior_cursor_proposal,
            derived_next_cursor,
        }
    }

    pub const fn policy_root(&self) -> CommitmentV3 {
        self.policy_root
    }

    pub const fn certificate_root(&self) -> CommitmentV3 {
        self.certificate_root
    }

    pub const fn supplied_binding(&self) -> SuppliedCheckpointFinalityBindingV2 {
        self.supplied_binding
    }

    pub const fn prior_cursor_proposal(&self) -> CheckpointCursorProposalV2 {
        self.prior_cursor_proposal
    }

    pub const fn derived_next_cursor(&self) -> DerivedCheckpointCursorV2 {
        self.derived_next_cursor
    }
}
