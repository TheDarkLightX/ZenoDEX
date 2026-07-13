mod certificate;
mod codec;
mod cursor;
mod error;
mod hash;
mod policy;
mod transition;

pub use certificate::{CheckpointFinalityCertificateInputV2, CheckpointFinalityCertificateV2};
pub use codec::{
    decode_exact_checkpoint_finality_certificate_v2, encode_checkpoint_finality_certificate_v2,
};
pub use cursor::{
    CheckpointCursorProposalV2, DerivedCheckpointCursorV2,
    ProposedPriorApplicationCheckpointRecordInputV2, ProposedPriorApplicationCheckpointRecordV2,
};
pub use error::CheckpointFinalityCertificateErrorV2;
pub use policy::{
    check_checkpoint_finality_policy_satisfied_v2, CheckpointFinalityPolicyCheckInputV2,
    CheckpointFinalityPolicyErrorV2, CheckpointFinalityPolicyInputV2, CheckpointFinalityPolicyV2,
    SuppliedCheckpointFinalityBindingV2, CHECKPOINT_FINALITY_POLICY_VERSION_V2,
};
pub use transition::CheckedCheckpointFinalityTransitionV2;

pub const CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V2: u16 = 2;
pub const CHECKPOINT_FINALITY_CURSOR_VERSION_V2: u16 = 2;
pub const MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2: usize = 576;
