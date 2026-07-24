mod certificate;
mod codec;
mod error;
mod hash;
mod policy;

pub use certificate::{CheckpointFinalityCertificateInputV1, CheckpointFinalityCertificateV1};
pub use codec::{
    decode_exact_checkpoint_finality_certificate_v1, encode_checkpoint_finality_certificate_v1,
};
pub use error::CheckpointFinalityCertificateErrorV1;
pub use policy::{
    check_checkpoint_finality_policy_satisfied_v1, CheckpointFinalityPolicyCheckInputV1,
    CheckpointFinalityPolicyErrorV1, CheckpointFinalityPolicyInputV1, CheckpointFinalityPolicyV1,
    ExpectedFinalizedCheckpointBindingV1, CHECKPOINT_FINALITY_POLICY_VERSION_V1,
};

pub const CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V1: u16 = 1;
pub const MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V1: usize = 512;
