mod certificate;
mod codec;
mod error;
mod hash;
mod policy;

pub use certificate::{
    FullBlobDataAvailabilityCertificateInputV1, FullBlobDataAvailabilityCertificateV1,
    ValidatedFullBlobContentV1,
};
pub use codec::{decode_exact_full_blob_da_certificate_v1, encode_full_blob_da_certificate_v1};
pub use error::FullBlobDataAvailabilityErrorV1;
pub use policy::{
    check_local_full_blob_policy_satisfied_v1, LocalFullBlobPolicyCheckInputV1,
    LocalFullBlobPolicyErrorV1, LocalFullBlobPolicyInputV1, LocalFullBlobPolicyV1,
    LOCAL_FULL_BLOB_POLICY_VERSION_V1,
};

pub const FULL_BLOB_DA_CERTIFICATE_VERSION_V1: u16 = 1;
pub const FULL_BLOB_DA_CHUNK_BYTES_V1: u32 = 65_536;
pub const MAX_FULL_BLOB_DA_BYTES_V1: usize = 8 * 1_024 * 1_024;
pub const MAX_FULL_BLOB_DA_CHUNKS_V1: u32 = 128;
pub const MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1: usize = 512;
