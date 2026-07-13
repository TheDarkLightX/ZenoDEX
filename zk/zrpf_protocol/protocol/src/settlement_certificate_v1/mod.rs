mod certificate;
mod codec;
mod error;
mod hash;

pub use certificate::{
    SettlementEpochCertificateInputV1, SettlementEpochCertificateV1, SettlementSemanticRootV1,
};
pub use codec::{
    decode_exact_settlement_epoch_certificate_v1, encode_settlement_epoch_certificate_v1,
};
pub use error::SettlementEpochCertificateErrorV1;

pub const SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1: u16 = 1;
pub const MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1: usize = 1_024;
