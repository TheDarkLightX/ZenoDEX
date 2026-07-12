mod codec;
mod error;
mod hash;
mod journal;

pub use codec::{
    decode_exact_settlement_admission_journal_v1, encode_settlement_admission_journal_v1,
};
pub use error::SettlementAdmissionJournalErrorV1;
pub use journal::SettlementAdmissionJournalV1;

use crate::{MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2, MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1};

pub const SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1: u16 = 1;
pub const SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1: [u8; 8] = *b"ZRPFSAV1";

/// Fixed header and duplicated-field bytes, excluding the two framed objects.
pub const SETTLEMENT_ADMISSION_FIXED_BYTES_V1: usize = 971;
pub const MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1: usize = SETTLEMENT_ADMISSION_FIXED_BYTES_V1
    + MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1
    + MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2;

const _: () = assert!(MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1 <= u32::MAX as usize);
