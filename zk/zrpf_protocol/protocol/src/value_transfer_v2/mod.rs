mod codec;
mod error;
mod hash;
mod record;
mod set;

pub use codec::{
    decode_exact_value_transfer_set_v2, decode_exact_value_transfer_v2,
    encode_value_transfer_set_v2, encode_value_transfer_v2,
};
pub use error::ValueTransferErrorV2;
pub use record::{ValueTransferIdV2, ValueTransferInputV2, ValueTransferKindV2, ValueTransferV2};
pub use set::ValueTransferSetV2;

pub const VALUE_TRANSFER_VERSION_V2: u16 = 2;
pub const VALUE_TRANSFER_SET_VERSION_V2: u16 = 2;
pub const MAX_VALUE_TRANSFERS_PER_SET_V2: usize = 128;
pub const MAX_VALUE_TRANSFER_BYTES_V2: usize = 1_024;
pub const MAX_VALUE_TRANSFER_SET_BYTES_V2: usize = 131_072;
pub const MAX_VALUE_TRANSFER_ACTION_INDEX_V2: u32 = 8_191;
