mod error;
mod request;
mod response;

pub use error::NetnsHelperErrorV1;
pub use request::{
    decode_request_v1, encode_request_v1, DecodedNetnsRequestV1, NetnsOperationV1,
    NetnsRequestInputV1, PROTOCOL_VERSION_V1, REQUEST_BYTES_V1, REQUEST_DIGEST_OFFSET_V1,
    REQUEST_EXPECTED_DEVICE_OFFSET_V1, REQUEST_EXPECTED_INODE_OFFSET_V1, REQUEST_FLAGS_OFFSET_V1,
    REQUEST_MAGIC_V1, REQUEST_NAME_BYTES_V1, REQUEST_NAME_LENGTH_OFFSET_V1, REQUEST_NAME_OFFSET_V1,
    REQUEST_RESERVED_OFFSET_V1, REQUEST_ROOT_BYTES_V1, REQUEST_ROOT_LENGTH_OFFSET_V1,
    REQUEST_ROOT_OFFSET_V1, REQUEST_TRUSTED_UID_OFFSET_V1,
};
pub use response::{
    execute_request_with_kernel_v1, NetnsKernelObservationV1, NetnsKernelV1, RESPONSE_BYTES_V1,
    RESPONSE_MAGIC_V1,
};

#[cfg(target_os = "linux")]
pub mod linux;
