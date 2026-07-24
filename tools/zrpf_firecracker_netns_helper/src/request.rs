use sha2::{Digest, Sha256};

use crate::NetnsHelperErrorV1;

pub const REQUEST_BYTES_V1: usize = 512;
pub const REQUEST_MAGIC_V1: [u8; 16] = *b"ZRPFLNXNSREQV1!!";
pub const PROTOCOL_VERSION_V1: u16 = 1;

pub const REQUEST_FLAGS_OFFSET_V1: usize = 20;
pub const REQUEST_TRUSTED_UID_OFFSET_V1: usize = 24;
pub const REQUEST_ROOT_LENGTH_OFFSET_V1: usize = 28;
pub const REQUEST_NAME_LENGTH_OFFSET_V1: usize = 30;
pub const REQUEST_EXPECTED_DEVICE_OFFSET_V1: usize = 32;
pub const REQUEST_EXPECTED_INODE_OFFSET_V1: usize = 40;
pub const REQUEST_ROOT_OFFSET_V1: usize = 48;
pub const REQUEST_ROOT_BYTES_V1: usize = 256;
pub const REQUEST_NAME_OFFSET_V1: usize = 304;
pub const REQUEST_NAME_BYTES_V1: usize = 64;
pub const REQUEST_RESERVED_OFFSET_V1: usize = 368;
pub const REQUEST_DIGEST_OFFSET_V1: usize = 480;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u16)]
pub enum NetnsOperationV1 {
    Create = 1,
    Inspect = 2,
    Destroy = 3,
    Cleanup = 4,
    Absence = 5,
}

impl TryFrom<u16> for NetnsOperationV1 {
    type Error = NetnsHelperErrorV1;

    fn try_from(value: u16) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(Self::Create),
            2 => Ok(Self::Inspect),
            3 => Ok(Self::Destroy),
            4 => Ok(Self::Cleanup),
            5 => Ok(Self::Absence),
            _ => Err(NetnsHelperErrorV1::RequestOperation(value)),
        }
    }
}

impl NetnsOperationV1 {
    pub const fn code(self) -> u16 {
        match self {
            Self::Create => 1,
            Self::Inspect => 2,
            Self::Destroy => 3,
            Self::Cleanup => 4,
            Self::Absence => 5,
        }
    }
}

pub struct NetnsRequestInputV1<'a> {
    pub operation: NetnsOperationV1,
    pub namespace_root: &'a str,
    pub namespace_name: &'a str,
    pub expected_device: u64,
    pub expected_inode: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodedNetnsRequestV1 {
    operation: NetnsOperationV1,
    namespace_root: String,
    namespace_name: String,
    expected_device: u64,
    expected_inode: u64,
    request_sha256: [u8; 32],
}

impl DecodedNetnsRequestV1 {
    pub fn operation(&self) -> NetnsOperationV1 {
        self.operation
    }

    pub fn namespace_root(&self) -> &str {
        &self.namespace_root
    }

    pub fn namespace_name(&self) -> &str {
        &self.namespace_name
    }

    pub fn expected_device(&self) -> u64 {
        self.expected_device
    }

    pub fn expected_inode(&self) -> u64 {
        self.expected_inode
    }

    pub fn request_sha256(&self) -> [u8; 32] {
        self.request_sha256
    }
}

pub fn encode_request_v1(input: NetnsRequestInputV1<'_>) -> Result<Vec<u8>, NetnsHelperErrorV1> {
    validate_namespace_root(input.namespace_root)?;
    validate_namespace_name(input.namespace_name)?;
    validate_identity(input.operation, input.expected_device, input.expected_inode)?;
    let root_length = u16::try_from(input.namespace_root.len())
        .map_err(|_| NetnsHelperErrorV1::NamespaceRootLength)?;
    let name_length = u16::try_from(input.namespace_name.len())
        .map_err(|_| NetnsHelperErrorV1::NamespaceNameLength)?;
    let mut request = vec![0_u8; REQUEST_BYTES_V1];
    request[0..16].copy_from_slice(&REQUEST_MAGIC_V1);
    request[16..18].copy_from_slice(&PROTOCOL_VERSION_V1.to_be_bytes());
    request[18..20].copy_from_slice(&input.operation.code().to_be_bytes());
    request[REQUEST_ROOT_LENGTH_OFFSET_V1..REQUEST_ROOT_LENGTH_OFFSET_V1 + 2]
        .copy_from_slice(&root_length.to_be_bytes());
    request[REQUEST_NAME_LENGTH_OFFSET_V1..REQUEST_NAME_LENGTH_OFFSET_V1 + 2]
        .copy_from_slice(&name_length.to_be_bytes());
    request[REQUEST_EXPECTED_DEVICE_OFFSET_V1..REQUEST_EXPECTED_DEVICE_OFFSET_V1 + 8]
        .copy_from_slice(&input.expected_device.to_be_bytes());
    request[REQUEST_EXPECTED_INODE_OFFSET_V1..REQUEST_EXPECTED_INODE_OFFSET_V1 + 8]
        .copy_from_slice(&input.expected_inode.to_be_bytes());
    request[REQUEST_ROOT_OFFSET_V1..REQUEST_ROOT_OFFSET_V1 + input.namespace_root.len()]
        .copy_from_slice(input.namespace_root.as_bytes());
    request[REQUEST_NAME_OFFSET_V1..REQUEST_NAME_OFFSET_V1 + input.namespace_name.len()]
        .copy_from_slice(input.namespace_name.as_bytes());
    let digest = sha256(&request[..REQUEST_DIGEST_OFFSET_V1]);
    request[REQUEST_DIGEST_OFFSET_V1..].copy_from_slice(&digest);
    Ok(request)
}

pub fn decode_request_v1(request: &[u8]) -> Result<DecodedNetnsRequestV1, NetnsHelperErrorV1> {
    require_fixed_header(request)?;
    let operation = NetnsOperationV1::try_from(read_u16(request, 18)?)?;
    require_zero_control_fields(request)?;
    let root_length = usize::from(read_u16(request, REQUEST_ROOT_LENGTH_OFFSET_V1)?);
    let name_length = usize::from(read_u16(request, REQUEST_NAME_LENGTH_OFFSET_V1)?);
    require_lengths(root_length, name_length)?;
    let expected_device = read_u64(request, REQUEST_EXPECTED_DEVICE_OFFSET_V1)?;
    let expected_inode = read_u64(request, REQUEST_EXPECTED_INODE_OFFSET_V1)?;
    validate_identity(operation, expected_device, expected_inode)?;
    let root_slot = &request[REQUEST_ROOT_OFFSET_V1..REQUEST_NAME_OFFSET_V1];
    let name_slot = &request[REQUEST_NAME_OFFSET_V1..REQUEST_RESERVED_OFFSET_V1];
    require_canonical_tail_bytes(request, root_slot, name_slot, root_length, name_length)?;
    let namespace_root = core::str::from_utf8(&root_slot[..root_length])
        .map_err(|_| NetnsHelperErrorV1::NamespaceRootEncoding)?;
    let namespace_name = core::str::from_utf8(&name_slot[..name_length])
        .map_err(|_| NetnsHelperErrorV1::NamespaceNameEncoding)?;
    validate_namespace_root(namespace_root)?;
    validate_namespace_name(namespace_name)?;
    Ok(DecodedNetnsRequestV1 {
        operation,
        namespace_root: namespace_root.to_owned(),
        namespace_name: namespace_name.to_owned(),
        expected_device,
        expected_inode,
        request_sha256: sha256(request),
    })
}

fn require_fixed_header(request: &[u8]) -> Result<(), NetnsHelperErrorV1> {
    if request.len() != REQUEST_BYTES_V1 {
        return Err(NetnsHelperErrorV1::RequestSize);
    }
    if request[0..16] != REQUEST_MAGIC_V1 {
        return Err(NetnsHelperErrorV1::RequestMagic);
    }
    let version = read_u16(request, 16)?;
    if version != PROTOCOL_VERSION_V1 {
        return Err(NetnsHelperErrorV1::RequestVersion(version));
    }
    Ok(())
}

fn require_zero_control_fields(request: &[u8]) -> Result<(), NetnsHelperErrorV1> {
    if read_u32(request, REQUEST_FLAGS_OFFSET_V1)? != 0 {
        return Err(NetnsHelperErrorV1::RequestFlags);
    }
    if read_u32(request, REQUEST_TRUSTED_UID_OFFSET_V1)? != 0 {
        return Err(NetnsHelperErrorV1::TrustedUid);
    }
    Ok(())
}

fn require_lengths(root_length: usize, name_length: usize) -> Result<(), NetnsHelperErrorV1> {
    if root_length == 0 || root_length > REQUEST_ROOT_BYTES_V1 {
        return Err(NetnsHelperErrorV1::NamespaceRootLength);
    }
    if !(8..=REQUEST_NAME_BYTES_V1).contains(&name_length) {
        return Err(NetnsHelperErrorV1::NamespaceNameLength);
    }
    Ok(())
}

fn require_canonical_tail_bytes(
    request: &[u8],
    root_slot: &[u8],
    name_slot: &[u8],
    root_length: usize,
    name_length: usize,
) -> Result<(), NetnsHelperErrorV1> {
    if root_slot[root_length..].iter().any(|byte| *byte != 0) {
        return Err(NetnsHelperErrorV1::NamespaceRootPadding);
    }
    if name_slot[name_length..].iter().any(|byte| *byte != 0) {
        return Err(NetnsHelperErrorV1::NamespaceNamePadding);
    }
    if request[REQUEST_RESERVED_OFFSET_V1..REQUEST_DIGEST_OFFSET_V1]
        .iter()
        .any(|byte| *byte != 0)
    {
        return Err(NetnsHelperErrorV1::RequestReserved);
    }
    let expected_digest = sha256(&request[..REQUEST_DIGEST_OFFSET_V1]);
    if request[REQUEST_DIGEST_OFFSET_V1..] != expected_digest {
        return Err(NetnsHelperErrorV1::RequestDigest);
    }
    Ok(())
}

fn validate_identity(
    operation: NetnsOperationV1,
    device: u64,
    inode: u64,
) -> Result<(), NetnsHelperErrorV1> {
    let both_zero = device == 0 && inode == 0;
    let both_present = device != 0 && inode != 0;
    match operation {
        NetnsOperationV1::Create | NetnsOperationV1::Cleanup if !both_zero => {
            Err(NetnsHelperErrorV1::UnexpectedIdentity)
        }
        NetnsOperationV1::Inspect | NetnsOperationV1::Destroy if !both_present => {
            Err(NetnsHelperErrorV1::MissingIdentity)
        }
        NetnsOperationV1::Absence if !both_zero && !both_present => {
            Err(NetnsHelperErrorV1::MissingIdentity)
        }
        _ => Ok(()),
    }
}

fn validate_namespace_root(value: &str) -> Result<(), NetnsHelperErrorV1> {
    if value.len() > REQUEST_ROOT_BYTES_V1 || !value.is_ascii() || value == "/" {
        return Err(NetnsHelperErrorV1::NamespaceRootCanonical);
    }
    if !value.starts_with('/') || value.ends_with('/') {
        return Err(NetnsHelperErrorV1::NamespaceRootCanonical);
    }
    if value[1..].split('/').any(|component| {
        component.is_empty()
            || component == "."
            || component == ".."
            || !component
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    }) {
        return Err(NetnsHelperErrorV1::NamespaceRootCanonical);
    }
    Ok(())
}

fn validate_namespace_name(value: &str) -> Result<(), NetnsHelperErrorV1> {
    let bytes = value.as_bytes();
    if !(8..=REQUEST_NAME_BYTES_V1).contains(&bytes.len())
        || !bytes[0].is_ascii_lowercase()
        || !bytes
            .iter()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || *byte == b'-')
    {
        return Err(NetnsHelperErrorV1::NamespaceNameCanonical);
    }
    Ok(())
}

fn read_u16(bytes: &[u8], offset: usize) -> Result<u16, NetnsHelperErrorV1> {
    let raw: [u8; 2] = bytes
        .get(offset..offset + 2)
        .ok_or(NetnsHelperErrorV1::RequestSize)?
        .try_into()
        .map_err(|_| NetnsHelperErrorV1::RequestSize)?;
    Ok(u16::from_be_bytes(raw))
}

fn read_u32(bytes: &[u8], offset: usize) -> Result<u32, NetnsHelperErrorV1> {
    let raw: [u8; 4] = bytes
        .get(offset..offset + 4)
        .ok_or(NetnsHelperErrorV1::RequestSize)?
        .try_into()
        .map_err(|_| NetnsHelperErrorV1::RequestSize)?;
    Ok(u32::from_be_bytes(raw))
}

fn read_u64(bytes: &[u8], offset: usize) -> Result<u64, NetnsHelperErrorV1> {
    let raw: [u8; 8] = bytes
        .get(offset..offset + 8)
        .ok_or(NetnsHelperErrorV1::RequestSize)?
        .try_into()
        .map_err(|_| NetnsHelperErrorV1::RequestSize)?;
    Ok(u64::from_be_bytes(raw))
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
