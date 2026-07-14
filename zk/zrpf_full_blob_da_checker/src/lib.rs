use core::fmt;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    check_local_full_blob_policy_satisfied_v1, decode_exact_full_blob_da_certificate_v1,
    ApplicationIdV3, CommitmentV3, DomainIdV3, LocalFullBlobPolicyCheckInputV1,
    LocalFullBlobPolicyInputV1, LocalFullBlobPolicyV1, MAX_FULL_BLOB_DA_BYTES_V1,
    MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
};

pub const CHECKER_PROTOCOL_VERSION_V1: u16 = 1;
pub const REQUEST_MAGIC_V1: [u8; 16] = *b"ZRPFFBDAREQV1!!!";
pub const RESPONSE_MAGIC_V1: [u8; 16] = *b"ZRPFFBDARESV1!!!";
pub const REQUEST_HEADER_BYTES_V1: usize = 198;
pub const RESPONSE_BODY_BYTES_V1: usize = 298;
pub const RESPONSE_BYTES_V1: usize = RESPONSE_BODY_BYTES_V1 + 32;
pub const MAX_CHECKER_REQUEST_BYTES_V1: usize =
    REQUEST_HEADER_BYTES_V1 + MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1 + MAX_FULL_BLOB_DA_BYTES_V1;

const RESPONSE_COMMITMENT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.full_blob_da_checker.response_commitment.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FullBlobDaCheckerErrorV1 {
    RequestSize,
    RequestMagic,
    RequestVersion(u16),
    InvalidTypedField(&'static str),
    CertificateLength,
    BlobLength,
    ArithmeticOverflow,
    CertificateRejected,
    PolicyRejected,
    ResponseEncoding,
}

impl fmt::Display for FullBlobDaCheckerErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RequestSize => formatter.write_str("full-blob checker request size rejected"),
            Self::RequestMagic => formatter.write_str("full-blob checker request magic rejected"),
            Self::RequestVersion(version) => {
                write!(
                    formatter,
                    "full-blob checker request version {version} rejected"
                )
            }
            Self::InvalidTypedField(field) => {
                write!(formatter, "full-blob checker typed field rejected: {field}")
            }
            Self::CertificateLength => {
                formatter.write_str("full-blob checker certificate length rejected")
            }
            Self::BlobLength => formatter.write_str("full-blob checker blob length rejected"),
            Self::ArithmeticOverflow => {
                formatter.write_str("full-blob checker request arithmetic overflow")
            }
            Self::CertificateRejected => {
                formatter.write_str("full-blob checker certificate rejected")
            }
            Self::PolicyRejected => formatter.write_str("full-blob checker policy rejected"),
            Self::ResponseEncoding => {
                formatter.write_str("full-blob checker response encoding rejected")
            }
        }
    }
}

pub struct FullBlobDaCheckerRequestInputV1<'a> {
    pub policy: &'a LocalFullBlobPolicyV1,
    pub expected_certificate_epoch: u64,
    pub checked_epoch: u64,
    pub exact_certificate_bytes: &'a [u8],
    pub exact_blob_bytes: &'a [u8],
}

struct DecodedCheckerRequestV1<'a> {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    data_schema_id: CommitmentV3,
    expected_storage_policy_hash: CommitmentV3,
    minimum_retention_epochs: u64,
    minimum_remaining_epochs: u64,
    maximum_blob_bytes: u64,
    expected_certificate_epoch: u64,
    checked_epoch: u64,
    certificate_bytes: &'a [u8],
    blob_bytes: &'a [u8],
}

pub fn encode_checker_request_v1(
    input: FullBlobDaCheckerRequestInputV1<'_>,
) -> Result<Vec<u8>, FullBlobDaCheckerErrorV1> {
    let certificate_length = u32::try_from(input.exact_certificate_bytes.len())
        .map_err(|_| FullBlobDaCheckerErrorV1::CertificateLength)?;
    let blob_length = u64::try_from(input.exact_blob_bytes.len())
        .map_err(|_| FullBlobDaCheckerErrorV1::BlobLength)?;
    require_declared_lengths(
        usize::try_from(certificate_length)
            .map_err(|_| FullBlobDaCheckerErrorV1::CertificateLength)?,
        usize::try_from(blob_length).map_err(|_| FullBlobDaCheckerErrorV1::BlobLength)?,
    )?;
    let capacity = REQUEST_HEADER_BYTES_V1
        .checked_add(input.exact_certificate_bytes.len())
        .and_then(|value| value.checked_add(input.exact_blob_bytes.len()))
        .ok_or(FullBlobDaCheckerErrorV1::ArithmeticOverflow)?;
    let mut request = Vec::with_capacity(capacity);
    request.extend_from_slice(&REQUEST_MAGIC_V1);
    request.extend_from_slice(&CHECKER_PROTOCOL_VERSION_V1.to_be_bytes());
    request.extend_from_slice(input.policy.application_id().as_bytes());
    request.extend_from_slice(input.policy.chain_or_domain_id().as_bytes());
    request.extend_from_slice(input.policy.data_schema_id().as_bytes());
    request.extend_from_slice(input.policy.expected_storage_policy_hash().as_bytes());
    request.extend_from_slice(&input.policy.minimum_retention_epochs().to_be_bytes());
    request.extend_from_slice(&input.policy.minimum_remaining_epochs().to_be_bytes());
    request.extend_from_slice(&input.policy.maximum_blob_bytes().to_be_bytes());
    request.extend_from_slice(&input.expected_certificate_epoch.to_be_bytes());
    request.extend_from_slice(&input.checked_epoch.to_be_bytes());
    request.extend_from_slice(&certificate_length.to_be_bytes());
    request.extend_from_slice(&blob_length.to_be_bytes());
    request.extend_from_slice(input.exact_certificate_bytes);
    request.extend_from_slice(input.exact_blob_bytes);
    if request.len() != capacity {
        return Err(FullBlobDaCheckerErrorV1::RequestSize);
    }
    Ok(request)
}

pub fn check_request_bytes_v1(
    request: &[u8],
) -> Result<[u8; RESPONSE_BYTES_V1], FullBlobDaCheckerErrorV1> {
    let decoded = decode_checker_request_v1(request)?;
    let policy = LocalFullBlobPolicyV1::new(LocalFullBlobPolicyInputV1 {
        application_id: decoded.application_id,
        chain_or_domain_id: decoded.chain_or_domain_id,
        data_schema_id: decoded.data_schema_id,
        expected_storage_policy_hash: decoded.expected_storage_policy_hash,
        minimum_retention_epochs: decoded.minimum_retention_epochs,
        minimum_remaining_epochs: decoded.minimum_remaining_epochs,
        maximum_blob_bytes: decoded.maximum_blob_bytes,
    })
    .map_err(|_| FullBlobDaCheckerErrorV1::PolicyRejected)?;
    let certificate = decode_exact_full_blob_da_certificate_v1(decoded.certificate_bytes)
        .map_err(|_| FullBlobDaCheckerErrorV1::CertificateRejected)?;
    check_local_full_blob_policy_satisfied_v1(LocalFullBlobPolicyCheckInputV1 {
        policy: &policy,
        certificate: &certificate,
        blob: decoded.blob_bytes,
        expected_certificate_epoch: decoded.expected_certificate_epoch,
        checked_epoch: decoded.checked_epoch,
    })
    .map_err(|_| FullBlobDaCheckerErrorV1::PolicyRejected)?;
    let policy_root = policy
        .policy_root()
        .map_err(|_| FullBlobDaCheckerErrorV1::PolicyRejected)?;
    encode_response_v1(CheckedResponseFieldsV1 {
        application_id: policy.application_id().into_bytes(),
        chain_or_domain_id: policy.chain_or_domain_id().into_bytes(),
        epoch_id: certificate.epoch_id(),
        certificate_root: certificate.certificate_root().into_bytes(),
        data_root: certificate.data_root().into_bytes(),
        policy_root: policy_root.into_bytes(),
        exact_blob_sha256: sha256(decoded.blob_bytes),
        exact_certificate_sha256: sha256(decoded.certificate_bytes),
        checked_epoch: decoded.checked_epoch,
        retention_through_epoch: certificate.retention_through_epoch(),
        request_sha256: sha256(request),
    })
}

fn decode_checker_request_v1(
    request: &[u8],
) -> Result<DecodedCheckerRequestV1<'_>, FullBlobDaCheckerErrorV1> {
    if request.len() < REQUEST_HEADER_BYTES_V1 || request.len() > MAX_CHECKER_REQUEST_BYTES_V1 {
        return Err(FullBlobDaCheckerErrorV1::RequestSize);
    }
    let mut cursor = RequestCursorV1::new(request);
    if cursor.take_array::<16>()? != REQUEST_MAGIC_V1 {
        return Err(FullBlobDaCheckerErrorV1::RequestMagic);
    }
    let version = cursor.take_u16()?;
    if version != CHECKER_PROTOCOL_VERSION_V1 {
        return Err(FullBlobDaCheckerErrorV1::RequestVersion(version));
    }
    let application_id = ApplicationIdV3::new(cursor.take_array::<32>()?)
        .map_err(|_| FullBlobDaCheckerErrorV1::InvalidTypedField("application_id"))?;
    let chain_or_domain_id = DomainIdV3::new(cursor.take_array::<32>()?)
        .map_err(|_| FullBlobDaCheckerErrorV1::InvalidTypedField("chain_or_domain_id"))?;
    let data_schema_id = CommitmentV3::new(cursor.take_array::<32>()?)
        .map_err(|_| FullBlobDaCheckerErrorV1::InvalidTypedField("data_schema_id"))?;
    let expected_storage_policy_hash = CommitmentV3::new(cursor.take_array::<32>()?)
        .map_err(|_| FullBlobDaCheckerErrorV1::InvalidTypedField("storage_policy_hash"))?;
    let minimum_retention_epochs = cursor.take_u64()?;
    let minimum_remaining_epochs = cursor.take_u64()?;
    let maximum_blob_bytes = cursor.take_u64()?;
    let expected_certificate_epoch = cursor.take_u64()?;
    let checked_epoch = cursor.take_u64()?;
    let certificate_length = usize::try_from(cursor.take_u32()?)
        .map_err(|_| FullBlobDaCheckerErrorV1::CertificateLength)?;
    let blob_length =
        usize::try_from(cursor.take_u64()?).map_err(|_| FullBlobDaCheckerErrorV1::BlobLength)?;
    require_declared_lengths(certificate_length, blob_length)?;
    let expected_length = REQUEST_HEADER_BYTES_V1
        .checked_add(certificate_length)
        .and_then(|value| value.checked_add(blob_length))
        .ok_or(FullBlobDaCheckerErrorV1::ArithmeticOverflow)?;
    if request.len() != expected_length {
        return Err(FullBlobDaCheckerErrorV1::RequestSize);
    }
    let certificate_bytes = cursor.take_slice(certificate_length)?;
    let blob_bytes = cursor.take_slice(blob_length)?;
    if !cursor.is_finished() {
        return Err(FullBlobDaCheckerErrorV1::RequestSize);
    }
    Ok(DecodedCheckerRequestV1 {
        application_id,
        chain_or_domain_id,
        data_schema_id,
        expected_storage_policy_hash,
        minimum_retention_epochs,
        minimum_remaining_epochs,
        maximum_blob_bytes,
        expected_certificate_epoch,
        checked_epoch,
        certificate_bytes,
        blob_bytes,
    })
}

fn require_declared_lengths(
    certificate_length: usize,
    blob_length: usize,
) -> Result<(), FullBlobDaCheckerErrorV1> {
    if certificate_length == 0 || certificate_length > MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1 {
        return Err(FullBlobDaCheckerErrorV1::CertificateLength);
    }
    if blob_length == 0 || blob_length > MAX_FULL_BLOB_DA_BYTES_V1 {
        return Err(FullBlobDaCheckerErrorV1::BlobLength);
    }
    Ok(())
}

struct CheckedResponseFieldsV1 {
    application_id: [u8; 32],
    chain_or_domain_id: [u8; 32],
    epoch_id: u64,
    certificate_root: [u8; 32],
    data_root: [u8; 32],
    policy_root: [u8; 32],
    exact_blob_sha256: [u8; 32],
    exact_certificate_sha256: [u8; 32],
    checked_epoch: u64,
    retention_through_epoch: u64,
    request_sha256: [u8; 32],
}

fn encode_response_v1(
    fields: CheckedResponseFieldsV1,
) -> Result<[u8; RESPONSE_BYTES_V1], FullBlobDaCheckerErrorV1> {
    let mut response = [0_u8; RESPONSE_BYTES_V1];
    let mut cursor = 0;
    append(&mut response, &mut cursor, &RESPONSE_MAGIC_V1)?;
    append(
        &mut response,
        &mut cursor,
        &CHECKER_PROTOCOL_VERSION_V1.to_be_bytes(),
    )?;
    append(&mut response, &mut cursor, &fields.application_id)?;
    append(&mut response, &mut cursor, &fields.chain_or_domain_id)?;
    append(&mut response, &mut cursor, &fields.epoch_id.to_be_bytes())?;
    append(&mut response, &mut cursor, &fields.certificate_root)?;
    append(&mut response, &mut cursor, &fields.data_root)?;
    append(&mut response, &mut cursor, &fields.policy_root)?;
    append(&mut response, &mut cursor, &fields.exact_blob_sha256)?;
    append(&mut response, &mut cursor, &fields.exact_certificate_sha256)?;
    append(
        &mut response,
        &mut cursor,
        &fields.checked_epoch.to_be_bytes(),
    )?;
    append(
        &mut response,
        &mut cursor,
        &fields.retention_through_epoch.to_be_bytes(),
    )?;
    append(&mut response, &mut cursor, &fields.request_sha256)?;
    if cursor != RESPONSE_BODY_BYTES_V1 {
        return Err(FullBlobDaCheckerErrorV1::ResponseEncoding);
    }
    let body = response
        .get(..RESPONSE_BODY_BYTES_V1)
        .ok_or(FullBlobDaCheckerErrorV1::ResponseEncoding)?;
    let commitment = response_commitment_v1(body);
    append(&mut response, &mut cursor, &commitment)?;
    if cursor != RESPONSE_BYTES_V1 {
        return Err(FullBlobDaCheckerErrorV1::ResponseEncoding);
    }
    Ok(response)
}

fn append(
    output: &mut [u8; RESPONSE_BYTES_V1],
    cursor: &mut usize,
    value: &[u8],
) -> Result<(), FullBlobDaCheckerErrorV1> {
    let end = cursor
        .checked_add(value.len())
        .ok_or(FullBlobDaCheckerErrorV1::ResponseEncoding)?;
    let target = output
        .get_mut(*cursor..end)
        .ok_or(FullBlobDaCheckerErrorV1::ResponseEncoding)?;
    target.copy_from_slice(value);
    *cursor = end;
    Ok(())
}

fn sha256(value: &[u8]) -> [u8; 32] {
    Sha256::digest(value).into()
}

fn response_commitment_v1(value: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(RESPONSE_COMMITMENT_DOMAIN_V1);
    hasher.update(value);
    hasher.finalize().into()
}

struct RequestCursorV1<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> RequestCursorV1<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take_array<const N: usize>(&mut self) -> Result<[u8; N], FullBlobDaCheckerErrorV1> {
        let value = self.take_slice(N)?;
        value
            .try_into()
            .map_err(|_| FullBlobDaCheckerErrorV1::RequestSize)
    }

    fn take_u16(&mut self) -> Result<u16, FullBlobDaCheckerErrorV1> {
        Ok(u16::from_be_bytes(self.take_array::<2>()?))
    }

    fn take_u32(&mut self) -> Result<u32, FullBlobDaCheckerErrorV1> {
        Ok(u32::from_be_bytes(self.take_array::<4>()?))
    }

    fn take_u64(&mut self) -> Result<u64, FullBlobDaCheckerErrorV1> {
        Ok(u64::from_be_bytes(self.take_array::<8>()?))
    }

    fn take_slice(&mut self, length: usize) -> Result<&'a [u8], FullBlobDaCheckerErrorV1> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(FullBlobDaCheckerErrorV1::ArithmeticOverflow)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(FullBlobDaCheckerErrorV1::RequestSize)?;
        self.offset = end;
        Ok(value)
    }

    fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}
