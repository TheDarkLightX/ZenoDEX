use std::io::{Read, Write};

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    check_local_full_blob_policy_satisfied_v1, decode_exact_full_blob_da_certificate_v1,
    ApplicationIdV3, CommitmentV3, DomainIdV3, LocalFullBlobPolicyCheckInputV1,
    LocalFullBlobPolicyInputV1, LocalFullBlobPolicyV1, MAX_FULL_BLOB_DA_BYTES_V1,
    MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
};

const REQUEST_MAGIC: &[u8; 8] = b"ZDAREQ1\0";
const RESPONSE_MAGIC: &[u8; 8] = b"ZDAOK1\0\0";
const REQUEST_VERSION: u16 = 1;
const REQUEST_FIXED_BYTES: usize = 8 + 2 + (4 * 32) + (5 * 8) + (2 * 4);
const MAX_REQUEST_BYTES: usize =
    REQUEST_FIXED_BYTES + MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1 + MAX_FULL_BLOB_DA_BYTES_V1;
const RESPONSE_BYTES: usize = 8 + (4 * 32) + (3 * 8);

fn main() {
    if let Err(error) = run() {
        let _ = writeln!(std::io::stderr(), "ZRPF_DA_POLICY_REJECTED: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let request = read_bounded_stdin()?;
    let response = verify_request(&request)?;
    if response.len() != RESPONSE_BYTES {
        return Err("internal response length mismatch".to_string());
    }
    std::io::stdout()
        .write_all(&response)
        .map_err(|error| format!("stdout write failed: {error}"))?;
    Ok(())
}

fn read_bounded_stdin() -> Result<Vec<u8>, String> {
    let limit = u64::try_from(MAX_REQUEST_BYTES + 1)
        .map_err(|_| "request byte limit conversion failed".to_string())?;
    let mut request = Vec::new();
    std::io::stdin()
        .take(limit)
        .read_to_end(&mut request)
        .map_err(|error| format!("stdin read failed: {error}"))?;
    if request.len() > MAX_REQUEST_BYTES {
        return Err("request exceeds the bounded byte limit".to_string());
    }
    if request.len() < REQUEST_FIXED_BYTES {
        return Err("request is truncated".to_string());
    }
    Ok(request)
}

fn verify_request(request: &[u8]) -> Result<Vec<u8>, String> {
    let mut cursor = 0usize;
    if take_array::<8>(request, &mut cursor)? != *REQUEST_MAGIC {
        return Err("request magic mismatch".to_string());
    }
    if read_u16(request, &mut cursor)? != REQUEST_VERSION {
        return Err("request version mismatch".to_string());
    }

    let application_id = ApplicationIdV3::new(take_array::<32>(request, &mut cursor)?)
        .map_err(|error| format!("application ID rejected: {error}"))?;
    let chain_or_domain_id = DomainIdV3::new(take_array::<32>(request, &mut cursor)?)
        .map_err(|error| format!("domain ID rejected: {error}"))?;
    let data_schema_id = CommitmentV3::new(take_array::<32>(request, &mut cursor)?)
        .map_err(|error| format!("data schema ID rejected: {error}"))?;
    let expected_storage_policy_hash =
        CommitmentV3::new(take_array::<32>(request, &mut cursor)?)
            .map_err(|error| format!("storage policy hash rejected: {error}"))?;
    let minimum_retention_epochs = read_u64(request, &mut cursor)?;
    let minimum_remaining_epochs = read_u64(request, &mut cursor)?;
    let maximum_blob_bytes = read_u64(request, &mut cursor)?;
    let expected_certificate_epoch = read_u64(request, &mut cursor)?;
    let checked_epoch = read_u64(request, &mut cursor)?;
    let certificate_length = usize::try_from(read_u32(request, &mut cursor)?)
        .map_err(|_| "certificate length conversion failed".to_string())?;
    let blob_length = usize::try_from(read_u32(request, &mut cursor)?)
        .map_err(|_| "blob length conversion failed".to_string())?;

    if certificate_length == 0 || certificate_length > MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1 {
        return Err("certificate length is outside the protocol bound".to_string());
    }
    if blob_length == 0 || blob_length > MAX_FULL_BLOB_DA_BYTES_V1 {
        return Err("blob length is outside the protocol bound".to_string());
    }
    let certificate_bytes = take_slice(request, &mut cursor, certificate_length)?;
    let blob = take_slice(request, &mut cursor, blob_length)?;
    if cursor != request.len() {
        return Err("request has trailing bytes".to_string());
    }

    let policy = LocalFullBlobPolicyV1::new(LocalFullBlobPolicyInputV1 {
        application_id,
        chain_or_domain_id,
        data_schema_id,
        expected_storage_policy_hash,
        minimum_retention_epochs,
        minimum_remaining_epochs,
        maximum_blob_bytes,
    })
    .map_err(|error| format!("local policy rejected: {error}"))?;
    let certificate = decode_exact_full_blob_da_certificate_v1(certificate_bytes)
        .map_err(|error| format!("certificate rejected: {error}"))?;
    check_local_full_blob_policy_satisfied_v1(LocalFullBlobPolicyCheckInputV1 {
        policy: &policy,
        certificate: &certificate,
        blob,
        expected_certificate_epoch,
        checked_epoch,
    })
    .map_err(|error| format!("policy check rejected: {error}"))?;

    let policy_root = policy
        .policy_root()
        .map_err(|error| format!("policy root rejected: {error}"))?;
    let blob_sha256: [u8; 32] = Sha256::digest(blob).into();
    let mut response = Vec::with_capacity(RESPONSE_BYTES);
    response.extend_from_slice(RESPONSE_MAGIC);
    response.extend_from_slice(policy_root.as_bytes());
    response.extend_from_slice(certificate.certificate_root().as_bytes());
    response.extend_from_slice(certificate.data_root().as_bytes());
    response.extend_from_slice(&blob_sha256);
    response.extend_from_slice(&certificate.epoch_id().to_be_bytes());
    response.extend_from_slice(&checked_epoch.to_be_bytes());
    response.extend_from_slice(&certificate.retention_through_epoch().to_be_bytes());
    Ok(response)
}

fn take_array<const N: usize>(input: &[u8], cursor: &mut usize) -> Result<[u8; N], String> {
    let bytes = take_slice(input, cursor, N)?;
    bytes
        .try_into()
        .map_err(|_| "fixed-width field conversion failed".to_string())
}

fn take_slice<'a>(input: &'a [u8], cursor: &mut usize, length: usize) -> Result<&'a [u8], String> {
    let end = cursor
        .checked_add(length)
        .ok_or_else(|| "request cursor overflow".to_string())?;
    let value = input
        .get(*cursor..end)
        .ok_or_else(|| "request is truncated".to_string())?;
    *cursor = end;
    Ok(value)
}

fn read_u16(input: &[u8], cursor: &mut usize) -> Result<u16, String> {
    Ok(u16::from_be_bytes(take_array::<2>(input, cursor)?))
}

fn read_u32(input: &[u8], cursor: &mut usize) -> Result<u32, String> {
    Ok(u32::from_be_bytes(take_array::<4>(input, cursor)?))
}

fn read_u64(input: &[u8], cursor: &mut usize) -> Result<u64, String> {
    Ok(u64::from_be_bytes(take_array::<8>(input, cursor)?))
}
