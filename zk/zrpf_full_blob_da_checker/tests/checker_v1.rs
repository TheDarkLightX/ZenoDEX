use zenodex_zrpf_full_blob_da_checker_v1::{
    check_request_bytes_v1, encode_checker_request_v1, FullBlobDaCheckerErrorV1,
    FullBlobDaCheckerRequestInputV1, REQUEST_HEADER_BYTES_V1, RESPONSE_BYTES_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_full_blob_da_certificate_v1, ApplicationIdV3, CommitmentV3, DomainIdV3,
    FullBlobDataAvailabilityCertificateInputV1, FullBlobDataAvailabilityCertificateV1,
    LocalFullBlobPolicyInputV1, LocalFullBlobPolicyV1,
};

fn application_id(seed: u8) -> ApplicationIdV3 {
    ApplicationIdV3::new([seed; 32]).unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn domain_id(seed: u8) -> DomainIdV3 {
    DomainIdV3::new([seed; 32]).unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed; 32]).unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn policy() -> LocalFullBlobPolicyV1 {
    LocalFullBlobPolicyV1::new(LocalFullBlobPolicyInputV1 {
        application_id: application_id(1),
        chain_or_domain_id: domain_id(2),
        data_schema_id: commitment(3),
        expected_storage_policy_hash: commitment(4),
        minimum_retention_epochs: 20,
        minimum_remaining_epochs: 5,
        maximum_blob_bytes: 1_048_576,
    })
    .unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn certificate(blob: &[u8]) -> FullBlobDataAvailabilityCertificateV1 {
    FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
        application_id: application_id(1),
        chain_or_domain_id: domain_id(2),
        epoch_id: 40,
        data_schema_id: commitment(3),
        blob,
        retention_through_epoch: 65,
        storage_policy_hash: commitment(4),
    })
    .unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn request(blob: &[u8]) -> Vec<u8> {
    let policy = policy();
    let certificate = certificate(blob);
    let certificate_bytes = encode_full_blob_da_certificate_v1(&certificate)
        .unwrap_or_else(|error| panic!("fixture rejected: {error}"));
    encode_checker_request_v1(FullBlobDaCheckerRequestInputV1 {
        policy: &policy,
        expected_certificate_epoch: 40,
        checked_epoch: 52,
        exact_certificate_bytes: &certificate_bytes,
        exact_blob_bytes: blob,
    })
    .unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

#[test]
fn exact_request_runs_the_protocol_checker_and_emits_fixed_response() {
    let blob = b"exact governed full-blob DA bytes\x00\xff";
    let request = request(blob);

    let first = check_request_bytes_v1(&request)
        .unwrap_or_else(|error| panic!("valid request rejected: {error}"));
    let second = check_request_bytes_v1(&request)
        .unwrap_or_else(|error| panic!("valid request rejected: {error}"));

    assert_eq!(first.len(), RESPONSE_BYTES_V1);
    assert_eq!(first, second);
}

#[test]
fn every_blob_byte_mutation_rejects_against_the_exact_certificate() {
    let blob = b"exact governed full-blob DA bytes\x00\xff";
    let request = request(blob);
    let blob_start = request.len() - blob.len();

    for index in blob_start..request.len() {
        let mut mutated = request.clone();
        mutated[index] ^= 1;
        assert_eq!(
            check_request_bytes_v1(&mutated),
            Err(FullBlobDaCheckerErrorV1::PolicyRejected),
            "mutation at byte {index} was accepted"
        );
    }
}

#[test]
fn framing_truncation_extension_and_unknown_magic_reject() {
    let request = request(b"bounded blob");
    for length in 0..REQUEST_HEADER_BYTES_V1 {
        assert!(check_request_bytes_v1(&request[..length]).is_err());
    }
    let mut extended = request.clone();
    extended.push(0);
    assert_eq!(
        check_request_bytes_v1(&extended),
        Err(FullBlobDaCheckerErrorV1::RequestSize)
    );
    let mut wrong_magic = request;
    wrong_magic[0] ^= 1;
    assert_eq!(
        check_request_bytes_v1(&wrong_magic),
        Err(FullBlobDaCheckerErrorV1::RequestMagic)
    );
}

#[test]
fn checked_epoch_that_exhausts_remaining_retention_rejects() {
    let mut request = request(b"bounded blob");
    let checked_epoch_offset = 178;
    request[checked_epoch_offset..checked_epoch_offset + 8].copy_from_slice(&65_u64.to_be_bytes());

    assert_eq!(
        check_request_bytes_v1(&request),
        Err(FullBlobDaCheckerErrorV1::PolicyRejected)
    );
}
