use std::io::Write;
use std::process::{Command, Output, Stdio};

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    encode_full_blob_da_certificate_v1, ApplicationIdV3, CommitmentV3, DomainIdV3,
    FullBlobDataAvailabilityCertificateInputV1, FullBlobDataAvailabilityCertificateV1,
    LocalFullBlobPolicyInputV1, LocalFullBlobPolicyV1,
};

const REQUEST_MAGIC: &[u8; 8] = b"ZDAREQ1\0";
const RESPONSE_MAGIC: &[u8; 8] = b"ZDAOK1\0\0";
const BINARY: &str = env!("CARGO_BIN_EXE_zrpf-full-blob-da-policy-verifier-v1");

fn bytes32(seed: u8) -> [u8; 32] {
    [seed; 32]
}

struct Fixture {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    data_schema_id: CommitmentV3,
    storage_policy_hash: CommitmentV3,
    certificate: FullBlobDataAvailabilityCertificateV1,
    certificate_bytes: Vec<u8>,
    blob: Vec<u8>,
    policy: LocalFullBlobPolicyV1,
}

fn fixture() -> Fixture {
    let application_id = ApplicationIdV3::new(bytes32(1)).expect("application ID");
    let chain_or_domain_id = DomainIdV3::new(bytes32(2)).expect("domain ID");
    let data_schema_id = CommitmentV3::new(bytes32(3)).expect("data schema ID");
    let storage_policy_hash = CommitmentV3::new(bytes32(4)).expect("storage policy");
    let blob = b"exact full-blob DA verifier fixture".to_vec();
    let certificate = FullBlobDataAvailabilityCertificateV1::derive(
        FullBlobDataAvailabilityCertificateInputV1 {
            application_id,
            chain_or_domain_id,
            epoch_id: 50,
            data_schema_id,
            blob: &blob,
            retention_through_epoch: 200,
            storage_policy_hash,
        },
    )
    .expect("certificate");
    let certificate_bytes =
        encode_full_blob_da_certificate_v1(&certificate).expect("certificate bytes");
    let policy = LocalFullBlobPolicyV1::new(LocalFullBlobPolicyInputV1 {
        application_id,
        chain_or_domain_id,
        data_schema_id,
        expected_storage_policy_hash: storage_policy_hash,
        minimum_retention_epochs: 100,
        minimum_remaining_epochs: 25,
        maximum_blob_bytes: 8 * 1024 * 1024,
    })
    .expect("policy");
    Fixture {
        application_id,
        chain_or_domain_id,
        data_schema_id,
        storage_policy_hash,
        certificate,
        certificate_bytes,
        blob,
        policy,
    }
}

fn request(
    fixture: &Fixture,
    checked_epoch: u64,
    storage_policy_hash: CommitmentV3,
    blob: &[u8],
) -> Vec<u8> {
    let certificate_length =
        u32::try_from(fixture.certificate_bytes.len()).expect("certificate len");
    let blob_length = u32::try_from(blob.len()).expect("blob len");
    let mut request = Vec::new();
    request.extend_from_slice(REQUEST_MAGIC);
    request.extend_from_slice(&1u16.to_be_bytes());
    request.extend_from_slice(fixture.application_id.as_bytes());
    request.extend_from_slice(fixture.chain_or_domain_id.as_bytes());
    request.extend_from_slice(fixture.data_schema_id.as_bytes());
    request.extend_from_slice(storage_policy_hash.as_bytes());
    request.extend_from_slice(&100u64.to_be_bytes());
    request.extend_from_slice(&25u64.to_be_bytes());
    request.extend_from_slice(&(8u64 * 1024 * 1024).to_be_bytes());
    request.extend_from_slice(&fixture.certificate.epoch_id().to_be_bytes());
    request.extend_from_slice(&checked_epoch.to_be_bytes());
    request.extend_from_slice(&certificate_length.to_be_bytes());
    request.extend_from_slice(&blob_length.to_be_bytes());
    request.extend_from_slice(&fixture.certificate_bytes);
    request.extend_from_slice(blob);
    request
}

fn execute(request: &[u8]) -> Output {
    let mut child = Command::new(BINARY)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn verifier");
    child
        .stdin
        .take()
        .expect("verifier stdin")
        .write_all(request)
        .expect("write verifier request");
    child.wait_with_output().expect("wait for verifier")
}

#[test]
fn exact_policy_and_blob_emit_canonical_fixed_response() {
    let fixture = fixture();
    let output = execute(&request(
        &fixture,
        75,
        fixture.storage_policy_hash,
        &fixture.blob,
    ));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    assert_eq!(output.stdout.len(), 160);
    assert_eq!(&output.stdout[..8], RESPONSE_MAGIC);

    let expected_blob_sha256: [u8; 32] = Sha256::digest(&fixture.blob).into();
    assert_eq!(
        &output.stdout[8..40],
        fixture.policy.policy_root().unwrap().as_bytes()
    );
    assert_eq!(
        &output.stdout[40..72],
        fixture.certificate.certificate_root().as_bytes()
    );
    assert_eq!(
        &output.stdout[72..104],
        fixture.certificate.data_root().as_bytes()
    );
    assert_eq!(&output.stdout[104..136], &expected_blob_sha256);
    assert_eq!(&output.stdout[136..144], &50u64.to_be_bytes());
    assert_eq!(&output.stdout[144..152], &75u64.to_be_bytes());
    assert_eq!(&output.stdout[152..160], &200u64.to_be_bytes());
}

#[test]
fn coherent_certificate_with_mutated_blob_rejects() {
    let fixture = fixture();
    let mut blob = fixture.blob.clone();
    blob[0] ^= 1;
    let output = execute(&request(
        &fixture,
        75,
        fixture.storage_policy_hash,
        &blob,
    ));
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("ZRPF_DA_POLICY_REJECTED"));
}

#[test]
fn wrong_storage_policy_and_early_check_reject() {
    let fixture = fixture();
    let wrong_storage = CommitmentV3::new(bytes32(9)).expect("wrong storage policy");
    for candidate in [
        request(&fixture, 75, wrong_storage, &fixture.blob),
        request(
            &fixture,
            49,
            fixture.storage_policy_hash,
            &fixture.blob,
        ),
    ] {
        let output = execute(&candidate);
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn framing_mutations_reject() {
    let fixture = fixture();
    let baseline = request(
        &fixture,
        75,
        fixture.storage_policy_hash,
        &fixture.blob,
    );
    let mut wrong_magic = baseline.clone();
    wrong_magic[0] ^= 1;
    let mut wrong_version = baseline.clone();
    wrong_version[9] = 2;
    let mut trailing = baseline.clone();
    trailing.push(0);
    let truncated = baseline[..baseline.len() - 1].to_vec();

    for candidate in [wrong_magic, wrong_version, trailing, truncated] {
        let output = execute(&candidate);
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
    }
}
