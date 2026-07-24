use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    check_local_full_blob_policy_satisfied_v1, decode_exact_full_blob_da_certificate_v1,
    encode_full_blob_da_certificate_v1, ApplicationIdV3, CommitmentV3, DomainIdV3,
    FullBlobDataAvailabilityCertificateInputV1, FullBlobDataAvailabilityCertificateV1,
    FullBlobDataAvailabilityErrorV1, LocalFullBlobPolicyCheckInputV1, LocalFullBlobPolicyErrorV1,
    LocalFullBlobPolicyInputV1, LocalFullBlobPolicyV1, FULL_BLOB_DA_CERTIFICATE_VERSION_V1,
    FULL_BLOB_DA_CHUNK_BYTES_V1, MAX_FULL_BLOB_DA_BYTES_V1, MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
};

const DATA_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.data_root.v1";
const CHUNK_HASH_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.chunk.v1";
const CHUNK_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.chunk_root.v1";
const CERTIFICATE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.certificate_root.v1";
const LOCAL_POLICY_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.local_full_blob_policy.root.v1";

fn application(byte: u8) -> ApplicationIdV3 {
    ApplicationIdV3::new([byte; 32]).expect("fixture application is nonzero")
}

fn domain(byte: u8) -> DomainIdV3 {
    DomainIdV3::new([byte; 32]).expect("fixture domain is nonzero")
}

fn commitment(byte: u8) -> CommitmentV3 {
    CommitmentV3::new([byte; 32]).expect("fixture commitment is nonzero")
}

fn certificate(blob: &[u8]) -> FullBlobDataAvailabilityCertificateV1 {
    certificate_with(
        blob,
        application(1),
        domain(2),
        7,
        commitment(3),
        100,
        commitment(4),
    )
}

fn certificate_with(
    blob: &[u8],
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    data_schema_id: CommitmentV3,
    retention_through_epoch: u64,
    storage_policy_hash: CommitmentV3,
) -> FullBlobDataAvailabilityCertificateV1 {
    FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
        application_id,
        chain_or_domain_id,
        epoch_id,
        data_schema_id,
        blob,
        retention_through_epoch,
        storage_policy_hash,
    })
    .expect("fixture certificate derives")
}

#[test]
fn certificate_root_separates_every_scope_and_policy_field() {
    let blob = b"scope separation fixture";
    let baseline = certificate(blob).certificate_root();
    for changed in [
        certificate_with(
            blob,
            application(9),
            domain(2),
            7,
            commitment(3),
            100,
            commitment(4),
        ),
        certificate_with(
            blob,
            application(1),
            domain(9),
            7,
            commitment(3),
            100,
            commitment(4),
        ),
        certificate_with(
            blob,
            application(1),
            domain(2),
            8,
            commitment(3),
            100,
            commitment(4),
        ),
        certificate_with(
            blob,
            application(1),
            domain(2),
            7,
            commitment(9),
            100,
            commitment(4),
        ),
        certificate_with(
            blob,
            application(1),
            domain(2),
            7,
            commitment(3),
            101,
            commitment(4),
        ),
        certificate_with(
            blob,
            application(1),
            domain(2),
            7,
            commitment(3),
            100,
            commitment(9),
        ),
    ] {
        assert_ne!(changed.certificate_root(), baseline);
    }
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(
        u16::try_from(domain.len())
            .expect("fixture domain length fits")
            .to_be_bytes(),
    );
    hasher.update(domain);
    hasher
}

fn independent_roots(blob: &[u8]) -> ([u8; 32], u32, [u8; 32]) {
    let mut data_hasher = domain_hasher(DATA_ROOT_DOMAIN_V1);
    data_hasher.update(
        u64::try_from(blob.len())
            .expect("fixture length fits")
            .to_be_bytes(),
    );
    data_hasher.update(blob);
    let chunk_size = usize::try_from(FULL_BLOB_DA_CHUNK_BYTES_V1).expect("chunk size fits");
    let chunk_count = u32::try_from(blob.len().div_ceil(chunk_size)).expect("chunk count fits");
    let mut root_hasher = domain_hasher(CHUNK_ROOT_DOMAIN_V1);
    root_hasher.update(chunk_count.to_be_bytes());
    for (index, chunk) in blob.chunks(chunk_size).enumerate() {
        let mut chunk_hasher = domain_hasher(CHUNK_HASH_DOMAIN_V1);
        chunk_hasher.update(
            u32::try_from(index)
                .expect("chunk index fits")
                .to_be_bytes(),
        );
        chunk_hasher.update(
            u32::try_from(chunk.len())
                .expect("chunk length fits")
                .to_be_bytes(),
        );
        chunk_hasher.update(chunk);
        root_hasher.update(chunk_hasher.finalize());
    }
    (
        data_hasher.finalize().into(),
        chunk_count,
        root_hasher.finalize().into(),
    )
}

fn independent_certificate_root(certificate: &FullBlobDataAvailabilityCertificateV1) -> [u8; 32] {
    let mut hasher = domain_hasher(CERTIFICATE_ROOT_DOMAIN_V1);
    hasher.update(certificate.certificate_version().to_be_bytes());
    hasher.update(certificate.application_id().as_bytes());
    hasher.update(certificate.chain_or_domain_id().as_bytes());
    hasher.update(certificate.epoch_id().to_be_bytes());
    hasher.update(certificate.data_schema_id().as_bytes());
    hasher.update(certificate.data_root().as_bytes());
    hasher.update(certificate.blob_length().to_be_bytes());
    hasher.update(certificate.chunk_size().to_be_bytes());
    hasher.update(certificate.chunk_count().to_be_bytes());
    hasher.update(certificate.chunk_root().as_bytes());
    hasher.update(certificate.retention_through_epoch().to_be_bytes());
    hasher.update(certificate.storage_policy_hash().as_bytes());
    hasher.finalize().into()
}

#[test]
fn certificate_matches_independent_data_chunk_and_certificate_preimages() {
    let blob = b"canonical ZRPF epoch data";
    let certificate = certificate(blob);
    let (data_root, chunk_count, chunk_root) = independent_roots(blob);
    assert_eq!(certificate.data_root().into_bytes(), data_root);
    assert_eq!(certificate.chunk_count(), chunk_count);
    assert_eq!(certificate.chunk_root().into_bytes(), chunk_root);
    assert_eq!(
        certificate.certificate_root().into_bytes(),
        independent_certificate_root(&certificate)
    );
}

#[test]
fn content_validation_rejects_every_single_byte_mutation() {
    let blob = (0u8..64).collect::<Vec<_>>();
    let certificate = certificate(&blob);
    let validated = certificate
        .validate_blob(&blob)
        .expect("exact blob validates");
    assert_eq!(validated.certificate(), &certificate);
    for index in 0..blob.len() {
        let mut mutated = blob.clone();
        mutated[index] ^= 1;
        assert_eq!(
            certificate.validate_blob(&mutated),
            Err(FullBlobDataAvailabilityErrorV1::DataRootMismatch)
        );
    }
}

#[test]
fn chunk_count_and_root_change_at_the_exact_boundary() {
    let one_chunk = vec![7; usize::try_from(FULL_BLOB_DA_CHUNK_BYTES_V1).expect("size fits")];
    let mut two_chunks = one_chunk.clone();
    two_chunks.push(8);
    let first = certificate(&one_chunk);
    let second = certificate(&two_chunks);
    assert_eq!(first.chunk_count(), 1);
    assert_eq!(second.chunk_count(), 2);
    assert_ne!(first.data_root(), second.data_root());
    assert_ne!(first.chunk_root(), second.chunk_root());
    assert_ne!(first.certificate_root(), second.certificate_root());
}

#[test]
fn empty_oversized_and_reversed_retention_reject_before_certificate_exists() {
    assert_eq!(
        FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
            application_id: application(1),
            chain_or_domain_id: domain(2),
            epoch_id: 7,
            data_schema_id: commitment(3),
            blob: &[],
            retention_through_epoch: 7,
            storage_policy_hash: commitment(4),
        }),
        Err(FullBlobDataAvailabilityErrorV1::EmptyBlob)
    );
    let oversized = vec![0; MAX_FULL_BLOB_DA_BYTES_V1 + 1];
    assert!(matches!(
        FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
            application_id: application(1),
            chain_or_domain_id: domain(2),
            epoch_id: 7,
            data_schema_id: commitment(3),
            blob: &oversized,
            retention_through_epoch: 7,
            storage_policy_hash: commitment(4),
        }),
        Err(FullBlobDataAvailabilityErrorV1::BlobTooLarge { .. })
    ));
    assert_eq!(
        FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
            application_id: application(1),
            chain_or_domain_id: domain(2),
            epoch_id: 7,
            data_schema_id: commitment(3),
            blob: b"data",
            retention_through_epoch: 6,
            storage_policy_hash: commitment(4),
        }),
        Err(FullBlobDataAvailabilityErrorV1::RetentionBeforeEpoch)
    );
}

#[test]
fn exact_maximum_blob_is_accepted_as_128_chunks() {
    let maximum = vec![5; MAX_FULL_BLOB_DA_BYTES_V1];
    let certificate = certificate(&maximum);
    assert_eq!(certificate.blob_length(), 8_388_608);
    assert_eq!(certificate.chunk_count(), 128);
    certificate
        .validate_blob(&maximum)
        .expect("exact maximum blob validates");
}

#[test]
fn exact_codec_round_trips_and_rejects_every_truncated_prefix() {
    let certificate = certificate(b"canonical full-blob replay data");
    let bytes = encode_full_blob_da_certificate_v1(&certificate).expect("certificate encodes");
    assert_eq!(
        decode_exact_full_blob_da_certificate_v1(&bytes).expect("certificate decodes"),
        certificate
    );
    for end in 0..bytes.len() {
        assert!(decode_exact_full_blob_da_certificate_v1(&bytes[..end]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_full_blob_da_certificate_v1(&trailing),
        Err(FullBlobDataAvailabilityErrorV1::TrailingBytes)
    );
    assert!(matches!(
        decode_exact_full_blob_da_certificate_v1(&vec![
            0;
            MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1 + 1
        ]),
        Err(FullBlobDataAvailabilityErrorV1::InputTooLarge { .. })
    ));
}

#[test]
fn wire_rejects_unknown_fields_and_incoherent_derived_values() {
    let certificate = certificate(b"wire fixture");
    let mut unknown = serde_json::to_value(&certificate).expect("certificate renders");
    unknown["unexpected"] = serde_json::json!(1);
    assert!(serde_json::from_value::<FullBlobDataAvailabilityCertificateV1>(unknown).is_err());

    let mut stale_version = serde_json::to_value(&certificate).expect("certificate renders");
    stale_version["certificate_version"] =
        serde_json::json!(FULL_BLOB_DA_CERTIFICATE_VERSION_V1 + 1);
    assert!(
        serde_json::from_value::<FullBlobDataAvailabilityCertificateV1>(stale_version).is_err()
    );

    let mut wrong_count = serde_json::to_value(&certificate).expect("certificate renders");
    wrong_count["chunk_count"] = serde_json::json!(2);
    assert!(serde_json::from_value::<FullBlobDataAvailabilityCertificateV1>(wrong_count).is_err());

    let mut wrong_root = serde_json::to_value(&certificate).expect("certificate renders");
    wrong_root["certificate_root"] = serde_json::json!(vec![99; 32]);
    assert!(serde_json::from_value::<FullBlobDataAvailabilityCertificateV1>(wrong_root).is_err());
}

#[test]
fn coherent_certificate_for_other_bytes_cannot_validate_the_expected_blob() {
    let expected = b"expected canonical epoch bytes";
    let alternate = b"alternate canonical data bytes";
    assert_eq!(expected.len(), alternate.len());
    let alternate_certificate = certificate(alternate);
    assert_eq!(
        alternate_certificate.validate_blob(expected),
        Err(FullBlobDataAvailabilityErrorV1::DataRootMismatch)
    );
}

fn local_policy_with(
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    data_schema_id: CommitmentV3,
    expected_storage_policy_hash: CommitmentV3,
    minimum_retention_epochs: u64,
    minimum_remaining_epochs: u64,
    maximum_blob_bytes: u64,
) -> LocalFullBlobPolicyV1 {
    LocalFullBlobPolicyV1::new(LocalFullBlobPolicyInputV1 {
        application_id,
        chain_or_domain_id,
        data_schema_id,
        expected_storage_policy_hash,
        minimum_retention_epochs,
        minimum_remaining_epochs,
        maximum_blob_bytes,
    })
    .expect("fixture local policy derives")
}

fn local_policy() -> LocalFullBlobPolicyV1 {
    local_policy_with(
        application(1),
        domain(2),
        commitment(3),
        commitment(4),
        20,
        5,
        1024,
    )
}

fn check_local_policy(
    policy: &LocalFullBlobPolicyV1,
    certificate: &FullBlobDataAvailabilityCertificateV1,
    blob: &[u8],
    expected_certificate_epoch: u64,
    checked_epoch: u64,
) -> Result<(), LocalFullBlobPolicyErrorV1> {
    check_local_full_blob_policy_satisfied_v1(LocalFullBlobPolicyCheckInputV1 {
        policy,
        certificate,
        blob,
        expected_certificate_epoch,
        checked_epoch,
    })
}

fn independent_local_policy_root(policy: &LocalFullBlobPolicyV1) -> [u8; 32] {
    let mut hasher = domain_hasher(LOCAL_POLICY_ROOT_DOMAIN_V1);
    hasher.update(policy.policy_version().to_be_bytes());
    hasher.update(policy.application_id().as_bytes());
    hasher.update(policy.chain_or_domain_id().as_bytes());
    hasher.update(policy.data_schema_id().as_bytes());
    hasher.update(policy.expected_storage_policy_hash().as_bytes());
    hasher.update(policy.minimum_retention_epochs().to_be_bytes());
    hasher.update(policy.minimum_remaining_epochs().to_be_bytes());
    hasher.update(policy.maximum_blob_bytes().to_be_bytes());
    hasher.finalize().into()
}

#[test]
fn local_policy_accepts_exact_present_blob_and_matches_independent_policy_root() {
    let blob = b"locally present governed replay blob";
    let certificate = certificate_with(
        blob,
        application(1),
        domain(2),
        7,
        commitment(3),
        30,
        commitment(4),
    );
    let policy = local_policy();

    check_local_policy(&policy, &certificate, blob, 7, 20)
        .expect("exact present blob satisfies the local policy");
    assert_eq!(
        policy.policy_root().unwrap().into_bytes(),
        independent_local_policy_root(&policy)
    );
}

#[test]
fn local_policy_root_separates_every_governed_field() {
    let baseline = local_policy().policy_root().unwrap();
    for changed in [
        local_policy_with(
            application(9),
            domain(2),
            commitment(3),
            commitment(4),
            20,
            5,
            1024,
        ),
        local_policy_with(
            application(1),
            domain(9),
            commitment(3),
            commitment(4),
            20,
            5,
            1024,
        ),
        local_policy_with(
            application(1),
            domain(2),
            commitment(9),
            commitment(4),
            20,
            5,
            1024,
        ),
        local_policy_with(
            application(1),
            domain(2),
            commitment(3),
            commitment(9),
            20,
            5,
            1024,
        ),
        local_policy_with(
            application(1),
            domain(2),
            commitment(3),
            commitment(4),
            21,
            5,
            1024,
        ),
        local_policy_with(
            application(1),
            domain(2),
            commitment(3),
            commitment(4),
            20,
            6,
            1024,
        ),
        local_policy_with(
            application(1),
            domain(2),
            commitment(3),
            commitment(4),
            20,
            5,
            1025,
        ),
    ] {
        assert_ne!(changed.policy_root().unwrap(), baseline);
    }
}

#[test]
fn local_policy_rejects_each_scope_schema_storage_policy_and_epoch_substitution() {
    let blob = b"exact local blob";
    let policy = local_policy();
    let cases = [
        (
            certificate_with(
                blob,
                application(9),
                domain(2),
                7,
                commitment(3),
                30,
                commitment(4),
            ),
            7,
            LocalFullBlobPolicyErrorV1::ApplicationMismatch,
        ),
        (
            certificate_with(
                blob,
                application(1),
                domain(9),
                7,
                commitment(3),
                30,
                commitment(4),
            ),
            7,
            LocalFullBlobPolicyErrorV1::DomainMismatch,
        ),
        (
            certificate_with(
                blob,
                application(1),
                domain(2),
                7,
                commitment(9),
                30,
                commitment(4),
            ),
            7,
            LocalFullBlobPolicyErrorV1::DataSchemaMismatch,
        ),
        (
            certificate_with(
                blob,
                application(1),
                domain(2),
                7,
                commitment(3),
                30,
                commitment(9),
            ),
            7,
            LocalFullBlobPolicyErrorV1::StoragePolicyMismatch,
        ),
        (
            certificate_with(
                blob,
                application(1),
                domain(2),
                8,
                commitment(3),
                30,
                commitment(4),
            ),
            7,
            LocalFullBlobPolicyErrorV1::CertificateEpochMismatch {
                actual: 8,
                expected: 7,
            },
        ),
    ];

    for (certificate, expected_epoch, expected_error) in cases {
        assert_eq!(
            check_local_policy(&policy, &certificate, blob, expected_epoch, 20),
            Err(expected_error)
        );
    }
}

#[test]
fn local_policy_rejects_mutated_blob_and_policy_byte_cap() {
    let blob = b"exact local blob";
    let certificate = certificate_with(
        blob,
        application(1),
        domain(2),
        7,
        commitment(3),
        30,
        commitment(4),
    );
    let mut mutation = blob.to_vec();
    mutation[0] ^= 1;
    assert_eq!(
        check_local_policy(&local_policy(), &certificate, &mutation, 7, 20),
        Err(LocalFullBlobPolicyErrorV1::Content(
            FullBlobDataAvailabilityErrorV1::DataRootMismatch
        ))
    );

    let restrictive = local_policy_with(
        application(1),
        domain(2),
        commitment(3),
        commitment(4),
        20,
        5,
        u64::try_from(blob.len() - 1).unwrap(),
    );
    assert_eq!(
        check_local_policy(&restrictive, &certificate, blob, 7, 20),
        Err(LocalFullBlobPolicyErrorV1::BlobExceedsPolicyMaximum {
            actual: u64::try_from(blob.len()).unwrap(),
            maximum: u64::try_from(blob.len() - 1).unwrap(),
        })
    );
}

#[test]
fn local_policy_accepts_exact_retention_boundaries() {
    let blob = b"retention boundary fixture";
    let policy = local_policy();
    let certificate = certificate_with(
        blob,
        application(1),
        domain(2),
        7,
        commitment(3),
        27,
        commitment(4),
    );

    check_local_policy(&policy, &certificate, blob, 7, 22)
        .expect("equal initial and remaining retention horizons are accepted");
}

#[test]
fn local_policy_rejects_short_or_expired_retention_and_both_epoch_overflows() {
    let blob = b"retention fixture";
    let policy = local_policy();
    let short_initial = certificate_with(
        blob,
        application(1),
        domain(2),
        7,
        commitment(3),
        26,
        commitment(4),
    );
    assert_eq!(
        check_local_policy(&policy, &short_initial, blob, 7, 20),
        Err(LocalFullBlobPolicyErrorV1::InitialRetentionTooShort {
            actual_through_epoch: 26,
            required_through_epoch: 27,
        })
    );

    let adequate = certificate_with(
        blob,
        application(1),
        domain(2),
        7,
        commitment(3),
        30,
        commitment(4),
    );
    assert_eq!(
        check_local_policy(&policy, &adequate, blob, 7, 5),
        Err(LocalFullBlobPolicyErrorV1::CheckBeforeCertificateEpoch {
            checked_epoch: 5,
            certificate_epoch: 7,
        })
    );
    assert_eq!(
        check_local_policy(&policy, &adequate, blob, 7, 26),
        Err(LocalFullBlobPolicyErrorV1::RemainingRetentionTooShort {
            actual_through_epoch: 30,
            required_through_epoch: 31,
        })
    );

    let overflow_policy = local_policy_with(
        application(1),
        domain(2),
        commitment(3),
        commitment(4),
        0,
        2,
        1024,
    );
    assert_eq!(
        check_local_policy(&overflow_policy, &adequate, blob, 7, u64::MAX),
        Err(LocalFullBlobPolicyErrorV1::ArithmeticOverflow(
            "remaining_retention_through_epoch"
        ))
    );

    let initial_overflow_certificate = certificate_with(
        blob,
        application(1),
        domain(2),
        u64::MAX,
        commitment(3),
        u64::MAX,
        commitment(4),
    );
    let initial_overflow_policy = local_policy_with(
        application(1),
        domain(2),
        commitment(3),
        commitment(4),
        1,
        0,
        1024,
    );
    assert_eq!(
        check_local_policy(
            &initial_overflow_policy,
            &initial_overflow_certificate,
            blob,
            u64::MAX,
            u64::MAX,
        ),
        Err(LocalFullBlobPolicyErrorV1::ArithmeticOverflow(
            "initial_retention_through_epoch"
        ))
    );
}

#[test]
fn local_policy_rejects_zero_or_protocol_exceeding_blob_maximum() {
    assert_eq!(
        LocalFullBlobPolicyV1::new(LocalFullBlobPolicyInputV1 {
            application_id: application(1),
            chain_or_domain_id: domain(2),
            data_schema_id: commitment(3),
            expected_storage_policy_hash: commitment(4),
            minimum_retention_epochs: 0,
            minimum_remaining_epochs: 0,
            maximum_blob_bytes: 0,
        }),
        Err(LocalFullBlobPolicyErrorV1::InvalidMaximumBlobBytes {
            actual: 0,
            maximum: u64::try_from(MAX_FULL_BLOB_DA_BYTES_V1).unwrap(),
        })
    );
    let too_large = u64::try_from(MAX_FULL_BLOB_DA_BYTES_V1).unwrap() + 1;
    assert_eq!(
        LocalFullBlobPolicyV1::new(LocalFullBlobPolicyInputV1 {
            application_id: application(1),
            chain_or_domain_id: domain(2),
            data_schema_id: commitment(3),
            expected_storage_policy_hash: commitment(4),
            minimum_retention_epochs: 0,
            minimum_remaining_epochs: 0,
            maximum_blob_bytes: too_large,
        }),
        Err(LocalFullBlobPolicyErrorV1::InvalidMaximumBlobBytes {
            actual: too_large,
            maximum: u64::try_from(MAX_FULL_BLOB_DA_BYTES_V1).unwrap(),
        })
    );
}
