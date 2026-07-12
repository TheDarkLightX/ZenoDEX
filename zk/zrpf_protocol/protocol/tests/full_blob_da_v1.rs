use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_full_blob_da_certificate_v1, encode_full_blob_da_certificate_v1, ApplicationIdV3,
    CommitmentV3, DomainIdV3, FullBlobDataAvailabilityCertificateInputV1,
    FullBlobDataAvailabilityCertificateV1, FullBlobDataAvailabilityErrorV1,
    FULL_BLOB_DA_CERTIFICATE_VERSION_V1, FULL_BLOB_DA_CHUNK_BYTES_V1, MAX_FULL_BLOB_DA_BYTES_V1,
    MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
};

const DATA_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.data_root.v1";
const CHUNK_HASH_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.chunk.v1";
const CHUNK_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.chunk_root.v1";
const CERTIFICATE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.certificate_root.v1";

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
