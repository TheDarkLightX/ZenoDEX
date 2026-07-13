use sha2::{Digest, Sha256};

use super::{
    FullBlobDataAvailabilityCertificateV1, FullBlobDataAvailabilityErrorV1,
    FULL_BLOB_DA_CHUNK_BYTES_V1, MAX_FULL_BLOB_DA_BYTES_V1, MAX_FULL_BLOB_DA_CHUNKS_V1,
};
use crate::CommitmentV3;

const DATA_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.data_root.v1";
const CHUNK_HASH_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.chunk.v1";
const CHUNK_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.chunk_root.v1";
const CERTIFICATE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.full_blob_da.certificate_root.v1";

pub(super) struct DerivedBlobCommitmentsV1 {
    pub data_root: CommitmentV3,
    pub chunk_count: u32,
    pub chunk_root: CommitmentV3,
}

pub(super) fn derive_blob_commitments_v1(
    blob: &[u8],
) -> Result<DerivedBlobCommitmentsV1, FullBlobDataAvailabilityErrorV1> {
    require_blob_size(blob.len())?;
    let blob_length = u64::try_from(blob.len())
        .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("blob_length"))?;
    let mut data_hasher = domain_hasher(DATA_ROOT_DOMAIN_V1)?;
    data_hasher.update(blob_length.to_be_bytes());
    data_hasher.update(blob);
    let data_root = commitment(data_hasher, "data_root")?;

    let chunk_size = usize::try_from(FULL_BLOB_DA_CHUNK_BYTES_V1)
        .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("chunk_size"))?;
    let chunk_count_usize = blob.len().div_ceil(chunk_size);
    let chunk_count = u32::try_from(chunk_count_usize)
        .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("chunk_count"))?;
    if chunk_count > MAX_FULL_BLOB_DA_CHUNKS_V1 {
        return Err(FullBlobDataAvailabilityErrorV1::TooManyChunks {
            actual: chunk_count,
            maximum: MAX_FULL_BLOB_DA_CHUNKS_V1,
        });
    }
    let mut root_hasher = domain_hasher(CHUNK_ROOT_DOMAIN_V1)?;
    root_hasher.update(chunk_count.to_be_bytes());
    for (index, chunk) in blob.chunks(chunk_size).enumerate() {
        let index = u32::try_from(index)
            .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("chunk_index"))?;
        let chunk_length = u32::try_from(chunk.len())
            .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("chunk_length"))?;
        let mut chunk_hasher = domain_hasher(CHUNK_HASH_DOMAIN_V1)?;
        chunk_hasher.update(index.to_be_bytes());
        chunk_hasher.update(chunk_length.to_be_bytes());
        chunk_hasher.update(chunk);
        root_hasher.update(chunk_hasher.finalize());
    }
    let chunk_root = commitment(root_hasher, "chunk_root")?;
    Ok(DerivedBlobCommitmentsV1 {
        data_root,
        chunk_count,
        chunk_root,
    })
}

pub(super) fn derive_certificate_root_v1(
    certificate: &FullBlobDataAvailabilityCertificateV1,
) -> Result<CommitmentV3, FullBlobDataAvailabilityErrorV1> {
    let mut hasher = domain_hasher(CERTIFICATE_ROOT_DOMAIN_V1)?;
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
    commitment(hasher, "certificate_root")
}

pub(super) fn expected_chunk_count(
    blob_length: u64,
) -> Result<u32, FullBlobDataAvailabilityErrorV1> {
    if blob_length == 0 {
        return Err(FullBlobDataAvailabilityErrorV1::EmptyBlob);
    }
    let maximum = u64::try_from(MAX_FULL_BLOB_DA_BYTES_V1)
        .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("maximum_blob_length"))?;
    if blob_length > maximum {
        let actual = usize::try_from(blob_length).unwrap_or(usize::MAX);
        return Err(FullBlobDataAvailabilityErrorV1::BlobTooLarge {
            actual,
            maximum: MAX_FULL_BLOB_DA_BYTES_V1,
        });
    }
    let chunk_size = u64::from(FULL_BLOB_DA_CHUNK_BYTES_V1);
    let count = blob_length.div_ceil(chunk_size);
    u32::try_from(count)
        .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("chunk_count"))
}

fn require_blob_size(size: usize) -> Result<(), FullBlobDataAvailabilityErrorV1> {
    if size == 0 {
        return Err(FullBlobDataAvailabilityErrorV1::EmptyBlob);
    }
    if size > MAX_FULL_BLOB_DA_BYTES_V1 {
        return Err(FullBlobDataAvailabilityErrorV1::BlobTooLarge {
            actual: size,
            maximum: MAX_FULL_BLOB_DA_BYTES_V1,
        });
    }
    Ok(())
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, FullBlobDataAvailabilityErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, FullBlobDataAvailabilityErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| FullBlobDataAvailabilityErrorV1::InvalidDerivedCommitment(field))
}
