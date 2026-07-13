use serde::{de, Deserialize, Deserializer, Serialize};

use super::hash::{derive_blob_commitments_v1, derive_certificate_root_v1, expected_chunk_count};
use super::{
    FullBlobDataAvailabilityErrorV1, FULL_BLOB_DA_CERTIFICATE_VERSION_V1,
    FULL_BLOB_DA_CHUNK_BYTES_V1, MAX_FULL_BLOB_DA_CHUNKS_V1,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

pub struct FullBlobDataAvailabilityCertificateInputV1<'a> {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub epoch_id: u64,
    pub data_schema_id: CommitmentV3,
    pub blob: &'a [u8],
    pub retention_through_epoch: u64,
    pub storage_policy_hash: CommitmentV3,
}

/// Proof-neutral commitment to one complete bounded data blob.
///
/// This type proves neither persistence nor retrievability. A consuming policy
/// must validate the exact bytes and atomically persist them before treating
/// the certificate root as locally available data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FullBlobDataAvailabilityCertificateV1 {
    certificate_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    data_schema_id: CommitmentV3,
    data_root: CommitmentV3,
    blob_length: u64,
    chunk_size: u32,
    chunk_count: u32,
    chunk_root: CommitmentV3,
    retention_through_epoch: u64,
    storage_policy_hash: CommitmentV3,
    certificate_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FullBlobDataAvailabilityCertificateWireV1 {
    certificate_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    data_schema_id: CommitmentV3,
    data_root: CommitmentV3,
    blob_length: u64,
    chunk_size: u32,
    chunk_count: u32,
    chunk_root: CommitmentV3,
    retention_through_epoch: u64,
    storage_policy_hash: CommitmentV3,
    certificate_root: CommitmentV3,
}

/// Content-checked full-blob certificate with no persistence authority.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ValidatedFullBlobContentV1;
/// let certificate = unimplemented!();
/// let _ = ValidatedFullBlobContentV1 { certificate };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedFullBlobContentV1 {
    certificate: FullBlobDataAvailabilityCertificateV1,
}

impl FullBlobDataAvailabilityCertificateV1 {
    pub fn derive(
        input: FullBlobDataAvailabilityCertificateInputV1<'_>,
    ) -> Result<Self, FullBlobDataAvailabilityErrorV1> {
        if input.retention_through_epoch < input.epoch_id {
            return Err(FullBlobDataAvailabilityErrorV1::RetentionBeforeEpoch);
        }
        let roots = derive_blob_commitments_v1(input.blob)?;
        let blob_length = u64::try_from(input.blob.len())
            .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("blob_length"))?;
        let mut certificate = Self {
            certificate_version: FULL_BLOB_DA_CERTIFICATE_VERSION_V1,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            epoch_id: input.epoch_id,
            data_schema_id: input.data_schema_id,
            data_root: roots.data_root,
            blob_length,
            chunk_size: FULL_BLOB_DA_CHUNK_BYTES_V1,
            chunk_count: roots.chunk_count,
            chunk_root: roots.chunk_root,
            retention_through_epoch: input.retention_through_epoch,
            storage_policy_hash: input.storage_policy_hash,
            certificate_root: roots.data_root,
        };
        certificate.certificate_root = derive_certificate_root_v1(&certificate)?;
        certificate.validate_self_consistency()?;
        Ok(certificate)
    }

    pub fn validate_self_consistency(&self) -> Result<(), FullBlobDataAvailabilityErrorV1> {
        if self.certificate_version != FULL_BLOB_DA_CERTIFICATE_VERSION_V1 {
            return Err(FullBlobDataAvailabilityErrorV1::InvalidVersion(
                self.certificate_version,
            ));
        }
        if self.chunk_size != FULL_BLOB_DA_CHUNK_BYTES_V1 {
            return Err(FullBlobDataAvailabilityErrorV1::InvalidChunkSize(
                self.chunk_size,
            ));
        }
        let expected_count = expected_chunk_count(self.blob_length)?;
        if self.chunk_count != expected_count {
            return Err(FullBlobDataAvailabilityErrorV1::InvalidChunkCount {
                actual: self.chunk_count,
                expected: expected_count,
            });
        }
        if self.chunk_count > MAX_FULL_BLOB_DA_CHUNKS_V1 {
            return Err(FullBlobDataAvailabilityErrorV1::TooManyChunks {
                actual: self.chunk_count,
                maximum: MAX_FULL_BLOB_DA_CHUNKS_V1,
            });
        }
        if self.retention_through_epoch < self.epoch_id {
            return Err(FullBlobDataAvailabilityErrorV1::RetentionBeforeEpoch);
        }
        if self.certificate_root != derive_certificate_root_v1(self)? {
            return Err(FullBlobDataAvailabilityErrorV1::CertificateRootMismatch);
        }
        Ok(())
    }

    pub fn validate_blob(
        &self,
        blob: &[u8],
    ) -> Result<ValidatedFullBlobContentV1, FullBlobDataAvailabilityErrorV1> {
        self.validate_self_consistency()?;
        let length = u64::try_from(blob.len())
            .map_err(|_| FullBlobDataAvailabilityErrorV1::ArithmeticOverflow("blob_length"))?;
        if length != self.blob_length {
            return Err(FullBlobDataAvailabilityErrorV1::DataRootMismatch);
        }
        let roots = derive_blob_commitments_v1(blob)?;
        if roots.data_root != self.data_root {
            return Err(FullBlobDataAvailabilityErrorV1::DataRootMismatch);
        }
        if roots.chunk_count != self.chunk_count || roots.chunk_root != self.chunk_root {
            return Err(FullBlobDataAvailabilityErrorV1::ChunkRootMismatch);
        }
        Ok(ValidatedFullBlobContentV1 {
            certificate: self.clone(),
        })
    }

    pub const fn certificate_version(&self) -> u16 {
        self.certificate_version
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn epoch_id(&self) -> u64 {
        self.epoch_id
    }

    pub const fn data_schema_id(&self) -> CommitmentV3 {
        self.data_schema_id
    }

    pub const fn data_root(&self) -> CommitmentV3 {
        self.data_root
    }

    pub const fn blob_length(&self) -> u64 {
        self.blob_length
    }

    pub const fn chunk_size(&self) -> u32 {
        self.chunk_size
    }

    pub const fn chunk_count(&self) -> u32 {
        self.chunk_count
    }

    pub const fn chunk_root(&self) -> CommitmentV3 {
        self.chunk_root
    }

    pub const fn retention_through_epoch(&self) -> u64 {
        self.retention_through_epoch
    }

    pub const fn storage_policy_hash(&self) -> CommitmentV3 {
        self.storage_policy_hash
    }

    pub const fn certificate_root(&self) -> CommitmentV3 {
        self.certificate_root
    }

    fn from_wire(
        wire: FullBlobDataAvailabilityCertificateWireV1,
    ) -> Result<Self, FullBlobDataAvailabilityErrorV1> {
        let certificate = Self {
            certificate_version: wire.certificate_version,
            application_id: wire.application_id,
            chain_or_domain_id: wire.chain_or_domain_id,
            epoch_id: wire.epoch_id,
            data_schema_id: wire.data_schema_id,
            data_root: wire.data_root,
            blob_length: wire.blob_length,
            chunk_size: wire.chunk_size,
            chunk_count: wire.chunk_count,
            chunk_root: wire.chunk_root,
            retention_through_epoch: wire.retention_through_epoch,
            storage_policy_hash: wire.storage_policy_hash,
            certificate_root: wire.certificate_root,
        };
        certificate.validate_self_consistency()?;
        Ok(certificate)
    }
}

impl ValidatedFullBlobContentV1 {
    pub const fn certificate(&self) -> &FullBlobDataAvailabilityCertificateV1 {
        &self.certificate
    }
}

impl<'de> Deserialize<'de> for FullBlobDataAvailabilityCertificateV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(FullBlobDataAvailabilityCertificateWireV1::deserialize(
            deserializer,
        )?)
        .map_err(de::Error::custom)
    }
}
