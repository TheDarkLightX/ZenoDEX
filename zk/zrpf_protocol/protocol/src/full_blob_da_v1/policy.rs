use core::fmt;

use sha2::{Digest, Sha256};

use super::{
    FullBlobDataAvailabilityCertificateV1, FullBlobDataAvailabilityErrorV1,
    MAX_FULL_BLOB_DA_BYTES_V1,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

pub const LOCAL_FULL_BLOB_POLICY_VERSION_V1: u16 = 1;

const LOCAL_POLICY_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.local_full_blob_policy.root.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalFullBlobPolicyInputV1 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub data_schema_id: CommitmentV3,
    pub expected_storage_policy_hash: CommitmentV3,
    pub minimum_retention_epochs: u64,
    pub minimum_remaining_epochs: u64,
    pub maximum_blob_bytes: u64,
}

/// Governed policy for checking one exact, locally present full blob.
///
/// The policy contains no caller verdict. Its hash binds every acceptance
/// parameter, while the checker recomputes certificate and content relations.
/// Policy provenance and governance are external to this proof-neutral value;
/// a successful local check does not establish that this policy is authorized.
/// It grants no persistence, remote retrieval, replication, quorum, consensus,
/// finality, settlement, release, or production authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalFullBlobPolicyV1 {
    policy_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    data_schema_id: CommitmentV3,
    expected_storage_policy_hash: CommitmentV3,
    minimum_retention_epochs: u64,
    minimum_remaining_epochs: u64,
    maximum_blob_bytes: u64,
}

pub struct LocalFullBlobPolicyCheckInputV1<'a> {
    pub policy: &'a LocalFullBlobPolicyV1,
    pub certificate: &'a FullBlobDataAvailabilityCertificateV1,
    pub blob: &'a [u8],
    /// Epoch committed by the transition or journal that consumes the blob.
    pub expected_certificate_epoch: u64,
    /// Governed epoch cursor at which the exact bytes are checked locally.
    pub checked_epoch: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LocalFullBlobPolicyErrorV1 {
    InvalidMaximumBlobBytes {
        actual: u64,
        maximum: u64,
    },
    ApplicationMismatch,
    DomainMismatch,
    DataSchemaMismatch,
    StoragePolicyMismatch,
    CertificateEpochMismatch {
        actual: u64,
        expected: u64,
    },
    BlobExceedsPolicyMaximum {
        actual: u64,
        maximum: u64,
    },
    CheckBeforeCertificateEpoch {
        checked_epoch: u64,
        certificate_epoch: u64,
    },
    InitialRetentionTooShort {
        actual_through_epoch: u64,
        required_through_epoch: u64,
    },
    RemainingRetentionTooShort {
        actual_through_epoch: u64,
        required_through_epoch: u64,
    },
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    Content(FullBlobDataAvailabilityErrorV1),
}

impl fmt::Display for LocalFullBlobPolicyErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidMaximumBlobBytes { actual, maximum } => write!(
                formatter,
                "local full-blob policy maximum {actual} is outside 1..={maximum}"
            ),
            Self::ApplicationMismatch => {
                formatter.write_str("local full-blob policy application mismatch")
            }
            Self::DomainMismatch => {
                formatter.write_str("local full-blob policy domain mismatch")
            }
            Self::DataSchemaMismatch => {
                formatter.write_str("local full-blob policy data schema mismatch")
            }
            Self::StoragePolicyMismatch => {
                formatter.write_str("local full-blob storage policy mismatch")
            }
            Self::CertificateEpochMismatch { actual, expected } => write!(
                formatter,
                "local full-blob certificate epoch {actual} differs from expected {expected}"
            ),
            Self::BlobExceedsPolicyMaximum { actual, maximum } => write!(
                formatter,
                "local full-blob length {actual} exceeds policy maximum {maximum}"
            ),
            Self::CheckBeforeCertificateEpoch {
                checked_epoch,
                certificate_epoch,
            } => write!(
                formatter,
                "local full-blob check epoch {checked_epoch} precedes certificate epoch {certificate_epoch}"
            ),
            Self::InitialRetentionTooShort {
                actual_through_epoch,
                required_through_epoch,
            } => write!(
                formatter,
                "local full-blob certificate retains through {actual_through_epoch}, below initial policy requirement {required_through_epoch}"
            ),
            Self::RemainingRetentionTooShort {
                actual_through_epoch,
                required_through_epoch,
            } => write!(
                formatter,
                "local full-blob certificate retains through {actual_through_epoch}, below remaining policy requirement {required_through_epoch}"
            ),
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived local full-blob commitment: {field}")
            }
            Self::Content(error) => write!(formatter, "local full-blob content rejected: {error}"),
        }
    }
}

impl From<FullBlobDataAvailabilityErrorV1> for LocalFullBlobPolicyErrorV1 {
    fn from(error: FullBlobDataAvailabilityErrorV1) -> Self {
        Self::Content(error)
    }
}

impl LocalFullBlobPolicyV1 {
    pub fn new(input: LocalFullBlobPolicyInputV1) -> Result<Self, LocalFullBlobPolicyErrorV1> {
        let maximum = protocol_maximum_blob_bytes()?;
        if input.maximum_blob_bytes == 0 || input.maximum_blob_bytes > maximum {
            return Err(LocalFullBlobPolicyErrorV1::InvalidMaximumBlobBytes {
                actual: input.maximum_blob_bytes,
                maximum,
            });
        }
        Ok(Self {
            policy_version: LOCAL_FULL_BLOB_POLICY_VERSION_V1,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            data_schema_id: input.data_schema_id,
            expected_storage_policy_hash: input.expected_storage_policy_hash,
            minimum_retention_epochs: input.minimum_retention_epochs,
            minimum_remaining_epochs: input.minimum_remaining_epochs,
            maximum_blob_bytes: input.maximum_blob_bytes,
        })
    }

    pub fn policy_root(&self) -> Result<CommitmentV3, LocalFullBlobPolicyErrorV1> {
        derive_policy_root_v1(self)
    }

    pub const fn policy_version(&self) -> u16 {
        self.policy_version
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn data_schema_id(&self) -> CommitmentV3 {
        self.data_schema_id
    }

    pub const fn expected_storage_policy_hash(&self) -> CommitmentV3 {
        self.expected_storage_policy_hash
    }

    pub const fn minimum_retention_epochs(&self) -> u64 {
        self.minimum_retention_epochs
    }

    pub const fn minimum_remaining_epochs(&self) -> u64 {
        self.minimum_remaining_epochs
    }

    pub const fn maximum_blob_bytes(&self) -> u64 {
        self.maximum_blob_bytes
    }
}

/// Checks exact local content against one governed policy.
///
/// Successful return means only `local_full_blob_policy_satisfied` for the
/// supplied bytes and epochs in this invocation. It is a unit result, not an
/// authority-bearing token.
pub fn check_local_full_blob_policy_satisfied_v1(
    input: LocalFullBlobPolicyCheckInputV1<'_>,
) -> Result<(), LocalFullBlobPolicyErrorV1> {
    input.certificate.validate_self_consistency()?;
    require_scope_and_epoch(&input)?;
    require_blob_and_retention(&input)?;
    input.certificate.validate_blob(input.blob)?;
    Ok(())
}

fn require_scope_and_epoch(
    input: &LocalFullBlobPolicyCheckInputV1<'_>,
) -> Result<(), LocalFullBlobPolicyErrorV1> {
    let policy = input.policy;
    let certificate = input.certificate;
    if certificate.application_id() != policy.application_id {
        return Err(LocalFullBlobPolicyErrorV1::ApplicationMismatch);
    }
    if certificate.chain_or_domain_id() != policy.chain_or_domain_id {
        return Err(LocalFullBlobPolicyErrorV1::DomainMismatch);
    }
    if certificate.data_schema_id() != policy.data_schema_id {
        return Err(LocalFullBlobPolicyErrorV1::DataSchemaMismatch);
    }
    if certificate.storage_policy_hash() != policy.expected_storage_policy_hash {
        return Err(LocalFullBlobPolicyErrorV1::StoragePolicyMismatch);
    }
    if certificate.epoch_id() != input.expected_certificate_epoch {
        return Err(LocalFullBlobPolicyErrorV1::CertificateEpochMismatch {
            actual: certificate.epoch_id(),
            expected: input.expected_certificate_epoch,
        });
    }
    Ok(())
}

fn require_blob_and_retention(
    input: &LocalFullBlobPolicyCheckInputV1<'_>,
) -> Result<(), LocalFullBlobPolicyErrorV1> {
    let certificate = input.certificate;
    let policy = input.policy;
    if certificate.blob_length() > policy.maximum_blob_bytes {
        return Err(LocalFullBlobPolicyErrorV1::BlobExceedsPolicyMaximum {
            actual: certificate.blob_length(),
            maximum: policy.maximum_blob_bytes,
        });
    }
    if input.checked_epoch < certificate.epoch_id() {
        return Err(LocalFullBlobPolicyErrorV1::CheckBeforeCertificateEpoch {
            checked_epoch: input.checked_epoch,
            certificate_epoch: certificate.epoch_id(),
        });
    }
    require_retention_horizon(RetentionHorizonCheckV1 {
        start_epoch: certificate.epoch_id(),
        minimum_epochs: policy.minimum_retention_epochs,
        actual_through_epoch: certificate.retention_through_epoch(),
        overflow_field: "initial_retention_through_epoch",
        kind: RetentionHorizonKindV1::Initial,
    })?;
    require_retention_horizon(RetentionHorizonCheckV1 {
        start_epoch: input.checked_epoch,
        minimum_epochs: policy.minimum_remaining_epochs,
        actual_through_epoch: certificate.retention_through_epoch(),
        overflow_field: "remaining_retention_through_epoch",
        kind: RetentionHorizonKindV1::Remaining,
    })
}

struct RetentionHorizonCheckV1 {
    start_epoch: u64,
    minimum_epochs: u64,
    actual_through_epoch: u64,
    overflow_field: &'static str,
    kind: RetentionHorizonKindV1,
}

fn require_retention_horizon(
    check: RetentionHorizonCheckV1,
) -> Result<(), LocalFullBlobPolicyErrorV1> {
    let required_through_epoch = check.start_epoch.checked_add(check.minimum_epochs).ok_or(
        LocalFullBlobPolicyErrorV1::ArithmeticOverflow(check.overflow_field),
    )?;
    if check.actual_through_epoch >= required_through_epoch {
        return Ok(());
    }
    match check.kind {
        RetentionHorizonKindV1::Initial => {
            Err(LocalFullBlobPolicyErrorV1::InitialRetentionTooShort {
                actual_through_epoch: check.actual_through_epoch,
                required_through_epoch,
            })
        }
        RetentionHorizonKindV1::Remaining => {
            Err(LocalFullBlobPolicyErrorV1::RemainingRetentionTooShort {
                actual_through_epoch: check.actual_through_epoch,
                required_through_epoch,
            })
        }
    }
}

#[derive(Clone, Copy)]
enum RetentionHorizonKindV1 {
    Initial,
    Remaining,
}

fn derive_policy_root_v1(
    policy: &LocalFullBlobPolicyV1,
) -> Result<CommitmentV3, LocalFullBlobPolicyErrorV1> {
    let mut hasher = domain_hasher(LOCAL_POLICY_ROOT_DOMAIN_V1)?;
    hasher.update(policy.policy_version.to_be_bytes());
    hasher.update(policy.application_id.as_bytes());
    hasher.update(policy.chain_or_domain_id.as_bytes());
    hasher.update(policy.data_schema_id.as_bytes());
    hasher.update(policy.expected_storage_policy_hash.as_bytes());
    hasher.update(policy.minimum_retention_epochs.to_be_bytes());
    hasher.update(policy.minimum_remaining_epochs.to_be_bytes());
    hasher.update(policy.maximum_blob_bytes.to_be_bytes());
    commitment(hasher, "policy_root")
}

fn protocol_maximum_blob_bytes() -> Result<u64, LocalFullBlobPolicyErrorV1> {
    u64::try_from(MAX_FULL_BLOB_DA_BYTES_V1)
        .map_err(|_| LocalFullBlobPolicyErrorV1::ArithmeticOverflow("protocol_blob_maximum"))
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, LocalFullBlobPolicyErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| LocalFullBlobPolicyErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, LocalFullBlobPolicyErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| LocalFullBlobPolicyErrorV1::InvalidDerivedCommitment(field))
}
