use core::fmt;

use serde::{de, Deserialize, Deserializer, Serialize};

use super::base::{
    ReceiptCodecIdV1, MAX_TASK_CYCLES_V1, MAX_TASK_INPUT_BYTES_V1, MAX_TASK_MEMORY_BYTES_V1,
};
use crate::{CommitmentV3, ProfileIdV3};

pub const PROOF_ASSIGNMENT_POLICY_VERSION_V1: u16 = 1;
pub const MAX_PROOF_ASSIGNMENT_POLICY_BYTES_V1: usize = 512;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofAssignmentPolicyErrorV1 {
    InvalidVersion(u16),
    InvalidSecurityLevel,
    InvalidValidityRange,
    InvalidResourceCeiling { field: &'static str, maximum: u64 },
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for ProofAssignmentPolicyErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVersion(version) => {
                write!(
                    formatter,
                    "invalid proof assignment policy version: {version}"
                )
            }
            Self::InvalidSecurityLevel => {
                formatter.write_str("invalid assignment policy security level")
            }
            Self::InvalidValidityRange => {
                formatter.write_str("assignment policy validity range is reversed")
            }
            Self::InvalidResourceCeiling { field, maximum } => {
                write!(
                    formatter,
                    "invalid resource ceiling {field}; maximum {maximum}"
                )
            }
            Self::EmptyInput => formatter.write_str("assignment policy input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "assignment policy input length {actual} exceeds {maximum}"
                )
            }
            Self::PostcardDecode => formatter.write_str("assignment policy postcard decode failed"),
            Self::TrailingBytes => {
                formatter.write_str("assignment policy postcard input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("assignment policy postcard input is noncanonical")
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofAssignmentPolicyInputV1 {
    pub authorized_program_manifest_root: CommitmentV3,
    pub required_proof_profile_id: ProfileIdV3,
    pub required_receipt_codec_id: ReceiptCodecIdV1,
    pub required_verifier_policy_root: CommitmentV3,
    pub minimum_security_level_bits: u16,
    pub valid_from_epoch: u64,
    pub valid_through_epoch: u64,
    pub max_input_bytes: u64,
    pub max_cycles_or_trace_rows: u64,
    pub max_memory_bytes: u64,
}

/// Bounded untrusted mapping between task and manifest compatibility fields.
///
/// Construction validates shape and limits only. A caller must authenticate
/// the exact canonical policy bytes before relying on the mapping.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct ProofAssignmentPolicyV1 {
    policy_version: u16,
    authorized_program_manifest_root: CommitmentV3,
    required_proof_profile_id: ProfileIdV3,
    required_receipt_codec_id: ReceiptCodecIdV1,
    required_verifier_policy_root: CommitmentV3,
    minimum_security_level_bits: u16,
    valid_from_epoch: u64,
    valid_through_epoch: u64,
    max_input_bytes: u64,
    max_cycles_or_trace_rows: u64,
    max_memory_bytes: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofAssignmentPolicyWireV1 {
    policy_version: u16,
    authorized_program_manifest_root: CommitmentV3,
    required_proof_profile_id: ProfileIdV3,
    required_receipt_codec_id: ReceiptCodecIdV1,
    required_verifier_policy_root: CommitmentV3,
    minimum_security_level_bits: u16,
    valid_from_epoch: u64,
    valid_through_epoch: u64,
    max_input_bytes: u64,
    max_cycles_or_trace_rows: u64,
    max_memory_bytes: u64,
}

impl ProofAssignmentPolicyV1 {
    pub fn new(input: ProofAssignmentPolicyInputV1) -> Result<Self, ProofAssignmentPolicyErrorV1> {
        Self::from_parts(PROOF_ASSIGNMENT_POLICY_VERSION_V1, input)
    }

    fn from_parts(
        policy_version: u16,
        input: ProofAssignmentPolicyInputV1,
    ) -> Result<Self, ProofAssignmentPolicyErrorV1> {
        let value = Self {
            policy_version,
            authorized_program_manifest_root: input.authorized_program_manifest_root,
            required_proof_profile_id: input.required_proof_profile_id,
            required_receipt_codec_id: input.required_receipt_codec_id,
            required_verifier_policy_root: input.required_verifier_policy_root,
            minimum_security_level_bits: input.minimum_security_level_bits,
            valid_from_epoch: input.valid_from_epoch,
            valid_through_epoch: input.valid_through_epoch,
            max_input_bytes: input.max_input_bytes,
            max_cycles_or_trace_rows: input.max_cycles_or_trace_rows,
            max_memory_bytes: input.max_memory_bytes,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> Result<(), ProofAssignmentPolicyErrorV1> {
        if self.policy_version != PROOF_ASSIGNMENT_POLICY_VERSION_V1 {
            return Err(ProofAssignmentPolicyErrorV1::InvalidVersion(
                self.policy_version,
            ));
        }
        if self.minimum_security_level_bits == 0 || self.minimum_security_level_bits > 512 {
            return Err(ProofAssignmentPolicyErrorV1::InvalidSecurityLevel);
        }
        if self.valid_from_epoch > self.valid_through_epoch {
            return Err(ProofAssignmentPolicyErrorV1::InvalidValidityRange);
        }
        for (field, value, maximum) in [
            (
                "max_input_bytes",
                self.max_input_bytes,
                MAX_TASK_INPUT_BYTES_V1,
            ),
            (
                "max_cycles_or_trace_rows",
                self.max_cycles_or_trace_rows,
                MAX_TASK_CYCLES_V1,
            ),
            (
                "max_memory_bytes",
                self.max_memory_bytes,
                MAX_TASK_MEMORY_BYTES_V1,
            ),
        ] {
            if value == 0 || value > maximum {
                return Err(ProofAssignmentPolicyErrorV1::InvalidResourceCeiling {
                    field,
                    maximum,
                });
            }
        }
        Ok(())
    }

    pub const fn authorized_program_manifest_root(&self) -> CommitmentV3 {
        self.authorized_program_manifest_root
    }

    pub const fn required_proof_profile_id(&self) -> ProfileIdV3 {
        self.required_proof_profile_id
    }

    pub const fn required_receipt_codec_id(&self) -> ReceiptCodecIdV1 {
        self.required_receipt_codec_id
    }

    pub const fn required_verifier_policy_root(&self) -> CommitmentV3 {
        self.required_verifier_policy_root
    }

    pub const fn minimum_security_level_bits(&self) -> u16 {
        self.minimum_security_level_bits
    }

    pub const fn valid_from_epoch(&self) -> u64 {
        self.valid_from_epoch
    }

    pub const fn valid_through_epoch(&self) -> u64 {
        self.valid_through_epoch
    }

    pub const fn max_input_bytes(&self) -> u64 {
        self.max_input_bytes
    }

    pub const fn max_cycles_or_trace_rows(&self) -> u64 {
        self.max_cycles_or_trace_rows
    }

    pub const fn max_memory_bytes(&self) -> u64 {
        self.max_memory_bytes
    }
}

impl<'de> Deserialize<'de> for ProofAssignmentPolicyV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProofAssignmentPolicyWireV1::deserialize(deserializer)?;
        Self::from_parts(
            wire.policy_version,
            ProofAssignmentPolicyInputV1 {
                authorized_program_manifest_root: wire.authorized_program_manifest_root,
                required_proof_profile_id: wire.required_proof_profile_id,
                required_receipt_codec_id: wire.required_receipt_codec_id,
                required_verifier_policy_root: wire.required_verifier_policy_root,
                minimum_security_level_bits: wire.minimum_security_level_bits,
                valid_from_epoch: wire.valid_from_epoch,
                valid_through_epoch: wire.valid_through_epoch,
                max_input_bytes: wire.max_input_bytes,
                max_cycles_or_trace_rows: wire.max_cycles_or_trace_rows,
                max_memory_bytes: wire.max_memory_bytes,
            },
        )
        .map_err(de::Error::custom)
    }
}
