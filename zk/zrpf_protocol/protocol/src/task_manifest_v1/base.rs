use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};

pub const PROGRAM_MANIFEST_VERSION_V1: u16 = 1;
pub const PROOF_TASK_VERSION_V1: u16 = 1;
pub const MAX_ACCEPTED_PROOF_SYSTEMS_V1: usize = 8;
pub const MAX_PROGRAM_MANIFEST_BYTES_V1: usize = 4_096;
pub const MAX_PROOF_TASK_BYTES_V1: usize = 4_096;
pub const MAX_TASK_INPUT_BYTES_V1: u64 = 64 * 1024 * 1024;
pub const MAX_TASK_CYCLES_V1: u64 = 1 << 48;
pub const MAX_TASK_MEMORY_BYTES_V1: u64 = 16 * 1024 * 1024 * 1024;
pub const MAX_TASK_REDUNDANCY_V1: u8 = 8;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TaskManifestErrorV1 {
    InvalidVersion { field: &'static str, actual: u16 },
    ZeroIdentifier(&'static str),
    EmptyProofSystems,
    TooManyProofSystems { actual: usize, maximum: usize },
    DuplicateProofSystem,
    InvalidSecurityLevel,
    InvalidChildBinding,
    InvalidResourceBound(&'static str),
    InvalidDeadline,
    InvalidRedundancy,
    InvalidDerivedIdentity(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
    ArithmeticOverflow(&'static str),
}

impl fmt::Display for TaskManifestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVersion { field, actual } => {
                write!(formatter, "invalid {field} version: {actual}")
            }
            Self::ZeroIdentifier(field) => write!(formatter, "zero identifier: {field}"),
            Self::EmptyProofSystems => formatter.write_str("accepted proof systems are empty"),
            Self::TooManyProofSystems { actual, maximum } => {
                write!(formatter, "proof system count {actual} exceeds {maximum}")
            }
            Self::DuplicateProofSystem => formatter.write_str("duplicate proof system"),
            Self::InvalidSecurityLevel => formatter.write_str("invalid security level"),
            Self::InvalidChildBinding => formatter.write_str("task child binding is inconsistent"),
            Self::InvalidResourceBound(field) => {
                write!(formatter, "invalid resource bound: {field}")
            }
            Self::InvalidDeadline => formatter.write_str("task deadline must follow creation"),
            Self::InvalidRedundancy => formatter.write_str("invalid task redundancy policy"),
            Self::InvalidDerivedIdentity(field) => {
                write!(formatter, "derived identity mismatch: {field}")
            }
            Self::EmptyInput => formatter.write_str("input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "input length {actual} exceeds {maximum}")
            }
            Self::PostcardDecode => formatter.write_str("postcard decode failed"),
            Self::TrailingBytes => formatter.write_str("postcard input has trailing bytes"),
            Self::NonCanonicalEncoding => formatter.write_str("postcard input is noncanonical"),
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
        }
    }
}

macro_rules! nonzero_id {
    ($name:ident, $label:literal) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name([u8; 32]);

        impl $name {
            pub fn new(bytes: [u8; 32]) -> Result<Self, TaskManifestErrorV1> {
                if bytes == [0; 32] {
                    return Err(TaskManifestErrorV1::ZeroIdentifier($label));
                }
                Ok(Self(bytes))
            }

            pub const fn as_bytes(&self) -> &[u8; 32] {
                &self.0
            }
        }

        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                self.0.serialize(serializer)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                Self::new(<[u8; 32]>::deserialize(deserializer)?).map_err(de::Error::custom)
            }
        }
    };
}

nonzero_id!(ProofSystemIdV1, "proof_system_id");
nonzero_id!(ProofSystemVersionIdV1, "proof_system_version_id");
nonzero_id!(ReceiptCodecIdV1, "receipt_codec_id");
nonzero_id!(RewardAssetIdV1, "reward_asset_id");

pub(super) fn deserialize_bounded_proof_systems<'de, D>(
    deserializer: D,
) -> Result<Vec<ProofSystemIdV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct ProofSystemsVisitor;

    impl<'de> Visitor<'de> for ProofSystemsVisitor {
        type Value = Vec<ProofSystemIdV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "at most {MAX_ACCEPTED_PROOF_SYSTEMS_V1} proof system identifiers"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_ACCEPTED_PROOF_SYSTEMS_V1 {
                return Err(de::Error::custom(
                    TaskManifestErrorV1::TooManyProofSystems {
                        actual: declared,
                        maximum: MAX_ACCEPTED_PROOF_SYSTEMS_V1,
                    },
                ));
            }
            let mut systems = Vec::with_capacity(declared);
            while let Some(system) = sequence.next_element()? {
                if systems.len() == MAX_ACCEPTED_PROOF_SYSTEMS_V1 {
                    return Err(de::Error::custom(
                        TaskManifestErrorV1::TooManyProofSystems {
                            actual: MAX_ACCEPTED_PROOF_SYSTEMS_V1 + 1,
                            maximum: MAX_ACCEPTED_PROOF_SYSTEMS_V1,
                        },
                    ));
                }
                systems.push(system);
            }
            Ok(systems)
        }
    }

    deserializer.deserialize_seq(ProofSystemsVisitor)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrivacyClaimV1 {
    PublicComputation,
    WitnessPrivate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofTaskKindV1 {
    Leaf,
    Aggregate,
    EpochCheckpoint,
    DataAvailability,
}

impl ProofTaskKindV1 {
    pub(super) const fn requires_child_root(self) -> bool {
        matches!(self, Self::Aggregate | Self::EpochCheckpoint)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofTaskPriorityV1 {
    Normal,
    Urgent,
    CriticalCheckpoint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofTaskPrivacyPolicyV1 {
    PublicInputs,
    PrivateWitnessAllowed,
    PrivateWitnessRequired,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RedundancyPolicyV1 {
    required_primary_proofs: u8,
    standby_provers: u8,
    minimum_distinct_proof_systems: u8,
}

impl RedundancyPolicyV1 {
    pub fn new(
        required_primary_proofs: u8,
        standby_provers: u8,
        minimum_distinct_proof_systems: u8,
    ) -> Result<Self, TaskManifestErrorV1> {
        let value = Self {
            required_primary_proofs,
            standby_provers,
            minimum_distinct_proof_systems,
        };
        value.validate(MAX_ACCEPTED_PROOF_SYSTEMS_V1)?;
        Ok(value)
    }

    pub(super) fn validate(self, accepted_system_count: usize) -> Result<(), TaskManifestErrorV1> {
        let primary = usize::from(self.required_primary_proofs);
        let standby = usize::from(self.standby_provers);
        let distinct = usize::from(self.minimum_distinct_proof_systems);
        if primary == 0
            || primary > usize::from(MAX_TASK_REDUNDANCY_V1)
            || standby > usize::from(MAX_TASK_REDUNDANCY_V1)
            || distinct == 0
            || distinct > accepted_system_count
        {
            return Err(TaskManifestErrorV1::InvalidRedundancy);
        }
        Ok(())
    }

    pub const fn required_primary_proofs(self) -> u8 {
        self.required_primary_proofs
    }

    pub const fn standby_provers(self) -> u8 {
        self.standby_provers
    }

    pub const fn minimum_distinct_proof_systems(self) -> u8 {
        self.minimum_distinct_proof_systems
    }
}
