mod codec;
mod record;

use core::fmt;

use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

pub use codec::{
    decode_exact_authorization_consumption_nullifier_v1, decode_exact_economic_action_record_v1,
    encode_authorization_consumption_nullifier_v1, encode_economic_action_record_v1,
};
pub use record::{EconomicActionRecordInputV1, EconomicActionRecordV1};

pub const ECONOMIC_ACTION_RECORD_VERSION_V1: u16 = 1;
pub const AUTHORIZATION_CONSUMPTION_NULLIFIER_VERSION_V1: u16 = 1;
pub const MAX_CONSUMED_OBJECTS_PER_ACTION_V1: usize = 128;
pub const MAX_ECONOMIC_ACTION_RECORD_BYTES_V1: usize = 8_192;
pub const MAX_AUTHORIZATION_CONSUMPTION_NULLIFIER_BYTES_V1: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EconomicActionErrorV1 {
    InvalidRecordVersion(u16),
    InvalidValidityRange,
    ZeroIdentifier(&'static str),
    TooManyConsumedObjects { actual: usize, maximum: usize },
    DuplicateConsumedObject,
    ArithmeticOverflow(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for EconomicActionErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRecordVersion(version) => {
                write!(
                    formatter,
                    "invalid economic action record version: {version}"
                )
            }
            Self::InvalidValidityRange => {
                formatter.write_str("economic action validity range is reversed")
            }
            Self::ZeroIdentifier(field) => write!(formatter, "zero identifier: {field}"),
            Self::TooManyConsumedObjects { actual, maximum } => write!(
                formatter,
                "economic action consumed object count {actual} exceeds {maximum}"
            ),
            Self::DuplicateConsumedObject => formatter.write_str("duplicate consumed object"),
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::EmptyInput => formatter.write_str("economic action input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "economic action input length {actual} exceeds {maximum}"
                )
            }
            Self::PostcardDecode => formatter.write_str("economic action postcard decode failed"),
            Self::TrailingBytes => {
                formatter.write_str("economic action postcard input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("economic action postcard input is not canonical")
            }
        }
    }
}

macro_rules! nonzero_identifier_type {
    ($name:ident, $label:literal) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name([u8; 32]);

        impl $name {
            pub fn new(bytes: [u8; 32]) -> Result<Self, EconomicActionErrorV1> {
                if bytes == [0; 32] {
                    return Err(EconomicActionErrorV1::ZeroIdentifier($label));
                }
                Ok(Self(bytes))
            }

            pub const fn as_bytes(&self) -> &[u8; 32] {
                &self.0
            }

            pub const fn into_bytes(self) -> [u8; 32] {
                self.0
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
                let bytes = <[u8; 32]>::deserialize(deserializer)?;
                Self::new(bytes).map_err(de::Error::custom)
            }
        }
    };
}

nonzero_identifier_type!(EconomicActionTypeIdV1, "action_type_id");
nonzero_identifier_type!(AuthorizationSubjectIdV1, "authorization_subject_id");
nonzero_identifier_type!(AuthorizationScopeIdV1, "authorization_scope_id");
nonzero_identifier_type!(AuthorizationGrantIdV1, "authorization_grant_id");
nonzero_identifier_type!(EconomicActionIdV1, "economic_action_id");
nonzero_identifier_type!(
    AuthorizationConsumptionNullifierV1,
    "authorization_consumption_nullifier"
);
