use core::fmt;

use serde::{de::DeserializeOwned, Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const GLOBAL_SETTLEMENT_ABI_V2: &str = "zenodex/global-settlement-abi/v2";
pub const MAX_TOKEN_BYTES_V2: usize = 160;
pub const MAX_CANONICAL_INPUT_BYTES_V2: usize = 1_048_576;
pub const ZERO_ROOT_V2: &str = "0x0000000000000000000000000000000000000000000000000000000000000000";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AbiErrorV2 {
    CanonicalEncoding(String),
    InvalidSchema(&'static str),
    InvalidToken(&'static str),
    InvalidRoot(&'static str),
    InvalidOrder(&'static str),
    InvalidBounds(&'static str),
    InvalidBinding(&'static str),
    Conservation(&'static str),
}

impl fmt::Display for AbiErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CanonicalEncoding(message) => write!(formatter, "canonical encoding: {message}"),
            Self::InvalidSchema(field) => write!(formatter, "invalid ABI V2 schema: {field}"),
            Self::InvalidToken(field) => {
                write!(formatter, "invalid printable ASCII token: {field}")
            }
            Self::InvalidRoot(field) => write!(formatter, "invalid canonical root: {field}"),
            Self::InvalidOrder(field) => write!(formatter, "invalid canonical order: {field}"),
            Self::InvalidBounds(field) => write!(formatter, "invalid ABI V2 bound: {field}"),
            Self::InvalidBinding(field) => write!(formatter, "invalid ABI V2 binding: {field}"),
            Self::Conservation(field) => write!(formatter, "conservation failure: {field}"),
        }
    }
}

impl std::error::Error for AbiErrorV2 {}

pub type AbiResultV2<T> = Result<T, AbiErrorV2>;

pub trait ValidateCanonicalV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()>;
}

#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct RootV2(String);

impl RootV2 {
    pub fn parse(
        value: impl Into<String>,
        field: &'static str,
        allow_zero: bool,
    ) -> AbiResultV2<Self> {
        let root = Self(value.into());
        root.validate(field, allow_zero)?;
        Ok(root)
    }

    pub fn zero() -> Self {
        Self(ZERO_ROOT_V2.to_owned())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn is_zero(&self) -> bool {
        self.0 == ZERO_ROOT_V2
    }

    pub fn validate(&self, field: &'static str, allow_zero: bool) -> AbiResultV2<()> {
        let bytes = self.0.as_bytes();
        let valid_hex = bytes.get(2..).is_some_and(|tail| {
            tail.iter()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
        });
        if bytes.len() != 66 || !self.0.starts_with("0x") || !valid_hex {
            return Err(AbiErrorV2::InvalidRoot(field));
        }
        if !allow_zero && self.is_zero() {
            return Err(AbiErrorV2::InvalidRoot(field));
        }
        Ok(())
    }
}

impl fmt::Display for RootV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

pub fn validate_schema_v2(schema: &str, expected: &str, field: &'static str) -> AbiResultV2<()> {
    if schema == expected {
        Ok(())
    } else {
        Err(AbiErrorV2::InvalidSchema(field))
    }
}

pub fn validate_token_v2(value: &str, field: &'static str) -> AbiResultV2<()> {
    let bytes = value.as_bytes();
    if bytes.is_empty()
        || bytes.len() > MAX_TOKEN_BYTES_V2
        || !bytes.iter().all(|byte| (0x21..=0x7e).contains(byte))
    {
        return Err(AbiErrorV2::InvalidToken(field));
    }
    Ok(())
}

pub fn validate_sorted_unique_tokens_v2(
    values: &[String],
    field: &'static str,
    allow_empty: bool,
) -> AbiResultV2<()> {
    if !allow_empty && values.is_empty() {
        return Err(AbiErrorV2::InvalidBounds(field));
    }
    for value in values {
        validate_token_v2(value, field)?;
    }
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(AbiErrorV2::InvalidOrder(field));
    }
    Ok(())
}

pub fn canonical_bytes_v2<T: Serialize>(value: &T) -> AbiResultV2<Vec<u8>> {
    let canonical_value = serde_json::to_value(value)
        .map_err(|error| AbiErrorV2::CanonicalEncoding(error.to_string()))?;
    reject_floating_point_values_v2(&canonical_value)?;
    serde_json::to_vec(&canonical_value)
        .map_err(|error| AbiErrorV2::CanonicalEncoding(error.to_string()))
}

fn reject_floating_point_values_v2(value: &serde_json::Value) -> AbiResultV2<()> {
    match value {
        serde_json::Value::Number(number)
            if number
                .to_string()
                .bytes()
                .any(|byte| matches!(byte, b'.' | b'e' | b'E')) =>
        {
            Err(AbiErrorV2::CanonicalEncoding(
                "floating-point values are unsupported".to_owned(),
            ))
        }
        serde_json::Value::Array(values) => {
            for item in values {
                reject_floating_point_values_v2(item)?;
            }
            Ok(())
        }
        serde_json::Value::Object(values) => {
            for item in values.values() {
                reject_floating_point_values_v2(item)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

pub fn decode_canonical_v2<T>(bytes: &[u8]) -> AbiResultV2<T>
where
    T: DeserializeOwned + Serialize + ValidateCanonicalV2,
{
    if bytes.is_empty() || bytes.len() > MAX_CANONICAL_INPUT_BYTES_V2 {
        return Err(AbiErrorV2::InvalidBounds("canonical input bytes"));
    }
    let value = serde_json::from_slice::<T>(bytes)
        .map_err(|error| AbiErrorV2::CanonicalEncoding(error.to_string()))?;
    if canonical_bytes_v2(&value)? != bytes {
        return Err(AbiErrorV2::CanonicalEncoding(
            "input bytes are not canonical".to_owned(),
        ));
    }
    value.validate_canonical_v2()?;
    Ok(value)
}

pub fn hash_global_v2<T: Serialize>(domain: &str, value: &T) -> AbiResultV2<RootV2> {
    validate_token_v2(domain, "hash domain")?;
    let canonical_bytes = canonical_bytes_v2(value)?;
    let mut digest = Sha256::new();
    digest.update(b"zenodex:");
    digest.update(domain.as_bytes());
    digest.update(b":v2\0");
    digest.update(canonical_bytes);
    RootV2::parse(
        format!("0x{}", hex::encode(digest.finalize())),
        "derived root",
        false,
    )
}

#[derive(Serialize)]
struct EconomicCommandBodyContentV2<'a, T: Serialize> {
    command_kind: &'a str,
    command: &'a T,
}

pub fn canonical_economic_command_body_bytes_v2<T: Serialize>(
    command_kind: &str,
    command: &T,
) -> AbiResultV2<Vec<u8>> {
    validate_token_v2(command_kind, "economic command body kind")?;
    canonical_bytes_v2(&EconomicCommandBodyContentV2 {
        command_kind,
        command,
    })
}

pub fn hash_economic_command_body_bytes_v2(command_body_bytes: &[u8]) -> AbiResultV2<RootV2> {
    if command_body_bytes.is_empty() {
        return Err(AbiErrorV2::InvalidBounds("economic command body bytes"));
    }
    let mut digest = Sha256::new();
    digest.update(b"zenodex:");
    digest.update(b"authenticated-economic-command-body-v2");
    digest.update(b":v2\0");
    digest.update(command_body_bytes);
    RootV2::parse(
        format!("0x{}", hex::encode(digest.finalize())),
        "economic command body hash",
        false,
    )
}

pub fn hash_economic_command_body_v2<T: Serialize>(
    command_kind: &str,
    command: &T,
) -> AbiResultV2<RootV2> {
    hash_economic_command_body_bytes_v2(&canonical_economic_command_body_bytes_v2(
        command_kind,
        command,
    )?)
}

pub fn hash_bytes_sha256_v2(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}
