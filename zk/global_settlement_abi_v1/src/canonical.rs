use core::fmt;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const GLOBAL_SETTLEMENT_ABI_V1: &str = "zenodex/global-settlement-abi/v1";
pub const MAX_TOKEN_BYTES_V1: usize = 160;
pub const MAX_ROUTE_MODULES_V1: usize = 8;
pub const MAX_EPOCH_COMMANDS_V1: usize = 64;
pub const MAX_EPOCH_LEAF_OCCURRENCES_V1: u64 = 64;
pub const MAX_POLICY_BINDINGS_V1: usize = 256;
pub const MAX_ASSET_POLICY_ROWS_V1: usize = 256;
pub const MAX_ASSET_BALANCE_ROWS_V1: usize = 4_096;
pub const MAX_ASSET_CUSTODY_ROWS_V1: usize = 4_096;
pub const MAX_EFFECT_PLAN_ROWS_V1: usize = 4_096;
pub const MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1: usize = 256;
pub const MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1: usize = 256;
pub const MAX_EFFECT_PLAN_LANE_WRITES_V1: usize = 12;
pub const MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1: usize = 4_096;
pub const MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1: usize = 4_096;
pub const MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1: usize = 4_096;
pub const MAX_GLOBAL_SUPPLY_ROWS_V1: usize = 256;
pub const MAX_GLOBAL_ORACLE_ROWS_V1: usize = 4_096;
pub const MAX_GLOBAL_REPLAY_ROWS_V1: usize = 4_096;
pub const MAX_GLOBAL_TERMINAL_ROWS_V1: usize = 4_096;
pub const MAX_GLOBAL_OUTBOX_ROWS_V1: usize = 4_096;
pub const MAX_JOURNAL_BYTES_V1: u64 = 1_048_576;
pub const MAX_LANE_MODULE_RECEIPT_BYTES_V1: usize = 16 * 1_048_576;
pub const MAX_CYCLE_BUDGET_V1: u64 = 1 << 40;
pub const MAX_ATOMS_V1: u128 = u128::MAX;
pub const ZERO_ROOT_V1: &str = "0x0000000000000000000000000000000000000000000000000000000000000000";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AbiErrorV1 {
    CanonicalEncoding(String),
    InvalidSchema,
    InvalidToken(&'static str),
    InvalidRoot(&'static str),
    InvalidOrder(&'static str),
    InvalidBounds(&'static str),
    InvalidBinding(&'static str),
    Conservation(&'static str),
}

impl fmt::Display for AbiErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CanonicalEncoding(message) => write!(formatter, "canonical encoding: {message}"),
            Self::InvalidSchema => formatter.write_str("invalid GlobalSettlementABI V1 schema"),
            Self::InvalidToken(field) => {
                write!(formatter, "invalid printable ASCII token: {field}")
            }
            Self::InvalidRoot(field) => write!(formatter, "invalid canonical root: {field}"),
            Self::InvalidOrder(field) => write!(formatter, "invalid canonical order: {field}"),
            Self::InvalidBounds(field) => write!(formatter, "invalid ABI V1 bound: {field}"),
            Self::InvalidBinding(field) => write!(formatter, "invalid ABI V1 binding: {field}"),
            Self::Conservation(field) => write!(formatter, "conservation failure: {field}"),
        }
    }
}

impl std::error::Error for AbiErrorV1 {}

pub type AbiResultV1<T> = Result<T, AbiErrorV1>;

#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct RootV1(String);

impl RootV1 {
    pub fn parse(
        value: impl Into<String>,
        field: &'static str,
        allow_zero: bool,
    ) -> AbiResultV1<Self> {
        let root = Self(value.into());
        root.validate(field, allow_zero)?;
        Ok(root)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn is_zero(&self) -> bool {
        self.0 == ZERO_ROOT_V1
    }

    pub fn validate(&self, field: &'static str, allow_zero: bool) -> AbiResultV1<()> {
        let bytes = self.0.as_bytes();
        let valid_hex = bytes.get(2..).is_some_and(|tail| {
            tail.iter()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
        });
        if bytes.len() != 66 || !self.0.starts_with("0x") || !valid_hex {
            return Err(AbiErrorV1::InvalidRoot(field));
        }
        if !allow_zero && self.is_zero() {
            return Err(AbiErrorV1::InvalidRoot(field));
        }
        Ok(())
    }
}

impl fmt::Display for RootV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

pub fn validate_schema_v1(schema: &str) -> AbiResultV1<()> {
    if schema == GLOBAL_SETTLEMENT_ABI_V1 {
        Ok(())
    } else {
        Err(AbiErrorV1::InvalidSchema)
    }
}

pub fn validate_token_v1(value: &str, field: &'static str) -> AbiResultV1<()> {
    let bytes = value.as_bytes();
    if bytes.is_empty()
        || bytes.len() > MAX_TOKEN_BYTES_V1
        || !bytes.iter().all(|byte| (0x21..=0x7e).contains(byte))
    {
        return Err(AbiErrorV1::InvalidToken(field));
    }
    Ok(())
}

pub fn validate_sorted_unique_tokens_v1(
    values: &[String],
    field: &'static str,
    allow_empty: bool,
) -> AbiResultV1<()> {
    if !allow_empty && values.is_empty() {
        return Err(AbiErrorV1::InvalidBounds(field));
    }
    for value in values {
        validate_token_v1(value, field)?;
    }
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(AbiErrorV1::InvalidOrder(field));
    }
    Ok(())
}

pub fn validate_semantic_unique_tokens_v1(
    values: &[String],
    field: &'static str,
) -> AbiResultV1<()> {
    for (index, value) in values.iter().enumerate() {
        validate_token_v1(value, field)?;
        if values[..index].contains(value) {
            return Err(AbiErrorV1::InvalidOrder(field));
        }
    }
    Ok(())
}

pub fn validate_root_sequence_v1(
    values: &[RootV1],
    field: &'static str,
    semantic_order: bool,
) -> AbiResultV1<()> {
    for (index, root) in values.iter().enumerate() {
        root.validate(field, false)?;
        if semantic_order && values[..index].contains(root) {
            return Err(AbiErrorV1::InvalidOrder(field));
        }
    }
    if !semantic_order && values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(AbiErrorV1::InvalidOrder(field));
    }
    Ok(())
}

pub fn canonical_bytes_v1<T: Serialize>(value: &T) -> AbiResultV1<Vec<u8>> {
    let canonical_value = serde_json::to_value(value)
        .map_err(|error| AbiErrorV1::CanonicalEncoding(error.to_string()))?;
    serde_json::to_vec(&canonical_value)
        .map_err(|error| AbiErrorV1::CanonicalEncoding(error.to_string()))
}

pub fn hash_global_v1<T: Serialize>(domain: &str, value: &T) -> AbiResultV1<RootV1> {
    validate_token_v1(domain, "hash domain")?;
    let canonical_bytes = canonical_bytes_v1(value)?;
    let mut digest = Sha256::new();
    digest.update(b"zenodex:");
    digest.update(domain.as_bytes());
    digest.update(b":v1\0");
    digest.update(canonical_bytes);
    RootV1::parse(
        format!("0x{}", hex::encode(digest.finalize())),
        "derived root",
        false,
    )
}

#[derive(Serialize)]
struct EconomicCommandBodyContentV1<'a, T: Serialize> {
    command_kind: &'a str,
    command: &'a T,
}

pub fn canonical_economic_command_body_bytes_v1<T: Serialize>(
    command_kind: &str,
    command: &T,
) -> AbiResultV1<Vec<u8>> {
    validate_token_v1(command_kind, "economic command body kind")?;
    canonical_bytes_v1(&EconomicCommandBodyContentV1 {
        command_kind,
        command,
    })
}

pub fn hash_economic_command_body_bytes_v1(command_body_bytes: &[u8]) -> AbiResultV1<RootV1> {
    if command_body_bytes.is_empty() {
        return Err(AbiErrorV1::InvalidBounds("economic command body bytes"));
    }
    let mut digest = Sha256::new();
    digest.update(b"zenodex:");
    digest.update(b"authenticated-economic-command-body-v1");
    digest.update(b":v1\0");
    digest.update(command_body_bytes);
    RootV1::parse(
        format!("0x{}", hex::encode(digest.finalize())),
        "economic command body hash",
        false,
    )
}

pub fn hash_economic_command_body_v1<T: Serialize>(
    command_kind: &str,
    command: &T,
) -> AbiResultV1<RootV1> {
    hash_economic_command_body_bytes_v1(&canonical_economic_command_body_bytes_v1(
        command_kind,
        command,
    )?)
}

pub fn hash_bytes_sha256_v1(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}
