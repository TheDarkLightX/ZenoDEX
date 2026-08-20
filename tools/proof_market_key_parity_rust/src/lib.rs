//! Research-only Rust projection of the Python EconomicWorkKey V2 encoding.
//!
//! This crate owns no settlement, proof-admission, reserve, or runtime writer
//! authority.  Its ASCII input subset exists to compare canonical bytes and
//! SHA-256 output against the independent Python reference.

use sha2::{Digest, Sha256};
use std::fmt;

pub const CANONICAL_WORK_KEY_PREFIX_V2: &str = "ewk:v2:";
pub const CANONICAL_WORK_KEY_DOMAIN_V2: &[u8] = b"ZenoDEX/EconomicWorkKey/v2\0";
pub const MAX_CANONICAL_WORK_FIELD_BYTES_V2: usize = 1_048_576;

const ECONOMIC_WORK_FIELDS_V2: [(&str, usize); 7] = [
    ("product_kind", 0),
    ("claim", 1),
    ("assumptions", 2),
    ("public_inputs", 3),
    ("requested_output", 4),
    ("verifier_profile", 5),
    ("release", 6),
];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EconomicWorkDescriptorV2 {
    pub product_kind: String,
    pub claim: String,
    pub assumptions: String,
    pub public_inputs: String,
    pub requested_output: String,
    pub verifier_profile: String,
    pub release: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WorkKeyErrorV2 {
    EmptyField(&'static str),
    NonAsciiField(&'static str),
    WhitespaceField(&'static str),
    ControlField(&'static str),
    OversizedField(&'static str),
}

impl fmt::Display for WorkKeyErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyField(field) => write!(formatter, "{field} is empty"),
            Self::NonAsciiField(field) => write!(formatter, "{field} is not ASCII"),
            Self::WhitespaceField(field) => {
                write!(formatter, "{field} has leading or trailing whitespace")
            }
            Self::ControlField(field) => write!(formatter, "{field} has control characters"),
            Self::OversizedField(field) => write!(formatter, "{field} exceeds the byte bound"),
        }
    }
}

impl std::error::Error for WorkKeyErrorV2 {}

fn descriptor_fields(descriptor: &EconomicWorkDescriptorV2) -> [(&'static str, &str); 7] {
    [
        ("product_kind", descriptor.product_kind.as_str()),
        ("claim", descriptor.claim.as_str()),
        ("assumptions", descriptor.assumptions.as_str()),
        ("public_inputs", descriptor.public_inputs.as_str()),
        ("requested_output", descriptor.requested_output.as_str()),
        ("verifier_profile", descriptor.verifier_profile.as_str()),
        ("release", descriptor.release.as_str()),
    ]
}

fn validate_field<'a>(value: &'a str, field: &'static str) -> Result<&'a [u8], WorkKeyErrorV2> {
    if value.is_empty() {
        return Err(WorkKeyErrorV2::EmptyField(field));
    }
    if !value.is_ascii() {
        return Err(WorkKeyErrorV2::NonAsciiField(field));
    }
    if value.trim() != value {
        return Err(WorkKeyErrorV2::WhitespaceField(field));
    }
    if value.chars().any(char::is_control) {
        return Err(WorkKeyErrorV2::ControlField(field));
    }
    if value.len() > MAX_CANONICAL_WORK_FIELD_BYTES_V2 {
        return Err(WorkKeyErrorV2::OversizedField(field));
    }
    Ok(value.as_bytes())
}

fn append_frame(output: &mut Vec<u8>, value: &[u8]) {
    output.extend_from_slice(&(value.len() as u32).to_be_bytes());
    output.extend_from_slice(value);
}

#[must_use]
pub fn canonical_economic_work_key_bytes_v2(
    descriptor: &EconomicWorkDescriptorV2,
) -> Result<Vec<u8>, WorkKeyErrorV2> {
    let fields = descriptor_fields(descriptor);
    let mut output = Vec::new();
    output.extend_from_slice(CANONICAL_WORK_KEY_DOMAIN_V2);
    for ((field_name, _), (_, field_value)) in ECONOMIC_WORK_FIELDS_V2.iter().zip(fields.iter()) {
        append_frame(&mut output, field_name.as_bytes());
        append_frame(&mut output, validate_field(field_value, field_name)?);
    }
    Ok(output)
}

#[must_use]
pub fn canonical_economic_work_key_v2(
    descriptor: &EconomicWorkDescriptorV2,
) -> Result<String, WorkKeyErrorV2> {
    let bytes = canonical_economic_work_key_bytes_v2(descriptor)?;
    let digest = Sha256::digest(bytes);
    Ok(format!(
        "{}{}",
        CANONICAL_WORK_KEY_PREFIX_V2,
        hex::encode(digest)
    ))
}
