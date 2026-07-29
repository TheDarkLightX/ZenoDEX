//! Exact untrusted carrier values for the unmounted FCIS B1B-1 checkpoint.
//!
//! This module contains canonical data, codecs, and audit roots only.  It has no
//! pinned verifier, migration authority, committed V2 state, transition,
//! receipt, bundle, proof, publication, shell, or mounted-runtime authority.

use num_bigint::{BigInt, BigUint};

use crate::canonical::{canonical_json_bytes, domain_sep_bytes, sha256_hex, JsonValue};

pub const FCIS_B1B_AUTHORITY_SCHEMA_REVISION_V2: &str = "zenodex/fcis/b1b-authority-carriers/v2";
pub const FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2: &str = "zenodex/fcis/state/authority-header/v2";
pub const DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2: &str =
    "zenodex/fcis/deployment/bootstrap-anchor-claim/v2";
pub const V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2: &str =
    "zenodex/fcis/migration/v1-to-v2-manifest/v2";

pub const BOOTSTRAP_ANCHOR_CLAIM_ROOT_DOMAIN_V2: &str = "fcis_deployment_bootstrap_anchor_claim";
pub const MIGRATION_MANIFEST_ROOT_DOMAIN_V2: &str = "fcis_v1_to_v2_migration_manifest";

pub const MAX_B1B_CANONICAL_BYTES_V2: usize = 65_536;
pub const MAX_B1B_JSON_DEPTH_V2: usize = 32;
pub const MAX_B1B_JSON_NODES_V2: usize = 256;
pub const MAX_B1B_JSON_COLLECTION_ITEMS_V2: usize = 64;
const MAX_TEXT_CHARACTERS_V2: usize = 4_096;
const MAX_TEXT_UTF8_BYTES_V2: usize = 16_384;

struct JsonResourceScannerV2 {
    depth: usize,
    nodes: usize,
    collection_commas: Vec<usize>,
    in_string: bool,
    escaped: bool,
    in_primitive: bool,
}

impl JsonResourceScannerV2 {
    fn new() -> Self {
        Self {
            depth: 0,
            nodes: 0,
            collection_commas: Vec::new(),
            in_string: false,
            escaped: false,
            in_primitive: false,
        }
    }

    fn scan(&mut self, text: &str) -> Result<(), B1BAuthorityCarrierRejectV2> {
        for character in text.chars() {
            if self.in_string {
                self.scan_string_character(character);
                continue;
            }
            if self.in_primitive
                && !matches!(character, ' ' | '\t' | '\r' | '\n' | ',' | ']' | '}' | ':')
            {
                continue;
            }
            self.in_primitive = false;
            self.scan_token(character)?;
        }
        Ok(())
    }

    fn scan_string_character(&mut self, character: char) {
        if self.escaped {
            self.escaped = false;
        } else if character == '\\' {
            self.escaped = true;
        } else if character == '"' {
            self.in_string = false;
        }
    }

    fn scan_token(&mut self, character: char) -> Result<(), B1BAuthorityCarrierRejectV2> {
        match character {
            '"' => {
                self.in_string = true;
                self.add_node()
            }
            '[' | '{' => {
                if self.depth >= MAX_B1B_JSON_DEPTH_V2 {
                    return Err(B1BAuthorityCarrierRejectV2::resource(
                        B1BAuthorityCarrierCodeV2::JsonDepthLimit,
                    ));
                }
                self.add_node()?;
                self.depth += 1;
                self.collection_commas.push(0);
                Ok(())
            }
            ']' | '}' => {
                if self.depth > 0 {
                    self.depth -= 1;
                    self.collection_commas.pop();
                }
                Ok(())
            }
            ',' => {
                if let Some(commas) = self.collection_commas.last_mut() {
                    let next_commas = *commas + 1;
                    if next_commas >= MAX_B1B_JSON_COLLECTION_ITEMS_V2 {
                        return Err(B1BAuthorityCarrierRejectV2::resource(
                            B1BAuthorityCarrierCodeV2::JsonCollectionLimit,
                        ));
                    }
                    *commas = next_commas;
                }
                Ok(())
            }
            '-' | '0'..='9' | 't' | 'f' | 'n' => {
                self.in_primitive = true;
                self.add_node()
            }
            _ => Ok(()),
        }
    }

    fn add_node(&mut self) -> Result<(), B1BAuthorityCarrierRejectV2> {
        self.nodes += 1;
        if self.nodes > MAX_B1B_JSON_NODES_V2 {
            return Err(B1BAuthorityCarrierRejectV2::resource(
                B1BAuthorityCarrierCodeV2::JsonNodeLimit,
            ));
        }
        Ok(())
    }
}

pub fn validate_fcis_b1b_json_resource_bounds_v2(
    payload: &[u8],
) -> Result<(), B1BAuthorityCarrierRejectV2> {
    if payload.len() > MAX_B1B_CANONICAL_BYTES_V2 {
        return Err(B1BAuthorityCarrierRejectV2::resource(
            B1BAuthorityCarrierCodeV2::ByteLimit,
        ));
    }
    let text = std::str::from_utf8(payload).map_err(|_| {
        B1BAuthorityCarrierRejectV2::resource(B1BAuthorityCarrierCodeV2::InvalidUtf8)
    })?;
    JsonResourceScannerV2::new().scan(text)
}

fn u256_max() -> BigUint {
    (BigUint::from(1_u8) << 256_usize) - BigUint::from(1_u8)
}

fn text_is_canonical(value: &str) -> bool {
    !value.is_empty()
        && value.chars().count() <= MAX_TEXT_CHARACTERS_V2
        && value.len() <= MAX_TEXT_UTF8_BYTES_V2
}

fn digest_is_canonical(value: &str) -> bool {
    value.len() == 66
        && value.starts_with("0x")
        && value
            .as_bytes()
            .iter()
            .skip(2)
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum B1BAuthorityCarrierCodeV2 {
    InvalidValue,
    ByteLimit,
    InvalidUtf8,
    JsonDepthLimit,
    JsonNodeLimit,
    JsonCollectionLimit,
}

impl B1BAuthorityCarrierCodeV2 {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::InvalidValue => "invalid_value",
            Self::ByteLimit => "byte_limit",
            Self::InvalidUtf8 => "invalid_utf8",
            Self::JsonDepthLimit => "json_depth_limit",
            Self::JsonNodeLimit => "json_node_limit",
            Self::JsonCollectionLimit => "json_collection_limit",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct B1BAuthorityCarrierRejectV2 {
    code: B1BAuthorityCarrierCodeV2,
    path: Vec<String>,
}

impl B1BAuthorityCarrierRejectV2 {
    fn resource(code: B1BAuthorityCarrierCodeV2) -> Self {
        Self {
            code,
            path: Vec::new(),
        }
    }

    fn invalid(path: &[&str]) -> Self {
        Self {
            code: B1BAuthorityCarrierCodeV2::InvalidValue,
            path: path.iter().map(|part| (*part).to_owned()).collect(),
        }
    }

    pub fn code(&self) -> B1BAuthorityCarrierCodeV2 {
        self.code
    }

    pub fn path(&self) -> &[String] {
        &self.path
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FCISAuthorityHeaderV2 {
    chain_deployment_id: String,
    sequence: BigUint,
    fee_distribution_configuration_root: String,
}

impl FCISAuthorityHeaderV2 {
    pub fn try_new(
        chain_deployment_id: String,
        sequence: BigUint,
        fee_distribution_configuration_root: String,
    ) -> Result<Self, B1BAuthorityCarrierRejectV2> {
        if !text_is_canonical(&chain_deployment_id) {
            return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                "authority_header",
                "chain_deployment_id",
            ]));
        }
        if sequence > u256_max() {
            return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                "authority_header",
                "sequence",
            ]));
        }
        if !digest_is_canonical(&fee_distribution_configuration_root) {
            return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                "authority_header",
                "fee_distribution_configuration_root",
            ]));
        }
        Ok(Self {
            chain_deployment_id,
            sequence,
            fee_distribution_configuration_root,
        })
    }

    pub fn chain_deployment_id(&self) -> &str {
        &self.chain_deployment_id
    }

    pub fn sequence(&self) -> &BigUint {
        &self.sequence
    }

    pub fn fee_distribution_configuration_root(&self) -> &str {
        &self.fee_distribution_configuration_root
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeploymentBootstrapAnchorClaimV2 {
    chain_deployment_id: String,
    expected_migration_manifest_root: String,
}

impl DeploymentBootstrapAnchorClaimV2 {
    pub fn try_new(
        chain_deployment_id: String,
        expected_migration_manifest_root: String,
    ) -> Result<Self, B1BAuthorityCarrierRejectV2> {
        if !text_is_canonical(&chain_deployment_id) {
            return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                "bootstrap_anchor_claim",
                "chain_deployment_id",
            ]));
        }
        if !digest_is_canonical(&expected_migration_manifest_root) {
            return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                "bootstrap_anchor_claim",
                "expected_migration_manifest_root",
            ]));
        }
        Ok(Self {
            chain_deployment_id,
            expected_migration_manifest_root,
        })
    }

    pub fn chain_deployment_id(&self) -> &str {
        &self.chain_deployment_id
    }

    pub fn expected_migration_manifest_root(&self) -> &str {
        &self.expected_migration_manifest_root
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct V1ToV2MigrationManifestV2 {
    chain_deployment_id: String,
    expected_v1_pre_root: String,
    fee_distribution_domain_id: String,
    expected_initial_configuration_root: String,
    initial_sequence: BigUint,
    initial_configuration_version: BigUint,
    initial_activation_sequence: BigUint,
    source_snapshot_version: BigUint,
    target_snapshot_version: BigUint,
}

impl V1ToV2MigrationManifestV2 {
    #[allow(clippy::too_many_arguments)]
    pub fn try_new(
        chain_deployment_id: String,
        expected_v1_pre_root: String,
        fee_distribution_domain_id: String,
        expected_initial_configuration_root: String,
        initial_sequence: BigUint,
        initial_configuration_version: BigUint,
        initial_activation_sequence: BigUint,
        source_snapshot_version: BigUint,
        target_snapshot_version: BigUint,
    ) -> Result<Self, B1BAuthorityCarrierRejectV2> {
        if !text_is_canonical(&chain_deployment_id) {
            return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                "migration_manifest",
                "chain_deployment_id",
            ]));
        }
        if !digest_is_canonical(&expected_v1_pre_root) {
            return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                "migration_manifest",
                "expected_v1_pre_root",
            ]));
        }
        if !text_is_canonical(&fee_distribution_domain_id) {
            return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                "migration_manifest",
                "fee_distribution_domain_id",
            ]));
        }
        if !digest_is_canonical(&expected_initial_configuration_root) {
            return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                "migration_manifest",
                "expected_initial_configuration_root",
            ]));
        }
        for (name, value, positive) in [
            ("initial_sequence", &initial_sequence, false),
            (
                "initial_configuration_version",
                &initial_configuration_version,
                true,
            ),
            (
                "initial_activation_sequence",
                &initial_activation_sequence,
                false,
            ),
            ("source_snapshot_version", &source_snapshot_version, false),
            ("target_snapshot_version", &target_snapshot_version, false),
        ] {
            if value > &u256_max() || (positive && value == &BigUint::ZERO) {
                return Err(B1BAuthorityCarrierRejectV2::invalid(&[
                    "migration_manifest",
                    name,
                ]));
            }
        }
        Ok(Self {
            chain_deployment_id,
            expected_v1_pre_root,
            fee_distribution_domain_id,
            expected_initial_configuration_root,
            initial_sequence,
            initial_configuration_version,
            initial_activation_sequence,
            source_snapshot_version,
            target_snapshot_version,
        })
    }

    pub fn chain_deployment_id(&self) -> &str {
        &self.chain_deployment_id
    }

    pub fn expected_v1_pre_root(&self) -> &str {
        &self.expected_v1_pre_root
    }

    pub fn fee_distribution_domain_id(&self) -> &str {
        &self.fee_distribution_domain_id
    }

    pub fn expected_initial_configuration_root(&self) -> &str {
        &self.expected_initial_configuration_root
    }

    pub fn initial_sequence(&self) -> &BigUint {
        &self.initial_sequence
    }

    pub fn initial_configuration_version(&self) -> &BigUint {
        &self.initial_configuration_version
    }

    pub fn initial_activation_sequence(&self) -> &BigUint {
        &self.initial_activation_sequence
    }

    pub fn source_snapshot_version(&self) -> &BigUint {
        &self.source_snapshot_version
    }

    pub fn target_snapshot_version(&self) -> &BigUint {
        &self.target_snapshot_version
    }
}

fn int_json(value: BigUint) -> JsonValue {
    JsonValue::Int(BigInt::from(value))
}

fn envelope(schema: &str, value: JsonValue) -> Vec<u8> {
    canonical_json_bytes(&JsonValue::Object(vec![
        ("schema".to_owned(), JsonValue::Str(schema.to_owned())),
        ("value".to_owned(), value),
    ]))
}

fn authority_header_json(value: &FCISAuthorityHeaderV2) -> JsonValue {
    JsonValue::Object(vec![
        (
            "chain_deployment_id".to_owned(),
            JsonValue::Str(value.chain_deployment_id.clone()),
        ),
        ("sequence".to_owned(), int_json(value.sequence.clone())),
        (
            "fee_distribution_configuration_root".to_owned(),
            JsonValue::Str(value.fee_distribution_configuration_root.clone()),
        ),
    ])
}

fn bootstrap_anchor_claim_json(value: &DeploymentBootstrapAnchorClaimV2) -> JsonValue {
    JsonValue::Object(vec![
        (
            "chain_deployment_id".to_owned(),
            JsonValue::Str(value.chain_deployment_id.clone()),
        ),
        (
            "expected_migration_manifest_root".to_owned(),
            JsonValue::Str(value.expected_migration_manifest_root.clone()),
        ),
    ])
}

fn migration_manifest_json(value: &V1ToV2MigrationManifestV2) -> JsonValue {
    JsonValue::Object(vec![
        (
            "chain_deployment_id".to_owned(),
            JsonValue::Str(value.chain_deployment_id.clone()),
        ),
        (
            "expected_v1_pre_root".to_owned(),
            JsonValue::Str(value.expected_v1_pre_root.clone()),
        ),
        (
            "fee_distribution_domain_id".to_owned(),
            JsonValue::Str(value.fee_distribution_domain_id.clone()),
        ),
        (
            "expected_initial_configuration_root".to_owned(),
            JsonValue::Str(value.expected_initial_configuration_root.clone()),
        ),
        (
            "initial_sequence".to_owned(),
            int_json(value.initial_sequence.clone()),
        ),
        (
            "initial_configuration_version".to_owned(),
            int_json(value.initial_configuration_version.clone()),
        ),
        (
            "initial_activation_sequence".to_owned(),
            int_json(value.initial_activation_sequence.clone()),
        ),
        (
            "source_snapshot_version".to_owned(),
            int_json(value.source_snapshot_version.clone()),
        ),
        (
            "target_snapshot_version".to_owned(),
            int_json(value.target_snapshot_version.clone()),
        ),
    ])
}

pub fn encode_fcis_authority_header_v2(value: &FCISAuthorityHeaderV2) -> Vec<u8> {
    envelope(
        FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
        authority_header_json(value),
    )
}

pub fn encode_deployment_bootstrap_anchor_claim_v2(
    value: &DeploymentBootstrapAnchorClaimV2,
) -> Vec<u8> {
    envelope(
        DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
        bootstrap_anchor_claim_json(value),
    )
}

pub fn encode_v1_to_v2_migration_manifest_v2(value: &V1ToV2MigrationManifestV2) -> Vec<u8> {
    envelope(
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
        migration_manifest_json(value),
    )
}

pub fn canonical_bootstrap_anchor_claim_root_v2(
    value: &DeploymentBootstrapAnchorClaimV2,
) -> String {
    let mut preimage = domain_sep_bytes(BOOTSTRAP_ANCHOR_CLAIM_ROOT_DOMAIN_V2, 2);
    preimage.extend(encode_deployment_bootstrap_anchor_claim_v2(value));
    sha256_hex(&preimage)
}

pub fn canonical_v1_to_v2_migration_manifest_root_v2(value: &V1ToV2MigrationManifestV2) -> String {
    let mut preimage = domain_sep_bytes(MIGRATION_MANIFEST_ROOT_DOMAIN_V2, 2);
    preimage.extend(encode_v1_to_v2_migration_manifest_v2(value));
    sha256_hex(&preimage)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> serde_json::Value {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/fixtures/fcis_b1b_authority_v2_golden.json"
        );
        let raw = std::fs::read_to_string(path).expect("shared B1B fixture exists");
        serde_json::from_str(&raw).expect("shared B1B fixture parses")
    }

    fn biguint(value: &serde_json::Value) -> BigUint {
        value
            .to_string()
            .parse::<BigUint>()
            .expect("fixture integer is a BigUint")
    }

    fn case<'a>(document: &'a serde_json::Value, id: &str) -> &'a serde_json::Value {
        document["cases"]
            .as_array()
            .expect("fixture cases")
            .iter()
            .find(|case| case["id"].as_str() == Some(id))
            .expect("fixture case exists")
    }

    #[test]
    fn fcis_b1b_authority_golden_shared_vectors_match_python_bytes_and_roots() {
        let document = fixture();

        let header_case = case(&document, "authority_header_initial");
        let header = FCISAuthorityHeaderV2::try_new(
            header_case["value"]["chain_deployment_id"]
                .as_str()
                .unwrap()
                .to_owned(),
            biguint(&header_case["value"]["sequence"]),
            header_case["value"]["fee_distribution_configuration_root"]
                .as_str()
                .unwrap()
                .to_owned(),
        )
        .unwrap();
        assert_eq!(
            String::from_utf8(encode_fcis_authority_header_v2(&header)).unwrap(),
            header_case["canonical_utf8"].as_str().unwrap()
        );

        let anchor_case = case(&document, "bootstrap_anchor_claim");
        let anchor = DeploymentBootstrapAnchorClaimV2::try_new(
            anchor_case["value"]["chain_deployment_id"]
                .as_str()
                .unwrap()
                .to_owned(),
            anchor_case["value"]["expected_migration_manifest_root"]
                .as_str()
                .unwrap()
                .to_owned(),
        )
        .unwrap();
        assert_eq!(
            String::from_utf8(encode_deployment_bootstrap_anchor_claim_v2(&anchor)).unwrap(),
            anchor_case["canonical_utf8"].as_str().unwrap()
        );
        assert_eq!(
            canonical_bootstrap_anchor_claim_root_v2(&anchor),
            anchor_case["root"].as_str().unwrap()
        );

        let manifest_case = case(&document, "v1_to_v2_migration_manifest");
        let value = &manifest_case["value"];
        let manifest = V1ToV2MigrationManifestV2::try_new(
            value["chain_deployment_id"].as_str().unwrap().to_owned(),
            value["expected_v1_pre_root"].as_str().unwrap().to_owned(),
            value["fee_distribution_domain_id"]
                .as_str()
                .unwrap()
                .to_owned(),
            value["expected_initial_configuration_root"]
                .as_str()
                .unwrap()
                .to_owned(),
            biguint(&value["initial_sequence"]),
            biguint(&value["initial_configuration_version"]),
            biguint(&value["initial_activation_sequence"]),
            biguint(&value["source_snapshot_version"]),
            biguint(&value["target_snapshot_version"]),
        )
        .unwrap();
        assert_eq!(
            String::from_utf8(encode_v1_to_v2_migration_manifest_v2(&manifest)).unwrap(),
            manifest_case["canonical_utf8"].as_str().unwrap()
        );
        assert_eq!(
            canonical_v1_to_v2_migration_manifest_root_v2(&manifest),
            manifest_case["root"].as_str().unwrap()
        );
    }

    #[test]
    fn fcis_b1b_authority_u256_boundaries_and_carrier_only_constants() {
        let document = fixture();
        let boundaries = document["u256_boundaries"]
            .as_array()
            .expect("u256 boundaries");
        assert_eq!(boundaries.len(), 4);
        for encoded in boundaries {
            let boundary = biguint(encoded);
            let header = FCISAuthorityHeaderV2::try_new(
                "deployment".to_owned(),
                boundary.clone(),
                format!("0x{}", "0".repeat(64)),
            )
            .unwrap();
            assert_eq!(header.sequence(), &boundary);

            let positive_version = if boundary == BigUint::ZERO {
                BigUint::from(1_u8)
            } else {
                boundary.clone()
            };
            let manifest = V1ToV2MigrationManifestV2::try_new(
                "deployment".to_owned(),
                format!("0x{}", "0".repeat(64)),
                "domain".to_owned(),
                format!("0x{}", "1".repeat(64)),
                boundary.clone(),
                positive_version.clone(),
                boundary.clone(),
                boundary.clone(),
                boundary.clone(),
            )
            .unwrap();
            assert_eq!(manifest.initial_sequence(), &boundary);
            assert_eq!(manifest.initial_configuration_version(), &positive_version);
            assert_eq!(manifest.initial_activation_sequence(), &boundary);
            assert_eq!(manifest.source_snapshot_version(), &boundary);
            assert_eq!(manifest.target_snapshot_version(), &boundary);
        }

        let carrier_only = case(&document, "structurally_exact_wrong_fixed_constants");
        let value = &carrier_only["value"];
        let manifest = V1ToV2MigrationManifestV2::try_new(
            value["chain_deployment_id"].as_str().unwrap().to_owned(),
            value["expected_v1_pre_root"].as_str().unwrap().to_owned(),
            value["fee_distribution_domain_id"]
                .as_str()
                .unwrap()
                .to_owned(),
            value["expected_initial_configuration_root"]
                .as_str()
                .unwrap()
                .to_owned(),
            biguint(&value["initial_sequence"]),
            biguint(&value["initial_configuration_version"]),
            biguint(&value["initial_activation_sequence"]),
            biguint(&value["source_snapshot_version"]),
            biguint(&value["target_snapshot_version"]),
        )
        .unwrap();
        assert_eq!(manifest.source_snapshot_version(), &BigUint::from(3_u8));
        assert_eq!(manifest.target_snapshot_version(), &BigUint::from(6_u8));
    }

    #[test]
    fn fcis_b1b_authority_golden_shared_negative_vectors_reject() {
        let document = fixture();
        let cases = document["negative_cases"]
            .as_array()
            .expect("negative cases");
        let mut rust_cases = 0_usize;
        for case in cases {
            let languages = case["languages"].as_array().expect("languages");
            let is_rust = languages.iter().any(|value| value.as_str() == Some("rust"));
            if !is_rust {
                assert!(case["rust_exclusion"].as_str().is_some());
                continue;
            }
            rust_cases += 1;
            assert_eq!(case["expected_code"].as_str(), Some("invalid_value"));
            let kind = case["kind"].as_str().expect("negative kind");
            let rejected = match kind {
                "identifier" => FCISAuthorityHeaderV2::try_new(
                    case["value"].as_str().expect("identifier").to_owned(),
                    BigUint::ZERO,
                    format!("0x{}", "0".repeat(64)),
                )
                .is_err(),
                "digest" => FCISAuthorityHeaderV2::try_new(
                    "deployment".to_owned(),
                    BigUint::ZERO,
                    case["value"].as_str().expect("digest").to_owned(),
                )
                .is_err(),
                "u256" => FCISAuthorityHeaderV2::try_new(
                    "deployment".to_owned(),
                    biguint(&case["value"]),
                    format!("0x{}", "0".repeat(64)),
                )
                .is_err(),
                "positive_u256" => V1ToV2MigrationManifestV2::try_new(
                    "deployment".to_owned(),
                    format!("0x{}", "0".repeat(64)),
                    "domain".to_owned(),
                    format!("0x{}", "1".repeat(64)),
                    BigUint::ZERO,
                    biguint(&case["value"]),
                    BigUint::ZERO,
                    BigUint::from(4_u8),
                    BigUint::from(5_u8),
                )
                .is_err(),
                other => panic!("unknown negative kind: {other}"),
            };
            assert!(rejected, "negative case accepted: {}", case["id"]);
        }
        assert_eq!(rust_cases, 6);
    }
}

#[cfg(test)]
mod resource_tests {
    use super::*;

    fn nested_array(depth: usize) -> Vec<u8> {
        format!("{}0{}", "[".repeat(depth), "]".repeat(depth)).into_bytes()
    }

    fn nested_object(depth: usize) -> Vec<u8> {
        format!("{}0{}", "{\"k\":".repeat(depth), "}".repeat(depth)).into_bytes()
    }

    fn nested_mixed(depth: usize) -> Vec<u8> {
        let mut prefixes = Vec::new();
        let mut suffixes = Vec::new();
        for index in 0..depth {
            if index % 2 == 0 {
                prefixes.push("[");
                suffixes.push("]");
            } else {
                prefixes.push("{\"k\":");
                suffixes.push("}");
            }
        }
        suffixes.reverse();
        format!("{}0{}", prefixes.join(""), suffixes.join("")).into_bytes()
    }

    fn resource_code(payload: &[u8]) -> Option<B1BAuthorityCarrierCodeV2> {
        validate_fcis_b1b_json_resource_bounds_v2(payload)
            .err()
            .map(|reject| {
                assert!(reject.path().is_empty());
                reject.code()
            })
    }

    #[test]
    fn fcis_b1b_json_resource_depth_boundaries_match_python() {
        for builder in [
            nested_array as fn(usize) -> Vec<u8>,
            nested_object,
            nested_mixed,
        ] {
            assert_eq!(resource_code(&builder(MAX_B1B_JSON_DEPTH_V2)), None);
            assert_eq!(
                resource_code(&builder(MAX_B1B_JSON_DEPTH_V2 + 1)),
                Some(B1BAuthorityCarrierCodeV2::JsonDepthLimit)
            );
        }
        assert_eq!(
            resource_code(&nested_array(1_000)),
            Some(B1BAuthorityCarrierCodeV2::JsonDepthLimit)
        );
    }

    #[test]
    fn fcis_b1b_json_resource_collection_boundaries_match_python() {
        let exact_array = format!(
            "[{}]",
            vec!["0"; MAX_B1B_JSON_COLLECTION_ITEMS_V2].join(",")
        );
        let oversized_array = format!(
            "[{}]",
            vec!["0"; MAX_B1B_JSON_COLLECTION_ITEMS_V2 + 1].join(",")
        );
        assert_eq!(resource_code(exact_array.as_bytes()), None);
        assert_eq!(
            resource_code(oversized_array.as_bytes()),
            Some(B1BAuthorityCarrierCodeV2::JsonCollectionLimit)
        );

        let exact_object = format!(
            "{{{}}}",
            (0..MAX_B1B_JSON_COLLECTION_ITEMS_V2)
                .map(|index| format!("\"k{index}\":0"))
                .collect::<Vec<_>>()
                .join(",")
        );
        let oversized_object = format!(
            "{{{}}}",
            (0..=MAX_B1B_JSON_COLLECTION_ITEMS_V2)
                .map(|index| format!("\"k{index}\":0"))
                .collect::<Vec<_>>()
                .join(",")
        );
        assert_eq!(resource_code(exact_object.as_bytes()), None);
        assert_eq!(
            resource_code(oversized_object.as_bytes()),
            Some(B1BAuthorityCarrierCodeV2::JsonCollectionLimit)
        );
    }

    #[test]
    fn fcis_b1b_json_resource_node_boundaries_match_python() {
        fn payload(sizes: &[usize]) -> Vec<u8> {
            let children = sizes
                .iter()
                .map(|size| format!("[{}]", vec!["0"; *size].join(",")))
                .collect::<Vec<_>>()
                .join(",");
            format!("[{children}]").into_bytes()
        }

        assert_eq!(MAX_B1B_JSON_NODES_V2, 256);
        assert_eq!(resource_code(&payload(&[63, 63, 63, 62])), None);
        assert_eq!(
            resource_code(&payload(&[63, 63, 63, 63])),
            Some(B1BAuthorityCarrierCodeV2::JsonNodeLimit)
        );
    }

    #[test]
    fn fcis_b1b_json_resource_byte_and_utf8_rejections_are_closed() {
        assert_eq!(
            resource_code(&vec![b'0'; MAX_B1B_CANONICAL_BYTES_V2 + 1]),
            Some(B1BAuthorityCarrierCodeV2::ByteLimit)
        );
        assert_eq!(
            resource_code(&[0xff]),
            Some(B1BAuthorityCarrierCodeV2::InvalidUtf8)
        );
        assert_eq!(
            B1BAuthorityCarrierCodeV2::JsonDepthLimit.as_str(),
            "json_depth_limit"
        );
    }

    #[test]
    fn fcis_b1b_json_resource_shared_vectors_match_python() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/fixtures/fcis_b1b_authority_v2_golden.json"
        );
        let raw = std::fs::read_to_string(path).expect("shared B1B fixture exists");
        let document: serde_json::Value =
            serde_json::from_str(&raw).expect("shared B1B fixture parses");
        let limits = &document["json_resource_limits"];
        assert_eq!(
            limits["maximum_depth"].as_u64(),
            Some(MAX_B1B_JSON_DEPTH_V2 as u64)
        );
        assert_eq!(
            limits["maximum_nodes"].as_u64(),
            Some(MAX_B1B_JSON_NODES_V2 as u64)
        );
        assert_eq!(
            limits["maximum_collection_items"].as_u64(),
            Some(MAX_B1B_JSON_COLLECTION_ITEMS_V2 as u64)
        );
        for case in limits["cases"].as_array().expect("resource cases") {
            let kind = case["kind"].as_str().expect("resource kind");
            let payload = match kind {
                "nested_array" => nested_array(case["parameter"].as_u64().expect("depth") as usize),
                "nested_object" => {
                    nested_object(case["parameter"].as_u64().expect("depth") as usize)
                }
                "nested_mixed" => nested_mixed(case["parameter"].as_u64().expect("depth") as usize),
                "flat_array" => {
                    let size = case["parameter"].as_u64().expect("array size") as usize;
                    format!("[{}]", vec!["0"; size].join(",")).into_bytes()
                }
                "node_fanout" => {
                    let children = case["parameter"]
                        .as_array()
                        .expect("fanout sizes")
                        .iter()
                        .map(|size| {
                            format!(
                                "[{}]",
                                vec!["0"; size.as_u64().expect("fanout size") as usize].join(",")
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(",");
                    format!("[{children}]").into_bytes()
                }
                "byte_repeat" => {
                    vec![b'0'; case["parameter"].as_u64().expect("byte count") as usize]
                }
                "invalid_utf8" => {
                    vec![case["parameter"].as_u64().expect("invalid byte") as u8]
                }
                other => panic!("unknown resource-vector kind: {other}"),
            };
            let actual = resource_code(&payload).map(B1BAuthorityCarrierCodeV2::as_str);
            assert_eq!(
                actual,
                case["expected_code"].as_str(),
                "resource case {}",
                case["id"]
            );
        }
    }
}
