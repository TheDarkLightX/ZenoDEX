//! Unmounted fee-distribution configuration claim validation.

use num_bigint::{BigInt, BigUint};

use crate::canonical::{canonical_json_bytes, domain_sep_bytes, sha256_hex, JsonValue};
use crate::fcis_fee_apportionment::{FeeDistributionPolicyV2, SRGD_ALGORITHM_VERSION_V1};

pub const FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2: &str = "zenodex/fcis/fee-distribution/policy/v2";
pub const FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2: &str =
    "zenodex/fcis/fee-distribution/configuration-body/v2";
pub const FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2: &str =
    "zenodex/fcis/fee-distribution/configuration-claim/v2";
pub const VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2: &str =
    "zenodex/fcis/fee-distribution/validated-configuration-claim/v2";
pub const PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2: &str =
    "PROVISIONAL_FEES_NO_SAME_BATCH_FUNDING_V2";

const MAX_TEXT_CHARACTERS_V2: usize = 4_096;
const MAX_TEXT_UTF8_BYTES_V2: usize = 16_384;

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
pub enum FeeDistributionConfigurationVerificationCodeV2 {
    WrongExactType,
    InvalidClaim,
    AlgorithmVersionMismatch,
    AcceptedLanguageVersionMismatch,
    PolicyRootMismatch,
    ConfigurationRootMismatch,
}

impl FeeDistributionConfigurationVerificationCodeV2 {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::WrongExactType => "wrong_exact_type",
            Self::InvalidClaim => "invalid_claim",
            Self::AlgorithmVersionMismatch => "algorithm_version_mismatch",
            Self::AcceptedLanguageVersionMismatch => "accepted_language_version_mismatch",
            Self::PolicyRootMismatch => "policy_root_mismatch",
            Self::ConfigurationRootMismatch => "configuration_root_mismatch",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeeDistributionConfigurationVerificationRejectV2 {
    code: FeeDistributionConfigurationVerificationCodeV2,
    path: Vec<String>,
}

impl FeeDistributionConfigurationVerificationRejectV2 {
    fn new(code: FeeDistributionConfigurationVerificationCodeV2, path: &[&str]) -> Self {
        Self {
            code,
            path: path.iter().map(|part| (*part).to_owned()).collect(),
        }
    }

    pub fn code(&self) -> FeeDistributionConfigurationVerificationCodeV2 {
        self.code
    }

    pub fn path(&self) -> &[String] {
        &self.path
    }
}

fn invalid_claim(path: &[&str]) -> FeeDistributionConfigurationVerificationRejectV2 {
    FeeDistributionConfigurationVerificationRejectV2::new(
        FeeDistributionConfigurationVerificationCodeV2::InvalidClaim,
        path,
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeeDistributionConfigurationBodyV2 {
    chain_deployment_id: String,
    configuration_version: BigUint,
    fee_distribution_domain_id: String,
    policy_root: String,
    policy: FeeDistributionPolicyV2,
    activation_sequence: BigUint,
    algorithm_version: String,
    accepted_language_version: String,
}

impl FeeDistributionConfigurationBodyV2 {
    #[allow(clippy::too_many_arguments)]
    pub fn try_new(
        chain_deployment_id: String,
        configuration_version: BigUint,
        fee_distribution_domain_id: String,
        policy_root: String,
        policy: FeeDistributionPolicyV2,
        activation_sequence: BigUint,
        algorithm_version: String,
        accepted_language_version: String,
    ) -> Result<Self, FeeDistributionConfigurationVerificationRejectV2> {
        if !text_is_canonical(&chain_deployment_id) {
            return Err(invalid_claim(&[
                "configuration",
                "body",
                "chain_deployment_id",
            ]));
        }
        if configuration_version == BigUint::ZERO || configuration_version > u256_max() {
            return Err(invalid_claim(&[
                "configuration",
                "body",
                "configuration_version",
            ]));
        }
        if !text_is_canonical(&fee_distribution_domain_id) {
            return Err(invalid_claim(&[
                "configuration",
                "body",
                "fee_distribution_domain_id",
            ]));
        }
        if !digest_is_canonical(&policy_root) {
            return Err(invalid_claim(&["configuration", "body", "policy_root"]));
        }
        if activation_sequence > u256_max() {
            return Err(invalid_claim(&[
                "configuration",
                "body",
                "activation_sequence",
            ]));
        }
        if !text_is_canonical(&algorithm_version) {
            return Err(invalid_claim(&[
                "configuration",
                "body",
                "algorithm_version",
            ]));
        }
        if !text_is_canonical(&accepted_language_version) {
            return Err(invalid_claim(&[
                "configuration",
                "body",
                "accepted_language_version",
            ]));
        }
        Ok(Self {
            chain_deployment_id,
            configuration_version,
            fee_distribution_domain_id,
            policy_root,
            policy,
            activation_sequence,
            algorithm_version,
            accepted_language_version,
        })
    }

    pub fn policy(&self) -> &FeeDistributionPolicyV2 {
        &self.policy
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeeDistributionConfigurationClaimV2 {
    body: FeeDistributionConfigurationBodyV2,
    configuration_root: String,
}

impl FeeDistributionConfigurationClaimV2 {
    pub fn try_new(
        body: FeeDistributionConfigurationBodyV2,
        configuration_root: String,
    ) -> Result<Self, FeeDistributionConfigurationVerificationRejectV2> {
        if !digest_is_canonical(&configuration_root) {
            return Err(invalid_claim(&["configuration", "configuration_root"]));
        }
        Ok(Self {
            body,
            configuration_root,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidatedFeeDistributionConfigurationClaimV2 {
    body: FeeDistributionConfigurationBodyV2,
    configuration_root: String,
}

impl ValidatedFeeDistributionConfigurationClaimV2 {
    pub fn body(&self) -> &FeeDistributionConfigurationBodyV2 {
        &self.body
    }
}

fn int_json<T: Into<BigInt>>(value: T) -> JsonValue {
    JsonValue::Int(value.into())
}

fn policy_json(value: &FeeDistributionPolicyV2) -> JsonValue {
    let weights = value.weights();
    let destinations = value.destinations();
    JsonValue::Object(vec![
        ("buyback_bps".to_owned(), int_json(weights[0])),
        ("treasury_bps".to_owned(), int_json(weights[1])),
        ("rewards_bps".to_owned(), int_json(weights[2])),
        (
            "buyback_destination".to_owned(),
            JsonValue::Str(destinations[0].clone()),
        ),
        (
            "treasury_destination".to_owned(),
            JsonValue::Str(destinations[1].clone()),
        ),
        (
            "rewards_destination".to_owned(),
            JsonValue::Str(destinations[2].clone()),
        ),
    ])
}

fn body_json(value: &FeeDistributionConfigurationBodyV2) -> JsonValue {
    JsonValue::Object(vec![
        (
            "chain_deployment_id".to_owned(),
            JsonValue::Str(value.chain_deployment_id.clone()),
        ),
        (
            "configuration_version".to_owned(),
            int_json(value.configuration_version.clone()),
        ),
        (
            "fee_distribution_domain_id".to_owned(),
            JsonValue::Str(value.fee_distribution_domain_id.clone()),
        ),
        (
            "policy_root".to_owned(),
            JsonValue::Str(value.policy_root.clone()),
        ),
        ("policy".to_owned(), policy_json(&value.policy)),
        (
            "activation_sequence".to_owned(),
            int_json(value.activation_sequence.clone()),
        ),
        (
            "algorithm_version".to_owned(),
            JsonValue::Str(value.algorithm_version.clone()),
        ),
        (
            "accepted_language_version".to_owned(),
            JsonValue::Str(value.accepted_language_version.clone()),
        ),
    ])
}

fn claim_json(value: &FeeDistributionConfigurationClaimV2) -> JsonValue {
    JsonValue::Object(vec![
        ("body".to_owned(), body_json(&value.body)),
        (
            "configuration_root".to_owned(),
            JsonValue::Str(value.configuration_root.clone()),
        ),
    ])
}

fn envelope(schema: &str, value: JsonValue) -> Vec<u8> {
    canonical_json_bytes(&JsonValue::Object(vec![
        ("schema".to_owned(), JsonValue::Str(schema.to_owned())),
        ("value".to_owned(), value),
    ]))
}

pub fn encode_fee_distribution_policy_v2(value: &FeeDistributionPolicyV2) -> Vec<u8> {
    envelope(FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2, policy_json(value))
}

pub fn encode_fee_distribution_configuration_body_v2(
    value: &FeeDistributionConfigurationBodyV2,
) -> Vec<u8> {
    envelope(
        FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2,
        body_json(value),
    )
}

pub fn encode_fee_distribution_configuration_claim_v2(
    value: &FeeDistributionConfigurationClaimV2,
) -> Vec<u8> {
    envelope(
        FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        claim_json(value),
    )
}

pub fn encode_validated_fee_distribution_configuration_claim_v2(
    value: &ValidatedFeeDistributionConfigurationClaimV2,
) -> Vec<u8> {
    let claim = FeeDistributionConfigurationClaimV2 {
        body: value.body.clone(),
        configuration_root: value.configuration_root.clone(),
    };
    envelope(
        VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        claim_json(&claim),
    )
}

pub fn canonical_fee_distribution_policy_root_v2(value: &FeeDistributionPolicyV2) -> String {
    let mut preimage = domain_sep_bytes("fee_distribution_policy", 2);
    preimage.extend(encode_fee_distribution_policy_v2(value));
    sha256_hex(&preimage)
}

pub fn canonical_fee_distribution_configuration_root_v2(
    value: &FeeDistributionConfigurationBodyV2,
) -> String {
    let mut preimage = domain_sep_bytes("fee_distribution_configuration", 2);
    preimage.extend(encode_fee_distribution_configuration_body_v2(value));
    sha256_hex(&preimage)
}

pub fn validate_fee_distribution_configuration_claim_v2(
    claim: &FeeDistributionConfigurationClaimV2,
) -> Result<
    ValidatedFeeDistributionConfigurationClaimV2,
    FeeDistributionConfigurationVerificationRejectV2,
> {
    if claim.body.algorithm_version != SRGD_ALGORITHM_VERSION_V1 {
        return Err(FeeDistributionConfigurationVerificationRejectV2::new(
            FeeDistributionConfigurationVerificationCodeV2::AlgorithmVersionMismatch,
            &["configuration", "body", "algorithm_version"],
        ));
    }
    if claim.body.accepted_language_version != PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2 {
        return Err(FeeDistributionConfigurationVerificationRejectV2::new(
            FeeDistributionConfigurationVerificationCodeV2::AcceptedLanguageVersionMismatch,
            &["configuration", "body", "accepted_language_version"],
        ));
    }
    if claim.body.policy_root != canonical_fee_distribution_policy_root_v2(&claim.body.policy) {
        return Err(FeeDistributionConfigurationVerificationRejectV2::new(
            FeeDistributionConfigurationVerificationCodeV2::PolicyRootMismatch,
            &["configuration", "body", "policy_root"],
        ));
    }
    if claim.configuration_root != canonical_fee_distribution_configuration_root_v2(&claim.body) {
        return Err(FeeDistributionConfigurationVerificationRejectV2::new(
            FeeDistributionConfigurationVerificationCodeV2::ConfigurationRootMismatch,
            &["configuration", "configuration_root"],
        ));
    }
    Ok(ValidatedFeeDistributionConfigurationClaimV2 {
        body: claim.body.clone(),
        configuration_root: claim.configuration_root.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> serde_json::Value {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/fixtures/fcis_fee_distribution_configuration_v2_golden.json"
        );
        let raw = std::fs::read_to_string(path).expect("shared fixture exists");
        serde_json::from_str(&raw).expect("shared fixture parses")
    }

    fn biguint(value: &serde_json::Value) -> BigUint {
        BigUint::parse_bytes(value.to_string().as_bytes(), 10).expect("fixture U256")
    }

    fn policy(value: &serde_json::Value) -> FeeDistributionPolicyV2 {
        let weight = |field: &str| {
            u16::try_from(value[field].as_u64().expect("fixture policy weight"))
                .expect("fixture policy weight bound")
        };
        FeeDistributionPolicyV2::try_new(
            [
                weight("buyback_bps"),
                weight("treasury_bps"),
                weight("rewards_bps"),
            ],
            [
                value["buyback_destination"]
                    .as_str()
                    .expect("buyback")
                    .to_owned(),
                value["treasury_destination"]
                    .as_str()
                    .expect("treasury")
                    .to_owned(),
                value["rewards_destination"]
                    .as_str()
                    .expect("rewards")
                    .to_owned(),
            ],
        )
        .expect("fixture policy")
    }

    fn claim(value: &serde_json::Value) -> FeeDistributionConfigurationClaimV2 {
        let body = &value["body"];
        let exact_body = FeeDistributionConfigurationBodyV2::try_new(
            body["chain_deployment_id"]
                .as_str()
                .expect("deployment")
                .to_owned(),
            biguint(&body["configuration_version"]),
            body["fee_distribution_domain_id"]
                .as_str()
                .expect("domain")
                .to_owned(),
            body["policy_root"]
                .as_str()
                .expect("policy root")
                .to_owned(),
            policy(&body["policy"]),
            biguint(&body["activation_sequence"]),
            body["algorithm_version"]
                .as_str()
                .expect("algorithm")
                .to_owned(),
            body["accepted_language_version"]
                .as_str()
                .expect("language")
                .to_owned(),
        )
        .expect("fixture body");
        FeeDistributionConfigurationClaimV2::try_new(
            exact_body,
            value["configuration_root"]
                .as_str()
                .expect("configuration root")
                .to_owned(),
        )
        .expect("fixture claim")
    }

    #[test]
    fn rust_matches_every_shared_python_configuration_vector() {
        let document = fixture();
        let cases = document["cases"].as_array().expect("fixture cases");
        assert_eq!(cases.len(), 7);
        for case in cases {
            let exact_claim = claim(&case["input"]);
            let result = validate_fee_distribution_configuration_claim_v2(&exact_claim);
            let expected = &case["expected"];
            if expected["accept"].as_bool().expect("decision") {
                let validated = result.expect("validated configuration claim");
                assert_eq!(
                    String::from_utf8(encode_fee_distribution_policy_v2(validated.body().policy()))
                        .expect("policy UTF-8"),
                    expected["policy_utf8"].as_str().expect("policy bytes")
                );
                assert_eq!(
                    canonical_fee_distribution_policy_root_v2(validated.body().policy()),
                    expected["policy_root"].as_str().expect("policy root")
                );
                assert_eq!(
                    String::from_utf8(encode_fee_distribution_configuration_body_v2(
                        validated.body()
                    ))
                    .expect("body UTF-8"),
                    expected["body_utf8"].as_str().expect("body bytes")
                );
                assert_eq!(
                    canonical_fee_distribution_configuration_root_v2(validated.body()),
                    expected["configuration_root"]
                        .as_str()
                        .expect("configuration root")
                );
                assert_eq!(
                    String::from_utf8(encode_fee_distribution_configuration_claim_v2(&exact_claim))
                        .expect("claim UTF-8"),
                    expected["claim_utf8"].as_str().expect("claim bytes")
                );
                assert_eq!(
                    String::from_utf8(encode_validated_fee_distribution_configuration_claim_v2(
                        &validated
                    ))
                    .expect("validated claim UTF-8"),
                    expected["validated_claim_utf8"]
                        .as_str()
                        .expect("validated claim bytes")
                );
            } else {
                let rejected = result.expect_err("fixture rejection");
                assert_eq!(
                    rejected.code().as_str(),
                    expected["code"].as_str().expect("code")
                );
                let path: Vec<String> = expected["path"]
                    .as_array()
                    .expect("path")
                    .iter()
                    .map(|part| part.as_str().expect("path part").to_owned())
                    .collect();
                assert_eq!(rejected.path(), path);
            }
        }
    }
}
