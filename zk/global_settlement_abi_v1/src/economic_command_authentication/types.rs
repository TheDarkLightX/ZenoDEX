use serde::Serialize;

use crate::canonical::{
    hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, MAX_JOURNAL_BYTES_V1,
};
use crate::economic_command_authorization_registry::{
    validate_authentication_schema_v1, EconomicCommandAuthorizationRegistryV1,
};
use crate::economic_command_signature_verifier_registry::{
    EconomicCommandSignatureVerifierRegistryV1, MAX_COMMAND_SIGNATURE_BYTES_V1,
};
use crate::release::{EconomicPolicyRegistryV1, EconomicProfileSnapshotV1, RouteRegistryV1};

#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicCommandIntentV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub command_kind: String,
    pub command_body_hash: RootV1,
    pub route_release_id: RootV1,
    pub subject_id: String,
    pub grant_root: RootV1,
    pub nonce: u64,
    pub consumed_object_ids: Vec<String>,
    pub valid_from_height: u64,
    pub valid_through_height: u64,
}

impl EconomicCommandIntentV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_authentication_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "command intent chain id")?;
        self.deployment_root
            .validate("command intent deployment root", false)?;
        self.profile_root
            .validate("command intent profile root", false)?;
        validate_token_v1(&self.command_kind, "command intent kind")?;
        self.command_body_hash
            .validate("command intent body hash", false)?;
        self.route_release_id
            .validate("command intent route", false)?;
        validate_token_v1(&self.subject_id, "command intent subject")?;
        self.grant_root.validate("command intent grant", false)?;
        for object_id in &self.consumed_object_ids {
            validate_token_v1(object_id, "command intent consumed object id")?;
        }
        if self
            .consumed_object_ids
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        {
            return Err(AbiErrorV1::InvalidOrder(
                "command intent consumed object ids",
            ));
        }
        if self.valid_from_height > self.valid_through_height {
            return Err(AbiErrorV1::InvalidBounds("command intent height interval"));
        }
        Ok(())
    }

    pub fn intent_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("economic-command-intent-v1", self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EconomicCommandAuthenticationEnvelopeV1 {
    pub command_body_bytes: Vec<u8>,
    pub signer_key_id: String,
    pub signer_public_key: String,
    pub signature_algorithm: String,
    pub signature_bytes: Vec<u8>,
}

impl EconomicCommandAuthenticationEnvelopeV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.command_body_bytes.is_empty()
            || u64::try_from(self.command_body_bytes.len()).ok().is_none()
            || u64::try_from(self.command_body_bytes.len()).ok() > Some(MAX_JOURNAL_BYTES_V1)
        {
            return Err(AbiErrorV1::InvalidBounds(
                "command authentication body bytes",
            ));
        }
        validate_token_v1(&self.signer_key_id, "command authentication signer key id")?;
        validate_token_v1(
            &self.signer_public_key,
            "command authentication signer public key",
        )?;
        validate_token_v1(
            &self.signature_algorithm,
            "command authentication signature algorithm",
        )?;
        if self.signature_bytes.is_empty()
            || self.signature_bytes.len() > MAX_COMMAND_SIGNATURE_BYTES_V1
        {
            return Err(AbiErrorV1::InvalidBounds(
                "command authentication signature bytes",
            ));
        }
        Ok(())
    }
}

pub struct EconomicCommandAuthenticationCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub routes: &'a RouteRegistryV1,
    pub policy_registry: &'a EconomicPolicyRegistryV1,
    pub authorization_registry: &'a EconomicCommandAuthorizationRegistryV1,
    pub signature_verifier_registry: &'a EconomicCommandSignatureVerifierRegistryV1,
    pub intent: &'a EconomicCommandIntentV1,
    pub envelope: &'a EconomicCommandAuthenticationEnvelopeV1,
}

pub trait EconomicCommandSignatureVerifierV1 {
    fn verifier_release_id(&self) -> &RootV1;

    fn verify_command_signature(
        &self,
        signature_algorithm: &str,
        signer_public_key: &str,
        message_bytes: &[u8],
        signature_bytes: &[u8],
    ) -> AbiResultV1<bool>;
}
