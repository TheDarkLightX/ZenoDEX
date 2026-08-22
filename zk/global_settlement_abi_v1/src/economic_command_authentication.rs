use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::canonical::{
    canonical_bytes_v1, hash_economic_command_body_bytes_v1, hash_global_v1, validate_token_v1,
    AbiErrorV1, AbiResultV1, RootV1, MAX_JOURNAL_BYTES_V1,
};
use crate::economic_command_authorization_registry::{
    validate_authentication_schema_v1, EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1, ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::{
    EconomicPolicyRegistryV1, EconomicProfileSnapshotV1, ProfileStatusV1, RouteRegistryV1,
};

mod witness;
use witness::{AuthenticatedEconomicCommandFieldsV1, AuthenticatedEconomicCommandIntentFieldsV1};
pub use witness::{AuthenticatedEconomicCommandIntentV1, AuthenticatedEconomicCommandV1};

pub const MAX_COMMAND_SIGNATURE_BYTES_V1: usize = 4_096;

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
    pub intent: &'a EconomicCommandIntentV1,
    pub envelope: &'a EconomicCommandAuthenticationEnvelopeV1,
}

pub trait EconomicCommandSignatureVerifierV1 {
    fn verify_command_signature(
        &self,
        signature_algorithm: &str,
        signer_public_key: &str,
        message_bytes: &[u8],
        signature_bytes: &[u8],
    ) -> AbiResultV1<bool>;
}

#[derive(Serialize)]
struct EconomicCommandAuthenticationMessageV1<'a> {
    schema: &'static str,
    policy_registry_root: &'a RootV1,
    authorization_registry_root: &'a RootV1,
    authorization_id: &'a RootV1,
    verifier_registry_root: &'a RootV1,
    intent: &'a EconomicCommandIntentV1,
    command_body_bytes_digest: &'a RootV1,
    signature_algorithm: &'a str,
    signer_key_id: &'a str,
    signer_public_key: &'a str,
}

pub fn economic_command_authentication_message_bytes_v1(
    candidate: &EconomicCommandAuthenticationCandidateV1<'_>,
    authorization: &EconomicCommandAuthorizationV1,
) -> AbiResultV1<Vec<u8>> {
    validate_candidate_v1(candidate)?;
    authorization.validate()?;
    let policy_registry_root = candidate.policy_registry.registry_root()?;
    let authorization_registry_root = candidate.authorization_registry.registry_root()?;
    let authorization_id = authorization.authorization_id()?;
    let command_body_bytes_digest = sha256_root_v1(
        &candidate.envelope.command_body_bytes,
        "command authentication body bytes digest",
    )?;
    let body = EconomicCommandAuthenticationMessageV1 {
        schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
        policy_registry_root: &policy_registry_root,
        authorization_registry_root: &authorization_registry_root,
        authorization_id: &authorization_id,
        verifier_registry_root: &candidate.profile.verifier_registry_root,
        intent: candidate.intent,
        command_body_bytes_digest: &command_body_bytes_digest,
        signature_algorithm: &candidate.envelope.signature_algorithm,
        signer_key_id: &candidate.envelope.signer_key_id,
        signer_public_key: &candidate.envelope.signer_public_key,
    };
    let mut message = b"zenodex:economic-command-intent-authentication-message-v1:v1\0".to_vec();
    message.extend(canonical_bytes_v1(&body)?);
    Ok(message)
}

pub fn authenticate_economic_command_intent_v1<V: EconomicCommandSignatureVerifierV1>(
    candidate: &EconomicCommandAuthenticationCandidateV1<'_>,
    signature_verifier: &V,
) -> AbiResultV1<AuthenticatedEconomicCommandIntentV1> {
    validate_candidate_v1(candidate)?;
    let intent = candidate.intent;
    let envelope = candidate.envelope;
    let policy_registry_root = candidate.policy_registry.registry_root()?;
    let authorization_registry_root = candidate.authorization_registry.registry_root()?;
    let authorization = select_authorization_for_intent_v1(candidate)?;
    let message_bytes = economic_command_authentication_message_bytes_v1(candidate, authorization)?;
    if !signature_verifier.verify_command_signature(
        &envelope.signature_algorithm,
        &envelope.signer_public_key,
        &message_bytes,
        &envelope.signature_bytes,
    )? {
        return Err(AbiErrorV1::InvalidBinding(
            "command authentication signature",
        ));
    }
    Ok(AuthenticatedEconomicCommandIntentV1::from_fields(
        AuthenticatedEconomicCommandIntentFieldsV1 {
            intent: intent.clone(),
            intent_id: intent.intent_id()?,
            policy_registry_root,
            authorization_registry_root,
            authorization_id: authorization.authorization_id()?,
            verifier_registry_root: candidate.profile.verifier_registry_root.clone(),
            command_body_bytes_digest: sha256_root_v1(
                &envelope.command_body_bytes,
                "command authentication body bytes digest",
            )?,
            authentication_message_digest: sha256_root_v1(
                &message_bytes,
                "command authentication message digest",
            )?,
            signature_digest: sha256_root_v1(
                &envelope.signature_bytes,
                "command authentication signature digest",
            )?,
        },
    ))
}

fn select_authorization_for_intent_v1<'a>(
    candidate: &EconomicCommandAuthenticationCandidateV1<'a>,
) -> AbiResultV1<&'a EconomicCommandAuthorizationV1> {
    let intent = candidate.intent;
    let envelope = candidate.envelope;
    let authorization = candidate.authorization_registry.authorization_for_fields(
        &intent.command_kind,
        &intent.subject_id,
        &intent.grant_root,
        &intent.route_release_id,
        &envelope.signer_key_id,
    )?;
    if !authorization.enabled {
        return Err(AbiErrorV1::InvalidBinding("command authorization disabled"));
    }
    if authorization.signer_public_key != envelope.signer_public_key {
        return Err(AbiErrorV1::InvalidBinding(
            "command authentication signer public key",
        ));
    }
    if authorization.signature_algorithm != envelope.signature_algorithm {
        return Err(AbiErrorV1::InvalidBinding(
            "command authentication signature algorithm",
        ));
    }
    if !(authorization.min_nonce..=authorization.max_nonce).contains(&intent.nonce) {
        return Err(AbiErrorV1::InvalidBinding(
            "command authorization nonce interval",
        ));
    }
    if intent.valid_from_height < authorization.valid_from_height
        || intent.valid_through_height > authorization.valid_through_height
    {
        return Err(AbiErrorV1::InvalidBinding(
            "command intent validity exceeds authorization interval",
        ));
    }
    Ok(authorization)
}

pub fn bind_authenticated_intent_to_occurrence_v1(
    authenticated_intent: &AuthenticatedEconomicCommandIntentV1,
    occurrence: &EconomicCommandOccurrenceV1,
) -> AbiResultV1<AuthenticatedEconomicCommandV1> {
    occurrence.validate()?;
    let intent = authenticated_intent.intent();
    if intent.chain_id != occurrence.chain_id {
        return Err(intent_occurrence_mismatch("chain"));
    }
    if intent.deployment_root != occurrence.deployment_root {
        return Err(intent_occurrence_mismatch("deployment"));
    }
    if intent.profile_root != occurrence.profile_root {
        return Err(intent_occurrence_mismatch("profile"));
    }
    if intent.command_kind != occurrence.command_kind {
        return Err(intent_occurrence_mismatch("command kind"));
    }
    if intent.command_body_hash != occurrence.command_body_hash {
        return Err(intent_occurrence_mismatch("command body"));
    }
    if intent.route_release_id != occurrence.route_release_id {
        return Err(intent_occurrence_mismatch("route"));
    }
    if intent.subject_id != occurrence.subject_id {
        return Err(intent_occurrence_mismatch("subject"));
    }
    if intent.grant_root != occurrence.grant_root {
        return Err(intent_occurrence_mismatch("grant"));
    }
    if intent.nonce != occurrence.nonce {
        return Err(intent_occurrence_mismatch("nonce"));
    }
    if intent.consumed_object_ids != occurrence.consumed_object_ids {
        return Err(intent_occurrence_mismatch("consumed objects"));
    }
    if !(intent.valid_from_height..=intent.valid_through_height).contains(&occurrence.height) {
        return Err(AbiErrorV1::InvalidBinding(
            "authenticated intent occurrence height outside validity",
        ));
    }
    Ok(AuthenticatedEconomicCommandV1::from_fields(
        AuthenticatedEconomicCommandFieldsV1 {
            occurrence: occurrence.clone(),
            occurrence_id: occurrence.occurrence_id()?,
            authenticated_intent_binding_root: authenticated_intent.binding_root()?,
            authentication_message_digest: authenticated_intent
                .authentication_message_digest()
                .clone(),
        },
    ))
}

fn validate_candidate_v1(
    candidate: &EconomicCommandAuthenticationCandidateV1<'_>,
) -> AbiResultV1<()> {
    candidate.profile.validate()?;
    candidate.routes.validate()?;
    candidate.policy_registry.validate()?;
    candidate.authorization_registry.validate()?;
    candidate.intent.validate()?;
    candidate.envelope.validate()?;
    if candidate.profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding(
            "command authentication requires active profile",
        ));
    }
    if candidate.profile.route_registry_root != candidate.routes.registry_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "command authentication route registry root",
        ));
    }
    let policy_registry_root = candidate.policy_registry.registry_root()?;
    if candidate.profile.policy_registry_root != policy_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "command authentication policy registry root",
        ));
    }
    let policy_binding = candidate.policy_registry.require_binding(
        ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
        &candidate.intent.command_kind,
    )?;
    if policy_binding.policy_root != candidate.authorization_registry.registry_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "command authorization registry profile governance",
        ));
    }
    if candidate.intent.profile_root != candidate.profile.profile_id {
        return Err(AbiErrorV1::InvalidBinding(
            "command authentication intent profile",
        ));
    }
    candidate.routes.route_for_command(
        &candidate.intent.command_kind,
        Some(&candidate.intent.route_release_id),
    )?;
    if hash_economic_command_body_bytes_v1(&candidate.envelope.command_body_bytes)?
        != candidate.intent.command_body_hash
    {
        return Err(AbiErrorV1::InvalidBinding(
            "command authentication body hash",
        ));
    }
    Ok(())
}

fn intent_occurrence_mismatch(field: &'static str) -> AbiErrorV1 {
    AbiErrorV1::InvalidBinding(field)
}

fn sha256_root_v1(bytes: &[u8], field: &'static str) -> AbiResultV1<RootV1> {
    RootV1::parse(
        format!("0x{}", hex::encode(Sha256::digest(bytes))),
        field,
        false,
    )
}
