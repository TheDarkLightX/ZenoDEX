use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::canonical::{
    canonical_bytes_v1, hash_economic_command_body_bytes_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::economic_command_authorization_registry::{
    EconomicCommandAuthorizationV1, ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
};
use crate::economic_command_signature_verifier_deployment::{
    BoundEconomicCommandSignatureVerifierV1, EconomicCommandSignatureVerifierBackendV1,
};
use crate::economic_command_signature_verifier_registry::{
    select_profile_governed_command_signature_verifier_release_v1,
    EconomicCommandSignatureVerifierReleaseV1,
};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::ProfileStatusV1;

mod types;
mod witness;
pub use types::*;
use witness::{AuthenticatedEconomicCommandFieldsV1, AuthenticatedEconomicCommandIntentFieldsV1};
pub use witness::{AuthenticatedEconomicCommandIntentV1, AuthenticatedEconomicCommandV1};

#[derive(Serialize)]
struct EconomicCommandAuthenticationMessageV1<'a> {
    schema: &'static str,
    policy_registry_root: &'a RootV1,
    authorization_registry_root: &'a RootV1,
    authorization_id: &'a RootV1,
    verifier_registry_root: &'a RootV1,
    signature_verifier_registry_root: &'a RootV1,
    signature_verifier_release_id: &'a RootV1,
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
    let release = select_signature_verifier_release_v1(candidate)?;
    authentication_message_bytes_for_release_v1(candidate, authorization, release)
}

fn authentication_message_bytes_for_release_v1(
    candidate: &EconomicCommandAuthenticationCandidateV1<'_>,
    authorization: &EconomicCommandAuthorizationV1,
    release: &EconomicCommandSignatureVerifierReleaseV1,
) -> AbiResultV1<Vec<u8>> {
    let policy_registry_root = candidate.policy_registry.registry_root()?;
    let authorization_registry_root = candidate.authorization_registry.registry_root()?;
    let signature_verifier_registry_root = candidate.signature_verifier_registry.registry_root()?;
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
        signature_verifier_registry_root: &signature_verifier_registry_root,
        signature_verifier_release_id: &release.release_id,
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

pub fn authenticate_economic_command_intent_v1<B: EconomicCommandSignatureVerifierBackendV1>(
    candidate: &EconomicCommandAuthenticationCandidateV1<'_>,
    signature_verifier: &BoundEconomicCommandSignatureVerifierV1<B>,
) -> AbiResultV1<AuthenticatedEconomicCommandIntentV1> {
    validate_candidate_v1(candidate)?;
    let intent = candidate.intent;
    let envelope = candidate.envelope;
    let policy_registry_root = candidate.policy_registry.registry_root()?;
    let authorization_registry_root = candidate.authorization_registry.registry_root()?;
    let authorization = select_authorization_for_intent_v1(candidate)?;
    let release = select_signature_verifier_release_v1(candidate)?;
    let message_bytes =
        authentication_message_bytes_for_release_v1(candidate, authorization, release)?;
    signature_verifier.require_binding(
        &release.release_id,
        &intent.deployment_root,
        &intent.profile_root,
    )?;
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
            signature_verifier_registry_root: candidate
                .signature_verifier_registry
                .registry_root()?,
            signature_verifier_release_id: release.release_id.clone(),
            signature_verifier_deployment_binding_root: signature_verifier.binding_root()?,
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

fn select_signature_verifier_release_v1<'a>(
    candidate: &'a EconomicCommandAuthenticationCandidateV1<'a>,
) -> AbiResultV1<&'a EconomicCommandSignatureVerifierReleaseV1> {
    select_profile_governed_command_signature_verifier_release_v1(
        candidate.policy_registry,
        candidate.signature_verifier_registry,
        &candidate.intent.command_kind,
        &candidate.envelope.signature_algorithm,
        &candidate.envelope.signer_public_key,
        &candidate.envelope.signature_bytes,
    )
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
    candidate.signature_verifier_registry.validate()?;
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
