use serde::Serialize;

use super::EconomicCommandIntentV1;
use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::economic_command_authorization_registry::ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1;
use crate::proof::EconomicCommandOccurrenceV1;

#[derive(Serialize)]
struct AuthenticatedEconomicCommandIntentBindingV1<'a> {
    schema: &'static str,
    intent_id: &'a RootV1,
    policy_registry_root: &'a RootV1,
    authorization_registry_root: &'a RootV1,
    authorization_id: &'a RootV1,
    verifier_registry_root: &'a RootV1,
    signature_verifier_registry_root: &'a RootV1,
    signature_verifier_release_id: &'a RootV1,
    signature_verifier_deployment_binding_root: &'a RootV1,
    command_body_bytes_digest: &'a RootV1,
    authentication_message_digest: &'a RootV1,
    signature_digest: &'a RootV1,
}

pub(super) struct AuthenticatedEconomicCommandIntentFieldsV1 {
    pub(super) intent: EconomicCommandIntentV1,
    pub(super) intent_id: RootV1,
    pub(super) policy_registry_root: RootV1,
    pub(super) authorization_registry_root: RootV1,
    pub(super) authorization_id: RootV1,
    pub(super) verifier_registry_root: RootV1,
    pub(super) signature_verifier_registry_root: RootV1,
    pub(super) signature_verifier_release_id: RootV1,
    pub(super) signature_verifier_deployment_binding_root: RootV1,
    pub(super) command_body_bytes_digest: RootV1,
    pub(super) authentication_message_digest: RootV1,
    pub(super) signature_digest: RootV1,
}

pub struct AuthenticatedEconomicCommandIntentV1 {
    fields: AuthenticatedEconomicCommandIntentFieldsV1,
}

impl AuthenticatedEconomicCommandIntentV1 {
    pub(super) fn from_fields(fields: AuthenticatedEconomicCommandIntentFieldsV1) -> Self {
        Self { fields }
    }

    pub fn intent(&self) -> &EconomicCommandIntentV1 {
        &self.fields.intent
    }

    pub fn authentication_message_digest(&self) -> &RootV1 {
        &self.fields.authentication_message_digest
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        if self.fields.intent.intent_id()? != self.fields.intent_id {
            return Err(AbiErrorV1::InvalidBinding(
                "authenticated command intent mutation",
            ));
        }
        hash_global_v1(
            "authenticated-economic-command-intent-v1",
            &AuthenticatedEconomicCommandIntentBindingV1 {
                schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
                intent_id: &self.fields.intent_id,
                policy_registry_root: &self.fields.policy_registry_root,
                authorization_registry_root: &self.fields.authorization_registry_root,
                authorization_id: &self.fields.authorization_id,
                verifier_registry_root: &self.fields.verifier_registry_root,
                signature_verifier_registry_root: &self.fields.signature_verifier_registry_root,
                signature_verifier_release_id: &self.fields.signature_verifier_release_id,
                signature_verifier_deployment_binding_root: &self
                    .fields
                    .signature_verifier_deployment_binding_root,
                command_body_bytes_digest: &self.fields.command_body_bytes_digest,
                authentication_message_digest: &self.fields.authentication_message_digest,
                signature_digest: &self.fields.signature_digest,
            },
        )
    }
}

#[derive(Serialize)]
struct AuthenticatedEconomicCommandBindingV1<'a> {
    schema: &'static str,
    occurrence_id: &'a RootV1,
    authenticated_intent_binding_root: &'a RootV1,
}

pub(super) struct AuthenticatedEconomicCommandFieldsV1 {
    pub(super) occurrence: EconomicCommandOccurrenceV1,
    pub(super) occurrence_id: RootV1,
    pub(super) authenticated_intent_binding_root: RootV1,
    pub(super) authentication_message_digest: RootV1,
}

pub struct AuthenticatedEconomicCommandV1 {
    fields: AuthenticatedEconomicCommandFieldsV1,
}

impl AuthenticatedEconomicCommandV1 {
    pub(super) fn from_fields(fields: AuthenticatedEconomicCommandFieldsV1) -> Self {
        Self { fields }
    }

    pub fn occurrence(&self) -> &EconomicCommandOccurrenceV1 {
        &self.fields.occurrence
    }

    pub fn occurrence_id(&self) -> &RootV1 {
        &self.fields.occurrence_id
    }

    pub fn authentication_message_digest(&self) -> &RootV1 {
        &self.fields.authentication_message_digest
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        if self.fields.occurrence.occurrence_id()? != self.fields.occurrence_id {
            return Err(AbiErrorV1::InvalidBinding(
                "authenticated command occurrence mutation",
            ));
        }
        hash_global_v1(
            "authenticated-economic-command-v1",
            &AuthenticatedEconomicCommandBindingV1 {
                schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
                occurrence_id: &self.fields.occurrence_id,
                authenticated_intent_binding_root: &self.fields.authenticated_intent_binding_root,
            },
        )
    }
}
