use serde::Serialize;

use crate::canonical::{hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::proof::EconomicCommandOccurrenceV1;

pub const ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1: &str =
    "zenodex/economic-command-authentication/v1";
pub const ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1: &str = "command_authentication_registry";
pub const MAX_COMMAND_AUTHORIZATIONS_V1: usize = 1_024;

#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicCommandAuthorizationV1 {
    pub schema: String,
    pub command_kind: String,
    pub subject_id: String,
    pub grant_root: RootV1,
    pub route_release_id: RootV1,
    pub signer_key_id: String,
    pub signer_public_key: String,
    pub signature_algorithm: String,
    pub valid_from_height: u64,
    pub valid_through_height: u64,
    pub min_nonce: u64,
    pub max_nonce: u64,
    pub enabled: bool,
}

impl EconomicCommandAuthorizationV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_authentication_schema_v1(&self.schema)?;
        validate_token_v1(&self.command_kind, "command authorization kind")?;
        validate_token_v1(&self.subject_id, "command authorization subject")?;
        self.grant_root
            .validate("command authorization grant", false)?;
        self.route_release_id
            .validate("command authorization route", false)?;
        validate_token_v1(&self.signer_key_id, "command authorization signer key id")?;
        validate_token_v1(
            &self.signer_public_key,
            "command authorization signer public key",
        )?;
        validate_token_v1(
            &self.signature_algorithm,
            "command authorization signature algorithm",
        )?;
        if self.valid_from_height > self.valid_through_height {
            return Err(AbiErrorV1::InvalidBounds(
                "command authorization height interval",
            ));
        }
        if self.min_nonce > self.max_nonce {
            return Err(AbiErrorV1::InvalidBounds(
                "command authorization nonce interval",
            ));
        }
        Ok(())
    }

    fn key(&self) -> (&str, &str, &RootV1, &RootV1, &str) {
        (
            &self.command_kind,
            &self.subject_id,
            &self.grant_root,
            &self.route_release_id,
            &self.signer_key_id,
        )
    }

    pub fn authorization_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("economic-command-authorization-v1", self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicCommandAuthorizationRegistryV1 {
    pub schema: String,
    pub authorizations: Vec<EconomicCommandAuthorizationV1>,
}

impl EconomicCommandAuthorizationRegistryV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_authentication_schema_v1(&self.schema)?;
        if self.authorizations.is_empty()
            || self.authorizations.len() > MAX_COMMAND_AUTHORIZATIONS_V1
        {
            return Err(AbiErrorV1::InvalidBounds("command authorization registry"));
        }
        for authorization in &self.authorizations {
            authorization.validate()?;
        }
        if self
            .authorizations
            .windows(2)
            .any(|pair| pair[0].key() >= pair[1].key())
        {
            return Err(AbiErrorV1::InvalidOrder("command authorization registry"));
        }
        Ok(())
    }

    pub fn registry_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("economic-command-authorization-registry-v1", self)
    }

    pub fn authorization_for(
        &self,
        occurrence: &EconomicCommandOccurrenceV1,
        signer_key_id: &str,
    ) -> AbiResultV1<&EconomicCommandAuthorizationV1> {
        occurrence.validate()?;
        self.authorization_for_fields(
            &occurrence.command_kind,
            &occurrence.subject_id,
            &occurrence.grant_root,
            &occurrence.route_release_id,
            signer_key_id,
        )
    }

    pub fn authorization_for_fields(
        &self,
        command_kind: &str,
        subject_id: &str,
        grant_root: &RootV1,
        route_release_id: &RootV1,
        signer_key_id: &str,
    ) -> AbiResultV1<&EconomicCommandAuthorizationV1> {
        self.validate()?;
        validate_token_v1(command_kind, "command authorization kind")?;
        validate_token_v1(subject_id, "command authorization subject")?;
        grant_root.validate("command authorization grant", false)?;
        route_release_id.validate("command authorization route", false)?;
        validate_token_v1(signer_key_id, "command authentication signer key id")?;
        self.authorizations
            .iter()
            .find(|authorization| {
                authorization.command_kind == command_kind
                    && authorization.subject_id == subject_id
                    && authorization.grant_root == *grant_root
                    && authorization.route_release_id == *route_release_id
                    && authorization.signer_key_id == signer_key_id
            })
            .ok_or(AbiErrorV1::InvalidBinding(
                "command authorization absent from governed registry",
            ))
    }
}

pub(crate) fn validate_authentication_schema_v1(schema: &str) -> AbiResultV1<()> {
    if schema == ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1 {
        Ok(())
    } else {
        Err(AbiErrorV1::InvalidSchema)
    }
}
