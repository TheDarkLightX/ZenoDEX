use serde::Serialize;

use crate::canonical::{
    hash_global_v1, validate_schema_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
    GLOBAL_SETTLEMENT_ABI_V1, MAX_TOKEN_BYTES_V1,
};
use crate::release::{EconomicPolicyRegistryV1, ReleaseStatusV1};

pub const ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1: &str =
    "command_signature_verifier_registry";
pub const MAX_COMMAND_SIGNATURE_VERIFIER_RELEASES_V1: usize = 32;
pub const MAX_COMMAND_SIGNATURE_BYTES_V1: usize = 4_096;

const REQUIRED_ACTIVE_VERIFIER_EVIDENCE_V1: [CommandSignatureVerifierEvidenceStatusV1; 10] = [
    CommandSignatureVerifierEvidenceStatusV1::DEPLOYMENT_BOUND,
    CommandSignatureVerifierEvidenceStatusV1::IMPLEMENTATION_REPLAYED,
    CommandSignatureVerifierEvidenceStatusV1::IMPLEMENTED,
    CommandSignatureVerifierEvidenceStatusV1::INDEPENDENTLY_REVIEWED,
    CommandSignatureVerifierEvidenceStatusV1::NO_BYPASS,
    CommandSignatureVerifierEvidenceStatusV1::RELEASE_BACKED,
    CommandSignatureVerifierEvidenceStatusV1::SOURCE_PINNED,
    CommandSignatureVerifierEvidenceStatusV1::SPECIFIED,
    CommandSignatureVerifierEvidenceStatusV1::TESTED,
    CommandSignatureVerifierEvidenceStatusV1::TOOLCHAIN_PINNED,
];

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, serde::Deserialize, Serialize)]
#[allow(non_camel_case_types)]
pub enum CommandSignatureVerifierEvidenceStatusV1 {
    DEPLOYMENT_BOUND,
    IMPLEMENTATION_REPLAYED,
    IMPLEMENTED,
    INDEPENDENTLY_REVIEWED,
    NO_BYPASS,
    RELEASE_BACKED,
    SOURCE_PINNED,
    SPECIFIED,
    TESTED,
    TOOLCHAIN_PINNED,
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicCommandSignatureVerifierReleaseV1 {
    pub schema: String,
    pub release_id: RootV1,
    pub semantic_version: String,
    pub signature_algorithm: String,
    pub implementation_root: RootV1,
    pub public_key_schema_root: RootV1,
    pub signature_schema_root: RootV1,
    pub message_schema_root: RootV1,
    pub specification_root: RootV1,
    pub source_root: RootV1,
    pub toolchain_root: RootV1,
    pub evidence_manifest_root: RootV1,
    pub max_public_key_bytes: u64,
    pub max_signature_bytes: u64,
    pub status: ReleaseStatusV1,
    pub accepts_new_authentications: bool,
    pub evidence_statuses: Vec<CommandSignatureVerifierEvidenceStatusV1>,
}

#[derive(Serialize)]
struct EconomicCommandSignatureVerifierReleaseContentV1<'a> {
    schema: &'static str,
    signature_algorithm: &'a str,
    implementation_root: &'a RootV1,
    public_key_schema_root: &'a RootV1,
    signature_schema_root: &'a RootV1,
    message_schema_root: &'a RootV1,
    specification_root: &'a RootV1,
    source_root: &'a RootV1,
    toolchain_root: &'a RootV1,
    evidence_manifest_root: &'a RootV1,
    max_public_key_bytes: u64,
    max_signature_bytes: u64,
}

impl EconomicCommandSignatureVerifierReleaseV1 {
    fn content(&self) -> EconomicCommandSignatureVerifierReleaseContentV1<'_> {
        EconomicCommandSignatureVerifierReleaseContentV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            signature_algorithm: &self.signature_algorithm,
            implementation_root: &self.implementation_root,
            public_key_schema_root: &self.public_key_schema_root,
            signature_schema_root: &self.signature_schema_root,
            message_schema_root: &self.message_schema_root,
            specification_root: &self.specification_root,
            source_root: &self.source_root,
            toolchain_root: &self.toolchain_root,
            evidence_manifest_root: &self.evidence_manifest_root,
            max_public_key_bytes: self.max_public_key_bytes,
            max_signature_bytes: self.max_signature_bytes,
        }
    }

    pub fn derived_release_id(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "economic-command-signature-verifier-release-content-v1",
            &self.content(),
        )
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        self.release_id
            .validate("command signature verifier release id", false)?;
        validate_token_v1(
            &self.semantic_version,
            "command signature verifier semantic version",
        )?;
        validate_token_v1(
            &self.signature_algorithm,
            "command signature verifier algorithm",
        )?;
        for root in [
            &self.implementation_root,
            &self.public_key_schema_root,
            &self.signature_schema_root,
            &self.message_schema_root,
            &self.specification_root,
            &self.source_root,
            &self.toolchain_root,
            &self.evidence_manifest_root,
        ] {
            root.validate("command signature verifier release root", false)?;
        }
        let max_token_bytes = u64::try_from(MAX_TOKEN_BYTES_V1).map_err(|_| {
            AbiErrorV1::InvalidBounds("command signature verifier max public-key bytes")
        })?;
        if self.max_public_key_bytes == 0 || self.max_public_key_bytes > max_token_bytes {
            return Err(AbiErrorV1::InvalidBounds(
                "command signature verifier max public-key bytes",
            ));
        }
        let max_signature_bytes = u64::try_from(MAX_COMMAND_SIGNATURE_BYTES_V1).map_err(|_| {
            AbiErrorV1::InvalidBounds("command signature verifier max signature bytes")
        })?;
        if self.max_signature_bytes == 0 || self.max_signature_bytes > max_signature_bytes {
            return Err(AbiErrorV1::InvalidBounds(
                "command signature verifier max signature bytes",
            ));
        }
        validate_verifier_evidence_v1(&self.evidence_statuses)?;
        let active = self.status == ReleaseStatusV1::ACTIVE_NEW;
        if self.accepts_new_authentications != active {
            return Err(AbiErrorV1::InvalidBinding(
                "command signature verifier active status",
            ));
        }
        if active && self.evidence_statuses != REQUIRED_ACTIVE_VERIFIER_EVIDENCE_V1 {
            return Err(AbiErrorV1::InvalidBinding(
                "active command signature verifier evidence",
            ));
        }
        if self.release_id != self.derived_release_id()? {
            return Err(AbiErrorV1::InvalidBinding(
                "command signature verifier content-derived release id",
            ));
        }
        Ok(())
    }

    fn key(&self) -> (&str, &RootV1) {
        (&self.signature_algorithm, &self.release_id)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicCommandSignatureVerifierRegistryV1 {
    pub schema: String,
    pub releases: Vec<EconomicCommandSignatureVerifierReleaseV1>,
}

impl EconomicCommandSignatureVerifierRegistryV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        if self.releases.is_empty()
            || self.releases.len() > MAX_COMMAND_SIGNATURE_VERIFIER_RELEASES_V1
        {
            return Err(AbiErrorV1::InvalidBounds(
                "command signature verifier registry",
            ));
        }
        for release in &self.releases {
            release.validate()?;
        }
        if self
            .releases
            .windows(2)
            .any(|pair| pair[0].key() >= pair[1].key())
        {
            return Err(AbiErrorV1::InvalidOrder(
                "command signature verifier registry",
            ));
        }
        Ok(())
    }

    pub fn registry_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("economic-command-signature-verifier-registry-v1", self)
    }

    pub fn release_for_new_authentication(
        &self,
        signature_algorithm: &str,
    ) -> AbiResultV1<&EconomicCommandSignatureVerifierReleaseV1> {
        self.validate()?;
        validate_token_v1(signature_algorithm, "command signature algorithm")?;
        let mut matches = self.releases.iter().filter(|release| {
            release.signature_algorithm == signature_algorithm
                && release.status == ReleaseStatusV1::ACTIVE_NEW
                && release.accepts_new_authentications
        });
        let selected = matches.next().ok_or(AbiErrorV1::InvalidBinding(
            "command signature algorithm has no active verifier release",
        ))?;
        if matches.next().is_some() {
            return Err(AbiErrorV1::InvalidBinding(
                "command signature algorithm has multiple active verifier releases",
            ));
        }
        Ok(selected)
    }
}

pub fn select_profile_governed_command_signature_verifier_release_v1<'a>(
    policy_registry: &EconomicPolicyRegistryV1,
    verifier_registry: &'a EconomicCommandSignatureVerifierRegistryV1,
    command_kind: &str,
    signature_algorithm: &str,
    signer_public_key: &str,
    signature_bytes: &[u8],
) -> AbiResultV1<&'a EconomicCommandSignatureVerifierReleaseV1> {
    let binding = policy_registry.require_binding(
        ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
        command_kind,
    )?;
    if binding.policy_root != verifier_registry.registry_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "command signature verifier registry profile governance",
        ));
    }
    let release = verifier_registry.release_for_new_authentication(signature_algorithm)?;
    let public_key_bytes = u64::try_from(signer_public_key.len())
        .map_err(|_| AbiErrorV1::InvalidBounds("command signature public key release ceiling"))?;
    if public_key_bytes > release.max_public_key_bytes {
        return Err(AbiErrorV1::InvalidBounds(
            "command signature public key release ceiling",
        ));
    }
    let signature_len = u64::try_from(signature_bytes.len())
        .map_err(|_| AbiErrorV1::InvalidBounds("command signature release ceiling"))?;
    if signature_len > release.max_signature_bytes {
        return Err(AbiErrorV1::InvalidBounds(
            "command signature release ceiling",
        ));
    }
    Ok(release)
}

fn validate_verifier_evidence_v1(
    statuses: &[CommandSignatureVerifierEvidenceStatusV1],
) -> AbiResultV1<()> {
    if statuses.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(AbiErrorV1::InvalidOrder(
            "command signature verifier evidence statuses",
        ));
    }
    Ok(())
}
