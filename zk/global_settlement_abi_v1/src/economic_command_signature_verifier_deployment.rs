use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::canonical::{
    hash_global_v1, validate_schema_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
    GLOBAL_SETTLEMENT_ABI_V1, MAX_JOURNAL_BYTES_V1, MAX_TOKEN_BYTES_V1,
};
use crate::economic_command_signature_verifier_registry::{
    CommandSignatureVerifierEvidenceStatusV1, EconomicCommandSignatureVerifierReleaseV1,
    MAX_COMMAND_SIGNATURE_BYTES_V1,
};

pub const MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1: usize = 16 * 1024 * 1024;
const IMPLEMENTATION_ROOT_DOMAIN_V1: &str = "economic-command-signature-verifier-implementation-v1";
const EVIDENCE_MANIFEST_ROOT_DOMAIN_V1: &str =
    "economic-command-signature-verifier-evidence-manifest-v1";
const DEPLOYMENT_BINDING_ROOT_DOMAIN_V1: &str =
    "economic-command-signature-verifier-deployment-binding-v1";
const BACKEND_PROTOCOL_ROOT_DOMAIN_V1: &str =
    "economic-command-signature-verifier-backend-protocol-v1";

pub trait EconomicCommandSignatureVerifierBackendV1 {
    fn verify_command_signature(
        &self,
        signature_algorithm: &str,
        signer_public_key: &str,
        message_bytes: &[u8],
        signature_bytes: &[u8],
    ) -> AbiResultV1<bool>;
}

impl<T: EconomicCommandSignatureVerifierBackendV1 + ?Sized>
    EconomicCommandSignatureVerifierBackendV1 for &T
{
    fn verify_command_signature(
        &self,
        signature_algorithm: &str,
        signer_public_key: &str,
        message_bytes: &[u8],
        signature_bytes: &[u8],
    ) -> AbiResultV1<bool> {
        (*self).verify_command_signature(
            signature_algorithm,
            signer_public_key,
            message_bytes,
            signature_bytes,
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CommandSignatureVerifierEvidenceArtifactV1 {
    pub status: CommandSignatureVerifierEvidenceStatusV1,
    pub artifact_root: RootV1,
}

impl CommandSignatureVerifierEvidenceArtifactV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.artifact_root
            .validate("command signature verifier evidence artifact root", false)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicCommandSignatureVerifierEvidenceManifestV1 {
    pub schema: String,
    pub signature_algorithm: String,
    pub implementation_root: RootV1,
    pub public_key_schema_root: RootV1,
    pub signature_schema_root: RootV1,
    pub message_schema_root: RootV1,
    pub specification_root: RootV1,
    pub source_root: RootV1,
    pub toolchain_root: RootV1,
    pub backend_protocol_root: RootV1,
    pub max_public_key_bytes: u64,
    pub max_signature_bytes: u64,
    pub evidence_artifacts: Vec<CommandSignatureVerifierEvidenceArtifactV1>,
}

impl EconomicCommandSignatureVerifierEvidenceManifestV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(
            &self.signature_algorithm,
            "command signature verifier manifest algorithm",
        )?;
        for root in [
            &self.implementation_root,
            &self.public_key_schema_root,
            &self.signature_schema_root,
            &self.message_schema_root,
            &self.specification_root,
            &self.source_root,
            &self.toolchain_root,
            &self.backend_protocol_root,
        ] {
            root.validate("command signature verifier manifest root", false)?;
        }
        let max_public_key_bytes = u64::try_from(MAX_TOKEN_BYTES_V1).map_err(|_| {
            AbiErrorV1::InvalidBounds("command signature verifier manifest public-key ceiling")
        })?;
        if self.max_public_key_bytes == 0 || self.max_public_key_bytes > max_public_key_bytes {
            return Err(AbiErrorV1::InvalidBounds(
                "command signature verifier manifest public-key ceiling",
            ));
        }
        let max_signature_bytes = u64::try_from(MAX_COMMAND_SIGNATURE_BYTES_V1).map_err(|_| {
            AbiErrorV1::InvalidBounds("command signature verifier manifest signature ceiling")
        })?;
        if self.max_signature_bytes == 0 || self.max_signature_bytes > max_signature_bytes {
            return Err(AbiErrorV1::InvalidBounds(
                "command signature verifier manifest signature ceiling",
            ));
        }
        if self.evidence_artifacts.is_empty() {
            return Err(AbiErrorV1::InvalidBounds(
                "command signature verifier evidence artifacts",
            ));
        }
        for row in &self.evidence_artifacts {
            row.validate()?;
        }
        if self
            .evidence_artifacts
            .windows(2)
            .any(|pair| pair[0].status >= pair[1].status)
        {
            return Err(AbiErrorV1::InvalidOrder(
                "command signature verifier evidence artifacts",
            ));
        }
        Ok(())
    }

    pub fn manifest_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1(EVIDENCE_MANIFEST_ROOT_DOMAIN_V1, self)
    }
}

#[derive(Serialize)]
struct CommandSignatureVerifierBackendProtocolV1<'a> {
    schema: &'static str,
    request_fields: [&'a str; 4],
    response_semantics: &'a str,
}

pub fn command_signature_verifier_backend_protocol_root_v1() -> AbiResultV1<RootV1> {
    hash_global_v1(
        BACKEND_PROTOCOL_ROOT_DOMAIN_V1,
        &CommandSignatureVerifierBackendProtocolV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            request_fields: [
                "signature_algorithm",
                "signer_public_key",
                "message_bytes",
                "signature_bytes",
            ],
            response_semantics: "EXACT_TRUE_ACCEPTS_OTHERWISE_REJECTS",
        },
    )
}

pub fn command_signature_verifier_implementation_root_v1(
    artifact_bytes: &[u8],
) -> AbiResultV1<RootV1> {
    if artifact_bytes.is_empty()
        || artifact_bytes.len() > MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1
    {
        return Err(AbiErrorV1::InvalidBounds(
            "command signature verifier artifact bytes",
        ));
    }
    let mut digest = Sha256::new();
    digest.update(b"zenodex:");
    digest.update(IMPLEMENTATION_ROOT_DOMAIN_V1.as_bytes());
    digest.update(b":v1\0");
    digest.update(artifact_bytes);
    RootV1::parse(
        format!("0x{}", hex::encode(digest.finalize())),
        "command signature verifier implementation root",
        false,
    )
}

#[derive(Serialize)]
struct CommandSignatureVerifierDeploymentBindingV1<'a> {
    schema: &'static str,
    release_id: &'a RootV1,
    deployment_root: &'a RootV1,
    profile_root: &'a RootV1,
    implementation_root: &'a RootV1,
    evidence_manifest_root: &'a RootV1,
    backend_protocol_root: &'a RootV1,
}

pub struct BoundEconomicCommandSignatureVerifierV1<B> {
    release_id: RootV1,
    deployment_root: RootV1,
    profile_root: RootV1,
    implementation_root: RootV1,
    evidence_manifest_root: RootV1,
    backend_protocol_root: RootV1,
    signature_algorithm: String,
    max_public_key_bytes: u64,
    max_signature_bytes: u64,
    backend: B,
}

impl<B: EconomicCommandSignatureVerifierBackendV1> BoundEconomicCommandSignatureVerifierV1<B> {
    pub fn release_id(&self) -> &RootV1 {
        &self.release_id
    }

    pub fn deployment_root(&self) -> &RootV1 {
        &self.deployment_root
    }

    pub fn profile_root(&self) -> &RootV1 {
        &self.profile_root
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            DEPLOYMENT_BINDING_ROOT_DOMAIN_V1,
            &CommandSignatureVerifierDeploymentBindingV1 {
                schema: GLOBAL_SETTLEMENT_ABI_V1,
                release_id: &self.release_id,
                deployment_root: &self.deployment_root,
                profile_root: &self.profile_root,
                implementation_root: &self.implementation_root,
                evidence_manifest_root: &self.evidence_manifest_root,
                backend_protocol_root: &self.backend_protocol_root,
            },
        )
    }

    pub fn require_binding(
        &self,
        release_id: &RootV1,
        deployment_root: &RootV1,
        profile_root: &RootV1,
    ) -> AbiResultV1<()> {
        if release_id != &self.release_id {
            return Err(AbiErrorV1::InvalidBinding(
                "command signature verifier release binding",
            ));
        }
        if deployment_root != &self.deployment_root {
            return Err(AbiErrorV1::InvalidBinding(
                "command signature verifier deployment binding",
            ));
        }
        if profile_root != &self.profile_root {
            return Err(AbiErrorV1::InvalidBinding(
                "command signature verifier profile binding",
            ));
        }
        Ok(())
    }

    pub(crate) fn verify_command_signature(
        &self,
        signature_algorithm: &str,
        signer_public_key: &str,
        message_bytes: &[u8],
        signature_bytes: &[u8],
    ) -> AbiResultV1<bool> {
        if signature_algorithm != self.signature_algorithm {
            return Err(AbiErrorV1::InvalidBinding(
                "command signature verifier algorithm binding",
            ));
        }
        let public_key_bytes = u64::try_from(signer_public_key.len()).map_err(|_| {
            AbiErrorV1::InvalidBounds("command signature verifier public key bytes")
        })?;
        if public_key_bytes > self.max_public_key_bytes {
            return Err(AbiErrorV1::InvalidBounds(
                "command signature verifier public key bytes",
            ));
        }
        let message_len = u64::try_from(message_bytes.len())
            .map_err(|_| AbiErrorV1::InvalidBounds("command signature verifier message bytes"))?;
        if message_len == 0 || message_len > MAX_JOURNAL_BYTES_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "command signature verifier message bytes",
            ));
        }
        let signature_len = u64::try_from(signature_bytes.len())
            .map_err(|_| AbiErrorV1::InvalidBounds("command signature verifier signature bytes"))?;
        if signature_len == 0 || signature_len > self.max_signature_bytes {
            return Err(AbiErrorV1::InvalidBounds(
                "command signature verifier signature bytes",
            ));
        }
        self.backend.verify_command_signature(
            signature_algorithm,
            signer_public_key,
            message_bytes,
            signature_bytes,
        )
    }
}

pub fn bind_economic_command_signature_verifier_deployment_v1<B>(
    release: &EconomicCommandSignatureVerifierReleaseV1,
    evidence_manifest: &EconomicCommandSignatureVerifierEvidenceManifestV1,
    measured_artifact_bytes: &[u8],
    deployment_root: &RootV1,
    profile_root: &RootV1,
    backend: B,
) -> AbiResultV1<BoundEconomicCommandSignatureVerifierV1<B>>
where
    B: EconomicCommandSignatureVerifierBackendV1,
{
    release.validate()?;
    evidence_manifest.validate()?;
    if evidence_manifest.manifest_root()? != release.evidence_manifest_root {
        return Err(AbiErrorV1::InvalidBinding(
            "command signature verifier evidence manifest root",
        ));
    }
    require_manifest_release_coordinates_v1(evidence_manifest, release)?;
    if evidence_manifest.backend_protocol_root
        != command_signature_verifier_backend_protocol_root_v1()?
    {
        return Err(AbiErrorV1::InvalidBinding(
            "command signature verifier backend protocol root",
        ));
    }
    if command_signature_verifier_implementation_root_v1(measured_artifact_bytes)?
        != release.implementation_root
    {
        return Err(AbiErrorV1::InvalidBinding(
            "command signature verifier measured implementation root",
        ));
    }
    deployment_root.validate("command signature verifier deployment root", false)?;
    profile_root.validate("command signature verifier profile root", false)?;
    Ok(BoundEconomicCommandSignatureVerifierV1 {
        release_id: release.release_id.clone(),
        deployment_root: deployment_root.clone(),
        profile_root: profile_root.clone(),
        implementation_root: release.implementation_root.clone(),
        evidence_manifest_root: release.evidence_manifest_root.clone(),
        backend_protocol_root: evidence_manifest.backend_protocol_root.clone(),
        signature_algorithm: release.signature_algorithm.clone(),
        max_public_key_bytes: release.max_public_key_bytes,
        max_signature_bytes: release.max_signature_bytes,
        backend,
    })
}

fn require_manifest_release_coordinates_v1(
    manifest: &EconomicCommandSignatureVerifierEvidenceManifestV1,
    release: &EconomicCommandSignatureVerifierReleaseV1,
) -> AbiResultV1<()> {
    let evidence_statuses = manifest
        .evidence_artifacts
        .iter()
        .map(|row| row.status)
        .collect::<Vec<_>>();
    let matches = manifest.signature_algorithm == release.signature_algorithm
        && manifest.implementation_root == release.implementation_root
        && manifest.public_key_schema_root == release.public_key_schema_root
        && manifest.signature_schema_root == release.signature_schema_root
        && manifest.message_schema_root == release.message_schema_root
        && manifest.specification_root == release.specification_root
        && manifest.source_root == release.source_root
        && manifest.toolchain_root == release.toolchain_root
        && manifest.max_public_key_bytes == release.max_public_key_bytes
        && manifest.max_signature_bytes == release.max_signature_bytes
        && evidence_statuses == release.evidence_statuses;
    if !matches {
        return Err(AbiErrorV1::InvalidBinding(
            "command signature verifier manifest release coordinate",
        ));
    }
    Ok(())
}
