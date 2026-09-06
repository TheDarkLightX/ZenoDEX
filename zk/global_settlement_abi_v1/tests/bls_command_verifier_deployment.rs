//! Successor binder checks with synthetic, non-published release fixtures.

use zenodex_global_settlement_abi_v1::*;

const ARTIFACT_BYTES: &[u8] = b"measured-native-bls-command-verifier-v1";

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).unwrap()
}

fn repeated_root(byte: &str) -> RootV1 {
    RootV1::parse(format!("0x{}", byte.repeat(32)), "test root", false).unwrap()
}

fn evidence_artifacts(
    purpose: EconomicCommandSignatureVerifierSelectionPurposeV1,
) -> Vec<CommandSignatureVerifierEvidenceArtifactV1> {
    let statuses: &[CommandSignatureVerifierEvidenceStatusV1] = match purpose {
        EconomicCommandSignatureVerifierSelectionPurposeV1::PRODUCTION_NEW => &[
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
        ],
        EconomicCommandSignatureVerifierSelectionPurposeV1::ISOLATED_QUALIFICATION => &[
            CommandSignatureVerifierEvidenceStatusV1::IMPLEMENTED,
            CommandSignatureVerifierEvidenceStatusV1::SOURCE_PINNED,
            CommandSignatureVerifierEvidenceStatusV1::SPECIFIED,
            CommandSignatureVerifierEvidenceStatusV1::TESTED,
            CommandSignatureVerifierEvidenceStatusV1::TOOLCHAIN_PINNED,
        ],
    };
    statuses
        .iter()
        .copied()
        .enumerate()
        .map(
            |(index, status)| CommandSignatureVerifierEvidenceArtifactV1 {
                status,
                artifact_root: root(500 + u64::try_from(index).unwrap()),
            },
        )
        .collect()
}

fn manifest(
    purpose: EconomicCommandSignatureVerifierSelectionPurposeV1,
) -> EconomicCommandSignatureVerifierEvidenceManifestV1 {
    EconomicCommandSignatureVerifierEvidenceManifestV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        signature_algorithm: BLS_COMMAND_ALGORITHM_V1.to_owned(),
        implementation_root: command_signature_verifier_implementation_root_v1(ARTIFACT_BYTES)
            .unwrap(),
        public_key_schema_root: root(311),
        signature_schema_root: root(312),
        message_schema_root: root(313),
        specification_root: root(314),
        source_root: root(315),
        toolchain_root: root(316),
        backend_protocol_root: bls_command_verifier_protocol_root_v1().unwrap(),
        max_public_key_bytes: BLS_COMMAND_PUBLIC_KEY_TOKEN_BYTES_V1,
        max_signature_bytes: BLS_COMMAND_SIGNATURE_BYTES_V1,
        evidence_artifacts: evidence_artifacts(purpose),
    }
}

fn release(
    manifest: &EconomicCommandSignatureVerifierEvidenceManifestV1,
    purpose: EconomicCommandSignatureVerifierSelectionPurposeV1,
) -> EconomicCommandSignatureVerifierReleaseV1 {
    let production = purpose == EconomicCommandSignatureVerifierSelectionPurposeV1::PRODUCTION_NEW;
    let mut release = EconomicCommandSignatureVerifierReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        release_id: root(1),
        semantic_version: "1.0.0-bls-deployment-test".to_owned(),
        signature_algorithm: manifest.signature_algorithm.clone(),
        implementation_root: manifest.implementation_root.clone(),
        public_key_schema_root: manifest.public_key_schema_root.clone(),
        signature_schema_root: manifest.signature_schema_root.clone(),
        message_schema_root: manifest.message_schema_root.clone(),
        specification_root: manifest.specification_root.clone(),
        source_root: manifest.source_root.clone(),
        toolchain_root: manifest.toolchain_root.clone(),
        evidence_manifest_root: manifest.manifest_root().unwrap(),
        max_public_key_bytes: manifest.max_public_key_bytes,
        max_signature_bytes: manifest.max_signature_bytes,
        status: if production {
            ReleaseStatusV1::ACTIVE_NEW
        } else {
            ReleaseStatusV1::SHADOW
        },
        accepts_new_authentications: production,
        evidence_statuses: manifest
            .evidence_artifacts
            .iter()
            .map(|row| row.status)
            .collect(),
    };
    release.release_id = release.derived_release_id().unwrap();
    release
}

struct AcceptingBackend;

impl EconomicCommandSignatureVerifierBackendV1 for AcceptingBackend {
    fn verify_command_signature(
        &self,
        _signature_algorithm: &str,
        _signer_public_key: &str,
        _message_bytes: &[u8],
        _signature_bytes: &[u8],
    ) -> AbiResultV1<bool> {
        Ok(true)
    }
}

#[test]
fn successor_protocol_root_and_isolated_binding_match_python() {
    let purpose = EconomicCommandSignatureVerifierSelectionPurposeV1::ISOLATED_QUALIFICATION;
    let manifest = manifest(purpose);
    let release = release(&manifest, purpose);
    let bound = bind_bls_command_signature_verifier_deployment_v1(
        &release,
        &manifest,
        ARTIFACT_BYTES,
        &repeated_root("41"),
        &repeated_root("42"),
        AcceptingBackend,
        purpose,
    )
    .unwrap();

    assert_eq!(
        bls_command_verifier_protocol_root_v1().unwrap().as_str(),
        "0xf5a1d92017eca916feccff07b5da8204f389ee15fbf3547b3ff9b72107f7d9dd"
    );
    assert_ne!(
        bls_command_verifier_protocol_root_v1().unwrap(),
        command_signature_verifier_backend_protocol_root_v1().unwrap()
    );
    assert_eq!(bound.selection_purpose(), purpose);
    bound
        .require_binding_for_purpose(
            &release.release_id,
            &repeated_root("41"),
            &repeated_root("42"),
            purpose,
        )
        .unwrap();
    assert_eq!(
        bound.binding_root().unwrap().as_str(),
        "0x1f77876303982338b7cd4e094ff2a45749666f80e1b9653473b06a6233252cda"
    );
}

#[test]
fn old_and_new_protocol_binders_reject_each_others_manifests() {
    let purpose = EconomicCommandSignatureVerifierSelectionPurposeV1::PRODUCTION_NEW;
    let bls_manifest = manifest(purpose);
    let bls_release = release(&bls_manifest, purpose);
    assert!(matches!(
        bind_economic_command_signature_verifier_deployment_v1(
            &bls_release,
            &bls_manifest,
            ARTIFACT_BYTES,
            &root(401),
            &root(402),
            AcceptingBackend,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier backend protocol root"
        ))
    ));

    let mut legacy_manifest = manifest(purpose);
    legacy_manifest.backend_protocol_root =
        command_signature_verifier_backend_protocol_root_v1().unwrap();
    let legacy_release = release(&legacy_manifest, purpose);
    assert!(matches!(
        bind_bls_command_signature_verifier_deployment_v1(
            &legacy_release,
            &legacy_manifest,
            ARTIFACT_BYTES,
            &root(401),
            &root(402),
            AcceptingBackend,
            purpose,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier backend protocol root"
        ))
    ));
}

#[test]
fn successor_binder_requires_exact_bls_algorithm_and_ceilings() {
    let purpose = EconomicCommandSignatureVerifierSelectionPurposeV1::ISOLATED_QUALIFICATION;
    for (algorithm, public_key_bytes, signature_bytes, expected) in [
        (
            "BLS12_381_G2_POP_V1",
            BLS_COMMAND_PUBLIC_KEY_TOKEN_BYTES_V1,
            BLS_COMMAND_SIGNATURE_BYTES_V1,
            "BLS command verifier algorithm",
        ),
        (
            BLS_COMMAND_ALGORITHM_V1,
            BLS_COMMAND_PUBLIC_KEY_TOKEN_BYTES_V1 - 1,
            BLS_COMMAND_SIGNATURE_BYTES_V1,
            "BLS command verifier public-key ceiling",
        ),
        (
            BLS_COMMAND_ALGORITHM_V1,
            BLS_COMMAND_PUBLIC_KEY_TOKEN_BYTES_V1 + 1,
            BLS_COMMAND_SIGNATURE_BYTES_V1,
            "BLS command verifier public-key ceiling",
        ),
        (
            BLS_COMMAND_ALGORITHM_V1,
            BLS_COMMAND_PUBLIC_KEY_TOKEN_BYTES_V1,
            BLS_COMMAND_SIGNATURE_BYTES_V1 - 1,
            "BLS command verifier signature ceiling",
        ),
        (
            BLS_COMMAND_ALGORITHM_V1,
            BLS_COMMAND_PUBLIC_KEY_TOKEN_BYTES_V1,
            BLS_COMMAND_SIGNATURE_BYTES_V1 + 1,
            "BLS command verifier signature ceiling",
        ),
    ] {
        let mut candidate = manifest(purpose);
        candidate.signature_algorithm = algorithm.to_owned();
        candidate.max_public_key_bytes = public_key_bytes;
        candidate.max_signature_bytes = signature_bytes;
        let candidate_release = release(&candidate, purpose);
        assert!(matches!(
            bind_bls_command_signature_verifier_deployment_v1(
                &candidate_release,
                &candidate,
                ARTIFACT_BYTES,
                &root(401),
                &root(402),
                AcceptingBackend,
                purpose,
            ),
            Err(AbiErrorV1::InvalidBinding(message)) if message == expected
        ));
    }
}

#[test]
fn successor_binder_rejects_artifact_manifest_scope_and_purpose_mismatches() {
    let isolated = EconomicCommandSignatureVerifierSelectionPurposeV1::ISOLATED_QUALIFICATION;
    let isolated_manifest = manifest(isolated);
    let isolated_release = release(&isolated_manifest, isolated);
    assert!(matches!(
        bind_bls_command_signature_verifier_deployment_v1(
            &isolated_release,
            &isolated_manifest,
            b"different artifact",
            &root(401),
            &root(402),
            AcceptingBackend,
            isolated,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier measured implementation root"
        ))
    ));

    let mut changed_manifest = isolated_manifest.clone();
    changed_manifest.source_root = root(999);
    assert!(matches!(
        bind_bls_command_signature_verifier_deployment_v1(
            &isolated_release,
            &changed_manifest,
            ARTIFACT_BYTES,
            &root(401),
            &root(402),
            AcceptingBackend,
            isolated,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier evidence manifest root"
        ))
    ));

    let zero = RootV1::parse(ZERO_ROOT_V1, "test zero root", true).unwrap();
    for (deployment_root, profile_root) in [(zero.clone(), root(402)), (root(401), zero)] {
        assert!(matches!(
            bind_bls_command_signature_verifier_deployment_v1(
                &isolated_release,
                &isolated_manifest,
                ARTIFACT_BYTES,
                &deployment_root,
                &profile_root,
                AcceptingBackend,
                isolated,
            ),
            Err(AbiErrorV1::InvalidRoot(_))
        ));
    }

    assert!(matches!(
        bind_bls_command_signature_verifier_deployment_v1(
            &isolated_release,
            &isolated_manifest,
            ARTIFACT_BYTES,
            &root(401),
            &root(402),
            AcceptingBackend,
            EconomicCommandSignatureVerifierSelectionPurposeV1::PRODUCTION_NEW,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "production command authentication requires an active verifier release"
        ))
    ));

    let production = EconomicCommandSignatureVerifierSelectionPurposeV1::PRODUCTION_NEW;
    let production_manifest = manifest(production);
    let production_release = release(&production_manifest, production);
    assert!(matches!(
        bind_bls_command_signature_verifier_deployment_v1(
            &production_release,
            &production_manifest,
            ARTIFACT_BYTES,
            &root(401),
            &root(402),
            AcceptingBackend,
            isolated,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "isolated command authentication requires a shadow verifier release"
        ))
    ));

    let mut incomplete_manifest = manifest(isolated);
    incomplete_manifest.evidence_artifacts.truncate(1);
    let incomplete_release = release(&incomplete_manifest, isolated);
    assert!(matches!(
        bind_bls_command_signature_verifier_deployment_v1(
            &incomplete_release,
            &incomplete_manifest,
            ARTIFACT_BYTES,
            &root(401),
            &root(402),
            AcceptingBackend,
            isolated,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "isolated command signature verifier lacks baseline evidence"
        ))
    ));

    let mut legacy_shadow_manifest = manifest(isolated);
    legacy_shadow_manifest.backend_protocol_root =
        command_signature_verifier_backend_protocol_root_v1().unwrap();
    let legacy_shadow_release = release(&legacy_shadow_manifest, isolated);
    assert!(matches!(
        bind_economic_command_signature_verifier_deployment_v1(
            &legacy_shadow_release,
            &legacy_shadow_manifest,
            ARTIFACT_BYTES,
            &root(401),
            &root(402),
            AcceptingBackend,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "production command authentication requires an active verifier release"
        ))
    ));
}
