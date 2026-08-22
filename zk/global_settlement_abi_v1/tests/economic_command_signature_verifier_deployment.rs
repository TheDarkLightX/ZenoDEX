use zenodex_global_settlement_abi_v1::*;

const ALGORITHM: &str = "BLS12_381_G2_BASIC_V1";
const ARTIFACT_BYTES: &[u8] = b"zenodex-command-signature-verifier-test-artifact-v1";

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).unwrap()
}

fn evidence_artifacts() -> Vec<CommandSignatureVerifierEvidenceArtifactV1> {
    [
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
    ]
    .into_iter()
    .enumerate()
    .map(
        |(index, status)| CommandSignatureVerifierEvidenceArtifactV1 {
            status,
            artifact_root: root(500 + u64::try_from(index).unwrap()),
        },
    )
    .collect()
}

fn manifest() -> EconomicCommandSignatureVerifierEvidenceManifestV1 {
    EconomicCommandSignatureVerifierEvidenceManifestV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        signature_algorithm: ALGORITHM.to_owned(),
        implementation_root: command_signature_verifier_implementation_root_v1(ARTIFACT_BYTES)
            .unwrap(),
        public_key_schema_root: root(311),
        signature_schema_root: root(312),
        message_schema_root: root(313),
        specification_root: root(314),
        source_root: root(315),
        toolchain_root: root(316),
        backend_protocol_root: command_signature_verifier_backend_protocol_root_v1().unwrap(),
        max_public_key_bytes: 160,
        max_signature_bytes: 4_096,
        evidence_artifacts: evidence_artifacts(),
    }
}

fn release(
    manifest: &EconomicCommandSignatureVerifierEvidenceManifestV1,
) -> EconomicCommandSignatureVerifierReleaseV1 {
    let mut release = EconomicCommandSignatureVerifierReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        release_id: root(1),
        semantic_version: "1.0.0-deployment-test".to_owned(),
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
        status: ReleaseStatusV1::ACTIVE_NEW,
        accepts_new_authentications: true,
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
fn exact_manifest_measurement_and_scope_construct_bound_capability() {
    let manifest = manifest();
    let release = release(&manifest);
    let bound = bind_economic_command_signature_verifier_deployment_v1(
        &release,
        &manifest,
        ARTIFACT_BYTES,
        &root(401),
        &root(402),
        AcceptingBackend,
    )
    .unwrap();

    assert_eq!(bound.release_id(), &release.release_id);
    assert_eq!(bound.deployment_root(), &root(401));
    assert_eq!(bound.profile_root(), &root(402));
    assert!(!bound.binding_root().unwrap().is_zero());
}

#[test]
fn wrong_artifact_and_manifest_reject_before_capability_construction() {
    let manifest = manifest();
    let release = release(&manifest);
    assert!(matches!(
        bind_economic_command_signature_verifier_deployment_v1(
            &release,
            &manifest,
            b"different-artifact",
            &root(401),
            &root(402),
            AcceptingBackend,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier measured implementation root"
        ))
    ));

    let mut mutated = manifest.clone();
    mutated.source_root = root(999);
    assert!(matches!(
        bind_economic_command_signature_verifier_deployment_v1(
            &release,
            &mutated,
            ARTIFACT_BYTES,
            &root(401),
            &root(402),
            AcceptingBackend,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier evidence manifest root"
        ))
    ));
}

#[test]
fn evidence_artifacts_require_nonempty_sorted_unique_rows() {
    let mut reversed_manifest = manifest();
    reversed_manifest.evidence_artifacts.reverse();
    assert!(matches!(
        reversed_manifest.validate(),
        Err(AbiErrorV1::InvalidOrder(
            "command signature verifier evidence artifacts"
        ))
    ));

    let mut duplicate_manifest = manifest();
    duplicate_manifest.evidence_artifacts.push(
        duplicate_manifest
            .evidence_artifacts
            .last()
            .unwrap()
            .clone(),
    );
    assert!(matches!(
        duplicate_manifest.validate(),
        Err(AbiErrorV1::InvalidOrder(
            "command signature verifier evidence artifacts"
        ))
    ));

    let mut empty_manifest = manifest();
    empty_manifest.evidence_artifacts.clear();
    assert!(matches!(
        empty_manifest.validate(),
        Err(AbiErrorV1::InvalidBounds(
            "command signature verifier evidence artifacts"
        ))
    ));
}

#[test]
fn unsupported_backend_protocol_rejects_even_when_release_commits_manifest() {
    let mut manifest = manifest();
    manifest.backend_protocol_root = root(999);
    let release = release(&manifest);

    assert!(matches!(
        bind_economic_command_signature_verifier_deployment_v1(
            &release,
            &manifest,
            ARTIFACT_BYTES,
            &root(401),
            &root(402),
            AcceptingBackend,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier backend protocol root"
        ))
    ));
}

#[test]
fn artifact_byte_length_uses_zero_one_maximum_neighbor_bva() {
    for (artifact_len, accepted) in [
        (0, false),
        (1, true),
        (MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1, true),
        (MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1 + 1, false),
    ] {
        let artifact = vec![b'a'; artifact_len];
        assert_eq!(
            command_signature_verifier_implementation_root_v1(&artifact).is_ok(),
            accepted
        );
    }
}

#[test]
fn binding_roots_match_cross_language_golden() {
    let manifest = manifest();
    let release = release(&manifest);
    let bound = bind_economic_command_signature_verifier_deployment_v1(
        &release,
        &manifest,
        ARTIFACT_BYTES,
        &root(401),
        &root(402),
        AcceptingBackend,
    )
    .unwrap();

    assert_eq!(
        command_signature_verifier_implementation_root_v1(ARTIFACT_BYTES)
            .unwrap()
            .as_str(),
        "0xd6b4fd058a7714e0fe9695a2aab134985cb10c3f471ce41fcca35feb6753cc93"
    );
    assert_eq!(
        manifest.manifest_root().unwrap().as_str(),
        "0x4ab6a095bdded66a5a2809734f097ff271daf80a397944e8ffa994305fb64983"
    );
    assert_eq!(
        bound.binding_root().unwrap().as_str(),
        "0x4ad7612be045c5b6d7ea52f458dc9814075030ee866ff825b215da92b93d68bd"
    );
}
