use zenodex_global_settlement_abi_v1::{
    authenticate_economic_command_intent_v1, bind_authenticated_intent_to_occurrence_v1,
    bind_economic_command_signature_verifier_deployment_v1,
    command_signature_verifier_backend_protocol_root_v1,
    command_signature_verifier_implementation_root_v1, AbiErrorV1, AuthenticatedEconomicCommandV1,
    CommandSignatureVerifierEvidenceArtifactV1, CommandSignatureVerifierEvidenceStatusV1,
    EconomicCommandAuthenticationCandidateV1, EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandAuthorizationRegistryV1, EconomicCommandAuthorizationV1,
    EconomicCommandIntentV1, EconomicCommandOccurrenceV1,
    EconomicCommandSignatureVerifierBackendV1, EconomicCommandSignatureVerifierEvidenceManifestV1,
    EconomicCommandSignatureVerifierRegistryV1, EconomicCommandSignatureVerifierReleaseV1,
    EconomicPolicyBindingV1, EconomicPolicyRegistryV1, EconomicProfileSnapshotV1, ReleaseStatusV1,
    RootV1, RouteRegistryV1, ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1, ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
    GLOBAL_SETTLEMENT_ABI_V1,
};

use super::root;

const COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1: &[u8] =
    b"asset-lane-host-command-signature-verifier-test-artifact-v1";

fn active_verifier_evidence() -> Vec<CommandSignatureVerifierEvidenceStatusV1> {
    vec![
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
}

fn signature_verifier_manifest() -> EconomicCommandSignatureVerifierEvidenceManifestV1 {
    let evidence_artifacts = active_verifier_evidence()
        .into_iter()
        .enumerate()
        .map(
            |(index, status)| CommandSignatureVerifierEvidenceArtifactV1 {
                status,
                artifact_root: root(700 + u64::try_from(index).unwrap()),
            },
        )
        .collect();
    EconomicCommandSignatureVerifierEvidenceManifestV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
        implementation_root: command_signature_verifier_implementation_root_v1(
            COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1,
        )
        .unwrap(),
        public_key_schema_root: root(711),
        signature_schema_root: root(712),
        message_schema_root: root(713),
        specification_root: root(714),
        source_root: root(715),
        toolchain_root: root(716),
        backend_protocol_root: command_signature_verifier_backend_protocol_root_v1().unwrap(),
        max_public_key_bytes: 160,
        max_signature_bytes: 4_096,
        evidence_artifacts,
    }
}

fn signature_verifier_registry() -> EconomicCommandSignatureVerifierRegistryV1 {
    let manifest = signature_verifier_manifest();
    let mut release = EconomicCommandSignatureVerifierReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        release_id: root(717),
        semantic_version: "1.0.0-asset-lane-host-test".to_owned(),
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
    EconomicCommandSignatureVerifierRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: vec![release],
    }
}

fn authorization_registry(routes: &RouteRegistryV1) -> EconomicCommandAuthorizationRegistryV1 {
    let route = routes
        .routes
        .first()
        .expect("asset lane host fixture route must exist");
    EconomicCommandAuthorizationRegistryV1 {
        schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
        authorizations: vec![EconomicCommandAuthorizationV1 {
            schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
            command_kind: route.command_kind.clone(),
            subject_id: "alice".to_owned(),
            grant_root: root(5),
            route_release_id: route.route_release_id.clone(),
            signer_key_id: "alice-key-1".to_owned(),
            signer_public_key: "bls12-381-g2:alice-public-key".to_owned(),
            signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
            valid_from_height: 0,
            valid_through_height: u64::MAX,
            min_nonce: 0,
            max_nonce: u64::MAX,
            enabled: true,
        }],
    }
}

fn authentication_policy_registry(routes: &RouteRegistryV1) -> EconomicPolicyRegistryV1 {
    let authorizations = authorization_registry(routes);
    let signature_verifiers = signature_verifier_registry();
    let command_kind = routes
        .routes
        .first()
        .expect("asset lane host fixture route must exist")
        .command_kind
        .clone();
    EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![
            EconomicPolicyBindingV1 {
                policy_kind: ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1.to_owned(),
                command_kind: command_kind.clone(),
                policy_root: authorizations.registry_root().unwrap(),
            },
            EconomicPolicyBindingV1 {
                policy_kind: ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1.to_owned(),
                command_kind,
                policy_root: signature_verifiers.registry_root().unwrap(),
            },
        ],
    }
}

pub(super) fn authentication_policy_registry_root_v1(routes: &RouteRegistryV1) -> RootV1 {
    authentication_policy_registry(routes)
        .registry_root()
        .unwrap()
}

struct AcceptingCommandSignatureVerifierV1;

impl EconomicCommandSignatureVerifierBackendV1 for AcceptingCommandSignatureVerifierV1 {
    fn verify_command_signature(
        &self,
        _signature_algorithm: &str,
        _signer_public_key: &str,
        message_bytes: &[u8],
        signature_bytes: &[u8],
    ) -> Result<bool, AbiErrorV1> {
        Ok(!message_bytes.is_empty() && !signature_bytes.is_empty())
    }
}

pub(super) fn authenticate_occurrence_v1(
    profile: &EconomicProfileSnapshotV1,
    routes: &RouteRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    command_body_bytes: Vec<u8>,
) -> AuthenticatedEconomicCommandV1 {
    let authorization_registry = authorization_registry(routes);
    let signature_verifier_registry = signature_verifier_registry();
    let policy_registry = authentication_policy_registry(routes);
    let authorization = authorization_registry
        .authorization_for(occurrence, "alice-key-1")
        .unwrap();
    let intent = EconomicCommandIntentV1 {
        schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        command_kind: occurrence.command_kind.clone(),
        command_body_hash: occurrence.command_body_hash.clone(),
        route_release_id: occurrence.route_release_id.clone(),
        subject_id: occurrence.subject_id.clone(),
        grant_root: occurrence.grant_root.clone(),
        nonce: occurrence.nonce,
        consumed_object_ids: occurrence.consumed_object_ids.clone(),
        valid_from_height: 0,
        valid_through_height: u64::MAX,
    };
    let envelope = EconomicCommandAuthenticationEnvelopeV1 {
        command_body_bytes,
        signer_key_id: authorization.signer_key_id.clone(),
        signer_public_key: authorization.signer_public_key.clone(),
        signature_algorithm: authorization.signature_algorithm.clone(),
        signature_bytes: b"asset-lane-host-test-command-signature-v1".to_vec(),
    };
    let authenticated_intent = authenticate_economic_command_intent_v1(
        &EconomicCommandAuthenticationCandidateV1 {
            profile,
            routes,
            policy_registry: &policy_registry,
            authorization_registry: &authorization_registry,
            signature_verifier_registry: &signature_verifier_registry,
            intent: &intent,
            envelope: &envelope,
        },
        &bind_economic_command_signature_verifier_deployment_v1(
            &signature_verifier_registry.releases[0],
            &signature_verifier_manifest(),
            COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1,
            &occurrence.deployment_root,
            &occurrence.profile_root,
            AcceptingCommandSignatureVerifierV1,
        )
        .unwrap(),
    )
    .unwrap();
    bind_authenticated_intent_to_occurrence_v1(&authenticated_intent, occurrence).unwrap()
}
