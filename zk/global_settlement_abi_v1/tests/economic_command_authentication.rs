use std::cell::RefCell;

use serde_json::json;
use zenodex_global_settlement_abi_v1::*;

const COMMAND_KIND: &str = "asset_transfer";
type RecordedSignatureCallV1 = (String, String, Vec<u8>, Vec<u8>);

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", value == 0).unwrap()
}

fn active_evidence() -> Vec<EvidenceStatusV1> {
    vec![
        EvidenceStatusV1::IMPLEMENTED,
        EvidenceStatusV1::MIGRATABLE,
        EvidenceStatusV1::MOUNTED,
        EvidenceStatusV1::NO_BYPASS,
        EvidenceStatusV1::PROVED,
        EvidenceStatusV1::RELEASE_BACKED,
        EvidenceStatusV1::SPECIFIED,
        EvidenceStatusV1::TERMINAL_COMPLETE,
        EvidenceStatusV1::TESTED,
    ]
}

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

fn signature_verifier_registry() -> EconomicCommandSignatureVerifierRegistryV1 {
    let mut release = EconomicCommandSignatureVerifierReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        release_id: root(1),
        semantic_version: "1.0.0-auth-test".to_owned(),
        signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
        implementation_root: root(310),
        public_key_schema_root: root(311),
        signature_schema_root: root(312),
        message_schema_root: root(313),
        specification_root: root(314),
        source_root: root(315),
        toolchain_root: root(316),
        evidence_manifest_root: root(317),
        max_public_key_bytes: 160,
        max_signature_bytes: 4_096,
        status: ReleaseStatusV1::ACTIVE_NEW,
        accepts_new_authentications: true,
        evidence_statuses: active_verifier_evidence(),
    };
    release.release_id = release.derived_release_id().unwrap();
    let registry = EconomicCommandSignatureVerifierRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: vec![release],
    };
    registry.validate().unwrap();
    registry
}

fn route() -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::ASSET_TRANSFER];
    let module_release_ids = vec![root(101)];
    let dependency_roles = vec!["VALUE_OWNER".to_owned()];
    let port_schema_roots = vec![root(102)];
    let guest_image_id = root(103);
    let specification_root = root(104);
    let source_root = root(105);
    let toolchain_root = root(106);
    let oracle_policy_root = root(107);
    let issue_burn_policy_root = root(108);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "command_kind": COMMAND_KIND,
        "ordered_lanes": ordered_lanes,
        "module_release_ids": module_release_ids,
        "dependency_roles": dependency_roles,
        "port_schema_roots": port_schema_roots,
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "oracle_policy_root": oracle_policy_root,
        "issue_burn_policy_root": issue_burn_policy_root,
        "max_cycles": 2_000_000,
        "max_journal_bytes": 131_072,
    });
    let route = RouteReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        route_release_id: hash_global_v1("global-route-release-content-v1", &content).unwrap(),
        semantic_version: "1.0.0-auth-test".to_owned(),
        command_kind: COMMAND_KIND.to_owned(),
        ordered_lanes,
        module_release_ids,
        dependency_roles,
        port_schema_roots,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        oracle_policy_root,
        issue_burn_policy_root,
        max_cycles: 2_000_000,
        max_journal_bytes: 131_072,
        status: ReleaseStatusV1::ACTIVE_NEW,
        accepts_new_objects: true,
        evidence_statuses: active_evidence(),
    };
    route.validate().unwrap();
    route
}

fn authorization(route: &RouteReleaseV1) -> EconomicCommandAuthorizationV1 {
    EconomicCommandAuthorizationV1 {
        schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
        command_kind: COMMAND_KIND.to_owned(),
        subject_id: "alice".to_owned(),
        grant_root: root(201),
        route_release_id: route.route_release_id.clone(),
        signer_key_id: "alice-key-1".to_owned(),
        signer_public_key: "bls12-381-g2:alice-public-key".to_owned(),
        signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
        valid_from_height: 10,
        valid_through_height: 12,
        min_nonce: 8,
        max_nonce: 10,
        enabled: true,
    }
}

fn profile(
    routes: &RouteRegistryV1,
    policy_registry: &EconomicPolicyRegistryV1,
    status: ProfileStatusV1,
) -> EconomicProfileSnapshotV1 {
    let lane_registry_root = root(301);
    let lane_coordinator_registry_root = root(302);
    let route_registry_root = routes.registry_root().unwrap();
    let proof_shape_root = root(303);
    let root_image_id = root(304);
    let verifier_registry_root = root(305);
    let migration_registry_root = root(306);
    let policy_registry_root = policy_registry.registry_root().unwrap();
    let terminal_registry_root = root(307);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "authority_epoch": 7,
        "lane_registry_root": lane_registry_root,
        "lane_coordinator_registry_root": lane_coordinator_registry_root,
        "route_registry_root": route_registry_root,
        "proof_shape_root": proof_shape_root,
        "root_image_id": root_image_id,
        "verifier_registry_root": verifier_registry_root,
        "migration_registry_root": migration_registry_root,
        "policy_registry_root": policy_registry_root,
        "terminal_registry_root": terminal_registry_root,
    });
    EconomicProfileSnapshotV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        profile_id: hash_global_v1("global-economic-profile-content-v1", &content).unwrap(),
        authority_epoch: 7,
        lane_registry_root,
        lane_coordinator_registry_root,
        route_registry_root,
        proof_shape_root,
        root_image_id,
        verifier_registry_root,
        migration_registry_root,
        policy_registry_root,
        terminal_registry_root,
        status,
    }
}

struct RecordingVerifier {
    result: bool,
    verifier_release_id: RootV1,
    calls: RefCell<Vec<RecordedSignatureCallV1>>,
}

impl RecordingVerifier {
    fn accepting() -> Self {
        Self {
            result: true,
            verifier_release_id: signature_verifier_registry().releases[0].release_id.clone(),
            calls: RefCell::new(Vec::new()),
        }
    }
}

impl EconomicCommandSignatureVerifierV1 for RecordingVerifier {
    fn verifier_release_id(&self) -> &RootV1 {
        &self.verifier_release_id
    }

    fn verify_command_signature(
        &self,
        signature_algorithm: &str,
        signer_public_key: &str,
        message_bytes: &[u8],
        signature_bytes: &[u8],
    ) -> AbiResultV1<bool> {
        self.calls.borrow_mut().push((
            signature_algorithm.to_owned(),
            signer_public_key.to_owned(),
            message_bytes.to_vec(),
            signature_bytes.to_vec(),
        ));
        Ok(self.result)
    }
}

struct Fixture {
    profile: EconomicProfileSnapshotV1,
    routes: RouteRegistryV1,
    policy_registry: EconomicPolicyRegistryV1,
    authorization_registry: EconomicCommandAuthorizationRegistryV1,
    signature_verifier_registry: EconomicCommandSignatureVerifierRegistryV1,
    intent: EconomicCommandIntentV1,
    occurrence: EconomicCommandOccurrenceV1,
    envelope: EconomicCommandAuthenticationEnvelopeV1,
}

impl Fixture {
    fn new() -> Self {
        let route = route();
        let routes = RouteRegistryV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            routes: vec![route.clone()],
        };
        let authorization_registry = EconomicCommandAuthorizationRegistryV1 {
            schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
            authorizations: vec![authorization(&route)],
        };
        let signature_verifier_registry = signature_verifier_registry();
        let mut bindings = vec![
            EconomicPolicyBindingV1 {
                policy_kind: ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1.to_owned(),
                command_kind: COMMAND_KIND.to_owned(),
                policy_root: authorization_registry.registry_root().unwrap(),
            },
            EconomicPolicyBindingV1 {
                policy_kind: ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1.to_owned(),
                command_kind: COMMAND_KIND.to_owned(),
                policy_root: signature_verifier_registry.registry_root().unwrap(),
            },
        ];
        bindings.sort_by(|left, right| {
            (&left.policy_kind, &left.command_kind).cmp(&(&right.policy_kind, &right.command_kind))
        });
        let policy_registry = EconomicPolicyRegistryV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            bindings,
        };
        let profile = profile(&routes, &policy_registry, ProfileStatusV1::ACTIVE);
        let command = AssetTransferCommandV1 {
            command_kind: COMMAND_KIND.to_owned(),
            asset: "USD".to_owned(),
            sender: "alice".to_owned(),
            recipient: "bob".to_owned(),
            amount_atoms: 30,
            max_fee_atoms: 2,
        };
        let intent = EconomicCommandIntentV1 {
            schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
            chain_id: "zeno-command-auth-rust-test".to_owned(),
            deployment_root: root(401),
            profile_root: profile.profile_id.clone(),
            command_kind: COMMAND_KIND.to_owned(),
            command_body_hash: command.command_body_hash().unwrap(),
            route_release_id: route.route_release_id,
            subject_id: "alice".to_owned(),
            grant_root: root(201),
            nonce: 9,
            consumed_object_ids: vec![],
            valid_from_height: 10,
            valid_through_height: 12,
        };
        let occurrence = EconomicCommandOccurrenceV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            chain_id: intent.chain_id.clone(),
            deployment_root: intent.deployment_root.clone(),
            height: 11,
            tx_index: 2,
            op_index: 3,
            command_kind: intent.command_kind.clone(),
            command_body_hash: intent.command_body_hash.clone(),
            route_release_id: intent.route_release_id.clone(),
            subject_id: intent.subject_id.clone(),
            grant_root: intent.grant_root.clone(),
            nonce: intent.nonce,
            profile_root: intent.profile_root.clone(),
            pre_state_root: root(402),
            consumed_object_ids: intent.consumed_object_ids.clone(),
        };
        let envelope = EconomicCommandAuthenticationEnvelopeV1 {
            command_body_bytes: canonical_economic_command_body_bytes_v1(COMMAND_KIND, &command)
                .unwrap(),
            signer_key_id: "alice-key-1".to_owned(),
            signer_public_key: "bls12-381-g2:alice-public-key".to_owned(),
            signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
            signature_bytes: b"test-signature-v1".to_vec(),
        };
        Self {
            profile,
            routes,
            policy_registry,
            authorization_registry,
            signature_verifier_registry,
            intent,
            occurrence,
            envelope,
        }
    }

    fn candidate(&self) -> EconomicCommandAuthenticationCandidateV1<'_> {
        EconomicCommandAuthenticationCandidateV1 {
            profile: &self.profile,
            routes: &self.routes,
            policy_registry: &self.policy_registry,
            authorization_registry: &self.authorization_registry,
            signature_verifier_registry: &self.signature_verifier_registry,
            intent: &self.intent,
            envelope: &self.envelope,
        }
    }

    fn authenticate_intent(
        &self,
        verifier: &RecordingVerifier,
    ) -> AbiResultV1<AuthenticatedEconomicCommandIntentV1> {
        authenticate_economic_command_intent_v1(&self.candidate(), verifier)
    }

    fn authenticate(
        &self,
        verifier: &RecordingVerifier,
    ) -> AbiResultV1<AuthenticatedEconomicCommandV1> {
        bind_authenticated_intent_to_occurrence_v1(
            &self.authenticate_intent(verifier)?,
            &self.occurrence,
        )
    }
}

#[test]
fn exact_body_intent_and_policy_authenticate_then_bind_occurrence() {
    let fixture = Fixture::new();
    let verifier = RecordingVerifier::accepting();
    let authenticated = fixture.authenticate(&verifier).unwrap();

    assert_eq!(authenticated.occurrence(), &fixture.occurrence);
    assert_eq!(
        authenticated.occurrence_id(),
        &fixture.occurrence.occurrence_id().unwrap()
    );
    assert_eq!(verifier.calls.borrow().len(), 1);
    assert!(!authenticated.binding_root().unwrap().is_zero());
}

#[test]
fn backend_claiming_an_unselected_verifier_release_rejects_before_use() {
    let fixture = Fixture::new();
    let verifier = RecordingVerifier {
        result: true,
        verifier_release_id: root(999),
        calls: RefCell::new(Vec::new()),
    };

    assert!(matches!(
        fixture.authenticate_intent(&verifier),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier release"
        ))
    ));
    assert!(verifier.calls.borrow().is_empty());
}

#[path = "economic_command_authentication/lifecycle_tests.rs"]
mod lifecycle_tests;
