use std::cell::RefCell;

use serde_json::json;
use zenodex_global_settlement_abi_v1::*;

type RecordedModuleReceiptVerifierCall = (Vec<u8>, RootV1, Vec<u8>);
type RecordedCompositionReceiptVerifierCall = (Vec<u8>, RootV1, Vec<u8>);
type RecordedRouteReceiptVerifierCall = (Vec<u8>, RootV1, Vec<u8>);
type RecordedEpochReceiptVerifierCall = (Vec<u8>, RootV1, Vec<u8>);
const COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1: &[u8] =
    b"lane-binding-command-signature-verifier-test-artifact-v1";

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
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

fn signature_verifier_manifest() -> EconomicCommandSignatureVerifierEvidenceManifestV1 {
    let evidence_artifacts = active_verifier_evidence()
        .into_iter()
        .enumerate()
        .map(
            |(index, status)| CommandSignatureVerifierEvidenceArtifactV1 {
                status,
                artifact_root: root(540 + u64::try_from(index).unwrap()),
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
        public_key_schema_root: root(527),
        signature_schema_root: root(528),
        message_schema_root: root(529),
        specification_root: root(530),
        source_root: root(531),
        toolchain_root: root(532),
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
        release_id: root(1),
        semantic_version: "1.0.0-lane-binding-test".to_owned(),
        signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
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

fn lane_release(lane_id: LaneIdV1, ordinal: u64) -> LaneModuleReleaseV1 {
    let is_asset_lane = lane_id == LaneIdV1::ASSET_TRANSFER;
    let command_variants = if is_asset_lane {
        vec![
            ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
            MANAGED_ASSET_BURN_COMMAND_KIND_V1.to_owned(),
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V1.to_owned(),
        ]
    } else {
        vec![]
    };
    let terminal_command_variants = if is_asset_lane {
        vec![MANAGED_ASSET_BURN_COMMAND_KIND_V1.to_owned()]
    } else {
        vec![]
    };
    let offset = ordinal * 16;
    let state_schema_root = root(100 + offset);
    let guest_image_id = root(101 + offset);
    let specification_root = root(102 + offset);
    let source_root = root(103 + offset);
    let toolchain_root = root(104 + offset);
    let terminal_coverage_root = root(105 + offset);
    let migration_compatibility_root = root(106 + offset);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": lane_id,
        "state_schema_root": state_schema_root,
        "command_variants": command_variants,
        "terminal_command_variants": terminal_command_variants,
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "terminal_coverage_root": terminal_coverage_root,
        "migration_compatibility_root": migration_compatibility_root,
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    });
    let release = LaneModuleReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        release_id: hash_global_v1("global-lane-module-release-content-v1", &content).unwrap(),
        semantic_version: "1.0.0-test".to_owned(),
        state_schema_root,
        command_variants,
        terminal_command_variants,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        terminal_coverage_root,
        migration_compatibility_root,
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: if is_asset_lane {
            ReleaseStatusV1::ACTIVE_NEW
        } else {
            ReleaseStatusV1::SHADOW
        },
        accepts_new_objects: is_asset_lane,
        evidence_statuses: if is_asset_lane {
            active_evidence()
        } else {
            vec![EvidenceStatusV1::DISABLED_PROVED_NO_WRITER]
        },
    };
    release.validate().expect("test release must validate");
    release
}

fn coordinator_release(lane_id: LaneIdV1, ordinal: u64) -> LaneCoordinatorReleaseV1 {
    let is_asset_lane = lane_id == LaneIdV1::ASSET_TRANSFER;
    let offset = ordinal * 16;
    let coordinator_schema_root = root(300 + offset);
    let guest_image_id = root(301 + offset);
    let specification_root = root(302 + offset);
    let source_root = root(303 + offset);
    let toolchain_root = root(304 + offset);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": lane_id,
        "coordinator_schema_root": coordinator_schema_root,
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    });
    let release = LaneCoordinatorReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        coordinator_release_id: hash_global_v1(
            "global-lane-coordinator-release-content-v1",
            &content,
        )
        .unwrap(),
        semantic_version: "1.0.0-test".to_owned(),
        coordinator_schema_root,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: if is_asset_lane {
            ReleaseStatusV1::ACTIVE_NEW
        } else {
            ReleaseStatusV1::SHADOW
        },
        accepts_new_objects: is_asset_lane,
        evidence_statuses: if is_asset_lane {
            active_evidence()
        } else {
            vec![EvidenceStatusV1::DISABLED_PROVED_NO_WRITER]
        },
    };
    release
        .validate()
        .expect("test coordinator release must validate");
    release
}

fn route(command_kind: &str, index: u64, release_id: &RootV1) -> RouteReleaseV1 {
    route_with_issue_burn_policy_root(command_kind, index, release_id, root(511))
}

fn route_with_issue_burn_policy_root(
    command_kind: &str,
    index: u64,
    release_id: &RootV1,
    issue_burn_policy_root: RootV1,
) -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::ASSET_TRANSFER];
    let module_release_ids = vec![release_id.clone()];
    let dependency_roles = vec!["VALUE_OWNER".to_owned()];
    let port_schema_roots = vec![root(500 + index)];
    let guest_image_id = root(520 + index);
    let specification_root = root(530 + index);
    let source_root = root(540 + index);
    let toolchain_root = root(550 + index);
    let oracle_policy_root = root(510);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "command_kind": command_kind,
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
        semantic_version: "1.0.0-test".to_owned(),
        command_kind: command_kind.to_owned(),
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
    route.validate().expect("test route must validate");
    route
}

fn authorization_registry(routes: &RouteRegistryV1) -> EconomicCommandAuthorizationRegistryV1 {
    let mut authorizations = routes
        .routes
        .iter()
        .map(|route| {
            let (subject_id, grant_root) = match route.command_kind.as_str() {
                ASSET_TRANSFER_COMMAND_KIND_V1 => ("alice", root(7)),
                MANAGED_ASSET_BURN_COMMAND_KIND_V1 => ("alice", root(6)),
                MANAGED_ASSET_ISSUE_COMMAND_KIND_V1 => ("issuer", root(5)),
                PERPS_MARGIN_CLOSE_COMMAND_KIND_V1
                | PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1
                | PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1 => ("alice", root(7)),
                _ => panic!("unsupported authentication test route"),
            };
            EconomicCommandAuthorizationV1 {
                schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
                command_kind: route.command_kind.clone(),
                subject_id: subject_id.to_owned(),
                grant_root,
                route_release_id: route.route_release_id.clone(),
                signer_key_id: format!("{subject_id}-key-1"),
                signer_public_key: format!("bls12-381-g2:{subject_id}-public-key"),
                signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
                valid_from_height: 0,
                valid_through_height: u64::MAX,
                min_nonce: 0,
                max_nonce: u64::MAX,
                enabled: true,
            }
        })
        .collect::<Vec<_>>();
    authorizations.sort_by(|left, right| {
        (
            &left.command_kind,
            &left.subject_id,
            &left.grant_root,
            &left.route_release_id,
            &left.signer_key_id,
        )
            .cmp(&(
                &right.command_kind,
                &right.subject_id,
                &right.grant_root,
                &right.route_release_id,
                &right.signer_key_id,
            ))
    });
    EconomicCommandAuthorizationRegistryV1 {
        schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
        authorizations,
    }
}

fn authentication_policy_registry(
    authorizations: &EconomicCommandAuthorizationRegistryV1,
    signature_verifiers: &EconomicCommandSignatureVerifierRegistryV1,
) -> EconomicPolicyRegistryV1 {
    let mut command_kinds = authorizations
        .authorizations
        .iter()
        .map(|authorization| authorization.command_kind.clone())
        .collect::<Vec<_>>();
    command_kinds.sort();
    let mut bindings = command_kinds
        .into_iter()
        .flat_map(|command_kind| {
            [
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
            ]
        })
        .collect::<Vec<_>>();
    bindings.sort_by(|left, right| {
        (&left.policy_kind, &left.command_kind).cmp(&(&right.policy_kind, &right.command_kind))
    });
    EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings,
    }
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

/// Authenticate under the default transfer-governed policy registry that
/// `profile()` commits for its routes.
fn authenticate_occurrence(
    profile: &EconomicProfileSnapshotV1,
    routes: &RouteRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    command_body_bytes: Vec<u8>,
) -> AuthenticatedEconomicCommandV1 {
    let policy_registry = transfer_registries(routes).policy_registry;
    authenticate_occurrence_with_policy_registry(
        profile,
        routes,
        occurrence,
        command_body_bytes,
        &policy_registry,
    )
}

fn authenticate_occurrence_with_policy_registry(
    profile: &EconomicProfileSnapshotV1,
    routes: &RouteRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    command_body_bytes: Vec<u8>,
    policy_registry: &EconomicPolicyRegistryV1,
) -> AuthenticatedEconomicCommandV1 {
    let authorization_registry = authorization_registry(routes);
    let signature_verifier_registry = signature_verifier_registry();
    let authorization = authorization_registry
        .authorization_for(occurrence, &format!("{}-key-1", occurrence.subject_id))
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
        signature_bytes: b"test-command-signature-v1".to_vec(),
    };
    let authenticated_intent = authenticate_economic_command_intent_v1(
        &EconomicCommandAuthenticationCandidateV1 {
            profile,
            routes,
            policy_registry,
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

const TRANSFER_POLICY_KINDS: &[&str] = &[
    ASSET_TRANSFER_ASSET_POLICY_KIND_V1,
    ASSET_TRANSFER_FEE_POLICY_KIND_V1,
];

fn asset_transfer_policy() -> AssetTransferPolicyV1 {
    AssetTransferPolicyV1 {
        asset: "USD".to_owned(),
        fee_owner: "treasury".to_owned(),
        transfer_fee_atoms: 2,
        enabled: true,
    }
}

fn asset_transfer_policy_registry(module_release_id: &RootV1) -> AssetTransferPolicyRegistryV1 {
    AssetTransferPolicyRegistryV1 {
        schema: ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1.to_owned(),
        module_release_id: module_release_id.clone(),
        policies: vec![asset_transfer_policy()],
    }
}

/// Authentication bindings plus the requested governed transfer policy
/// bindings, each carrying its own domain-separated registry root.
fn transfer_policy_registry(
    authorizations: &EconomicCommandAuthorizationRegistryV1,
    signature_verifiers: &EconomicCommandSignatureVerifierRegistryV1,
    asset_policy_registry: &AssetTransferPolicyRegistryV1,
    kinds: &[&str],
) -> EconomicPolicyRegistryV1 {
    let mut registry = authentication_policy_registry(authorizations, signature_verifiers);
    for kind in kinds {
        let policy_root = if *kind == ASSET_TRANSFER_ASSET_POLICY_KIND_V1 {
            asset_policy_registry.asset_policy_root().unwrap()
        } else {
            asset_policy_registry.fee_policy_root().unwrap()
        };
        registry.bindings.push(EconomicPolicyBindingV1 {
            policy_kind: (*kind).to_owned(),
            command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
            policy_root,
        });
    }
    registry.bindings.sort_by(|left, right| {
        (&left.policy_kind, &left.command_kind).cmp(&(&right.policy_kind, &right.command_kind))
    });
    registry.validate().unwrap();
    registry
}

/// The governed transfer registries an ACTIVE transfer profile commits.
struct TransferRegistries {
    policy_registry: EconomicPolicyRegistryV1,
    asset_policy_registry: AssetTransferPolicyRegistryV1,
}

fn transfer_registries_with(
    routes: &RouteRegistryV1,
    policies: Vec<AssetTransferPolicyV1>,
    kinds: &[&str],
) -> TransferRegistries {
    let route = routes
        .route_for_command(ASSET_TRANSFER_COMMAND_KIND_V1, None)
        .expect("transfer route must exist");
    let asset_policy_registry = AssetTransferPolicyRegistryV1 {
        schema: ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1.to_owned(),
        module_release_id: route.module_release_ids[0].clone(),
        policies,
    };
    let policy_registry = transfer_policy_registry(
        &authorization_registry(routes),
        &signature_verifier_registry(),
        &asset_policy_registry,
        kinds,
    );
    TransferRegistries {
        policy_registry,
        asset_policy_registry,
    }
}

/// The exact registries `profile()` commits: the USD fixture row under both
/// transfer policy kinds.
fn transfer_registries(routes: &RouteRegistryV1) -> TransferRegistries {
    transfer_registries_with(routes, vec![asset_transfer_policy()], TRANSFER_POLICY_KINDS)
}

#[derive(Clone, Copy)]
struct TransferGovernanceRefs<'a> {
    profile: &'a EconomicProfileSnapshotV1,
    lanes: &'a LaneRegistryV1,
    coordinators: &'a LaneCoordinatorRegistryV1,
    routes: &'a RouteRegistryV1,
    registries: &'a TransferRegistries,
}

fn transfer_binding_candidate<'a>(
    refs: &TransferGovernanceRefs<'a>,
    occurrence: &'a EconomicCommandOccurrenceV1,
    module_input: &'a AssetTransferLaneModuleInputV1,
    accepted: &'a AssetTransferLaneModuleAcceptedV1,
) -> AssetTransferReleaseRouteBindingCandidateV1<'a> {
    AssetTransferReleaseRouteBindingCandidateV1 {
        profile: refs.profile,
        policy_registry: &refs.registries.policy_registry,
        asset_policy_registry: &refs.registries.asset_policy_registry,
        lanes: refs.lanes,
        coordinators: refs.coordinators,
        routes: refs.routes,
        occurrence,
        module_input,
        accepted,
    }
}

fn bind_transfer(
    refs: &TransferGovernanceRefs<'_>,
    occurrence: &EconomicCommandOccurrenceV1,
    module_input: &AssetTransferLaneModuleInputV1,
    accepted: &AssetTransferLaneModuleAcceptedV1,
) -> AbiResultV1<ReleaseRouteBoundLaneTransitionV1> {
    bind_asset_transfer_lane_output_to_release_route_v1(transfer_binding_candidate(
        refs,
        occurrence,
        module_input,
        accepted,
    ))
}

fn transfer_receipt_candidate<'a>(
    refs: &TransferGovernanceRefs<'a>,
    authenticated_command: &'a AuthenticatedEconomicCommandV1,
    module_input: &'a AssetTransferLaneModuleInputV1,
    accepted: &'a AssetTransferLaneModuleAcceptedV1,
    release_route_binding: &'a ReleaseRouteBoundLaneTransitionV1,
    receipt_bytes: &'a [u8],
) -> AssetTransferLaneModuleReceiptCandidateV1<'a> {
    AssetTransferLaneModuleReceiptCandidateV1 {
        profile: refs.profile,
        policy_registry: &refs.registries.policy_registry,
        asset_policy_registry: &refs.registries.asset_policy_registry,
        lanes: refs.lanes,
        coordinators: refs.coordinators,
        routes: refs.routes,
        authenticated_command,
        module_input,
        accepted,
        release_route_binding,
        receipt: LaneModuleReceiptEnvelopeV1 {
            receipt_kind: ReceiptKindV1::SUCCINCT,
            receipt_bytes,
        },
    }
}

/// One ACTIVE profile whose economic policy registry governs transfers.
struct TransferGovernance {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    registries: TransferRegistries,
}

impl TransferGovernance {
    fn refs(&self) -> TransferGovernanceRefs<'_> {
        TransferGovernanceRefs {
            profile: &self.profile,
            lanes: &self.lanes,
            coordinators: &self.coordinators,
            routes: &self.routes,
            registries: &self.registries,
        }
    }
}

fn asset_registries() -> (LaneRegistryV1, LaneCoordinatorRegistryV1, RouteRegistryV1) {
    let lanes = LaneRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane)| lane_release(*lane, index as u64 + 1))
            .collect(),
    };
    let asset_release_id = lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .expect("asset release must exist")
        .release_id
        .clone();
    let routes = RouteRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        routes: [
            ASSET_TRANSFER_COMMAND_KIND_V1,
            MANAGED_ASSET_BURN_COMMAND_KIND_V1,
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        ]
        .iter()
        .enumerate()
        .map(|(index, command)| route(command, index as u64, &asset_release_id))
        .collect(),
    };
    let coordinators = LaneCoordinatorRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane)| coordinator_release(*lane, index as u64 + 1))
            .collect(),
    };
    (lanes, coordinators, routes)
}

fn transfer_governance_with(
    policies: Vec<AssetTransferPolicyV1>,
    kinds: &[&str],
) -> TransferGovernance {
    let (lanes, coordinators, routes) = asset_registries();
    let registries = transfer_registries_with(&routes, policies, kinds);
    let profile = asset_profile_snapshot(
        &lanes,
        &coordinators,
        &routes,
        registries.policy_registry.registry_root().unwrap(),
    );
    TransferGovernance {
        profile,
        lanes,
        coordinators,
        routes,
        registries,
    }
}

/// The default ACTIVE profile governs the USD fixture transfer row under both
/// transfer policy kinds; `transfer_registries(&routes)` recomputes exactly
/// the registries it commits.
fn profile() -> (
    EconomicProfileSnapshotV1,
    LaneRegistryV1,
    LaneCoordinatorRegistryV1,
    RouteRegistryV1,
) {
    let governance = transfer_governance_with(vec![asset_transfer_policy()], TRANSFER_POLICY_KINDS);
    (
        governance.profile,
        governance.lanes,
        governance.coordinators,
        governance.routes,
    )
}

fn asset_profile_snapshot(
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
    policy_registry_root: RootV1,
) -> EconomicProfileSnapshotV1 {
    let lane_registry_root = lanes.registry_root().unwrap();
    let lane_coordinator_registry_root = coordinators.registry_root().unwrap();
    let route_registry_root = routes.registry_root().unwrap();
    let proof_shape_root = root(520);
    let root_image_id = root(521);
    let verifier_registry_root = root(522);
    let migration_registry_root = root(523);
    let terminal_registry_root = root(525);
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
    let profile = EconomicProfileSnapshotV1 {
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
        status: ProfileStatusV1::ACTIVE,
    };
    profile
        .validate_registries(lanes, coordinators, routes)
        .expect("test profile must bind registries");
    profile
}

fn managed_asset_policy() -> ManagedAssetLifecyclePolicyV1 {
    ManagedAssetLifecyclePolicyV1 {
        asset: "USD".to_owned(),
        asset_class: ManagedAssetClassV1::REGISTERED_ORDINARY_TOKEN,
        issue_authority_subject: Some("issuer".to_owned()),
        issue_policy_root: Some(root(5)),
        burn_policy_root: Some(root(6)),
        enabled: true,
    }
}

fn managed_asset_policy_registry(module_release_id: &RootV1) -> ManagedAssetPolicyRegistryV1 {
    ManagedAssetPolicyRegistryV1 {
        schema: MANAGED_ASSET_POLICY_REGISTRY_SCHEMA_V1.to_owned(),
        module_release_id: module_release_id.clone(),
        policies: vec![managed_asset_policy()],
    }
}

fn managed_policy_registry(
    authorizations: &EconomicCommandAuthorizationRegistryV1,
    signature_verifiers: &EconomicCommandSignatureVerifierRegistryV1,
    asset_policy_registry: &ManagedAssetPolicyRegistryV1,
) -> EconomicPolicyRegistryV1 {
    let mut registry = authentication_policy_registry(authorizations, signature_verifiers);
    for command_kind in [
        MANAGED_ASSET_BURN_COMMAND_KIND_V1,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    ] {
        registry.bindings.push(EconomicPolicyBindingV1 {
            policy_kind: MANAGED_ASSET_POLICY_KIND_V1.to_owned(),
            command_kind: command_kind.to_owned(),
            policy_root: asset_policy_registry.registry_root().unwrap(),
        });
    }
    registry.bindings.sort_by(|left, right| {
        (&left.policy_kind, &left.command_kind).cmp(&(&right.policy_kind, &right.command_kind))
    });
    registry.validate().unwrap();
    registry
}

/// One ACTIVE profile whose economic policy registry governs managed assets.
struct ManagedGovernance {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    policy_registry: EconomicPolicyRegistryV1,
    asset_policy_registry: ManagedAssetPolicyRegistryV1,
}

fn managed_governance() -> ManagedGovernance {
    managed_governance_with(None)
}

/// Managed issue and burn routes own the typed registry root as their
/// `issue_burn_policy_root` unless a test overrides it.
fn managed_governance_with(route_issue_burn_policy_root: Option<RootV1>) -> ManagedGovernance {
    let (_, lanes, coordinators, _) = profile();
    let asset_release_id = lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .unwrap()
        .release_id
        .clone();
    let asset_policy_registry = managed_asset_policy_registry(&asset_release_id);
    let managed_policy_root = route_issue_burn_policy_root
        .unwrap_or_else(|| asset_policy_registry.registry_root().unwrap());
    let routes = RouteRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        routes: vec![
            route(ASSET_TRANSFER_COMMAND_KIND_V1, 0, &asset_release_id),
            route_with_issue_burn_policy_root(
                MANAGED_ASSET_BURN_COMMAND_KIND_V1,
                1,
                &asset_release_id,
                managed_policy_root.clone(),
            ),
            route_with_issue_burn_policy_root(
                MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
                2,
                &asset_release_id,
                managed_policy_root,
            ),
        ],
    };
    let policy_registry = managed_policy_registry(
        &authorization_registry(&routes),
        &signature_verifier_registry(),
        &asset_policy_registry,
    );
    let profile = asset_profile_snapshot(
        &lanes,
        &coordinators,
        &routes,
        policy_registry.registry_root().unwrap(),
    );
    ManagedGovernance {
        profile,
        lanes,
        coordinators,
        routes,
        policy_registry,
        asset_policy_registry,
    }
}

fn managed_binding_candidate<'a>(
    governance: &'a ManagedGovernance,
    occurrence: &'a EconomicCommandOccurrenceV1,
    module_input: &'a ManagedAssetLifecycleLaneModuleInputV1,
    accepted: &'a ManagedAssetLifecycleLaneModuleAcceptedV1,
) -> ManagedAssetLifecycleReleaseRouteBindingCandidateV1<'a> {
    ManagedAssetLifecycleReleaseRouteBindingCandidateV1 {
        profile: &governance.profile,
        policy_registry: &governance.policy_registry,
        asset_policy_registry: &governance.asset_policy_registry,
        lanes: &governance.lanes,
        coordinators: &governance.coordinators,
        routes: &governance.routes,
        occurrence,
        module_input,
        accepted,
    }
}

fn perps_lane_release(lane_id: LaneIdV1, ordinal: u64) -> LaneModuleReleaseV1 {
    let mut release = lane_release(lane_id, ordinal);
    let selected = lane_id == LaneIdV1::PERPS_MARKET;
    release.semantic_version = "1.0.0-perps-binding-test".to_owned();
    release.status = if selected {
        ReleaseStatusV1::ACTIVE_NEW
    } else {
        ReleaseStatusV1::SHADOW
    };
    release.accepts_new_objects = selected;
    release.evidence_statuses = if selected {
        active_evidence()
    } else {
        vec![EvidenceStatusV1::DISABLED_PROVED_NO_WRITER]
    };
    release.command_variants = if selected {
        vec![
            PERPS_MARGIN_CLOSE_COMMAND_KIND_V1.to_owned(),
            PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1.to_owned(),
            PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1.to_owned(),
        ]
    } else {
        vec![]
    };
    release.terminal_command_variants = if selected {
        vec![PERPS_MARGIN_CLOSE_COMMAND_KIND_V1.to_owned()]
    } else {
        vec![]
    };
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": release.lane_id,
        "state_schema_root": release.state_schema_root,
        "command_variants": release.command_variants,
        "terminal_command_variants": release.terminal_command_variants,
        "guest_image_id": release.guest_image_id,
        "specification_root": release.specification_root,
        "source_root": release.source_root,
        "toolchain_root": release.toolchain_root,
        "terminal_coverage_root": release.terminal_coverage_root,
        "migration_compatibility_root": release.migration_compatibility_root,
        "max_cycles": release.max_cycles,
        "max_journal_bytes": release.max_journal_bytes,
    });
    release.release_id = hash_global_v1("global-lane-module-release-content-v1", &content).unwrap();
    release.validate().unwrap();
    release
}

fn perps_coordinator_release(lane_id: LaneIdV1, ordinal: u64) -> LaneCoordinatorReleaseV1 {
    let mut release = coordinator_release(lane_id, ordinal);
    let selected = lane_id == LaneIdV1::PERPS_MARKET;
    release.semantic_version = "1.0.0-perps-binding-test".to_owned();
    release.status = if selected {
        ReleaseStatusV1::ACTIVE_NEW
    } else {
        ReleaseStatusV1::SHADOW
    };
    release.accepts_new_objects = selected;
    release.evidence_statuses = if selected {
        active_evidence()
    } else {
        vec![EvidenceStatusV1::DISABLED_PROVED_NO_WRITER]
    };
    release.validate().unwrap();
    release
}

fn perps_route(
    command_kind: &str,
    index: u64,
    release_id: &RootV1,
    oracle_policy_root: &RootV1,
) -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::PERPS_MARKET];
    let module_release_ids = vec![release_id.clone()];
    let dependency_roles = vec!["PERPS_MARGIN".to_owned()];
    let port_schema_roots = vec![root(500 + index)];
    let guest_image_id = root(520 + index);
    let specification_root = root(530 + index);
    let source_root = root(540 + index);
    let toolchain_root = root(550 + index);
    let issue_burn_policy_root = root(511);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "command_kind": command_kind,
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
        semantic_version: "1.0.0-perps-binding-test".to_owned(),
        command_kind: command_kind.to_owned(),
        ordered_lanes,
        module_release_ids,
        dependency_roles,
        port_schema_roots,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        oracle_policy_root: oracle_policy_root.clone(),
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

fn perps_market_policy() -> PerpsMarketPolicyV1 {
    PerpsMarketPolicyV1 {
        schema: PERPS_MARKET_POLICY_SCHEMA_V1.to_owned(),
        market_id: "BTC-ZUSD-PERP".to_owned(),
        base_asset: "BTC".to_owned(),
        quote_asset: "zUSD".to_owned(),
        oracle_id: "zenodex.oracle.perps-index-price.v1".to_owned(),
    }
}

fn perps_policy_registry(
    authorizations: &EconomicCommandAuthorizationRegistryV1,
    signature_verifiers: &EconomicCommandSignatureVerifierRegistryV1,
    market_policy: &PerpsMarketPolicyV1,
) -> EconomicPolicyRegistryV1 {
    let mut registry = authentication_policy_registry(authorizations, signature_verifiers);
    for command_kind in [
        PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
        PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
    ] {
        registry.bindings.push(EconomicPolicyBindingV1 {
            policy_kind: PERPS_MARKET_POLICY_KIND_V1.to_owned(),
            command_kind: command_kind.to_owned(),
            policy_root: market_policy.policy_root().unwrap(),
        });
    }
    registry.bindings.sort_by(|left, right| {
        (&left.policy_kind, &left.command_kind).cmp(&(&right.policy_kind, &right.command_kind))
    });
    registry.validate().unwrap();
    registry
}

fn perps_profile() -> (
    EconomicProfileSnapshotV1,
    LaneRegistryV1,
    LaneCoordinatorRegistryV1,
    RouteRegistryV1,
    GlobalOracleOccurrencePolicyV1,
    EconomicPolicyRegistryV1,
    PerpsMarketPolicyV1,
) {
    let lanes = LaneRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane)| perps_lane_release(*lane, index as u64 + 1))
            .collect(),
    };
    let coordinators = LaneCoordinatorRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane)| perps_coordinator_release(*lane, index as u64 + 1))
            .collect(),
    };
    let release_id = lanes
        .release_for(LaneIdV1::PERPS_MARKET)
        .unwrap()
        .release_id
        .clone();
    let policy = GlobalOracleOccurrencePolicyV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        oracle_id: "zenodex.oracle.perps-index-price.v1".to_owned(),
        max_observation_age_blocks: 1,
    };
    let policy_root = policy.policy_root().unwrap();
    let routes = RouteRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        routes: [
            PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
            PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
            PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
        ]
        .iter()
        .enumerate()
        .map(|(index, command)| perps_route(command, index as u64, &release_id, &policy_root))
        .collect(),
    };
    let lane_registry_root = lanes.registry_root().unwrap();
    let lane_coordinator_registry_root = coordinators.registry_root().unwrap();
    let route_registry_root = routes.registry_root().unwrap();
    let authorizations = authorization_registry(&routes);
    let signature_verifiers = signature_verifier_registry();
    let market_policy = perps_market_policy();
    let policy_registry =
        perps_policy_registry(&authorizations, &signature_verifiers, &market_policy);
    let policy_registry_root = policy_registry.registry_root().unwrap();
    let proof_shape_root = root(601);
    let root_image_id = root(602);
    let verifier_registry_root = root(603);
    let migration_registry_root = root(604);
    let terminal_registry_root = root(605);
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
    let profile = EconomicProfileSnapshotV1 {
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
        status: ProfileStatusV1::ACTIVE,
    };
    profile
        .validate_registries(&lanes, &coordinators, &routes)
        .unwrap();
    (
        profile,
        lanes,
        coordinators,
        routes,
        policy,
        policy_registry,
        market_policy,
    )
}

fn occurrence(
    profile: &EconomicProfileSnapshotV1,
    routes: &RouteRegistryV1,
    command_kind: &str,
    subject_id: &str,
    grant_root: RootV1,
) -> EconomicCommandOccurrenceV1 {
    let route = routes
        .route_for_command(command_kind, None)
        .expect("test route must exist");
    let command_body_hash = if command_kind == ASSET_TRANSFER_COMMAND_KIND_V1 {
        AssetTransferCommandV1 {
            command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
            asset: "USD".to_owned(),
            sender: "alice".to_owned(),
            recipient: "bob".to_owned(),
            amount_atoms: 30,
            max_fee_atoms: 2,
        }
        .command_body_hash()
        .expect("test transfer command must hash")
    } else if matches!(
        command_kind,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1 | MANAGED_ASSET_BURN_COMMAND_KIND_V1
    ) {
        ManagedAssetLifecycleCommandV1 {
            command_kind: command_kind.to_owned(),
            asset: "USD".to_owned(),
            account_owner: "alice".to_owned(),
            amount_atoms: if command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1 {
                7
            } else {
                4
            },
        }
        .command_body_hash()
        .expect("test managed command must hash")
    } else {
        panic!("unsupported test command kind")
    };
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-release-route-test".to_owned(),
        deployment_root: root(1),
        height: 11,
        tx_index: 2,
        op_index: 3,
        command_kind: command_kind.to_owned(),
        command_body_hash,
        route_release_id: route.route_release_id.clone(),
        subject_id: subject_id.to_owned(),
        grant_root,
        nonce: 9,
        profile_root: profile.profile_id.clone(),
        pre_state_root: root(2),
        consumed_object_ids: vec![],
    }
}

fn asset_input(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    module_release_id: Option<RootV1>,
) -> AssetTransferLaneModuleInputV1 {
    let governed_release_id = lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .unwrap()
        .release_id
        .clone();
    let release_id = module_release_id.unwrap_or_else(|| governed_release_id.clone());
    // The opaque roots are the governed registry's typed roots, so an input
    // executed under a foreign release still advertises the governed roots.
    let registry = asset_transfer_policy_registry(&governed_release_id);
    AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: occurrence.chain_id.clone(),
            deployment_root: occurrence.deployment_root.clone(),
            profile_root: occurrence.profile_root.clone(),
            writer_epoch: profile.authority_epoch,
            module_release_id: release_id.clone(),
            command_occurrence_id: occurrence.occurrence_id().unwrap(),
            subject_id: occurrence.subject_id.clone(),
            grant_root: occurrence.grant_root.clone(),
        },
        pre_state: AssetTransferStateV1 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: release_id,
            policies: registry.policies.clone(),
            balances: vec![
                EconomicAmountV1 {
                    owner: "alice".to_owned(),
                    asset: "USD".to_owned(),
                    custody_domain: "accounts".to_owned(),
                    amount_atoms: 100,
                },
                EconomicAmountV1 {
                    owner: "bob".to_owned(),
                    asset: "USD".to_owned(),
                    custody_domain: "accounts".to_owned(),
                    amount_atoms: 10,
                },
                EconomicAmountV1 {
                    owner: "treasury".to_owned(),
                    asset: "USD".to_owned(),
                    custody_domain: "accounts".to_owned(),
                    amount_atoms: 5,
                },
            ],
            supplies: vec![AssetSupplyV1 {
                asset: "USD".to_owned(),
                amount_atoms: 115,
            }],
        },
        command: AssetTransferCommandV1 {
            command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
            asset: "USD".to_owned(),
            sender: "alice".to_owned(),
            recipient: "bob".to_owned(),
            amount_atoms: 30,
            max_fee_atoms: 2,
        },
        asset_policy_registry_root: registry.asset_policy_root().unwrap(),
        fee_policy_registry_root: registry.fee_policy_root().unwrap(),
        custody: vec![],
    }
}

fn managed_input(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    command_kind: &str,
) -> ManagedAssetLifecycleLaneModuleInputV1 {
    let release_id = lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .unwrap()
        .release_id
        .clone();
    let is_issue = command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1;
    let asset_policy_registry_root = managed_asset_policy_registry(&release_id)
        .registry_root()
        .unwrap();
    ManagedAssetLifecycleLaneModuleInputV1 {
        schema: MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: ManagedAssetLifecycleContextV1 {
            chain_id: occurrence.chain_id.clone(),
            deployment_root: occurrence.deployment_root.clone(),
            profile_root: occurrence.profile_root.clone(),
            writer_epoch: profile.authority_epoch,
            module_release_id: release_id.clone(),
            command_occurrence_id: occurrence.occurrence_id().unwrap(),
            subject_id: occurrence.subject_id.clone(),
            grant_root: occurrence.grant_root.clone(),
        },
        pre_state: ManagedAssetLifecycleStateV1 {
            schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: release_id,
            policies: vec![managed_asset_policy()],
            balances: vec![EconomicAmountV1 {
                owner: "alice".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: "accounts".to_owned(),
                amount_atoms: 10,
            }],
            supplies: vec![AssetSupplyV1 {
                asset: "USD".to_owned(),
                amount_atoms: 10,
            }],
        },
        command: ManagedAssetLifecycleCommandV1 {
            command_kind: command_kind.to_owned(),
            asset: "USD".to_owned(),
            account_owner: "alice".to_owned(),
            amount_atoms: if is_issue { 7 } else { 4 },
        },
        asset_policy_registry_root,
        fee_policy_registry_root: root(12),
        custody: vec![],
    }
}

fn rebind_structural_module_receipt_root(
    domain: &str,
    statement_root: &RootV1,
    module_journal: &LaneModuleTransitionJournalV1,
    private_port: &AssetLanePrivatePortV1,
    effects: &GlobalEconomicEffectPlanV1,
) -> RootV1 {
    hash_global_v1(
        domain,
        &json!({
            "statement_root": statement_root,
            "pre_state_root": module_journal.pre_lane_root,
            "post_state_root": module_journal.post_lane_root,
            "effect_plan_root": effects.effect_plan_root().unwrap(),
            "private_port_root": private_port.port_root().unwrap(),
            "terminal_obligations_root": private_port.terminal_obligations_root,
        }),
    )
    .unwrap()
}

fn structurally_rebind_transfer_statement(
    accepted: &mut AssetTransferLaneModuleAcceptedV1,
    statement_root: RootV1,
) {
    accepted.statement_root = statement_root;
    accepted.module_journal.receipt_root = rebind_structural_module_receipt_root(
        "asset-transfer-lane-module-receipt-v1",
        &accepted.statement_root,
        &accepted.module_journal,
        &accepted.private_port,
        &accepted.effects,
    );
    accepted
        .validate()
        .expect("forged transfer output remains structurally self-consistent");
}

fn structurally_rebind_managed_statement(
    accepted: &mut ManagedAssetLifecycleLaneModuleAcceptedV1,
    statement_root: RootV1,
) {
    accepted.statement_root = statement_root;
    accepted.module_journal.receipt_root = rebind_structural_module_receipt_root(
        "managed-asset-lifecycle-lane-module-receipt-v1",
        &accepted.statement_root,
        &accepted.module_journal,
        &accepted.private_port,
        &accepted.effects,
    );
    accepted
        .validate()
        .expect("forged managed output remains structurally self-consistent");
}

#[test]
fn asset_issue_and_burn_outputs_bind_to_exact_active_profile_routes() {
    let (profile, lanes, coordinators, routes) = profile();
    let transfer_occurrence = occurrence(
        &profile,
        &routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let transfer_input = asset_input(&profile, &lanes, &transfer_occurrence, None);
    let AssetTransferLaneModuleResultV1::Accepted(transfer) =
        transition_asset_transfer_lane_module_v1(&transfer_input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let registries = transfer_registries(&routes);
    let refs = TransferGovernanceRefs {
        profile: &profile,
        lanes: &lanes,
        coordinators: &coordinators,
        routes: &routes,
        registries: &registries,
    };
    let bound = bind_transfer(&refs, &transfer_occurrence, &transfer_input, &transfer)
        .expect("valid transfer output must bind");
    assert_eq!(bound.profile_id(), &profile.profile_id);
    assert_eq!(bound.lane_id(), LaneIdV1::ASSET_TRANSFER);
    assert_eq!(bound.route_lane_index(), 0);
    assert_eq!(
        bound.statement_root(),
        &transfer_input.statement_root().unwrap()
    );
    // Cross-language vectors: the Python route-binding and membership suites
    // assert the same governed transfer binding root, registry roots, profile
    // id, and route release id for the same fixture.
    assert_eq!(
        bound.binding_root().unwrap().as_str(),
        "0x3c81585faeffa442eb7d83cff4ccd3c158358a67766f63c8c8f00a579e736fba"
    );
    assert_eq!(
        registries
            .asset_policy_registry
            .asset_policy_root()
            .unwrap()
            .as_str(),
        "0x410c0a5f51ec3b51ee53bf95eae3c11df09004bbe60be9b04a45f106c823fda7"
    );
    assert_eq!(
        registries
            .asset_policy_registry
            .fee_policy_root()
            .unwrap()
            .as_str(),
        "0xeb173aa23a9cbcb7db7e08d255068789dc081a056cac27f51cafa389b966dbd1"
    );
    assert_eq!(
        profile.profile_id.as_str(),
        "0x96b4fff45570fc2da3f522030cc06bb140390a99cb1fba7986a34cb11a9f298c"
    );
    assert_eq!(
        bound.route_release_id().as_str(),
        "0x2bba8b7eaf9df0e6d28b0f27933995a1872be2c41fed5a7b5ea0ee3f8ba01b1d"
    );
    assert_eq!(
        transfer_input.asset_policy_registry_root,
        registries
            .asset_policy_registry
            .asset_policy_root()
            .unwrap()
    );
    assert_eq!(
        transfer_input.fee_policy_registry_root,
        registries.asset_policy_registry.fee_policy_root().unwrap()
    );

    let governance = managed_governance();
    // Cross-language vector: the Python route-binding suite asserts the same
    // release-bound registry root for the same fixture.
    assert_eq!(
        &governance.asset_policy_registry.module_release_id,
        &lanes
            .release_for(LaneIdV1::ASSET_TRANSFER)
            .unwrap()
            .release_id
    );
    assert_eq!(
        governance
            .asset_policy_registry
            .registry_root()
            .unwrap()
            .as_str(),
        "0xba06d1d7425a1dff6633b077ad7da33eb7ff681a8623607e9cbda353d87c2879"
    );
    // Managed issue/burn routes own that registry root as issue_burn_policy_root.
    for (command_kind, expected_route_release_id) in [
        (
            MANAGED_ASSET_BURN_COMMAND_KIND_V1,
            "0xf9a0bf0ff296f198c5da915b0e612dcec24eee16b5fb7c65168b63c8b1db4fbc",
        ),
        (
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
            "0x13a98232cd5861c444fc022c3419967dc488f99ad636202599621f586344962f",
        ),
    ] {
        let route = governance
            .routes
            .route_for_command(command_kind, None)
            .unwrap();
        assert_eq!(
            route.issue_burn_policy_root,
            governance.asset_policy_registry.registry_root().unwrap()
        );
        assert_eq!(route.route_release_id.as_str(), expected_route_release_id);
    }
    assert_eq!(
        governance.profile.profile_id.as_str(),
        "0x8f65206657c02a3677706d7835b94da55e653c45d04abf035e4acd9fdc7a12bd"
    );
    for (command_kind, subject_id, grant_root) in [
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", root(6)),
    ] {
        let occurrence = occurrence(
            &governance.profile,
            &governance.routes,
            command_kind,
            subject_id,
            grant_root,
        );
        let input = managed_input(
            &governance.profile,
            &governance.lanes,
            &occurrence,
            command_kind,
        );
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) =
            transition_managed_asset_lifecycle_lane_module_v1(&input).unwrap()
        else {
            panic!("valid managed lifecycle command must accept")
        };
        let bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            managed_binding_candidate(&governance, &occurrence, &input, &accepted),
        )
        .expect("valid managed lifecycle output must bind");
        assert_eq!(bound.statement_root(), &input.statement_root().unwrap());
        assert_eq!(
            bound.producer_module_schema(),
            MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1
        );
    }
}

#[test]
fn authenticated_command_body_hashes_match_python_golden_vectors() {
    let transfer = AssetTransferCommandV1 {
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        sender: "alice".to_owned(),
        recipient: "bob".to_owned(),
        amount_atoms: 30,
        max_fee_atoms: 2,
    };
    let issue = ManagedAssetLifecycleCommandV1 {
        command_kind: MANAGED_ASSET_ISSUE_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        account_owner: "alice".to_owned(),
        amount_atoms: 7,
    };
    let burn = ManagedAssetLifecycleCommandV1 {
        command_kind: MANAGED_ASSET_BURN_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        account_owner: "alice".to_owned(),
        amount_atoms: 4,
    };

    assert_eq!(
        transfer.command_body_hash().unwrap().as_str(),
        "0x86c77102b725de42ba4928542495129ab51bbfa71d3ebf14218d16c403f4f9c6"
    );
    assert_eq!(
        issue.command_body_hash().unwrap().as_str(),
        "0xba582530e63ec9b3646fae1a361fb8b3aaa7cf4f9ea98d3c47d09d717fcb8983"
    );
    assert_eq!(
        burn.command_body_hash().unwrap().as_str(),
        "0xfea954a9c050efcb620a3971bdd7fabed19a56b82cb5ad6aacfaa8db6df847b6"
    );
}

#[test]
fn same_kind_transfer_body_substitution_rejects_before_receipt_binding() {
    // Arrange: the occurrence authenticates Bob, while the module executes Mallory.
    let (profile, lanes, coordinators, routes) = profile();
    let occurrence = occurrence(
        &profile,
        &routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let mut input = asset_input(&profile, &lanes, &occurrence, None);
    input.command.recipient = "mallory".to_owned();
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("substituted transfer remains economically valid")
    };
    let registries = transfer_registries(&routes);
    let refs = TransferGovernanceRefs {
        profile: &profile,
        lanes: &lanes,
        coordinators: &coordinators,
        routes: &routes,
        registries: &registries,
    };

    // Act / Assert
    assert_eq!(
        bind_transfer(&refs, &occurrence, &input, &accepted).unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module command body hash")
    );
}

#[test]
fn same_kind_managed_body_substitution_rejects_before_receipt_binding() {
    let governance = managed_governance();
    for (command_kind, subject_id) in [
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer"),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice"),
    ] {
        // Arrange
        let grant_root = if command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1 {
            root(5)
        } else {
            root(6)
        };
        let occurrence = occurrence(
            &governance.profile,
            &governance.routes,
            command_kind,
            subject_id,
            grant_root,
        );
        let mut input = managed_input(
            &governance.profile,
            &governance.lanes,
            &occurrence,
            command_kind,
        );
        input.command.amount_atoms += 1;
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) =
            transition_managed_asset_lifecycle_lane_module_v1(&input).unwrap()
        else {
            panic!("substituted managed command remains economically valid")
        };

        // Act / Assert
        assert_eq!(
            bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
                managed_binding_candidate(&governance, &occurrence, &input, &accepted),
            )
            .unwrap_err(),
            AbiErrorV1::InvalidBinding("lane module command body hash")
        );
    }
}

#[test]
fn coherent_transfer_output_for_another_amount_rejects_before_route_binding() {
    // Arrange
    let (profile, lanes, coordinators, routes) = profile();
    let occurrence = occurrence(
        &profile,
        &routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let input = asset_input(&profile, &lanes, &occurrence, None);
    let registries = transfer_registries(&routes);
    let refs = TransferGovernanceRefs {
        profile: &profile,
        lanes: &lanes,
        coordinators: &coordinators,
        routes: &routes,
        registries: &registries,
    };
    let mut foreign_input = input.clone();
    foreign_input.command.amount_atoms += 1;
    let AssetTransferLaneModuleResultV1::Accepted(mut forged) =
        transition_asset_transfer_lane_module_v1(&foreign_input).unwrap()
    else {
        panic!("foreign transfer must remain economically valid")
    };
    structurally_rebind_transfer_statement(&mut forged, input.statement_root().unwrap());

    // Act
    let result = bind_transfer(&refs, &occurrence, &input, &forged);

    // Assert
    assert_eq!(
        result.unwrap_err(),
        AbiErrorV1::InvalidBinding("asset transfer supplied acceptance differs from recomputation")
    );
}

#[test]
fn coherent_managed_output_for_another_amount_rejects_before_route_binding() {
    let governance = managed_governance();
    for (command_kind, subject_id, grant_root) in [
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", root(6)),
    ] {
        // Arrange
        let occurrence = occurrence(
            &governance.profile,
            &governance.routes,
            command_kind,
            subject_id,
            grant_root,
        );
        let input = managed_input(
            &governance.profile,
            &governance.lanes,
            &occurrence,
            command_kind,
        );
        let mut foreign_input = input.clone();
        foreign_input.command.amount_atoms += 1;
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(mut forged) =
            transition_managed_asset_lifecycle_lane_module_v1(&foreign_input).unwrap()
        else {
            panic!("foreign managed command must remain economically valid")
        };
        structurally_rebind_managed_statement(&mut forged, input.statement_root().unwrap());

        // Act
        let result = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            managed_binding_candidate(&governance, &occurrence, &input, &forged),
        );

        // Assert
        assert_eq!(
            result.unwrap_err(),
            AbiErrorV1::InvalidBinding(
                "managed lifecycle supplied acceptance differs from recomputation"
            )
        );
    }
}

#[test]
fn receipt_structural_binding_rejects_a_coherent_foreign_output_before_recomputation() {
    // Arrange: bind the honest output, then create a structurally valid output
    // for amount+1 and rebound only its public statement to the honest input.
    let (profile, lanes, coordinators, routes) = profile();
    let occurrence = occurrence(
        &profile,
        &routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let input = asset_input(&profile, &lanes, &occurrence, None);
    let registries = transfer_registries(&routes);
    let refs = TransferGovernanceRefs {
        profile: &profile,
        lanes: &lanes,
        coordinators: &coordinators,
        routes: &routes,
        registries: &registries,
    };
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let bound = bind_transfer(&refs, &occurrence, &input, &accepted).unwrap();
    let mut foreign_input = input.clone();
    foreign_input.command.amount_atoms += 1;
    let AssetTransferLaneModuleResultV1::Accepted(mut forged) =
        transition_asset_transfer_lane_module_v1(&foreign_input).unwrap()
    else {
        panic!("foreign transfer must remain economically valid")
    };
    structurally_rebind_transfer_statement(&mut forged, input.statement_root().unwrap());
    let authenticated = authenticate_occurrence(
        &profile,
        &routes,
        &occurrence,
        canonical_economic_command_body_bytes_v1(&input.command.command_kind, &input.command)
            .unwrap(),
    );
    let verifier = RecordingModuleReceiptVerifier::default();

    // Act
    let result = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &profile,
            policy_registry: &registries.policy_registry,
            asset_policy_registry: &registries.asset_policy_registry,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            authenticated_command: &authenticated,
            module_input: &input,
            accepted: &forged,
            release_route_binding: &bound,
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"untrusted-receipt-must-not-reach-verifier",
            },
        },
        &verifier,
    );

    // Assert: the historical structural envelope check retains precedence,
    // and no cryptographic verifier authority is invoked.
    assert_eq!(
        result.unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module structural binding")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn managed_receipt_structural_binding_rejects_coherent_foreign_outputs_first() {
    let governance = managed_governance();
    for (command_kind, subject_id, grant_root) in [
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", root(6)),
    ] {
        // Arrange: retain the honest route binding while supplying a coherent
        // amount+1 output rebound to the honest statement.
        let occurrence = occurrence(
            &governance.profile,
            &governance.routes,
            command_kind,
            subject_id,
            grant_root,
        );
        let input = managed_input(
            &governance.profile,
            &governance.lanes,
            &occurrence,
            command_kind,
        );
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) =
            transition_managed_asset_lifecycle_lane_module_v1(&input).unwrap()
        else {
            panic!("valid managed lifecycle command must accept")
        };
        let bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            managed_binding_candidate(&governance, &occurrence, &input, &accepted),
        )
        .unwrap();
        let mut foreign_input = input.clone();
        foreign_input.command.amount_atoms += 1;
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(mut forged) =
            transition_managed_asset_lifecycle_lane_module_v1(&foreign_input).unwrap()
        else {
            panic!("foreign managed command must remain economically valid")
        };
        structurally_rebind_managed_statement(&mut forged, input.statement_root().unwrap());
        let authenticated = authenticate_occurrence_with_policy_registry(
            &governance.profile,
            &governance.routes,
            &occurrence,
            canonical_economic_command_body_bytes_v1(&input.command.command_kind, &input.command)
                .unwrap(),
            &governance.policy_registry,
        );
        let verifier = RecordingModuleReceiptVerifier::default();

        // Act
        let result = verify_managed_asset_lifecycle_lane_module_receipt_v1(
            ManagedAssetLifecycleLaneModuleReceiptCandidateV1 {
                profile: &governance.profile,
                policy_registry: &governance.policy_registry,
                asset_policy_registry: &governance.asset_policy_registry,
                lanes: &governance.lanes,
                coordinators: &governance.coordinators,
                routes: &governance.routes,
                authenticated_command: &authenticated,
                module_input: &input,
                accepted: &forged,
                release_route_binding: &bound,
                receipt: LaneModuleReceiptEnvelopeV1 {
                    receipt_kind: ReceiptKindV1::SUCCINCT,
                    receipt_bytes: b"untrusted-receipt-must-not-reach-verifier",
                },
            },
            &verifier,
        );

        // Assert
        assert_eq!(
            result.unwrap_err(),
            AbiErrorV1::InvalidBinding("lane module structural binding")
        );
        assert!(verifier.calls.borrow().is_empty());
    }
}

#[test]
fn inactive_profile_reject_precedes_coherent_foreign_output_rejection() {
    // Arrange
    let (profile, lanes, coordinators, routes) = profile();
    let occurrence = occurrence(
        &profile,
        &routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let input = asset_input(&profile, &lanes, &occurrence, None);
    let registries = transfer_registries(&routes);
    let refs = TransferGovernanceRefs {
        profile: &profile,
        lanes: &lanes,
        coordinators: &coordinators,
        routes: &routes,
        registries: &registries,
    };
    let mut foreign_input = input.clone();
    foreign_input.command.amount_atoms += 1;
    let AssetTransferLaneModuleResultV1::Accepted(mut forged) =
        transition_asset_transfer_lane_module_v1(&foreign_input).unwrap()
    else {
        panic!("foreign transfer must remain economically valid")
    };
    structurally_rebind_transfer_statement(&mut forged, input.statement_root().unwrap());
    let mut inactive = profile.clone();
    inactive.status = ProfileStatusV1::SHADOW;
    let inactive_refs = TransferGovernanceRefs {
        profile: &inactive,
        ..refs
    };

    // Act
    let result = bind_transfer(&inactive_refs, &occurrence, &input, &forged);

    // Assert
    assert_eq!(
        result.unwrap_err(),
        AbiErrorV1::InvalidBinding("economic profile is not active")
    );
}

#[test]
fn caller_route_profile_domain_and_release_substitutions_fail_closed() {
    let (profile, lanes, coordinators, routes) = profile();
    let occurrence = occurrence(
        &profile,
        &routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let input = asset_input(&profile, &lanes, &occurrence, None);
    let registries = transfer_registries(&routes);
    let refs = TransferGovernanceRefs {
        profile: &profile,
        lanes: &lanes,
        coordinators: &coordinators,
        routes: &routes,
        registries: &registries,
    };
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };

    let mut wrong_route = occurrence.clone();
    wrong_route.route_release_id = root(998);
    assert_eq!(
        bind_transfer(&refs, &wrong_route, &input, &accepted).unwrap_err(),
        AbiErrorV1::InvalidBinding("caller-selected route does not match governed route")
    );

    let mut inactive = profile.clone();
    inactive.status = ProfileStatusV1::SHADOW;
    let inactive_refs = TransferGovernanceRefs {
        profile: &inactive,
        ..refs
    };
    assert_eq!(
        bind_transfer(&inactive_refs, &occurrence, &input, &accepted).unwrap_err(),
        AbiErrorV1::InvalidBinding("economic profile is not active")
    );

    let mut wrong_chain = occurrence.clone();
    wrong_chain.chain_id = "other-chain".to_owned();
    assert_eq!(
        bind_transfer(&refs, &wrong_chain, &input, &accepted).unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module chain id")
    );

    // A foreign module release now rejects at governed policy membership, which
    // precedes the release-route module release comparison.
    let foreign_input = asset_input(&profile, &lanes, &occurrence, Some(root(997)));
    let AssetTransferLaneModuleResultV1::Accepted(foreign) =
        transition_asset_transfer_lane_module_v1(&foreign_input).unwrap()
    else {
        panic!("internally consistent foreign release must evaluate")
    };
    assert_eq!(
        bind_transfer(&refs, &occurrence, &foreign_input, &foreign).unwrap_err(),
        AbiErrorV1::InvalidBinding("asset transfer policy registry module release")
    );
}

#[test]
fn managed_issue_occurrence_cannot_authorize_a_burn_output() {
    let governance = managed_governance();
    let issue_occurrence = occurrence(
        &governance.profile,
        &governance.routes,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        "alice",
        root(6),
    );
    let burn_input = managed_input(
        &governance.profile,
        &governance.lanes,
        &issue_occurrence,
        MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    );
    let ManagedAssetLifecycleLaneModuleResultV1::Accepted(burn) =
        transition_managed_asset_lifecycle_lane_module_v1(&burn_input).unwrap()
    else {
        panic!("valid self-burn must accept")
    };
    assert_eq!(
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(managed_binding_candidate(
            &governance,
            &issue_occurrence,
            &burn_input,
            &burn
        ),)
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module command kind")
    );
}

#[derive(Default)]
struct RecordingModuleReceiptVerifier {
    calls: RefCell<Vec<RecordedModuleReceiptVerifierCall>>,
    reject: bool,
}

impl LaneModuleSuccinctReceiptVerifierV1 for RecordingModuleReceiptVerifier {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> Result<(), AbiErrorV1> {
        self.calls.borrow_mut().push((
            receipt_bytes.to_vec(),
            expected_image_id.clone(),
            expected_journal_bytes.to_vec(),
        ));
        if self.reject {
            Err(AbiErrorV1::InvalidBinding(
                "test verifier rejected module receipt",
            ))
        } else {
            Ok(())
        }
    }
}

struct PerpsReceiptFixture {
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    market_policy: PerpsMarketPolicyV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    authenticated_command: AuthenticatedEconomicCommandV1,
    module_input: PerpsMarginLaneModuleInputV1,
    accepted: PerpsMarginAcceptedV1,
    verified_price: Option<VerifiedGlobalOraclePriceV1>,
}

fn perps_receipt_fixture(with_position: bool, price_e8: u128) -> PerpsReceiptFixture {
    perps_receipt_fixture_with_base(with_position, price_e8, "BTC")
}

fn perps_receipt_fixture_with_base(
    with_position: bool,
    price_e8: u128,
    base_asset: &str,
) -> PerpsReceiptFixture {
    let (profile, lanes, coordinators, routes, policy, policy_registry, market_policy) =
        perps_profile();
    let release_id = lanes
        .release_for(LaneIdV1::PERPS_MARKET)
        .unwrap()
        .release_id
        .clone();
    let command_kind = if with_position {
        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1
    } else {
        PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1
    };
    let command = PerpsMarginCommandV1 {
        command_kind: command_kind.to_owned(),
        account_id: "alice-margin".to_owned(),
        market_id: "BTC-ZUSD-PERP".to_owned(),
        owner: "alice".to_owned(),
        asset: "zUSD".to_owned(),
        amount_atoms: 10_000,
        nonce: 1,
    };
    let accounts = if with_position {
        vec![
            PerpsMarginAccountV1 {
                account_id: "alice-margin".to_owned(),
                owner: "alice".to_owned(),
                position_base: 1,
                entry_price_e8: price_e8,
                collateral_atoms: 1_000_000_000_000,
                nonce: 0,
                status: PerpsMarginAccountStatusV1::OPEN,
            },
            PerpsMarginAccountV1 {
                account_id: "bob-margin".to_owned(),
                owner: "bob".to_owned(),
                position_base: -1,
                entry_price_e8: price_e8,
                collateral_atoms: 1_000_000_000_000,
                nonce: 0,
                status: PerpsMarginAccountStatusV1::OPEN,
            },
        ]
    } else {
        vec![]
    };
    let pre_state = PerpsMarginStateV1 {
        schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: release_id,
        market_id: "BTC-ZUSD-PERP".to_owned(),
        collateral_asset: "zUSD".to_owned(),
        index_price_e8: price_e8,
        maintenance_margin_bps: 500,
        depeg_buffer_bps: 100,
        max_position_abs: 10,
        market_status: PerpsMarginMarketStatusV1::ACTIVE,
        accounts,
    };
    let payload = GlobalOraclePriceOccurrenceV1 {
        schema: GLOBAL_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1.to_owned(),
        oracle_id: policy.oracle_id.clone(),
        market_id: "BTC-ZUSD-PERP".to_owned(),
        base_asset: base_asset.to_owned(),
        quote_asset: "zUSD".to_owned(),
        price_e8,
        observed_height: 41,
    };
    let zero = RootV1::parse(ZERO_ROOT_V1, "perps binding zero root", true).unwrap();
    let global_state = GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-perps-binding-test".to_owned(),
        deployment_root: root(701),
        writer_epoch: profile.authority_epoch,
        height: 41,
        profile_root: profile.profile_id.clone(),
        lane_roots: ALL_LANE_IDS_V1
            .iter()
            .map(|lane_id| LaneStateRootV1 {
                lane_id: *lane_id,
                module_release_id: lanes.release_for(*lane_id).unwrap().release_id.clone(),
                enabled: *lane_id == LaneIdV1::PERPS_MARKET,
                state_root: if *lane_id == LaneIdV1::PERPS_MARKET {
                    pre_state.state_root().unwrap()
                } else {
                    zero.clone()
                },
            })
            .collect(),
        balances: vec![],
        supplies: vec![],
        custody: vec![],
        liabilities: vec![],
        reserves: vec![],
        oracle_occurrences: vec![OracleOccurrenceStateV1 {
            oracle_id: policy.oracle_id.clone(),
            occurrence_root: payload.occurrence_root().unwrap(),
            observed_height: 41,
            finalized: true,
        }],
        replay_state: vec![],
        terminal_obligations: vec![],
        history_root: zero,
        outbox: vec![],
    };
    let route = routes.route_for_command(command_kind, None).unwrap();
    let occurrence = EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: global_state.chain_id.clone(),
        deployment_root: global_state.deployment_root.clone(),
        height: 42,
        tx_index: 0,
        op_index: 0,
        command_kind: command_kind.to_owned(),
        command_body_hash: command.command_body_hash().unwrap(),
        route_release_id: route.route_release_id.clone(),
        subject_id: "alice".to_owned(),
        grant_root: root(7),
        nonce: 9,
        profile_root: profile.profile_id.clone(),
        pre_state_root: global_state.state_root().unwrap(),
        consumed_object_ids: vec![],
    };
    let authenticated_command = authenticate_occurrence_with_policy_registry(
        &profile,
        &routes,
        &occurrence,
        canonical_economic_command_body_bytes_v1(command_kind, &command).unwrap(),
        &policy_registry,
    );
    let verified_price = if with_position {
        let authority = verify_global_oracle_occurrence_authority_v1(
            GlobalOracleOccurrenceAuthorityCandidateV1 {
                pre_state: &global_state,
                route,
                occurrence: &occurrence,
                policy: &policy,
            },
        )
        .unwrap();
        Some(verify_global_oracle_price_occurrence_v1(&authority, &payload).unwrap())
    } else {
        None
    };
    let context = PerpsMarginContextV1 {
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: profile.profile_id.clone(),
        writer_epoch: profile.authority_epoch,
        module_release_id: pre_state.module_release_id.clone(),
        command_occurrence_id: occurrence.occurrence_id().unwrap(),
        subject_id: occurrence.subject_id.clone(),
        grant_root: occurrence.grant_root.clone(),
        oracle_authority_root: verified_price.as_ref().map_or_else(
            || RootV1::parse(ZERO_ROOT_V1, "zero authority", true).unwrap(),
            |value| value.oracle_authority_root().clone(),
        ),
        oracle_occurrence_root: verified_price.as_ref().map_or_else(
            || RootV1::parse(ZERO_ROOT_V1, "zero occurrence", true).unwrap(),
            |value| value.occurrence_root().clone(),
        ),
        oracle_price_e8: verified_price.as_ref().map_or(0, |value| value.price_e8()),
    };
    let module_input = PerpsMarginLaneModuleInputV1 {
        schema: PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context,
        pre_state,
        command,
    };
    let accepted = match transition_perps_margin_lane_module_v1(&module_input).unwrap() {
        PerpsMarginResultV1::Accepted(value) => *value,
        PerpsMarginResultV1::Rejected(value) => panic!("unexpected reject: {:?}", value.code),
    };
    PerpsReceiptFixture {
        profile,
        policy_registry,
        market_policy,
        lanes,
        coordinators,
        routes,
        authenticated_command,
        module_input,
        accepted,
        verified_price,
    }
}

fn perps_binding_candidate<'a>(
    fixture: &'a PerpsReceiptFixture,
    verified_price: Option<&'a VerifiedGlobalOraclePriceV1>,
) -> PerpsMarginReleaseRouteBindingCandidateV1<'a> {
    PerpsMarginReleaseRouteBindingCandidateV1 {
        profile: &fixture.profile,
        policy_registry: &fixture.policy_registry,
        market_policy: &fixture.market_policy,
        lanes: &fixture.lanes,
        coordinators: &fixture.coordinators,
        routes: &fixture.routes,
        occurrence: fixture.authenticated_command.occurrence(),
        module_input: &fixture.module_input,
        accepted: &fixture.accepted,
        verified_price,
    }
}

#[test]
fn perps_position_withdraw_binds_exact_price_and_succinct_receipt() {
    let fixture = perps_receipt_fixture(true, 6_500_000_000_000);
    let price = fixture.verified_price.as_ref().unwrap();
    let binding = bind_perps_margin_lane_output_to_release_route_v1(perps_binding_candidate(
        &fixture,
        Some(price),
    ))
    .unwrap();
    let verifier = RecordingModuleReceiptVerifier::default();
    let verified = verify_perps_margin_lane_module_receipt_v1(
        PerpsMarginLaneModuleReceiptCandidateV1 {
            profile: &fixture.profile,
            policy_registry: &fixture.policy_registry,
            market_policy: &fixture.market_policy,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            authenticated_command: &fixture.authenticated_command,
            module_input: &fixture.module_input,
            accepted: &fixture.accepted,
            release_route_binding: &binding,
            verified_price: Some(price),
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"perps-receipt",
            },
        },
        &verifier,
    )
    .unwrap();

    let release = fixture.lanes.release_for(LaneIdV1::PERPS_MARKET).unwrap();
    assert_eq!(verified.expected_image_id(), &release.guest_image_id);
    assert_eq!(
        fixture.module_input.statement_root().unwrap().as_str(),
        "0x5380448e82dcbb72189d026b0a1d13d5ac734af537f105ce8bf1d9dbeb0fff7a"
    );
    assert_eq!(
        fixture
            .accepted
            .module_journal
            .journal_root()
            .unwrap()
            .as_str(),
        "0xc3cfbf33da4c054e67a445e6c160c596a6a2e6a9b1eb5e2e93f8924ca7bbc62f"
    );
    assert_eq!(
        verified.authenticated_command_binding_root(),
        &fixture.authenticated_command.binding_root().unwrap()
    );
    assert_eq!(verifier.calls.borrow().len(), 1);
    assert_eq!(
        verifier.calls.borrow()[0],
        (
            b"perps-receipt".to_vec(),
            release.guest_image_id.clone(),
            canonical_bytes_v1(&fixture.accepted.module_journal).unwrap(),
        )
    );
}

#[test]
fn perps_account_close_cannot_alias_unresolved_terminal_closeout_capability() {
    // Arrange.
    let mut fixture = perps_receipt_fixture(false, 6_500_000_000_000);
    fixture.module_input.command.command_kind = PERPS_MARGIN_CLOSE_COMMAND_KIND_V1.to_owned();
    fixture.module_input.command.amount_atoms = 0;

    // Act.
    let error =
        bind_perps_margin_lane_output_to_release_route_v1(perps_binding_candidate(&fixture, None))
            .unwrap_err();

    // Assert.
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("perps margin command capability binding")
    );
}

#[test]
fn perps_account_close_capability_ambiguity_rejects_before_receipt_verifier() {
    // Arrange.
    let mut fixture = perps_receipt_fixture(false, 6_500_000_000_000);
    let binding =
        bind_perps_margin_lane_output_to_release_route_v1(perps_binding_candidate(&fixture, None))
            .unwrap();
    fixture.module_input.command.command_kind = PERPS_MARGIN_CLOSE_COMMAND_KIND_V1.to_owned();
    fixture.module_input.command.amount_atoms = 0;
    let verifier = RecordingModuleReceiptVerifier::default();

    // Act.
    let error = verify_perps_margin_lane_module_receipt_v1(
        PerpsMarginLaneModuleReceiptCandidateV1 {
            profile: &fixture.profile,
            policy_registry: &fixture.policy_registry,
            market_policy: &fixture.market_policy,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            authenticated_command: &fixture.authenticated_command,
            module_input: &fixture.module_input,
            accepted: &fixture.accepted,
            release_route_binding: &binding,
            verified_price: None,
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"must-not-be-verified",
            },
        },
        &verifier,
    )
    .unwrap_err();

    // Assert.
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("perps margin command capability binding")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn perps_price_substitution_extra_authority_and_wrong_kind_reject_pre_verifier() {
    let fixture = perps_receipt_fixture(true, 6_500_000_000_000);
    let wrong_price = perps_receipt_fixture(true, 6_500_000_000_001);
    assert_eq!(
        bind_perps_margin_lane_output_to_release_route_v1(perps_binding_candidate(
            &fixture,
            wrong_price.verified_price.as_ref()
        ),)
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("perps margin Oracle price binding")
    );

    let flat = perps_receipt_fixture(false, 6_500_000_000_000);
    assert_eq!(
        bind_perps_margin_lane_output_to_release_route_v1(perps_binding_candidate(
            &flat,
            fixture.verified_price.as_ref()
        ),)
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("perps margin unexpected Oracle price authority")
    );

    let price = fixture.verified_price.as_ref().unwrap();
    let binding = bind_perps_margin_lane_output_to_release_route_v1(perps_binding_candidate(
        &fixture,
        Some(price),
    ))
    .unwrap();
    let verifier = RecordingModuleReceiptVerifier::default();
    assert_eq!(
        verify_perps_margin_lane_module_receipt_v1(
            PerpsMarginLaneModuleReceiptCandidateV1 {
                profile: &fixture.profile,
                policy_registry: &fixture.policy_registry,
                market_policy: &fixture.market_policy,
                lanes: &fixture.lanes,
                coordinators: &fixture.coordinators,
                routes: &fixture.routes,
                authenticated_command: &fixture.authenticated_command,
                module_input: &fixture.module_input,
                accepted: &fixture.accepted,
                release_route_binding: &binding,
                verified_price: Some(price),
                receipt: LaneModuleReceiptEnvelopeV1 {
                    receipt_kind: ReceiptKindV1::COMPOSITE,
                    receipt_bytes: b"receipt",
                },
            },
            &verifier,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module receipt kind")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn perps_market_policy_root_matches_python_and_rejects_base_asset_substitution() {
    let policy = perps_market_policy();
    assert_eq!(
        policy.policy_root().unwrap().as_str(),
        "0xa41728c33880ba70f198f632be3f9677ef683a710ffe999b281689127edd505a"
    );
    let substituted = perps_receipt_fixture_with_base(true, 6_500_000_000_000, "WBTC");
    assert_eq!(
        bind_perps_margin_lane_output_to_release_route_v1(perps_binding_candidate(
            &substituted,
            substituted.verified_price.as_ref(),
        ))
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("perps margin market policy Oracle binding")
    );
    assert!(serde_json::from_value::<PerpsMarketPolicyV1>(json!({
        "schema": PERPS_MARKET_POLICY_SCHEMA_V1,
        "market_id": "BTC-ZUSD-PERP",
        "base_asset": "BTC",
        "quote_asset": "zUSD",
        "oracle_id": "zenodex.oracle.perps-index-price.v1",
        "caller_selected_market_alias": "forbidden",
    }))
    .is_err());
}

#[test]
fn perps_market_policy_identifier_length_bva_accepts_160_and_rejects_161_bytes() {
    // Arrange.
    let mut policy = perps_market_policy();
    policy.market_id = "M".repeat(160);

    // Act and assert.
    assert!(policy.validate().is_ok());
    policy.market_id.push('M');
    assert_eq!(
        policy.validate().unwrap_err(),
        AbiErrorV1::InvalidToken("perps market policy market id")
    );
}

fn perps_projection_pair() -> (
    PerpsReceiptFixture,
    PerpsMarginLaneProjectionV1,
    PerpsMarginLaneProjectionV1,
    PerpsMarginLaneCoordinatorContextV1,
) {
    let fixture = perps_receipt_fixture(true, 6_500_000_000_000);
    let pre_lane = fixture.module_input.pre_state.clone();
    let post_lane = fixture.accepted.post_state.clone();
    let pre = PerpsMarginLaneProjectionV1 {
        schema: PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1.to_owned(),
        lane_state: pre_lane.clone(),
        balances: vec![EconomicAmountV1 {
            owner: "alice".to_owned(),
            asset: "zUSD".to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            amount_atoms: 2_000_000_000_000,
        }],
        accounting_locations: vec![
            EconomicAmountV1 {
                owner: "alice-margin".to_owned(),
                asset: "zUSD".to_owned(),
                custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 1_000_000_000_000,
            },
            EconomicAmountV1 {
                owner: "bob-margin".to_owned(),
                asset: "zUSD".to_owned(),
                custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 1_000_000_000_000,
            },
        ],
        liabilities: vec![
            EconomicAmountV1 {
                owner: "alice".to_owned(),
                asset: "zUSD".to_owned(),
                custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 1_000_000_000_000,
            },
            EconomicAmountV1 {
                owner: "bob".to_owned(),
                asset: "zUSD".to_owned(),
                custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 1_000_000_000_000,
            },
        ],
        supplies: vec![AssetSupplyV1 {
            asset: "zUSD".to_owned(),
            amount_atoms: 4_000_000_000_000,
        }],
        terminal_obligations: pre_lane.terminal_obligations().unwrap(),
    };
    let post = PerpsMarginLaneProjectionV1 {
        schema: PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1.to_owned(),
        lane_state: post_lane.clone(),
        balances: vec![EconomicAmountV1 {
            owner: "alice".to_owned(),
            asset: "zUSD".to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            amount_atoms: 2_000_000_010_000,
        }],
        accounting_locations: vec![
            EconomicAmountV1 {
                owner: "alice-margin".to_owned(),
                asset: "zUSD".to_owned(),
                custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 999_999_990_000,
            },
            EconomicAmountV1 {
                owner: "bob-margin".to_owned(),
                asset: "zUSD".to_owned(),
                custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 1_000_000_000_000,
            },
        ],
        liabilities: vec![
            EconomicAmountV1 {
                owner: "alice".to_owned(),
                asset: "zUSD".to_owned(),
                custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 999_999_990_000,
            },
            EconomicAmountV1 {
                owner: "bob".to_owned(),
                asset: "zUSD".to_owned(),
                custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 1_000_000_000_000,
            },
        ],
        supplies: vec![AssetSupplyV1 {
            asset: "zUSD".to_owned(),
            amount_atoms: 4_000_000_000_000,
        }],
        terminal_obligations: post_lane.terminal_obligations().unwrap(),
    };
    pre.validate().unwrap();
    post.validate().unwrap();
    let coordinator = fixture
        .coordinators
        .release_for(LaneIdV1::PERPS_MARKET)
        .unwrap();
    let context = PerpsMarginLaneCoordinatorContextV1 {
        schema: PERPS_MARGIN_LANE_COORDINATOR_SCHEMA_V1.to_owned(),
        chain_id: fixture.authenticated_command.occurrence().chain_id.clone(),
        deployment_root: fixture
            .authenticated_command
            .occurrence()
            .deployment_root
            .clone(),
        profile_root: fixture.profile.profile_id.clone(),
        writer_epoch: fixture.profile.authority_epoch,
        coordinator_release_id: coordinator.coordinator_release_id.clone(),
        command_occurrence_id: fixture
            .authenticated_command
            .occurrence()
            .occurrence_id()
            .unwrap(),
        compatible_modules: vec![PerpsMarginModuleCompatibilityV1 {
            module_release_id: fixture.module_input.context.module_release_id.clone(),
            module_schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
        }],
    };
    (fixture, pre, post, context)
}

#[test]
fn perps_lane_coordinator_adds_complete_conservation_and_projection_roots() {
    let (fixture, pre, post, context) = perps_projection_pair();
    let result = compose_perps_margin_lane_single_v1(&PerpsMarginLaneCompositionCandidateV1 {
        context: context.clone(),
        module_journal: fixture.accepted.module_journal.clone(),
        private_port: fixture.accepted.private_port.clone(),
        pre_state: pre.clone(),
        post_state: post.clone(),
        module_effects: fixture.accepted.effects.clone(),
    })
    .unwrap();
    let PerpsMarginLaneCompositionResultV1::Accepted(accepted) = result else {
        panic!("exact perps composition must accept");
    };

    assert_eq!(accepted.post_state, post);
    assert_eq!(
        pre.state_root().unwrap().as_str(),
        "0x8570aa2d5eaaaa28aad048749250ab1b16588ac209a07a49cd043786d11867a9"
    );
    assert_eq!(
        post.state_root().unwrap().as_str(),
        "0x48efacb34784dfecbc0560e1233e6be8f4d589c58d26fdc4447f5c41928a5eb7"
    );
    assert_eq!(
        accepted.lane_journal.pre_lane_root,
        pre.state_root().unwrap()
    );
    assert_eq!(
        accepted.lane_journal.post_lane_root,
        post.state_root().unwrap()
    );
    assert_eq!(
        accepted.effects.effect_plan_root().unwrap().as_str(),
        "0x5cae7d4e468446992b37bf69ecf7172a08091d3d2c7dff547f18a556a8584f26"
    );
    assert_eq!(
        accepted.lane_journal.journal_root().unwrap().as_str(),
        "0xb0c2198082ba9a895af3a645ab7b788ab81c5183a1ace6ff5b4a2bcabc8cca1d"
    );
    assert_eq!(accepted.effects.rows, fixture.accepted.effects.rows);
    assert_eq!(accepted.effects.asset_conservation.len(), 1);
    let conservation = &accepted.effects.asset_conservation[0];
    assert_eq!(conservation.asset, "zUSD");
    assert_eq!(
        conservation.owned_and_custodied_pre_atoms,
        4_000_000_000_000
    );
    assert_eq!(
        conservation.owned_and_custodied_post_atoms,
        4_000_000_000_000
    );
    assert_eq!(conservation.supply_pre_atoms, 4_000_000_000_000);
    assert_eq!(conservation.supply_post_atoms, 4_000_000_000_000);
    assert_eq!(conservation.authorized_issue_atoms, 0);
    assert_eq!(conservation.authorized_burn_atoms, 0);
}

#[test]
fn perps_lane_coordinator_accepts_representable_delta_above_i128_absolute_base() {
    // Arrange: both authoritative balances exceed i128::MAX, while the
    // value-moving delta remains the exact module effect of 10_000 atoms.
    let (fixture, mut pre, mut post, context) = perps_projection_pair();
    let high_base_offset = i128::MAX as u128 + 1;
    pre.balances[0].amount_atoms = pre.balances[0]
        .amount_atoms
        .checked_add(high_base_offset)
        .unwrap();
    post.balances[0].amount_atoms = post.balances[0]
        .amount_atoms
        .checked_add(high_base_offset)
        .unwrap();
    pre.supplies[0].amount_atoms = pre.supplies[0]
        .amount_atoms
        .checked_add(high_base_offset)
        .unwrap();
    post.supplies[0].amount_atoms = post.supplies[0]
        .amount_atoms
        .checked_add(high_base_offset)
        .unwrap();
    pre.validate().unwrap();
    post.validate().unwrap();

    // Act.
    let result = compose_perps_margin_lane_single_v1(&PerpsMarginLaneCompositionCandidateV1 {
        context,
        module_journal: fixture.accepted.module_journal.clone(),
        private_port: fixture.accepted.private_port.clone(),
        pre_state: pre,
        post_state: post,
        module_effects: fixture.accepted.effects.clone(),
    });

    // Assert: absolute state magnitude cannot invalidate a representable
    // signed transition delta.
    assert!(matches!(
        result,
        Ok(PerpsMarginLaneCompositionResultV1::Accepted(_))
    ));
}

#[test]
fn perps_lane_projection_drift_and_context_substitution_are_exact_no_ops() {
    let (fixture, pre, post, context) = perps_projection_pair();
    let mut drifted = post.clone();
    drifted.balances[0].amount_atoms -= 1;
    drifted.accounting_locations.push(EconomicAmountV1 {
        owner: "treasury".to_owned(),
        asset: "zUSD".to_owned(),
        custody_domain: "treasury".to_owned(),
        amount_atoms: 1,
    });
    drifted.validate().unwrap();
    let drift_result =
        compose_perps_margin_lane_single_v1(&PerpsMarginLaneCompositionCandidateV1 {
            context: context.clone(),
            module_journal: fixture.accepted.module_journal.clone(),
            private_port: fixture.accepted.private_port.clone(),
            pre_state: pre.clone(),
            post_state: drifted,
            module_effects: fixture.accepted.effects.clone(),
        })
        .unwrap();
    let PerpsMarginLaneCompositionResultV1::Rejected(drift_reject) = drift_result else {
        panic!("unrecorded accounting movement must reject");
    };
    assert_eq!(
        drift_reject.code,
        PerpsMarginLaneCoordinatorRejectCodeV1::STATE_EFFECT_MISMATCH
    );
    assert_eq!(drift_reject.pre_state_root, pre.state_root().unwrap());
    assert_eq!(drift_reject.post_state_root, pre.state_root().unwrap());
    assert!(drift_reject.effects.is_empty());

    let mut wrong_context = context;
    wrong_context.profile_root = root(999);
    let context_result =
        compose_perps_margin_lane_single_v1(&PerpsMarginLaneCompositionCandidateV1 {
            context: wrong_context,
            module_journal: fixture.accepted.module_journal.clone(),
            private_port: fixture.accepted.private_port.clone(),
            pre_state: pre,
            post_state: post,
            module_effects: fixture.accepted.effects.clone(),
        })
        .unwrap();
    let PerpsMarginLaneCompositionResultV1::Rejected(context_reject) = context_result else {
        panic!("profile substitution must reject");
    };
    assert_eq!(
        context_reject.code,
        PerpsMarginLaneCoordinatorRejectCodeV1::CONTEXT_MISMATCH
    );
    assert!(context_reject.effects.is_empty());
}

fn structural_perps_lane_fixture() -> (
    PerpsReceiptFixture,
    LaneCompositionJournalV1,
    ReceiptBackedPerpsMarginLaneCompositionV1,
) {
    let (fixture, pre, post, context) = perps_projection_pair();
    let price = fixture.verified_price.as_ref().unwrap();
    let binding = bind_perps_margin_lane_output_to_release_route_v1(perps_binding_candidate(
        &fixture,
        Some(price),
    ))
    .unwrap();
    let verified_module = verify_perps_margin_lane_module_receipt_v1(
        PerpsMarginLaneModuleReceiptCandidateV1 {
            profile: &fixture.profile,
            policy_registry: &fixture.policy_registry,
            market_policy: &fixture.market_policy,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            authenticated_command: &fixture.authenticated_command,
            module_input: &fixture.module_input,
            accepted: &fixture.accepted,
            release_route_binding: &binding,
            verified_price: Some(price),
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"perps-module-receipt-v1",
            },
        },
        &RecordingModuleReceiptVerifier::default(),
    )
    .unwrap();
    let lane_result = compose_perps_margin_lane_single_v1(&PerpsMarginLaneCompositionCandidateV1 {
        context: context.clone(),
        module_journal: fixture.accepted.module_journal.clone(),
        private_port: fixture.accepted.private_port.clone(),
        pre_state: pre.clone(),
        post_state: post.clone(),
        module_effects: fixture.accepted.effects.clone(),
    })
    .unwrap();
    let PerpsMarginLaneCompositionResultV1::Accepted(lane_accepted) = lane_result else {
        panic!("exact perps composition must accept");
    };
    let structural = compose_receipt_backed_perps_margin_lane_single_v1(
        ReceiptBackedPerpsMarginLaneCompositionCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: fixture.authenticated_command.occurrence(),
            coordinator_context: &context,
            module_journal: &fixture.accepted.module_journal,
            private_port: &fixture.accepted.private_port,
            pre_state: &pre,
            post_state: &post,
            module_effects: &fixture.accepted.effects,
            verified_module: &verified_module,
        },
    )
    .unwrap();
    (fixture, lane_accepted.lane_journal, structural)
}

#[test]
fn perps_lane_receipt_uses_governed_coordinator_image_and_exact_journal() {
    // Arrange.
    let (fixture, lane_journal, structural) = structural_perps_lane_fixture();
    let verifier = RecordingCompositionReceiptVerifier::default();

    // Act.
    let verified = verify_perps_margin_lane_composition_receipt_v1(
        PerpsMarginLaneCompositionReceiptCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: fixture.authenticated_command.occurrence(),
            structural_composition: &structural,
            lane_journal: &lane_journal,
            receipt: LaneCompositionReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"perps-coordinator-receipt-v1",
            },
        },
        &verifier,
    )
    .unwrap();

    // Assert.
    let coordinator = fixture
        .coordinators
        .release_for(LaneIdV1::PERPS_MARKET)
        .unwrap();
    assert_eq!(verified.lane_id(), LaneIdV1::PERPS_MARKET);
    assert_eq!(verified.expected_image_id(), &coordinator.guest_image_id);
    assert_eq!(
        verifier.calls.borrow().as_slice(),
        &[(
            b"perps-coordinator-receipt-v1".to_vec(),
            coordinator.guest_image_id.clone(),
            canonical_bytes_v1(&lane_journal).unwrap(),
        )]
    );
}

#[test]
fn perps_lane_journal_substitution_rejects_before_receipt_verifier() {
    // Arrange.
    let (fixture, mut lane_journal, structural) = structural_perps_lane_fixture();
    lane_journal.post_lane_root = root(90_001);
    let verifier = RecordingCompositionReceiptVerifier::default();

    // Act.
    let error = verify_perps_margin_lane_composition_receipt_v1(
        PerpsMarginLaneCompositionReceiptCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: fixture.authenticated_command.occurrence(),
            structural_composition: &structural,
            lane_journal: &lane_journal,
            receipt: LaneCompositionReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"perps-coordinator-receipt-v1",
            },
        },
        &verifier,
    )
    .unwrap_err();

    // Assert.
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("perps lane composition exact journal")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn perps_lane_receipt_shape_and_verifier_rejection_create_no_witness() {
    // Arrange.
    let (fixture, lane_journal, structural) = structural_perps_lane_fixture();
    for (receipt_kind, receipt_bytes, expected) in [
        (
            ReceiptKindV1::SUCCINCT,
            &[][..],
            AbiErrorV1::InvalidBounds("perps lane composition receipt bytes"),
        ),
        (
            ReceiptKindV1::COMPOSITE,
            &b"composite"[..],
            AbiErrorV1::InvalidBinding("perps lane composition receipt kind"),
        ),
    ] {
        let verifier = RecordingCompositionReceiptVerifier::default();
        let error = verify_perps_margin_lane_composition_receipt_v1(
            PerpsMarginLaneCompositionReceiptCandidateV1 {
                profile: &fixture.profile,
                lanes: &fixture.lanes,
                coordinators: &fixture.coordinators,
                routes: &fixture.routes,
                occurrence: fixture.authenticated_command.occurrence(),
                structural_composition: &structural,
                lane_journal: &lane_journal,
                receipt: LaneCompositionReceiptEnvelopeV1 {
                    receipt_kind,
                    receipt_bytes,
                },
            },
            &verifier,
        )
        .unwrap_err();
        assert_eq!(error, expected);
        assert!(verifier.calls.borrow().is_empty());
    }

    let verifier = RecordingCompositionReceiptVerifier {
        reject: true,
        ..Default::default()
    };
    let error = verify_perps_margin_lane_composition_receipt_v1(
        PerpsMarginLaneCompositionReceiptCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: fixture.authenticated_command.occurrence(),
            structural_composition: &structural,
            lane_journal: &lane_journal,
            receipt: LaneCompositionReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"cryptographically-invalid-perps-lane-receipt",
            },
        },
        &verifier,
    )
    .unwrap_err();
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("test verifier rejected lane composition receipt")
    );
    assert_eq!(verifier.calls.borrow().len(), 1);
}

#[derive(Default)]
struct RecordingCompositionReceiptVerifier {
    calls: RefCell<Vec<RecordedCompositionReceiptVerifierCall>>,
    reject: bool,
}

impl LaneCompositionSuccinctReceiptVerifierV1 for RecordingCompositionReceiptVerifier {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> Result<(), AbiErrorV1> {
        self.calls.borrow_mut().push((
            receipt_bytes.to_vec(),
            expected_image_id.clone(),
            expected_journal_bytes.to_vec(),
        ));
        if self.reject {
            Err(AbiErrorV1::InvalidBinding(
                "test verifier rejected lane composition receipt",
            ))
        } else {
            Ok(())
        }
    }
}

#[derive(Default)]
struct RecordingRouteReceiptVerifier {
    calls: RefCell<Vec<RecordedRouteReceiptVerifierCall>>,
    reject: bool,
}

impl RouteCompositionSuccinctReceiptVerifierV1 for RecordingRouteReceiptVerifier {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> Result<(), AbiErrorV1> {
        self.calls.borrow_mut().push((
            receipt_bytes.to_vec(),
            expected_image_id.clone(),
            expected_journal_bytes.to_vec(),
        ));
        if self.reject {
            Err(AbiErrorV1::InvalidBinding(
                "test verifier rejected route composition receipt",
            ))
        } else {
            Ok(())
        }
    }
}

#[derive(Default)]
struct RecordingEpochReceiptVerifier {
    calls: RefCell<Vec<RecordedEpochReceiptVerifierCall>>,
    reject: bool,
}

impl EconomicEpochSuccinctReceiptVerifierV1 for RecordingEpochReceiptVerifier {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> Result<(), AbiErrorV1> {
        self.calls.borrow_mut().push((
            receipt_bytes.to_vec(),
            expected_image_id.clone(),
            expected_journal_bytes.to_vec(),
        ));
        if self.reject {
            Err(AbiErrorV1::InvalidBinding(
                "test verifier rejected economic epoch receipt",
            ))
        } else {
            Ok(())
        }
    }
}

struct VerifiedAssetLaneFixture {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    registries: TransferRegistries,
    occurrence: EconomicCommandOccurrenceV1,
    input: AssetTransferLaneModuleInputV1,
    accepted: Box<AssetTransferLaneModuleAcceptedV1>,
    verified: VerifiedLaneModuleTransitionV1,
    context: AssetLaneCoordinatorContextV1,
}

impl VerifiedAssetLaneFixture {
    fn refs(&self) -> TransferGovernanceRefs<'_> {
        TransferGovernanceRefs {
            profile: &self.profile,
            lanes: &self.lanes,
            coordinators: &self.coordinators,
            routes: &self.routes,
            registries: &self.registries,
        }
    }
}

fn asset_lane_coordinator_context(
    profile: &EconomicProfileSnapshotV1,
    coordinators: &LaneCoordinatorRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    input: &AssetTransferLaneModuleInputV1,
    accepted: &AssetTransferLaneModuleAcceptedV1,
) -> AssetLaneCoordinatorContextV1 {
    let coordinator = coordinators
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .expect("asset coordinator release must exist");
    AssetLaneCoordinatorContextV1 {
        schema: zenodex_global_settlement_abi_v1::ASSET_LANE_COORDINATOR_SCHEMA_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: profile.profile_id.clone(),
        writer_epoch: profile.authority_epoch,
        coordinator_release_id: coordinator.coordinator_release_id.clone(),
        command_occurrence_id: occurrence.occurrence_id().unwrap(),
        asset_policy_registry_root: input.asset_policy_registry_root.clone(),
        fee_policy_registry_root: input.fee_policy_registry_root.clone(),
        compatible_modules: vec![AssetLaneModuleCompatibilityV1 {
            module_release_id: accepted.module_journal.module_release_id.clone(),
            module_schema: accepted.private_port.producer_module_schema.clone(),
        }],
    }
}

fn verified_asset_lane_fixture_with_state_at(
    tx_index: u64,
    nonce: u64,
    pre_state_root: RootV1,
    module_pre_state: Option<AssetTransferStateV1>,
) -> VerifiedAssetLaneFixture {
    let (profile, lanes, coordinators, routes) = profile();
    let mut occurrence = occurrence(
        &profile,
        &routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    occurrence.tx_index = tx_index;
    occurrence.nonce = nonce;
    occurrence.pre_state_root = pre_state_root;
    let mut input = asset_input(&profile, &lanes, &occurrence, None);
    if let Some(pre_state) = module_pre_state {
        input.pre_state = pre_state;
    }
    let registries = transfer_registries(&routes);
    let refs = TransferGovernanceRefs {
        profile: &profile,
        lanes: &lanes,
        coordinators: &coordinators,
        routes: &routes,
        registries: &registries,
    };
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let bound = bind_transfer(&refs, &occurrence, &input, &accepted).unwrap();
    let authenticated = authenticate_occurrence(
        &profile,
        &routes,
        &occurrence,
        canonical_economic_command_body_bytes_v1(&input.command.command_kind, &input.command)
            .unwrap(),
    );
    let verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &profile,
            policy_registry: &registries.policy_registry,
            asset_policy_registry: &registries.asset_policy_registry,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            authenticated_command: &authenticated,
            module_input: &input,
            accepted: &accepted,
            release_route_binding: &bound,
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"succinct-asset-transfer-module-receipt-v1",
            },
        },
        &RecordingModuleReceiptVerifier::default(),
    )
    .unwrap();
    let context =
        asset_lane_coordinator_context(&profile, &coordinators, &occurrence, &input, &accepted);
    VerifiedAssetLaneFixture {
        profile,
        lanes,
        coordinators,
        routes,
        registries,
        occurrence,
        input,
        accepted,
        verified,
        context,
    }
}

fn verified_asset_lane_fixture_at(
    tx_index: u64,
    nonce: u64,
    pre_state_root: RootV1,
) -> VerifiedAssetLaneFixture {
    verified_asset_lane_fixture_with_state_at(tx_index, nonce, pre_state_root, None)
}

fn verified_asset_lane_fixture() -> VerifiedAssetLaneFixture {
    verified_asset_lane_fixture_at(2, 9, root(2))
}

fn structural_asset_lane_fixture_with_state_at(
    tx_index: u64,
    nonce: u64,
    pre_state_root: RootV1,
    module_pre_state: Option<AssetTransferStateV1>,
) -> (
    VerifiedAssetLaneFixture,
    LaneCompositionJournalV1,
    ReceiptBackedAssetLaneCompositionV1,
    GlobalEconomicEffectPlanV1,
) {
    let fixture = verified_asset_lane_fixture_with_state_at(
        tx_index,
        nonce,
        pre_state_root,
        module_pre_state,
    );
    let lane_accepted = match compose_asset_lane_single_v1(
        &fixture.context,
        &fixture.accepted.module_journal,
        &fixture.accepted.private_port,
        &fixture.accepted.effects,
    )
    .expect("asset lane composition must evaluate")
    {
        AssetLaneCompositionResultV1::Accepted(accepted) => *accepted,
        AssetLaneCompositionResultV1::Rejected(_) => panic!("valid asset lane must accept"),
    };
    let lane_journal = lane_accepted.lane_journal;
    let structural =
        compose_receipt_backed_asset_lane_single_v1(ReceiptBackedAssetLaneCompositionCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            coordinator_context: &fixture.context,
            module_journal: &fixture.accepted.module_journal,
            private_port: &fixture.accepted.private_port,
            module_effects: &fixture.accepted.effects,
            verified_module: &fixture.verified,
        })
        .expect("verified module must produce a structural lane candidate");
    (fixture, lane_journal, structural, lane_accepted.effects)
}

fn structural_asset_lane_fixture_at(
    tx_index: u64,
    nonce: u64,
    pre_state_root: RootV1,
) -> (
    VerifiedAssetLaneFixture,
    LaneCompositionJournalV1,
    ReceiptBackedAssetLaneCompositionV1,
    GlobalEconomicEffectPlanV1,
) {
    structural_asset_lane_fixture_with_state_at(tx_index, nonce, pre_state_root, None)
}

fn structural_asset_lane_fixture() -> (
    VerifiedAssetLaneFixture,
    LaneCompositionJournalV1,
    ReceiptBackedAssetLaneCompositionV1,
    GlobalEconomicEffectPlanV1,
) {
    structural_asset_lane_fixture_at(2, 9, root(2))
}

#[test]
fn module_receipt_verification_uses_release_image_and_exact_journal() {
    let (profile, lanes, coordinators, routes) = profile();
    let occurrence = occurrence(
        &profile,
        &routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let input = asset_input(&profile, &lanes, &occurrence, None);
    let registries = transfer_registries(&routes);
    let refs = TransferGovernanceRefs {
        profile: &profile,
        lanes: &lanes,
        coordinators: &coordinators,
        routes: &routes,
        registries: &registries,
    };
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let bound = bind_transfer(&refs, &occurrence, &input, &accepted).unwrap();
    let verifier = RecordingModuleReceiptVerifier::default();
    let receipt_bytes = b"succinct-asset-transfer-module-receipt-v1";
    let authenticated = authenticate_occurrence(
        &profile,
        &routes,
        &occurrence,
        canonical_economic_command_body_bytes_v1(&input.command.command_kind, &input.command)
            .unwrap(),
    );
    assert_eq!(
        authenticated.authentication_message_digest().as_str(),
        "0x934c666d99583fb49c28b98d4f16149bc650666b7c4509dcff02b35f0129acc7"
    );
    assert_eq!(
        authenticated.binding_root().unwrap().as_str(),
        "0x7e3060ff5951838276290685c975b6e51638aa40cce3239989370482cdda4c38"
    );

    let verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &profile,
            policy_registry: &registries.policy_registry,
            asset_policy_registry: &registries.asset_policy_registry,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            authenticated_command: &authenticated,
            module_input: &input,
            accepted: &accepted,
            release_route_binding: &bound,
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes,
            },
        },
        &verifier,
    )
    .expect("valid module receipt must verify");

    let release = lanes.release_for(LaneIdV1::ASSET_TRANSFER).unwrap();
    let journal_bytes =
        zenodex_global_settlement_abi_v1::canonical_bytes_v1(&accepted.module_journal).unwrap();
    assert_eq!(
        verifier.calls.into_inner(),
        vec![(
            receipt_bytes.to_vec(),
            release.guest_image_id.clone(),
            journal_bytes
        )]
    );
    assert_eq!(
        verified.release_route_binding_root(),
        &bound.binding_root().unwrap()
    );
    assert_eq!(
        verified.authenticated_command_binding_root(),
        &authenticated.binding_root().unwrap()
    );
    assert_eq!(verified.expected_image_id(), &release.guest_image_id);
    assert_eq!(
        verified.module_journal_root(),
        &accepted.module_journal.journal_root().unwrap()
    );
    assert_eq!(verified.receipt_kind(), ReceiptKindV1::SUCCINCT);
    assert_ne!(
        verified.receipt_digest(),
        &accepted.module_journal.receipt_root
    );
    assert_eq!(
        verified.binding_root().unwrap().as_str(),
        "0xa398f2c330729ccbe8a927d7f96d9e3f14ec8bc56e97a6afeed9b79393d66353"
    );
    assert_eq!(
        verified.module_journal_digest().as_str(),
        "0x4c4e16b91b7002240bd72373e7d3af1eb860fb6f8e2fdd5e84fc775f5357583e"
    );
    assert_eq!(
        verified.receipt_digest().as_str(),
        "0x02506ee4d450a18d7af3b72483d252996ec25283526c04c424d5de64cd42fe05"
    );
}

#[test]
fn managed_module_receipts_gain_release_image_bound_authority() {
    let governance = managed_governance();
    for (command_kind, subject_id, grant_root) in [
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", root(6)),
    ] {
        let occurrence = occurrence(
            &governance.profile,
            &governance.routes,
            command_kind,
            subject_id,
            grant_root,
        );
        let input = managed_input(
            &governance.profile,
            &governance.lanes,
            &occurrence,
            command_kind,
        );
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) =
            transition_managed_asset_lifecycle_lane_module_v1(&input).unwrap()
        else {
            panic!("valid managed lifecycle command must accept")
        };
        let bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            managed_binding_candidate(&governance, &occurrence, &input, &accepted),
        )
        .unwrap();
        let verifier = RecordingModuleReceiptVerifier::default();
        let authenticated = authenticate_occurrence_with_policy_registry(
            &governance.profile,
            &governance.routes,
            &occurrence,
            canonical_economic_command_body_bytes_v1(&input.command.command_kind, &input.command)
                .unwrap(),
            &governance.policy_registry,
        );

        let verified = verify_managed_asset_lifecycle_lane_module_receipt_v1(
            ManagedAssetLifecycleLaneModuleReceiptCandidateV1 {
                profile: &governance.profile,
                policy_registry: &governance.policy_registry,
                asset_policy_registry: &governance.asset_policy_registry,
                lanes: &governance.lanes,
                coordinators: &governance.coordinators,
                routes: &governance.routes,
                authenticated_command: &authenticated,
                module_input: &input,
                accepted: &accepted,
                release_route_binding: &bound,
                receipt: LaneModuleReceiptEnvelopeV1 {
                    receipt_kind: ReceiptKindV1::SUCCINCT,
                    receipt_bytes: command_kind.as_bytes(),
                },
            },
            &verifier,
        )
        .expect("valid managed module receipt must verify");

        assert_eq!(
            verified.command_occurrence_id(),
            &occurrence.occurrence_id().unwrap()
        );
        assert_eq!(verified.statement_root(), &input.statement_root().unwrap());
        assert_eq!(verifier.calls.borrow().len(), 1);
    }
}

#[test]
fn managed_receipt_rejects_wrong_route_issue_burn_policy_root_before_verifier() {
    // Arrange: the governed profile's issue and burn routes carry a stale
    // route-owned issue/burn policy root instead of the typed registry root.
    let governance = managed_governance_with(Some(root(511)));
    let stale_occurrence = occurrence(
        &governance.profile,
        &governance.routes,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        "issuer",
        root(5),
    );
    let input = managed_input(
        &governance.profile,
        &governance.lanes,
        &stale_occurrence,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    );
    let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) =
        transition_managed_asset_lifecycle_lane_module_v1(&input).unwrap()
    else {
        panic!("valid managed issue must accept")
    };
    assert_eq!(
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(managed_binding_candidate(
            &governance,
            &stale_occurrence,
            &input,
            &accepted
        ),)
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("managed asset route issue/burn policy root")
    );
    // A witness minted under the exact governed profile cannot stand in for it.
    let governed = managed_governance();
    let governed_occurrence = occurrence(
        &governed.profile,
        &governed.routes,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        "issuer",
        root(5),
    );
    let governed_input = managed_input(
        &governed.profile,
        &governed.lanes,
        &governed_occurrence,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    );
    let ManagedAssetLifecycleLaneModuleResultV1::Accepted(governed_accepted) =
        transition_managed_asset_lifecycle_lane_module_v1(&governed_input).unwrap()
    else {
        panic!("valid governed issue must accept")
    };
    let witness =
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(managed_binding_candidate(
            &governed,
            &governed_occurrence,
            &governed_input,
            &governed_accepted,
        ))
        .unwrap();
    let verifier = RecordingModuleReceiptVerifier::default();
    let authenticated = authenticate_occurrence_with_policy_registry(
        &governance.profile,
        &governance.routes,
        &stale_occurrence,
        canonical_economic_command_body_bytes_v1(&input.command.command_kind, &input.command)
            .unwrap(),
        &governance.policy_registry,
    );

    // Act / Assert: the rebind rejects before any receipt bytes reach the verifier.
    assert_eq!(
        verify_managed_asset_lifecycle_lane_module_receipt_v1(
            ManagedAssetLifecycleLaneModuleReceiptCandidateV1 {
                profile: &governance.profile,
                policy_registry: &governance.policy_registry,
                asset_policy_registry: &governance.asset_policy_registry,
                lanes: &governance.lanes,
                coordinators: &governance.coordinators,
                routes: &governance.routes,
                authenticated_command: &authenticated,
                module_input: &input,
                accepted: &accepted,
                release_route_binding: &witness,
                receipt: LaneModuleReceiptEnvelopeV1 {
                    receipt_kind: ReceiptKindV1::SUCCINCT,
                    receipt_bytes: b"wrong-route-policy-root",
                },
            },
            &verifier,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("managed asset route issue/burn policy root")
    );
    assert_eq!(verifier.calls.borrow().len(), 0);
}

fn transfer_command_body_bytes(input: &AssetTransferLaneModuleInputV1) -> Vec<u8> {
    canonical_economic_command_body_bytes_v1(&input.command.command_kind, &input.command).unwrap()
}

#[test]
fn transfer_receipt_with_ungoverned_fee_row_never_reaches_verifier() {
    // Arrange: the governed row is treasury/2; Mallory executes under mallory/1
    // while retaining both opaque registry roots and the honest witness.
    // Python exercises the same minimized witness and rejection precedence.
    let governance = transfer_governance_with(vec![asset_transfer_policy()], TRANSFER_POLICY_KINDS);
    let refs = governance.refs();
    let transfer_occurrence = occurrence(
        &governance.profile,
        &governance.routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let input = asset_input(
        &governance.profile,
        &governance.lanes,
        &transfer_occurrence,
        None,
    );
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let bound = bind_transfer(&refs, &transfer_occurrence, &input, &accepted).unwrap();
    let mut rogue_input = input.clone();
    rogue_input.pre_state.policies[0] = AssetTransferPolicyV1 {
        asset: "USD".to_owned(),
        fee_owner: "mallory".to_owned(),
        transfer_fee_atoms: 1,
        enabled: true,
    };
    let AssetTransferLaneModuleResultV1::Accepted(rogue) =
        transition_asset_transfer_lane_module_v1(&rogue_input).unwrap()
    else {
        panic!("the ungoverned fee row still executes")
    };
    assert_eq!(rogue.post_state.balance_atoms("mallory", "USD"), 1);
    assert_eq!(
        rogue_input.asset_policy_registry_root,
        input.asset_policy_registry_root
    );
    assert_eq!(
        rogue_input.fee_policy_registry_root,
        input.fee_policy_registry_root
    );
    let authenticated = authenticate_occurrence(
        &governance.profile,
        &governance.routes,
        &transfer_occurrence,
        transfer_command_body_bytes(&input),
    );
    let verifier = RecordingModuleReceiptVerifier::default();
    let member_mismatch =
        AbiErrorV1::InvalidBinding("asset transfer state policy is not a governed member");

    // Act / Assert: governed membership rejects before any witness or verifier.
    assert_eq!(
        bind_transfer(&refs, &transfer_occurrence, &rogue_input, &rogue).unwrap_err(),
        member_mismatch
    );
    assert_eq!(
        verify_asset_transfer_lane_module_receipt_v1(
            transfer_receipt_candidate(
                &refs,
                &authenticated,
                &rogue_input,
                &rogue,
                &bound,
                b"mallory-fee-policy",
            ),
            &verifier,
        )
        .unwrap_err(),
        member_mismatch
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn transfer_receipt_stale_roots_after_policy_rotation_never_reach_verifier() {
    // Arrange: an output executed and witnessed under the old profile is
    // presented to a profile whose governed fee owner rotated.
    let old = transfer_governance_with(vec![asset_transfer_policy()], TRANSFER_POLICY_KINDS);
    let old_refs = old.refs();
    let occurrence = occurrence(
        &old.profile,
        &old.routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let input = asset_input(&old.profile, &old.lanes, &occurrence, None);
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let old_witness = bind_transfer(&old_refs, &occurrence, &input, &accepted).unwrap();
    let authenticated = authenticate_occurrence(
        &old.profile,
        &old.routes,
        &occurrence,
        transfer_command_body_bytes(&input),
    );
    let mut rotated = asset_transfer_policy();
    rotated.fee_owner = "vault".to_owned();
    let new = transfer_governance_with(vec![rotated], TRANSFER_POLICY_KINDS);
    assert_ne!(new.profile.profile_id, old.profile.profile_id);
    let new_refs = new.refs();
    let verifier = RecordingModuleReceiptVerifier::default();
    let fee_root_mismatch =
        AbiErrorV1::InvalidBinding("asset transfer lane module fee policy root");

    // Act / Assert: the stale fee root rejects at membership before the old
    // witness or any receipt bytes are compared.
    assert_eq!(
        bind_transfer(&new_refs, &occurrence, &input, &accepted).unwrap_err(),
        fee_root_mismatch
    );
    assert_eq!(
        verify_asset_transfer_lane_module_receipt_v1(
            transfer_receipt_candidate(
                &new_refs,
                &authenticated,
                &input,
                &accepted,
                &old_witness,
                b"stale-roots",
            ),
            &verifier,
        )
        .unwrap_err(),
        fee_root_mismatch
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn old_profile_authentication_with_coherent_rotated_policy_never_reaches_witness_or_verifier() {
    // Arrange: P1 owns the rotated policy, both roots, the context, and the
    // accepted output. The authenticated occurrence and occurrence id remain P0.
    let old = transfer_governance_with(vec![asset_transfer_policy()], TRANSFER_POLICY_KINDS);
    let old_refs = old.refs();
    let occurrence = occurrence(
        &old.profile,
        &old.routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let old_input = asset_input(&old.profile, &old.lanes, &occurrence, None);
    let AssetTransferLaneModuleResultV1::Accepted(old_accepted) =
        transition_asset_transfer_lane_module_v1(&old_input).unwrap()
    else {
        panic!("valid P0 transfer must accept")
    };
    let old_witness = bind_transfer(&old_refs, &occurrence, &old_input, &old_accepted).unwrap();
    let authenticated = authenticate_occurrence(
        &old.profile,
        &old.routes,
        &occurrence,
        transfer_command_body_bytes(&old_input),
    );

    let mut rotated = asset_transfer_policy();
    rotated.fee_owner = "vault".to_owned();
    let new = transfer_governance_with(vec![rotated], TRANSFER_POLICY_KINDS);
    let new_refs = new.refs();
    let mut spliced_input = asset_input(&new.profile, &new.lanes, &occurrence, None);
    spliced_input.context.profile_root = new.profile.profile_id.clone();
    spliced_input.pre_state.policies = new.registries.asset_policy_registry.policies.clone();
    spliced_input.asset_policy_registry_root = new
        .registries
        .asset_policy_registry
        .asset_policy_root()
        .unwrap();
    spliced_input.fee_policy_registry_root = new
        .registries
        .asset_policy_registry
        .fee_policy_root()
        .unwrap();
    for balance in &mut spliced_input.pre_state.balances {
        if balance.owner == "treasury" {
            balance.owner = "vault".to_owned();
        }
    }
    let AssetTransferLaneModuleResultV1::Accepted(spliced_accepted) =
        transition_asset_transfer_lane_module_v1(&spliced_input).unwrap()
    else {
        panic!("coherent P1 transfer must accept")
    };
    let verifier = RecordingModuleReceiptVerifier::default();
    let profile_mismatch = AbiErrorV1::InvalidBinding("lane module occurrence profile root");

    // Act / Assert
    assert_eq!(
        bind_transfer(&new_refs, &occurrence, &spliced_input, &spliced_accepted).unwrap_err(),
        profile_mismatch
    );
    assert_eq!(
        verify_asset_transfer_lane_module_receipt_v1(
            transfer_receipt_candidate(
                &new_refs,
                &authenticated,
                &spliced_input,
                &spliced_accepted,
                &old_witness,
                b"p0-auth-p1-policy",
            ),
            &verifier,
        )
        .unwrap_err(),
        profile_mismatch
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn transfer_receipt_registry_substitution_and_missing_binding_never_reach_verifier() {
    // Arrange: the honest fixture, a substituted typed registry, and a profile
    // that governs only the asset policy kind.
    let governance = transfer_governance_with(vec![asset_transfer_policy()], TRANSFER_POLICY_KINDS);
    let refs = governance.refs();
    let transfer_occurrence = occurrence(
        &governance.profile,
        &governance.routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let input = asset_input(
        &governance.profile,
        &governance.lanes,
        &transfer_occurrence,
        None,
    );
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let bound = bind_transfer(&refs, &transfer_occurrence, &input, &accepted).unwrap();
    let authenticated = authenticate_occurrence(
        &governance.profile,
        &governance.routes,
        &transfer_occurrence,
        transfer_command_body_bytes(&input),
    );
    let mut substituted = governance.registries.asset_policy_registry.clone();
    substituted.policies[0].transfer_fee_atoms = 1;
    let verifier = RecordingModuleReceiptVerifier::default();

    // Act / Assert: the substituted registry keeps the asset root and changes
    // the fee root, so the fee binding comparison rejects.
    let mut candidate =
        transfer_receipt_candidate(&refs, &authenticated, &input, &accepted, &bound, b"r");
    candidate.asset_policy_registry = &substituted;
    assert_eq!(
        verify_asset_transfer_lane_module_receipt_v1(candidate, &verifier).unwrap_err(),
        AbiErrorV1::InvalidBinding("asset transfer fee policy root")
    );
    assert!(verifier.calls.borrow().is_empty());

    // Arrange / Act / Assert: one governed binding is never enough.
    let one_binding = transfer_governance_with(
        vec![asset_transfer_policy()],
        &[ASSET_TRANSFER_ASSET_POLICY_KIND_V1],
    );
    let one_refs = one_binding.refs();
    let one_occurrence = occurrence(
        &one_binding.profile,
        &one_binding.routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let one_input = asset_input(
        &one_binding.profile,
        &one_binding.lanes,
        &one_occurrence,
        None,
    );
    let AssetTransferLaneModuleResultV1::Accepted(one_accepted) =
        transition_asset_transfer_lane_module_v1(&one_input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let one_authenticated = authenticate_occurrence_with_policy_registry(
        &one_binding.profile,
        &one_binding.routes,
        &one_occurrence,
        transfer_command_body_bytes(&one_input),
        &one_binding.registries.policy_registry,
    );
    let binding_absent = AbiErrorV1::InvalidBinding("economic policy binding absent from registry");
    let one_verifier = RecordingModuleReceiptVerifier::default();
    assert_eq!(
        bind_transfer(&one_refs, &one_occurrence, &one_input, &one_accepted).unwrap_err(),
        binding_absent
    );
    assert_eq!(
        verify_asset_transfer_lane_module_receipt_v1(
            transfer_receipt_candidate(
                &one_refs,
                &one_authenticated,
                &one_input,
                &one_accepted,
                &bound,
                b"one-binding",
            ),
            &one_verifier,
        )
        .unwrap_err(),
        binding_absent
    );
    assert!(one_verifier.calls.borrow().is_empty());
}

#[test]
fn module_receipt_rejects_empty_nonsuccinct_mutated_and_verifier_failure() {
    let (profile, lanes, coordinators, routes) = profile();
    let occurrence = occurrence(
        &profile,
        &routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let input = asset_input(&profile, &lanes, &occurrence, None);
    let registries = transfer_registries(&routes);
    let refs = TransferGovernanceRefs {
        profile: &profile,
        lanes: &lanes,
        coordinators: &coordinators,
        routes: &routes,
        registries: &registries,
    };
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let bound = bind_transfer(&refs, &occurrence, &input, &accepted).unwrap();
    let authenticated = authenticate_occurrence(
        &profile,
        &routes,
        &occurrence,
        canonical_economic_command_body_bytes_v1(&input.command.command_kind, &input.command)
            .unwrap(),
    );

    for (kind, bytes, expected_error) in [
        (
            ReceiptKindV1::SUCCINCT,
            &[][..],
            AbiErrorV1::InvalidBounds("lane module receipt bytes"),
        ),
        (
            ReceiptKindV1::COMPOSITE,
            &b"composite"[..],
            AbiErrorV1::InvalidBinding("lane module receipt kind"),
        ),
    ] {
        let verifier = RecordingModuleReceiptVerifier::default();
        assert_eq!(
            verify_asset_transfer_lane_module_receipt_v1(
                AssetTransferLaneModuleReceiptCandidateV1 {
                    profile: &profile,
                    policy_registry: &registries.policy_registry,
                    asset_policy_registry: &registries.asset_policy_registry,
                    lanes: &lanes,
                    coordinators: &coordinators,
                    routes: &routes,
                    authenticated_command: &authenticated,
                    module_input: &input,
                    accepted: &accepted,
                    release_route_binding: &bound,
                    receipt: LaneModuleReceiptEnvelopeV1 {
                        receipt_kind: kind,
                        receipt_bytes: bytes,
                    },
                },
                &verifier,
            )
            .unwrap_err(),
            expected_error
        );
        assert!(verifier.calls.borrow().is_empty());
    }

    let at_limit = vec![0xa5; MAX_LANE_MODULE_RECEIPT_BYTES_V1];
    let at_limit_verifier = RecordingModuleReceiptVerifier::default();
    verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &profile,
            policy_registry: &registries.policy_registry,
            asset_policy_registry: &registries.asset_policy_registry,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            authenticated_command: &authenticated,
            module_input: &input,
            accepted: &accepted,
            release_route_binding: &bound,
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: &at_limit,
            },
        },
        &at_limit_verifier,
    )
    .expect("receipt at the exact byte ceiling must remain admissible");
    assert_eq!(at_limit_verifier.calls.borrow().len(), 1);
    drop(at_limit_verifier);
    drop(at_limit);

    let over_limit = vec![0xa5; MAX_LANE_MODULE_RECEIPT_BYTES_V1 + 1];
    let over_limit_verifier = RecordingModuleReceiptVerifier::default();
    assert_eq!(
        verify_asset_transfer_lane_module_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1 {
                profile: &profile,
                policy_registry: &registries.policy_registry,
                asset_policy_registry: &registries.asset_policy_registry,
                lanes: &lanes,
                coordinators: &coordinators,
                routes: &routes,
                authenticated_command: &authenticated,
                module_input: &input,
                accepted: &accepted,
                release_route_binding: &bound,
                receipt: LaneModuleReceiptEnvelopeV1 {
                    receipt_kind: ReceiptKindV1::SUCCINCT,
                    receipt_bytes: &over_limit,
                },
            },
            &over_limit_verifier,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBounds("lane module receipt bytes")
    );
    assert!(over_limit_verifier.calls.borrow().is_empty());

    let mut substituted_input = input.clone();
    substituted_input.command.amount_atoms = 29;
    let AssetTransferLaneModuleResultV1::Accepted(substituted) =
        transition_asset_transfer_lane_module_v1(&substituted_input).unwrap()
    else {
        panic!("valid substituted transfer must accept")
    };
    let verifier = RecordingModuleReceiptVerifier::default();
    assert_eq!(
        verify_asset_transfer_lane_module_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1 {
                profile: &profile,
                policy_registry: &registries.policy_registry,
                asset_policy_registry: &registries.asset_policy_registry,
                lanes: &lanes,
                coordinators: &coordinators,
                routes: &routes,
                authenticated_command: &authenticated,
                module_input: &substituted_input,
                accepted: &substituted,
                release_route_binding: &bound,
                receipt: LaneModuleReceiptEnvelopeV1 {
                    receipt_kind: ReceiptKindV1::SUCCINCT,
                    receipt_bytes: b"succinct-module-receipt",
                },
            },
            &verifier,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module command body hash")
    );
    assert!(verifier.calls.borrow().is_empty());

    let rejecting_verifier = RecordingModuleReceiptVerifier {
        reject: true,
        ..Default::default()
    };
    assert_eq!(
        verify_asset_transfer_lane_module_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1 {
                profile: &profile,
                policy_registry: &registries.policy_registry,
                asset_policy_registry: &registries.asset_policy_registry,
                lanes: &lanes,
                coordinators: &coordinators,
                routes: &routes,
                authenticated_command: &authenticated,
                module_input: &input,
                accepted: &accepted,
                release_route_binding: &bound,
                receipt: LaneModuleReceiptEnvelopeV1 {
                    receipt_kind: ReceiptKindV1::SUCCINCT,
                    receipt_bytes: b"cryptographically-invalid",
                },
            },
            &rejecting_verifier,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("test verifier rejected module receipt")
    );
    assert_eq!(rejecting_verifier.calls.borrow().len(), 1);
}

#[test]
fn exact_verified_module_receipt_backs_structural_lane_composition() {
    let fixture = verified_asset_lane_fixture();
    let composition =
        compose_receipt_backed_asset_lane_single_v1(ReceiptBackedAssetLaneCompositionCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            coordinator_context: &fixture.context,
            module_journal: &fixture.accepted.module_journal,
            private_port: &fixture.accepted.private_port,
            module_effects: &fixture.accepted.effects,
            verified_module: &fixture.verified,
        })
        .expect("verified module must back exact structural composition");

    assert_eq!(composition.profile_id(), &fixture.profile.profile_id);
    assert_eq!(
        composition.authority_level(),
        LaneCompositionAuthorityLevelV1::RECEIPT_BACKED_STRUCTURAL_ONLY
    );
    assert_eq!(
        composition.command_occurrence_id(),
        &fixture.occurrence.occurrence_id().unwrap()
    );
    assert_eq!(
        composition.verified_module_binding_root(),
        &fixture.verified.binding_root().unwrap()
    );
    assert_eq!(
        composition.module_receipt_digest(),
        fixture.verified.receipt_digest()
    );
    assert_eq!(
        composition.binding_root().unwrap().as_str(),
        "0xde7d72f618133ee16bced50044c8198fcdf6b047c3037a5f7ac474242168845b"
    );
}

#[test]
fn valid_module_receipt_for_another_journal_rejects() {
    // Arrange: a second valid journal under the same governed policy, produced
    // from a different pre-state balance rather than an ungoverned fee row.
    let fixture = verified_asset_lane_fixture();
    let mut substituted_input = fixture.input.clone();
    substituted_input.pre_state.balances[1].amount_atoms = 11;
    substituted_input.pre_state.supplies[0].amount_atoms = 116;
    let AssetTransferLaneModuleResultV1::Accepted(substituted) =
        transition_asset_transfer_lane_module_v1(&substituted_input).unwrap()
    else {
        panic!("valid substituted transfer must accept")
    };
    let substituted_bound = bind_transfer(
        &fixture.refs(),
        &fixture.occurrence,
        &substituted_input,
        &substituted,
    )
    .unwrap();
    let substituted_authenticated = authenticate_occurrence(
        &fixture.profile,
        &fixture.routes,
        &fixture.occurrence,
        canonical_economic_command_body_bytes_v1(
            &substituted_input.command.command_kind,
            &substituted_input.command,
        )
        .unwrap(),
    );
    let substituted_verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &fixture.profile,
            policy_registry: &fixture.registries.policy_registry,
            asset_policy_registry: &fixture.registries.asset_policy_registry,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            authenticated_command: &substituted_authenticated,
            module_input: &substituted_input,
            accepted: &substituted,
            release_route_binding: &substituted_bound,
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"succinct-substituted-module-receipt-v1",
            },
        },
        &RecordingModuleReceiptVerifier::default(),
    )
    .unwrap();

    assert_eq!(
        compose_receipt_backed_asset_lane_single_v1(ReceiptBackedAssetLaneCompositionCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            coordinator_context: &fixture.context,
            module_journal: &fixture.accepted.module_journal,
            private_port: &fixture.accepted.private_port,
            module_effects: &fixture.accepted.effects,
            verified_module: &substituted_verified,
        },)
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("verified module journal root")
    );
}

#[test]
fn writer_epoch_both_neighbors_reject() {
    let fixture = verified_asset_lane_fixture();

    for writer_epoch in [
        fixture.profile.authority_epoch - 1,
        fixture.profile.authority_epoch + 1,
    ] {
        let mut context = fixture.context.clone();
        context.writer_epoch = writer_epoch;

        assert_eq!(
            compose_receipt_backed_asset_lane_single_v1(
                ReceiptBackedAssetLaneCompositionCandidateV1 {
                    profile: &fixture.profile,
                    lanes: &fixture.lanes,
                    coordinators: &fixture.coordinators,
                    routes: &fixture.routes,
                    occurrence: &fixture.occurrence,
                    coordinator_context: &context,
                    module_journal: &fixture.accepted.module_journal,
                    private_port: &fixture.accepted.private_port,
                    module_effects: &fixture.accepted.effects,
                    verified_module: &fixture.verified,
                },
            )
            .unwrap_err(),
            AbiErrorV1::InvalidBinding("receipt-backed lane domain bindings")
        );
    }
}

#[test]
fn private_port_one_defect_rejects_before_structural_output() {
    let fixture = verified_asset_lane_fixture();
    let mut private_port = fixture.accepted.private_port.clone();
    private_port.module_effect_plan_root = root(999);

    assert_eq!(
        compose_receipt_backed_asset_lane_single_v1(ReceiptBackedAssetLaneCompositionCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            coordinator_context: &fixture.context,
            module_journal: &fixture.accepted.module_journal,
            private_port: &private_port,
            module_effects: &fixture.accepted.effects,
            verified_module: &fixture.verified,
        })
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("asset lane coordinator PRIVATE_PORT_ROOT_MISMATCH")
    );
}

#[test]
fn effect_plan_one_defect_rejects_before_structural_output() {
    let fixture = verified_asset_lane_fixture();
    let mut effects = fixture.accepted.effects.clone();
    effects.occurrence_consumptions = vec![root(999)];

    assert_eq!(
        compose_receipt_backed_asset_lane_single_v1(ReceiptBackedAssetLaneCompositionCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            coordinator_context: &fixture.context,
            module_journal: &fixture.accepted.module_journal,
            private_port: &fixture.accepted.private_port,
            module_effects: &effects,
            verified_module: &fixture.verified,
        })
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("asset lane coordinator EFFECT_PLAN_MISMATCH")
    );
}

#[test]
fn lane_composition_receipt_uses_governed_image_and_exact_journal() {
    // Arrange
    let (fixture, lane_journal, structural, _lane_effects) = structural_asset_lane_fixture();
    let receipt_bytes = b"x";
    let verifier = RecordingCompositionReceiptVerifier::default();

    // Act
    let verified: VerifiedLaneCompositionV1 = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            structural_composition: &structural,
            lane_journal: &lane_journal,
            receipt: LaneCompositionReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes,
            },
        },
        &verifier,
    )
    .expect("one-byte succinct coordinator receipt must verify");

    // Assert
    let coordinator = fixture
        .coordinators
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .expect("asset coordinator release must exist");
    let lane_journal_bytes =
        zenodex_global_settlement_abi_v1::canonical_bytes_v1(&lane_journal).unwrap();
    assert_eq!(
        verifier.calls.into_inner(),
        vec![(
            receipt_bytes.to_vec(),
            coordinator.guest_image_id.clone(),
            lane_journal_bytes,
        )]
    );
    assert_eq!(verified.profile_id(), &fixture.profile.profile_id);
    assert_eq!(verified.route_release_id(), structural.route_release_id());
    assert_eq!(verified.lane_id(), LaneIdV1::ASSET_TRANSFER);
    assert_eq!(
        verified.coordinator_release_id(),
        &coordinator.coordinator_release_id
    );
    assert_eq!(
        verified.command_occurrence_id(),
        &fixture.occurrence.occurrence_id().unwrap()
    );
    assert_eq!(verified.writer_epoch(), fixture.profile.authority_epoch);
    assert_eq!(
        verified.structural_composition_root(),
        &structural.binding_root().unwrap()
    );
    assert_eq!(
        verified.lane_journal_root(),
        &lane_journal.journal_root().unwrap()
    );
    assert_eq!(verified.expected_image_id(), &coordinator.guest_image_id);
    assert_eq!(verified.receipt_kind(), ReceiptKindV1::SUCCINCT);
    assert_eq!(
        verified.lane_journal_digest().as_str(),
        "0xa1f3c8dea5c1128f577be2fa2792bc50296b305d1926c6c499af39913abe8134"
    );
    assert_eq!(
        verified.binding_root().unwrap().as_str(),
        "0x059c6a971e386affd42808a2b762f1f33eef7812965de481fa4e38eda83e1d91"
    );
}

#[test]
fn lane_composition_receipt_zero_and_wrong_kind_reject_before_verifier() {
    // Arrange
    let (fixture, lane_journal, structural, _lane_effects) = structural_asset_lane_fixture();

    for (receipt_kind, receipt_bytes, expected_error) in [
        (
            ReceiptKindV1::SUCCINCT,
            &[][..],
            AbiErrorV1::InvalidBounds("lane composition receipt bytes"),
        ),
        (
            ReceiptKindV1::COMPOSITE,
            &b"composite"[..],
            AbiErrorV1::InvalidBinding("lane composition receipt kind"),
        ),
    ] {
        let verifier = RecordingCompositionReceiptVerifier::default();

        // Act
        let error = verify_asset_lane_composition_receipt_v1(
            LaneCompositionReceiptCandidateV1 {
                profile: &fixture.profile,
                lanes: &fixture.lanes,
                coordinators: &fixture.coordinators,
                routes: &fixture.routes,
                occurrence: &fixture.occurrence,
                structural_composition: &structural,
                lane_journal: &lane_journal,
                receipt: LaneCompositionReceiptEnvelopeV1 {
                    receipt_kind,
                    receipt_bytes,
                },
            },
            &verifier,
        )
        .unwrap_err();

        // Assert
        assert_eq!(error, expected_error);
        assert!(verifier.calls.borrow().is_empty());
    }
}

#[test]
fn lane_composition_receipt_journal_substitution_rejects_before_verifier() {
    // Arrange
    let (fixture, mut lane_journal, structural, _lane_effects) = structural_asset_lane_fixture();
    lane_journal.post_lane_root = root(999);
    let verifier = RecordingCompositionReceiptVerifier::default();

    // Act
    let error = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            structural_composition: &structural,
            lane_journal: &lane_journal,
            receipt: LaneCompositionReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"succinct-lane-composition-receipt",
            },
        },
        &verifier,
    )
    .unwrap_err();

    // Assert
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("lane composition exact journal bindings")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn lane_composition_receipt_verifier_rejection_creates_no_witness() {
    // Arrange
    let (fixture, lane_journal, structural, _lane_effects) = structural_asset_lane_fixture();
    let verifier = RecordingCompositionReceiptVerifier {
        reject: true,
        ..Default::default()
    };

    // Act
    let error = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            structural_composition: &structural,
            lane_journal: &lane_journal,
            receipt: LaneCompositionReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"cryptographically-invalid",
            },
        },
        &verifier,
    )
    .unwrap_err();

    // Assert
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("test verifier rejected lane composition receipt")
    );
    assert_eq!(verifier.calls.borrow().len(), 1);
}

struct VerifiedRouteCompositionFixture {
    base: VerifiedAssetLaneFixture,
    lane_journal: LaneCompositionJournalV1,
    verified_lane: VerifiedLaneCompositionV1,
    route_journal: RouteCompositionJournalV1,
    effect_plan: GlobalEconomicEffectPlanV1,
}

impl VerifiedRouteCompositionFixture {
    fn candidate<'a>(
        &'a self,
        receipt_kind: ReceiptKindV1,
        receipt_bytes: &'a [u8],
    ) -> RouteCompositionReceiptCandidateV1<'a> {
        RouteCompositionReceiptCandidateV1 {
            profile: &self.base.profile,
            lanes: &self.base.lanes,
            coordinators: &self.base.coordinators,
            routes: &self.base.routes,
            occurrence: &self.base.occurrence,
            lane_journals: std::slice::from_ref(&self.lane_journal),
            verified_lanes: std::slice::from_ref(&self.verified_lane),
            route_journal: &self.route_journal,
            receipt: RouteCompositionReceiptEnvelopeV1 {
                receipt_kind,
                receipt_bytes,
            },
        }
    }
}

fn verified_route_composition_fixture_with_state_at(
    tx_index: u64,
    nonce: u64,
    pre_state_root: RootV1,
    post_state_root: RootV1,
    module_pre_state: Option<AssetTransferStateV1>,
) -> VerifiedRouteCompositionFixture {
    let (fixture, lane_journal, structural, effect_plan) =
        structural_asset_lane_fixture_with_state_at(
            tx_index,
            nonce,
            pre_state_root,
            module_pre_state,
        );
    let verified_lane = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
            structural_composition: &structural,
            lane_journal: &lane_journal,
            receipt: LaneCompositionReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"succinct-lane-composition-receipt-v1",
            },
        },
        &RecordingCompositionReceiptVerifier::default(),
    )
    .expect("valid lane composition receipt must verify");
    let route_journal = RouteCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: fixture.occurrence.chain_id.clone(),
        deployment_root: fixture.occurrence.deployment_root.clone(),
        profile_root: fixture.profile.profile_id.clone(),
        writer_epoch: fixture.profile.authority_epoch,
        route_release_id: fixture.occurrence.route_release_id.clone(),
        command_occurrence_id: fixture.occurrence.occurrence_id().unwrap(),
        ordered_lane_journal_roots: vec![lane_journal.journal_root().unwrap()],
        pre_state_root: fixture.occurrence.pre_state_root.clone(),
        post_state_root,
        effect_plan_root: lane_journal.effect_plan_root.clone(),
        terminal_obligations_root: lane_journal.terminal_obligations_root.clone(),
    };
    route_journal.validate().unwrap();
    VerifiedRouteCompositionFixture {
        base: fixture,
        lane_journal,
        verified_lane,
        route_journal,
        effect_plan,
    }
}

fn verified_route_composition_fixture_at(
    tx_index: u64,
    nonce: u64,
    pre_state_root: RootV1,
    post_state_root: RootV1,
) -> VerifiedRouteCompositionFixture {
    verified_route_composition_fixture_with_state_at(
        tx_index,
        nonce,
        pre_state_root,
        post_state_root,
        None,
    )
}

fn verified_route_composition_fixture() -> VerifiedRouteCompositionFixture {
    verified_route_composition_fixture_at(2, 9, root(2), root(8_001))
}

fn assert_verified_route_receipt(
    fixture: &VerifiedRouteCompositionFixture,
    verified: &VerifiedRouteCompositionV1,
    receipt_bytes: &[u8],
    calls: Vec<RecordedRouteReceiptVerifierCall>,
) {
    let route = fixture
        .base
        .routes
        .route_for_command(
            &fixture.base.occurrence.command_kind,
            Some(&fixture.base.occurrence.route_release_id),
        )
        .unwrap();
    let route_journal_bytes =
        zenodex_global_settlement_abi_v1::canonical_bytes_v1(&fixture.route_journal).unwrap();
    assert_eq!(
        calls,
        vec![(
            receipt_bytes.to_vec(),
            route.guest_image_id.clone(),
            route_journal_bytes,
        )]
    );
    assert_eq!(verified.profile_id(), &fixture.base.profile.profile_id);
    assert_eq!(verified.route_release_id(), &route.route_release_id);
    assert_eq!(
        verified.command_occurrence_id(),
        &fixture.base.occurrence.occurrence_id().unwrap()
    );
    assert_eq!(
        verified.writer_epoch(),
        fixture.base.profile.authority_epoch
    );
    assert_eq!(verified.ordered_lane_ids(), route.ordered_lanes.as_slice());
    assert_eq!(
        verified.ordered_lane_binding_roots(),
        &[fixture.verified_lane.binding_root().unwrap()]
    );
    assert_eq!(
        verified.ordered_lane_journal_roots(),
        &[fixture.lane_journal.journal_root().unwrap()]
    );
    assert_eq!(
        verified.route_journal_root(),
        &fixture.route_journal.journal_root().unwrap()
    );
    assert_eq!(verified.expected_image_id(), &route.guest_image_id);
    assert_eq!(verified.receipt_kind(), ReceiptKindV1::SUCCINCT);
    assert_eq!(
        verified.route_journal_digest().as_str(),
        "0x66e8b22cc5dbf2b924deee342e983cf0bfb6d4911e30f1c5760feda3a8bd60c0"
    );
    assert_eq!(
        verified.binding_root().unwrap().as_str(),
        "0x2d0169204490a146c2b52249d5d9df8ec77f2cf148ef057efad65228664c2151"
    );
}

#[test]
fn route_composition_receipt_uses_governed_image_and_exact_lane_witness() {
    // Arrange
    let fixture = verified_route_composition_fixture();
    let receipt_bytes = b"x";
    let verifier = RecordingRouteReceiptVerifier::default();

    // Act
    let verified: VerifiedRouteCompositionV1 = verify_route_composition_receipt_v1(
        fixture.candidate(ReceiptKindV1::SUCCINCT, receipt_bytes),
        &verifier,
    )
    .expect("one-byte succinct route receipt must verify");

    // Assert
    assert_verified_route_receipt(
        &fixture,
        &verified,
        receipt_bytes,
        verifier.calls.into_inner(),
    );
}

#[test]
fn route_composition_zero_missing_and_duplicate_lane_inputs_reject_before_verifier() {
    // Arrange
    let fixture = verified_route_composition_fixture();

    let cases = [
        (
            Vec::new(),
            vec![fixture.verified_lane.clone()],
            AbiErrorV1::InvalidBinding("route composition lane journal count"),
        ),
        (
            vec![fixture.lane_journal.clone()],
            Vec::new(),
            AbiErrorV1::InvalidBinding("route composition lane witness count"),
        ),
        (
            vec![fixture.lane_journal.clone(), fixture.lane_journal.clone()],
            vec![fixture.verified_lane.clone(), fixture.verified_lane.clone()],
            AbiErrorV1::InvalidBinding("route composition lane journal count"),
        ),
    ];
    for (lane_journals, verified_lanes, expected_error) in cases {
        let verifier = RecordingRouteReceiptVerifier::default();

        // Act
        let error = verify_route_composition_receipt_v1(
            RouteCompositionReceiptCandidateV1 {
                profile: &fixture.base.profile,
                lanes: &fixture.base.lanes,
                coordinators: &fixture.base.coordinators,
                routes: &fixture.base.routes,
                occurrence: &fixture.base.occurrence,
                lane_journals: &lane_journals,
                verified_lanes: &verified_lanes,
                route_journal: &fixture.route_journal,
                receipt: RouteCompositionReceiptEnvelopeV1 {
                    receipt_kind: ReceiptKindV1::SUCCINCT,
                    receipt_bytes: b"route-receipt",
                },
            },
            &verifier,
        )
        .unwrap_err();

        // Assert
        assert_eq!(error, expected_error);
        assert!(verifier.calls.borrow().is_empty());
    }
}

#[test]
fn valid_lane_witness_cannot_back_a_different_route_lane_journal() {
    // Arrange: preserve route structure while changing the consumed lane statement.
    let fixture = verified_route_composition_fixture();
    let mut substituted_lane_journal = fixture.lane_journal.clone();
    substituted_lane_journal.post_lane_root = root(8_004);
    let mut substituted_route_journal = fixture.route_journal.clone();
    substituted_route_journal.ordered_lane_journal_roots =
        vec![substituted_lane_journal.journal_root().unwrap()];
    let lane_journals = vec![substituted_lane_journal];
    let verified_lanes = vec![fixture.verified_lane.clone()];
    let verifier = RecordingRouteReceiptVerifier::default();

    // Act
    let error = verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1 {
            profile: &fixture.base.profile,
            lanes: &fixture.base.lanes,
            coordinators: &fixture.base.coordinators,
            routes: &fixture.base.routes,
            occurrence: &fixture.base.occurrence,
            lane_journals: &lane_journals,
            verified_lanes: &verified_lanes,
            route_journal: &substituted_route_journal,
            receipt: RouteCompositionReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"route-receipt",
            },
        },
        &verifier,
    )
    .unwrap_err();

    // Assert
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("route composition exact lane witness")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn route_composition_occurrence_and_epoch_neighbors_reject_before_verifier() {
    // Arrange
    let fixture = verified_route_composition_fixture();
    let mut substitutions = Vec::new();
    let mut occurrence_substitution = fixture.route_journal.clone();
    occurrence_substitution.command_occurrence_id = root(8_002);
    substitutions.push(occurrence_substitution);
    for writer_epoch in [
        fixture.base.profile.authority_epoch - 1,
        fixture.base.profile.authority_epoch + 1,
    ] {
        let mut epoch_substitution = fixture.route_journal.clone();
        epoch_substitution.writer_epoch = writer_epoch;
        substitutions.push(epoch_substitution);
    }

    for substituted_journal in substitutions {
        let verifier = RecordingRouteReceiptVerifier::default();

        // Act
        let mut candidate = fixture.candidate(ReceiptKindV1::SUCCINCT, b"route-receipt");
        candidate.route_journal = &substituted_journal;
        let error = verify_route_composition_receipt_v1(candidate, &verifier).unwrap_err();

        // Assert
        assert_eq!(
            error,
            AbiErrorV1::InvalidBinding("route composition exact route journal")
        );
        assert!(verifier.calls.borrow().is_empty());
    }
}

#[test]
fn route_composition_receipt_zero_and_wrong_kind_reject_before_verifier() {
    // Arrange
    let fixture = verified_route_composition_fixture();

    for (receipt_kind, receipt_bytes, expected_error) in [
        (
            ReceiptKindV1::SUCCINCT,
            &[][..],
            AbiErrorV1::InvalidBounds("route composition receipt bytes"),
        ),
        (
            ReceiptKindV1::COMPOSITE,
            &b"composite"[..],
            AbiErrorV1::InvalidBinding("route composition receipt kind"),
        ),
    ] {
        let verifier = RecordingRouteReceiptVerifier::default();

        // Act
        let error = verify_route_composition_receipt_v1(
            fixture.candidate(receipt_kind, receipt_bytes),
            &verifier,
        )
        .unwrap_err();

        // Assert
        assert_eq!(error, expected_error);
        assert!(verifier.calls.borrow().is_empty());
    }
}

#[test]
fn route_composition_verifier_rejection_creates_no_witness() {
    // Arrange
    let fixture = verified_route_composition_fixture();
    let verifier = RecordingRouteReceiptVerifier {
        reject: true,
        ..Default::default()
    };

    // Act
    let error = verify_route_composition_receipt_v1(
        fixture.candidate(
            ReceiptKindV1::SUCCINCT,
            b"cryptographically-invalid-route-receipt",
        ),
        &verifier,
    )
    .unwrap_err();

    // Assert
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("test verifier rejected route composition receipt")
    );
    assert_eq!(verifier.calls.borrow().len(), 1);
}

struct VerifiedEconomicEpochFixture {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    certificate: GlobalEconomicEpochCertificateV1,
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    occurrences: Vec<EconomicCommandOccurrenceV1>,
    command_body_hashes: Vec<RootV1>,
    route_journals: Vec<RouteCompositionJournalV1>,
    route_state_disclosures: Vec<EconomicEpochRouteStateDisclosureV1>,
    verified_routes: Vec<VerifiedRouteCompositionV1>,
    route_effect_plans: Vec<GlobalEconomicEffectPlanV1>,
    effect_plan: GlobalEconomicEffectPlanV1,
    receipt_bytes: Vec<u8>,
}

impl VerifiedEconomicEpochFixture {
    fn candidate(&self) -> EconomicEpochReceiptCandidateV1<'_> {
        EconomicEpochReceiptCandidateV1 {
            profile: &self.profile,
            lanes: &self.lanes,
            coordinators: &self.coordinators,
            routes: &self.routes,
            certificate: &self.certificate,
            pre_state: &self.pre_state,
            post_state: &self.post_state,
            command_occurrences: &self.occurrences,
            ordered_command_body_hashes: &self.command_body_hashes,
            route_journals: &self.route_journals,
            route_state_disclosures: &self.route_state_disclosures,
            verified_routes: &self.verified_routes,
            route_effect_plans: &self.route_effect_plans,
            effect_plan: &self.effect_plan,
            receipt_bytes: &self.receipt_bytes,
            expected_chain_id: &self.certificate.chain_id,
            expected_deployment_root: &self.certificate.deployment_root,
            expected_pre_state_root: &self.certificate.pre_state_root,
            expected_body_commitment: &self.certificate.body_commitment,
        }
    }
}

fn digest_root(bytes: &[u8], field: &'static str) -> RootV1 {
    RootV1::parse(format!("0x{}", hash_bytes_sha256_v1(bytes)), field, false)
        .expect("test digest must be a root")
}

fn empty_effect_plan() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

fn epoch_asset_module_state(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    routes: &RouteRegistryV1,
) -> AssetTransferStateV1 {
    let occurrence = occurrence(
        profile,
        routes,
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "alice",
        root(7),
    );
    let mut state = asset_input(profile, lanes, &occurrence, None).pre_state;
    let epoch_spend_atoms = 64_u128 * 32;
    state.balances[0].amount_atoms += epoch_spend_atoms;
    state.supplies[0].amount_atoms += epoch_spend_atoms;
    state
}

struct VerifiedEpochRouteSequence {
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    occurrences: Vec<EconomicCommandOccurrenceV1>,
    route_journals: Vec<RouteCompositionJournalV1>,
    route_state_disclosures: Vec<EconomicEpochRouteStateDisclosureV1>,
    verified_routes: Vec<VerifiedRouteCompositionV1>,
    route_effect_plans: Vec<GlobalEconomicEffectPlanV1>,
}

fn epoch_global_state(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    module_state: &AssetTransferStateV1,
    height: u64,
    replay_state: Vec<ReplayStateV1>,
) -> GlobalEconomicStateV1 {
    let transfer_registry = asset_transfer_policy_registry(&module_state.module_release_id);
    assert_eq!(transfer_registry.policies, module_state.policies);
    let asset_lane = project_asset_transfer_state_v1(
        module_state,
        &transfer_registry.asset_policy_root().unwrap(),
        &transfer_registry.fee_policy_root().unwrap(),
        vec![],
    )
    .expect("test asset state must project");
    GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-release-route-test".to_owned(),
        deployment_root: root(1),
        writer_epoch: profile.authority_epoch,
        height,
        profile_root: profile.profile_id.clone(),
        lane_roots: lanes
            .releases
            .iter()
            .enumerate()
            .map(|(index, release)| LaneStateRootV1 {
                lane_id: release.lane_id,
                module_release_id: release.release_id.clone(),
                enabled: release.status == ReleaseStatusV1::ACTIVE_NEW
                    && release.accepts_new_objects,
                state_root: if release.lane_id == LaneIdV1::ASSET_TRANSFER {
                    asset_lane.state_root().expect("test lane state must hash")
                } else {
                    root(60_000 + index as u64)
                },
            })
            .collect(),
        balances: module_state.balances.clone(),
        supplies: module_state.supplies.clone(),
        custody: vec![],
        liabilities: vec![],
        reserves: vec![],
        oracle_occurrences: vec![],
        replay_state,
        terminal_obligations: vec![],
        history_root: RootV1::parse(ZERO_ROOT_V1, "test history root", true).unwrap(),
        outbox: vec![],
    }
}

fn verified_epoch_route_sequence(count: usize) -> VerifiedEpochRouteSequence {
    verified_epoch_route_sequence_with_hidden_state(count, None, None)
}

fn verified_epoch_route_sequence_with_hidden_state(
    count: usize,
    hidden_balance_after: Option<usize>,
    hidden_height_after: Option<usize>,
) -> VerifiedEpochRouteSequence {
    assert!((1..=64).contains(&count));
    let (profile, lanes, _coordinators, routes) = profile();
    let mut occurrences = Vec::with_capacity(count);
    let mut route_journals = Vec::with_capacity(count);
    let mut route_state_disclosures = Vec::with_capacity(count);
    let mut verified_routes = Vec::with_capacity(count);
    let mut route_effect_plans = Vec::with_capacity(count);
    let mut module_state = epoch_asset_module_state(&profile, &lanes, &routes);
    let pre_state = epoch_global_state(&profile, &lanes, &module_state, 10, vec![]);
    let mut current_state = pre_state.clone();

    for index in 0..count {
        let mut fixture = verified_route_composition_fixture_with_state_at(
            index as u64,
            index as u64 + 1,
            current_state.state_root().unwrap(),
            root(80_000 + index as u64),
            Some(module_state),
        );
        assert_eq!(fixture.base.profile.profile_id, profile.profile_id);
        let occurrence_id = fixture.base.occurrence.occurrence_id().unwrap();
        let replay_id = fixture.base.occurrence.replay_id().unwrap();
        let mut replay_state = current_state.replay_state.clone();
        replay_state.push(ReplayStateV1 {
            replay_id: replay_id.to_string(),
            occurrence_id,
        });
        replay_state.sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
        let mut next_state = epoch_global_state(
            &profile,
            &lanes,
            &fixture.base.accepted.post_state,
            11,
            replay_state,
        );
        if hidden_balance_after == Some(index) {
            next_state.balances[0].amount_atoms += 1;
        }
        if hidden_height_after == Some(index) {
            next_state.height += 1;
        }
        fixture.route_journal.post_state_root = next_state.state_root().unwrap();
        let route_receipt_bytes = format!("succinct-route-receipt-{index}").into_bytes();
        let verified_route = verify_route_composition_receipt_v1(
            fixture.candidate(ReceiptKindV1::SUCCINCT, &route_receipt_bytes),
            &RecordingRouteReceiptVerifier::default(),
        )
        .expect("route receipt must verify before epoch admission");
        occurrences.push(fixture.base.occurrence.clone());
        route_effect_plans.push(fixture.effect_plan.clone());
        module_state = fixture.base.accepted.post_state.clone();
        route_state_disclosures.push(EconomicEpochRouteStateDisclosureV1 {
            lane_journals: vec![fixture.lane_journal.clone()],
            post_state: next_state.clone(),
        });
        route_journals.push(fixture.route_journal);
        verified_routes.push(verified_route);
        current_state = next_state;
    }
    VerifiedEpochRouteSequence {
        pre_state,
        post_state: current_state,
        occurrences,
        route_journals,
        route_state_disclosures,
        verified_routes,
        route_effect_plans,
    }
}

fn verified_epoch_statement(
    profile: &EconomicProfileSnapshotV1,
    routes: &VerifiedEpochRouteSequence,
) -> (
    GlobalEconomicEffectPlanV1,
    Vec<u8>,
    GlobalEconomicEpochCertificateV1,
) {
    let count = routes.occurrences.len();
    let effect_plan = compose_asset_lane_epoch_effect_plans_v1(&routes.route_effect_plans)
        .expect("connected route effects must compose");
    let receipt_bytes = format!("succinct-economic-epoch-receipt-{count}").into_bytes();
    let mut certificate = GlobalEconomicEpochCertificateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-release-route-test".to_owned(),
        deployment_root: root(1),
        profile_root: profile.profile_id.clone(),
        writer_epoch: profile.authority_epoch,
        height: 11,
        pre_state_root: routes.pre_state.state_root().unwrap(),
        post_state_root: routes.post_state.state_root().unwrap(),
        ordered_occurrence_ids: routes
            .occurrences
            .iter()
            .map(EconomicCommandOccurrenceV1::occurrence_id)
            .collect::<Result<Vec<_>, _>>()
            .expect("test occurrences must hash"),
        ordered_route_journal_roots: routes
            .route_journals
            .iter()
            .map(RouteCompositionJournalV1::journal_root)
            .collect::<Result<Vec<_>, _>>()
            .expect("test route journals must hash"),
        ordered_route_assumption_roots: routes
            .verified_routes
            .iter()
            .map(VerifiedRouteCompositionV1::assumption_root)
            .collect::<Result<Vec<_>, _>>()
            .expect("test route assumptions must hash"),
        module_leaf_occurrences: count as u64,
        aggregation_fanout: 8,
        aggregation_levels: u64::from(count > 8),
        effect_plan_root: effect_plan.effect_plan_root().unwrap(),
        terminal_obligations_root: RootV1::parse(
            ZERO_ROOT_V1,
            "test epoch terminal obligations root",
            true,
        )
        .expect("zero terminal root must parse"),
        body_commitment: root(90_001),
        data_availability_root: root(90_002),
        finality_root: root(90_003),
        source_manifest_root: root(90_004),
        toolchain_manifest_root: root(90_005),
        root_image_id: profile.root_image_id.clone(),
        receipt_root: digest_root(&receipt_bytes, "test epoch receipt root"),
        receipt_kind: ReceiptKindV1::SUCCINCT,
        journal_bytes: 1,
        cycle_budget: 1_000_000,
    };
    certificate.journal_bytes = certificate
        .canonical_journal_bytes()
        .expect("test epoch journal must encode")
        .len() as u64;
    certificate.validate().expect("test epoch must validate");
    (effect_plan, receipt_bytes, certificate)
}

fn verified_economic_epoch_fixture(count: usize) -> VerifiedEconomicEpochFixture {
    verified_economic_epoch_fixture_from_sequence(verified_epoch_route_sequence(count))
}

fn verified_economic_epoch_fixture_from_sequence(
    sequence: VerifiedEpochRouteSequence,
) -> VerifiedEconomicEpochFixture {
    let (profile, lanes, coordinators, routes) = profile();
    let (effect_plan, receipt_bytes, certificate) = verified_epoch_statement(&profile, &sequence);

    VerifiedEconomicEpochFixture {
        profile,
        lanes,
        coordinators,
        routes,
        certificate,
        pre_state: sequence.pre_state,
        post_state: sequence.post_state,
        command_body_hashes: sequence
            .occurrences
            .iter()
            .map(|occurrence| occurrence.command_body_hash.clone())
            .collect(),
        occurrences: sequence.occurrences,
        route_journals: sequence.route_journals,
        route_state_disclosures: sequence.route_state_disclosures,
        verified_routes: sequence.verified_routes,
        route_effect_plans: sequence.route_effect_plans,
        effect_plan,
        receipt_bytes,
    }
}

#[test]
fn economic_epoch_admits_exact_route_witnesses_at_one_eight_nine_and_sixty_four() {
    for count in [1, 8, 9, 64] {
        // Arrange
        let fixture = verified_economic_epoch_fixture(count);
        let verifier = RecordingEpochReceiptVerifier::default();

        // Act
        let verified = verify_economic_epoch_receipt_v1(fixture.candidate(), &verifier)
            .expect("bounded exact route witnesses must verify");

        // Assert
        assert_eq!(verified.ordered_route_binding_roots().len(), count);
        assert_eq!(
            verified.ordered_command_body_hashes(),
            fixture.command_body_hashes
        );
        assert_eq!(
            verified.route_state_projection_roots().unwrap().len(),
            count
        );
        assert_eq!(
            verified
                .route_state_effect_refinement_roots()
                .unwrap()
                .len(),
            count
        );
        assert_eq!(verified.certificate(), &fixture.certificate);
        assert_eq!(verified.effect_plan(), &fixture.effect_plan);
        assert_eq!(
            verified.effect_occurrences().len(),
            fixture
                .route_effect_plans
                .iter()
                .map(|plan| plan.rows.len())
                .sum::<usize>()
        );
        assert_eq!(
            verified
                .effect_occurrences()
                .iter()
                .map(|item| &item.effect_occurrence_id)
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            verified.effect_occurrences().len()
        );
        let mut offset = 0;
        for (occurrence, plan) in fixture.occurrences.iter().zip(&fixture.route_effect_plans) {
            let next = offset + plan.rows.len();
            let route_occurrences = &verified.effect_occurrences()[offset..next];
            assert!(route_occurrences.iter().enumerate().all(|(index, item)| {
                item.command_occurrence_id == occurrence.occurrence_id().unwrap()
                    && item.effect_index == u64::try_from(index).unwrap()
            }));
            offset = next;
        }
        assert_eq!(verified.receipt_digest(), &fixture.certificate.receipt_root);
        assert_eq!(
            verified.state_effect_refinement().pre_state_root(),
            &fixture.certificate.pre_state_root
        );
        assert_eq!(
            verified.state_effect_refinement().post_state_root(),
            &fixture.certificate.post_state_root
        );
        assert_eq!(verifier.calls.borrow().len(), 1);
        assert_eq!(verifier.calls.borrow()[0].1, fixture.profile.root_image_id);
        assert_eq!(
            verifier.calls.borrow()[0].2,
            fixture.certificate.canonical_journal_bytes().unwrap()
        );
    }
}

#[test]
fn economic_epoch_v1_quarantines_single_object_consumption_before_receipt() {
    // Arrange: retain a coherent occurrence/certificate identity while adding
    // one consumed object. ABI V1 cannot remember its nullifier across epochs.
    let fixture = verified_economic_epoch_fixture(1);
    let mut occurrences = fixture.occurrences.clone();
    occurrences[0].consumed_object_ids = vec![root(48_700).to_string()];
    let mut certificate = fixture.certificate.clone();
    certificate.ordered_occurrence_ids = occurrences
        .iter()
        .map(EconomicCommandOccurrenceV1::occurrence_id)
        .collect::<Result<Vec<_>, _>>()
        .expect("test occurrence must hash");
    certificate.journal_bytes = certificate
        .canonical_journal_bytes()
        .expect("test epoch journal must encode")
        .len() as u64;
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut candidate = fixture.candidate();
    candidate.certificate = &certificate;
    candidate.command_occurrences = &occurrences;

    // Act / Assert: no receipt verification can mint an epoch witness.
    assert_eq!(
        verify_economic_epoch_receipt_v1(candidate, &verifier).unwrap_err(),
        AbiErrorV1::InvalidBinding(
            "economic epoch V1 object consumption lacks durable nullifier state"
        )
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_occurrence_identity_binds_exact_command_body_hash() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(1);
    let occurrence = fixture.occurrences[0].clone();
    let mut changed_body = occurrence.clone();
    changed_body.command_body_hash = root(99_001);

    // Act / Assert
    assert_ne!(
        occurrence.occurrence_id().unwrap(),
        changed_body.occurrence_id().unwrap()
    );
    assert_eq!(
        occurrence.replay_id().unwrap(),
        changed_body.replay_id().unwrap()
    );
}

#[test]
fn economic_epoch_rejects_unpaired_command_body_hashes_before_receipt() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(1);
    let verifier = RecordingEpochReceiptVerifier::default();
    let empty = Vec::new();
    let extra = vec![fixture.command_body_hashes[0].clone(), root(99_002)];
    let substituted = vec![root(99_003)];

    // Act / Assert: 0, 2, and same-width substitution all fail before verification.
    for (hashes, expected) in [
        (
            &empty,
            AbiErrorV1::InvalidBinding("economic epoch occurrence count"),
        ),
        (
            &extra,
            AbiErrorV1::InvalidBinding("economic epoch occurrence count"),
        ),
        (
            &substituted,
            AbiErrorV1::InvalidBinding("economic epoch command body hash binding"),
        ),
    ] {
        assert_eq!(
            verify_economic_epoch_receipt_v1(
                EconomicEpochReceiptCandidateV1 {
                    ordered_command_body_hashes: hashes,
                    ..fixture.candidate()
                },
                &verifier,
            )
            .unwrap_err(),
            expected
        );
    }
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_two_route_state_evidence_has_stable_rust_golden_roots() {
    let fixture = verified_economic_epoch_fixture(2);
    assert_eq!(
        fixture.command_body_hashes,
        vec![
            fixture.occurrences[0].command_body_hash.clone(),
            fixture.occurrences[0].command_body_hash.clone(),
        ]
    );
    let verified = verify_economic_epoch_receipt_v1(
        fixture.candidate(),
        &RecordingEpochReceiptVerifier::default(),
    )
    .expect("two exact route transitions must verify");

    assert_eq!(
        verified.route_state_projection_roots().unwrap(),
        vec![
            RootV1::parse(
                "0x22f9ad725ade82167a8c896d391c8e8f4da4871f26f42be6cb6af5ad0e8f1824",
                "projection golden",
                false,
            )
            .unwrap(),
            RootV1::parse(
                "0xd4b998eaf8b75a0aadf94e91ff12f2876b7916246d805158a012af98f8afdcee",
                "projection golden",
                false,
            )
            .unwrap(),
        ]
    );
    assert_eq!(
        verified.route_state_effect_refinement_roots().unwrap(),
        vec![
            RootV1::parse(
                "0x673900afa1a4da52bdb8345fb5c4d26cf283e60537b4f60fa5de3812a8c26c81",
                "refinement golden",
                false,
            )
            .unwrap(),
            RootV1::parse(
                "0xed90dde7cca5beb632c14e526d6872f04e5853e13f85f82215effe9e57383e2f",
                "refinement golden",
                false,
            )
            .unwrap(),
        ]
    );
}

#[test]
fn economic_epoch_route_state_disclosures_reject_count_neighbors_before_receipt() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(1);
    let empty = Vec::new();
    let extra = vec![
        fixture.route_state_disclosures[0].clone(),
        fixture.route_state_disclosures[0].clone(),
    ];

    for disclosures in [&empty, &extra] {
        let verifier = RecordingEpochReceiptVerifier::default();
        let mut candidate = fixture.candidate();
        candidate.route_state_disclosures = disclosures;

        // Act
        let error = verify_economic_epoch_receipt_v1(candidate, &verifier).unwrap_err();

        // Assert
        assert_eq!(
            error,
            AbiErrorV1::InvalidBinding("economic epoch route state disclosure count")
        );
        assert!(verifier.calls.borrow().is_empty());
    }
}

#[test]
fn economic_epoch_route_state_projection_rejects_hidden_intermediate_lane_mutation() {
    // Arrange: alter an unselected lane only in the first disclosed intermediate state.
    let fixture = verified_economic_epoch_fixture(2);
    let mut disclosures = fixture.route_state_disclosures.clone();
    disclosures[0].post_state.lane_roots[1].state_root = root(88_101);
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut candidate = fixture.candidate();
    candidate.route_state_disclosures = &disclosures;

    // Act
    let error = verify_economic_epoch_receipt_v1(candidate, &verifier).unwrap_err();

    // Assert
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("route global projection exact global context")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_route_refinement_rejects_transient_hidden_balance() {
    // Arrange: route one injects one unlabelled atom into full state. Route two
    // restores the honest endpoint while every route/lane witness remains coherent.
    let sequence = verified_epoch_route_sequence_with_hidden_state(2, Some(0), None);
    let fixture = verified_economic_epoch_fixture_from_sequence(sequence);
    let verifier = RecordingEpochReceiptVerifier::default();

    // Act
    let error = verify_economic_epoch_receipt_v1(fixture.candidate(), &verifier).unwrap_err();

    // Assert
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("economic refinement balance delta mismatch")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_route_refinement_rejects_transient_hidden_height() {
    // Arrange: route one temporarily advances beyond the occurrence epoch;
    // route two restores the valid endpoint while all state roots are rebuilt.
    let sequence = verified_epoch_route_sequence_with_hidden_state(2, None, Some(0));
    let fixture = verified_economic_epoch_fixture_from_sequence(sequence);
    let verifier = RecordingEpochReceiptVerifier::default();

    // Act
    let error = verify_economic_epoch_receipt_v1(fixture.candidate(), &verifier).unwrap_err();

    // Assert
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("route economic refinement epoch height context")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_rejects_global_effect_plan_unrelated_to_verified_route_effects() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(1);
    let unrelated_effect_plan = empty_effect_plan();
    let mut substituted_certificate = fixture.certificate.clone();
    substituted_certificate.effect_plan_root = unrelated_effect_plan.effect_plan_root().unwrap();
    substituted_certificate.journal_bytes = substituted_certificate
        .canonical_journal_bytes()
        .unwrap()
        .len() as u64;
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut candidate = fixture.candidate();
    candidate.certificate = &substituted_certificate;
    candidate.effect_plan = &unrelated_effect_plan;

    // Act
    let error = verify_economic_epoch_receipt_v1(candidate, &verifier).unwrap_err();

    // Assert
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("economic epoch route effect plan aggregation")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_rejects_route_effect_plan_with_wrong_committed_root() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(1);
    let foreign = verified_route_composition_fixture_at(1, 2, root(2), root(80_000));
    let substituted_effect_plans = vec![foreign.effect_plan];
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut candidate = fixture.candidate();
    candidate.route_effect_plans = &substituted_effect_plans;

    // Act
    let error = verify_economic_epoch_receipt_v1(candidate, &verifier).unwrap_err();

    // Assert
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("economic epoch route effect plan root")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_state_refinement_rejects_missing_replay_before_receipt() {
    // Arrange: rebuild the authenticated route and certificate around a post-state
    // that omits the occurrence's required replay insertion.
    let fixture = verified_economic_epoch_fixture(1);
    let mut defective_post = fixture.post_state.clone();
    defective_post.replay_state.clear();
    let mut route_fixture = verified_route_composition_fixture_with_state_at(
        0,
        1,
        fixture.pre_state.state_root().unwrap(),
        defective_post.state_root().unwrap(),
        Some(epoch_asset_module_state(
            &fixture.profile,
            &fixture.lanes,
            &fixture.routes,
        )),
    );
    route_fixture.route_journal.post_state_root = defective_post.state_root().unwrap();
    let verified_route = verify_route_composition_receipt_v1(
        route_fixture.candidate(ReceiptKindV1::SUCCINCT, b"succinct-route-replay-mutant"),
        &RecordingRouteReceiptVerifier::default(),
    )
    .expect("mutant route remains structurally receipt-backed");
    let route_journals = vec![route_fixture.route_journal.clone()];
    let verified_routes = vec![verified_route];
    let route_effect_plans = vec![route_fixture.effect_plan.clone()];
    let effect_plan = compose_asset_lane_epoch_effect_plans_v1(&route_effect_plans).unwrap();
    let mut certificate = fixture.certificate.clone();
    certificate.post_state_root = defective_post.state_root().unwrap();
    certificate.ordered_route_journal_roots = vec![route_journals[0].journal_root().unwrap()];
    certificate.ordered_route_assumption_roots =
        vec![verified_routes[0].assumption_root().unwrap()];
    certificate.effect_plan_root = effect_plan.effect_plan_root().unwrap();
    certificate.journal_bytes = certificate.canonical_journal_bytes().unwrap().len() as u64;
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut candidate = fixture.candidate();
    candidate.certificate = &certificate;
    candidate.post_state = &defective_post;
    candidate.route_journals = &route_journals;
    candidate.verified_routes = &verified_routes;
    candidate.route_effect_plans = &route_effect_plans;
    candidate.effect_plan = &effect_plan;

    // Act
    let error = verify_economic_epoch_receipt_v1(candidate, &verifier).unwrap_err();

    // Assert: the epoch receipt verifier is never reached.
    assert_eq!(
        error,
        AbiErrorV1::InvalidBinding("economic refinement replay state delta mismatch")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn asset_lane_epoch_effect_composer_rejects_zero_and_sixty_five_plans() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(1);
    let empty = Vec::new();
    let oversized = vec![fixture.route_effect_plans[0].clone(); 65];

    // Act / Assert
    assert_eq!(
        compose_asset_lane_epoch_effect_plans_v1(&empty).unwrap_err(),
        AbiErrorV1::InvalidBounds("asset lane epoch route effect plan count")
    );
    assert_eq!(
        compose_asset_lane_epoch_effect_plans_v1(&oversized).unwrap_err(),
        AbiErrorV1::InvalidBounds("asset lane epoch route effect plan count")
    );
}

#[test]
fn asset_lane_epoch_effect_composer_rejects_disconnected_histories() {
    // Arrange: lane roots must connect in route order.
    let fixture = verified_economic_epoch_fixture(2);
    let mut disconnected_lane = fixture.route_effect_plans.clone();
    disconnected_lane[1].lane_writes[0].pre_root = root(99_001);

    // Act / Assert
    assert_eq!(
        compose_asset_lane_epoch_effect_plans_v1(&disconnected_lane).unwrap_err(),
        AbiErrorV1::InvalidBinding("asset lane epoch lane write history")
    );

    // Arrange: per-asset conservation snapshots must also connect.
    let mut disconnected_conservation = fixture.route_effect_plans;
    let second = &mut disconnected_conservation[1].asset_conservation[0];
    second.owned_and_custodied_pre_atoms += 1;
    second.owned_and_custodied_post_atoms += 1;
    second.supply_pre_atoms += 1;
    second.supply_post_atoms += 1;

    // Act / Assert
    assert_eq!(
        compose_asset_lane_epoch_effect_plans_v1(&disconnected_conservation).unwrap_err(),
        AbiErrorV1::Conservation("asset lane epoch conservation history")
    );
}

#[test]
fn asset_lane_epoch_effect_composer_rejects_duplicate_and_overflowed_totals() {
    // Arrange: duplicate consumption remains invalid across individually valid plans.
    let fixture = verified_economic_epoch_fixture(2);
    let mut duplicate = fixture.route_effect_plans.clone();
    duplicate[1].occurrence_consumptions = duplicate[0].occurrence_consumptions.clone();

    // Act / Assert
    assert_eq!(
        compose_asset_lane_epoch_effect_plans_v1(&duplicate).unwrap_err(),
        AbiErrorV1::InvalidOrder("asset lane epoch occurrence consumptions")
    );

    // Arrange: each signed row is valid alone; the aggregate exceeds i128.
    let mut overflow = fixture.route_effect_plans;
    let first_index = overflow[0]
        .rows
        .iter()
        .position(|row| {
            row.kind == EconomicEffectKindV1::ACCOUNT_MOVEMENT && row.principal == "alice"
        })
        .expect("asset fixture must debit alice");
    let second_index = overflow[1]
        .rows
        .iter()
        .position(|row| {
            row.kind == EconomicEffectKindV1::ACCOUNT_MOVEMENT && row.principal == "alice"
        })
        .expect("asset fixture must debit alice");
    overflow[0].rows[first_index].delta_atoms = i128::MAX;
    overflow[1].rows[second_index].delta_atoms = 1;

    // Act / Assert
    assert_eq!(
        compose_asset_lane_epoch_effect_plans_v1(&overflow).unwrap_err(),
        AbiErrorV1::InvalidBounds("asset lane epoch effect total")
    );

    // Arrange: distinct fee principals avoid signed-row aggregation while the
    // common asset fee total exceeds u128 on the third valid route plan.
    let mut fee_overflow = verified_economic_epoch_fixture(3).route_effect_plans;
    for (index, plan) in fee_overflow.iter_mut().enumerate() {
        let fee_row = plan
            .rows
            .iter_mut()
            .find(|row| row.kind == EconomicEffectKindV1::FEE_ALLOCATION)
            .expect("asset fixture must allocate a fee");
        fee_row.principal = format!("fee_owner_{index}");
        fee_row.delta_atoms = i128::MAX;
        plan.fee_conservation[0].fee_charged_atoms = i128::MAX as u128;
        plan.fee_conservation[0].current_allocations_atoms = i128::MAX as u128;
    }

    // Act / Assert
    assert_eq!(
        compose_asset_lane_epoch_effect_plans_v1(&fee_overflow).unwrap_err(),
        AbiErrorV1::InvalidBounds("asset lane epoch fee total")
    );
}

#[test]
fn asset_lane_epoch_effect_composer_rejects_outbox_and_terminal_scope_expansion() {
    // Arrange: the current same-ledger composer has no external-delivery law.
    let fixture = verified_economic_epoch_fixture(1);
    let mut outbox = fixture.route_effect_plans.clone();
    outbox[0].external_outbox_enqueue = vec![ExternalOutboxEnqueueV1 {
        effect_id: root(99_010),
        destination_id: "ethereum:test".to_owned(),
        payload_hash: root(99_011),
        adapter_profile_root: root(99_012),
    }];

    // Act / Assert
    assert_eq!(
        compose_asset_lane_epoch_effect_plans_v1(&outbox).unwrap_err(),
        AbiErrorV1::InvalidBinding("asset lane epoch external outbox")
    );

    // Arrange: terminal-obligation aggregation remains outside this release.
    let mut certificate = fixture.certificate.clone();
    certificate.terminal_obligations_root = root(99_013);
    certificate.journal_bytes = certificate.canonical_journal_bytes().unwrap().len() as u64;
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut candidate = fixture.candidate();
    candidate.certificate = &certificate;

    // Act / Assert
    assert_eq!(
        verify_economic_epoch_receipt_v1(candidate, &verifier).unwrap_err(),
        AbiErrorV1::InvalidBinding("economic epoch terminal composition")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_certificate_binds_exact_guest_route_assumption_roots() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(1);
    let witness = &fixture.verified_routes[0];
    let expected = derive_route_composition_assumption_root_v1(
        witness.profile_id(),
        witness.route_release_id(),
        witness.command_occurrence_id(),
        witness.writer_epoch(),
        witness.route_journal_root(),
        witness.route_journal_digest(),
        witness.expected_image_id(),
    )
    .expect("exact route assumption must hash");
    assert_eq!(witness.assumption_root().unwrap(), expected);
    assert_eq!(
        fixture.certificate.ordered_route_assumption_roots,
        vec![expected]
    );
    let mut substituted = fixture.certificate.clone();
    substituted.ordered_route_assumption_roots = vec![root(98_999)];
    substituted.journal_bytes = substituted.canonical_journal_bytes().unwrap().len() as u64;
    let verifier = RecordingEpochReceiptVerifier::default();

    // Act
    let result = verify_economic_epoch_receipt_v1(
        EconomicEpochReceiptCandidateV1 {
            certificate: &substituted,
            ..fixture.candidate()
        },
        &verifier,
    );

    // Assert
    assert!(matches!(
        result,
        Err(AbiErrorV1::InvalidBinding(
            "economic epoch route assumption roots"
        ))
    ));
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_missing_foreign_and_journal_substituted_route_witnesses_reject() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(1);
    let empty_routes = Vec::new();
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut missing = fixture.candidate();
    missing.verified_routes = &empty_routes;

    // Act / Assert
    assert_eq!(
        verify_economic_epoch_receipt_v1(missing, &verifier).unwrap_err(),
        AbiErrorV1::InvalidBinding("economic epoch route witness count")
    );
    assert!(verifier.calls.borrow().is_empty());

    // Arrange: a valid witness for a distinct occurrence must remain foreign.
    let foreign_fixture = verified_route_composition_fixture_at(1, 2, root(2), root(80_000));
    let foreign_receipt = b"succinct-foreign-route-receipt";
    let foreign_verified = verify_route_composition_receipt_v1(
        foreign_fixture.candidate(ReceiptKindV1::SUCCINCT, foreign_receipt),
        &RecordingRouteReceiptVerifier::default(),
    )
    .unwrap();
    let foreign_routes = vec![foreign_verified];
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut foreign = fixture.candidate();
    foreign.verified_routes = &foreign_routes;

    // Act / Assert
    assert_eq!(
        verify_economic_epoch_receipt_v1(foreign, &verifier).unwrap_err(),
        AbiErrorV1::InvalidBinding("economic epoch exact route witness")
    );
    assert!(verifier.calls.borrow().is_empty());

    // Arrange: preserve a valid epoch shape while changing its route journal.
    let mut substituted_journals = fixture.route_journals.clone();
    substituted_journals[0].post_state_root = root(99_999);
    let mut substituted_certificate = fixture.certificate.clone();
    substituted_certificate.post_state_root = substituted_journals[0].post_state_root.clone();
    substituted_certificate.ordered_route_journal_roots =
        vec![substituted_journals[0].journal_root().unwrap()];
    substituted_certificate.journal_bytes = substituted_certificate
        .canonical_journal_bytes()
        .unwrap()
        .len() as u64;
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut substituted = fixture.candidate();
    substituted.certificate = &substituted_certificate;
    substituted.route_journals = &substituted_journals;

    // Act / Assert
    assert_eq!(
        verify_economic_epoch_receipt_v1(substituted, &verifier).unwrap_err(),
        AbiErrorV1::InvalidBinding("economic epoch exact route witness")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_reordered_occurrences_and_routes_reject_before_verifier() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(2);
    let mut occurrences = fixture.occurrences.clone();
    let mut route_journals = fixture.route_journals.clone();
    let mut verified_routes = fixture.verified_routes.clone();
    let mut route_effect_plans = fixture.route_effect_plans.clone();
    occurrences.reverse();
    let command_body_hashes = occurrences
        .iter()
        .map(|occurrence| occurrence.command_body_hash.clone())
        .collect::<Vec<_>>();
    route_journals.reverse();
    verified_routes.reverse();
    route_effect_plans.reverse();
    let mut certificate = fixture.certificate.clone();
    certificate.ordered_occurrence_ids = occurrences
        .iter()
        .map(EconomicCommandOccurrenceV1::occurrence_id)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    certificate.ordered_route_journal_roots = route_journals
        .iter()
        .map(RouteCompositionJournalV1::journal_root)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    certificate.journal_bytes = certificate.canonical_journal_bytes().unwrap().len() as u64;
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut candidate = fixture.candidate();
    candidate.certificate = &certificate;
    candidate.command_occurrences = &occurrences;
    candidate.ordered_command_body_hashes = &command_body_hashes;
    candidate.route_journals = &route_journals;
    candidate.verified_routes = &verified_routes;
    candidate.route_effect_plans = &route_effect_plans;

    // Act / Assert
    assert_eq!(
        verify_economic_epoch_receipt_v1(candidate, &verifier).unwrap_err(),
        AbiErrorV1::InvalidOrder("economic epoch command occurrences")
    );
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn economic_epoch_wrong_kind_empty_receipt_and_verifier_rejection_create_no_witness() {
    // Arrange
    let fixture = verified_economic_epoch_fixture(1);
    let mut wrong_kind_certificate = fixture.certificate.clone();
    wrong_kind_certificate.receipt_kind = ReceiptKindV1::COMPOSITE;
    let verifier = RecordingEpochReceiptVerifier::default();
    let mut wrong_kind = fixture.candidate();
    wrong_kind.certificate = &wrong_kind_certificate;

    // Act / Assert
    assert_eq!(
        verify_economic_epoch_receipt_v1(wrong_kind, &verifier).unwrap_err(),
        AbiErrorV1::InvalidBinding("economic epoch receipt kind")
    );
    assert!(verifier.calls.borrow().is_empty());

    let verifier = RecordingEpochReceiptVerifier::default();
    let mut empty = fixture.candidate();
    empty.receipt_bytes = b"";
    assert_eq!(
        verify_economic_epoch_receipt_v1(empty, &verifier).unwrap_err(),
        AbiErrorV1::InvalidBounds("economic epoch receipt bytes")
    );
    assert!(verifier.calls.borrow().is_empty());

    let verifier = RecordingEpochReceiptVerifier {
        reject: true,
        ..Default::default()
    };
    assert_eq!(
        verify_economic_epoch_receipt_v1(fixture.candidate(), &verifier).unwrap_err(),
        AbiErrorV1::InvalidBinding("test verifier rejected economic epoch receipt")
    );
    assert_eq!(verifier.calls.borrow().len(), 1);
}
