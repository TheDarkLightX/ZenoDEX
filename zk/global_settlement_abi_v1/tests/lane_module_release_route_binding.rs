use std::cell::RefCell;

use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    bind_asset_transfer_lane_output_to_release_route_v1,
    bind_managed_asset_lifecycle_lane_output_to_release_route_v1,
    compose_asset_lane_epoch_effect_plans_v1, compose_asset_lane_single_v1,
    compose_receipt_backed_asset_lane_single_v1, derive_route_composition_assumption_root_v1,
    hash_bytes_sha256_v1, hash_global_v1, transition_asset_transfer_lane_module_v1,
    transition_managed_asset_lifecycle_lane_module_v1, verify_asset_lane_composition_receipt_v1,
    verify_asset_transfer_lane_module_receipt_v1, verify_economic_epoch_receipt_v1,
    verify_managed_asset_lifecycle_lane_module_receipt_v1, verify_route_composition_receipt_v1,
    AbiErrorV1, AssetLaneCompositionResultV1, AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1, AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1,
    AssetTransferLaneModuleAcceptedV1, AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleReceiptCandidateV1, AssetTransferLaneModuleResultV1,
    AssetTransferPolicyV1, AssetTransferStateV1, EconomicAmountV1, EconomicCommandOccurrenceV1,
    EconomicEffectKindV1, EconomicEpochReceiptCandidateV1, EconomicEpochSuccinctReceiptVerifierV1,
    EconomicProfileSnapshotV1, EvidenceStatusV1, ExternalOutboxEnqueueV1,
    GlobalEconomicEffectPlanV1, GlobalEconomicEpochCertificateV1, LaneCompositionAuthorityLevelV1,
    LaneCompositionJournalV1, LaneCompositionReceiptCandidateV1, LaneCompositionReceiptEnvelopeV1,
    LaneCompositionSuccinctReceiptVerifierV1, LaneCoordinatorRegistryV1, LaneCoordinatorReleaseV1,
    LaneIdV1, LaneModuleReceiptEnvelopeV1, LaneModuleReleaseV1,
    LaneModuleSuccinctReceiptVerifierV1, LaneRegistryV1, ManagedAssetClassV1,
    ManagedAssetLifecycleCommandV1, ManagedAssetLifecycleContextV1,
    ManagedAssetLifecycleLaneModuleInputV1, ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
    ManagedAssetLifecycleLaneModuleResultV1, ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleStateV1, ProfileStatusV1, ReceiptBackedAssetLaneCompositionCandidateV1,
    ReceiptBackedAssetLaneCompositionV1, ReceiptKindV1, ReleaseStatusV1, RootV1,
    RouteCompositionJournalV1, RouteCompositionReceiptCandidateV1,
    RouteCompositionReceiptEnvelopeV1, RouteCompositionSuccinctReceiptVerifierV1, RouteRegistryV1,
    RouteReleaseV1, VerifiedLaneCompositionV1, VerifiedLaneModuleTransitionV1,
    VerifiedRouteCompositionV1, ALL_LANE_IDS_V1, ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
    GLOBAL_SETTLEMENT_ABI_V1, MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1, ZERO_ROOT_V1,
};

type RecordedModuleReceiptVerifierCall = (Vec<u8>, RootV1, Vec<u8>);
type RecordedCompositionReceiptVerifierCall = (Vec<u8>, RootV1, Vec<u8>);
type RecordedRouteReceiptVerifierCall = (Vec<u8>, RootV1, Vec<u8>);
type RecordedEpochReceiptVerifierCall = (Vec<u8>, RootV1, Vec<u8>);

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
    let ordered_lanes = vec![LaneIdV1::ASSET_TRANSFER];
    let module_release_ids = vec![release_id.clone()];
    let dependency_roles = vec!["VALUE_OWNER".to_owned()];
    let port_schema_roots = vec![root(500 + index)];
    let guest_image_id = root(520 + index);
    let specification_root = root(530 + index);
    let source_root = root(540 + index);
    let toolchain_root = root(550 + index);
    let oracle_policy_root = root(510);
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

fn profile() -> (
    EconomicProfileSnapshotV1,
    LaneRegistryV1,
    LaneCoordinatorRegistryV1,
    RouteRegistryV1,
) {
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
    let lane_registry_root = lanes.registry_root().unwrap();
    let lane_coordinator_registry_root = coordinators.registry_root().unwrap();
    let route_registry_root = routes.registry_root().unwrap();
    let proof_shape_root = root(520);
    let root_image_id = root(521);
    let verifier_registry_root = root(522);
    let migration_registry_root = root(523);
    let policy_registry_root = root(524);
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
        .validate_registries(&lanes, &coordinators, &routes)
        .expect("test profile must bind registries");
    (profile, lanes, coordinators, routes)
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
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-release-route-test".to_owned(),
        deployment_root: root(1),
        height: 11,
        tx_index: 2,
        op_index: 3,
        command_kind: command_kind.to_owned(),
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
    let release_id = module_release_id.unwrap_or_else(|| {
        lanes
            .release_for(LaneIdV1::ASSET_TRANSFER)
            .unwrap()
            .release_id
            .clone()
    });
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
            policies: vec![AssetTransferPolicyV1 {
                asset: "USD".to_owned(),
                fee_owner: "treasury".to_owned(),
                transfer_fee_atoms: 2,
                enabled: true,
            }],
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
        asset_policy_registry_root: root(11),
        fee_policy_registry_root: root(12),
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
            policies: vec![ManagedAssetLifecyclePolicyV1 {
                asset: "USD".to_owned(),
                asset_class: ManagedAssetClassV1::REGISTERED_ORDINARY_TOKEN,
                issue_authority_subject: Some("issuer".to_owned()),
                issue_policy_root: Some(root(5)),
                burn_policy_root: Some(root(6)),
                enabled: true,
            }],
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
        asset_policy_registry_root: root(11),
        fee_policy_registry_root: root(12),
        custody: vec![],
    }
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
    let bound = bind_asset_transfer_lane_output_to_release_route_v1(
        &profile,
        &lanes,
        &coordinators,
        &routes,
        &transfer_occurrence,
        &transfer_input,
        &transfer,
    )
    .expect("valid transfer output must bind");
    assert_eq!(bound.profile_id(), &profile.profile_id);
    assert_eq!(bound.lane_id(), LaneIdV1::ASSET_TRANSFER);
    assert_eq!(bound.route_lane_index(), 0);
    assert_eq!(
        bound.statement_root(),
        &transfer_input.statement_root().unwrap()
    );
    assert_eq!(
        bound.binding_root().unwrap().as_str(),
        "0x8c984258df8fd4c7f20ad262ac180e5a91d0ba2da1997831bebf3d8ca7608724"
    );

    for (command_kind, subject_id, grant_root) in [
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", root(6)),
    ] {
        let occurrence = occurrence(&profile, &routes, command_kind, subject_id, grant_root);
        let input = managed_input(&profile, &lanes, &occurrence, command_kind);
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) =
            transition_managed_asset_lifecycle_lane_module_v1(&input).unwrap()
        else {
            panic!("valid managed lifecycle command must accept")
        };
        let bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            &profile,
            &lanes,
            &coordinators,
            &routes,
            &occurrence,
            &input,
            &accepted,
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
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };

    let mut wrong_route = occurrence.clone();
    wrong_route.route_release_id = root(998);
    assert_eq!(
        bind_asset_transfer_lane_output_to_release_route_v1(
            &profile,
            &lanes,
            &coordinators,
            &routes,
            &wrong_route,
            &input,
            &accepted,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("caller-selected route does not match governed route")
    );

    let mut inactive = profile.clone();
    inactive.status = ProfileStatusV1::SHADOW;
    assert_eq!(
        bind_asset_transfer_lane_output_to_release_route_v1(
            &inactive,
            &lanes,
            &coordinators,
            &routes,
            &occurrence,
            &input,
            &accepted,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("economic profile is not active")
    );

    let mut wrong_chain = occurrence.clone();
    wrong_chain.chain_id = "other-chain".to_owned();
    assert_eq!(
        bind_asset_transfer_lane_output_to_release_route_v1(
            &profile,
            &lanes,
            &coordinators,
            &routes,
            &wrong_chain,
            &input,
            &accepted,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module chain id")
    );

    let foreign_input = asset_input(&profile, &lanes, &occurrence, Some(root(997)));
    let AssetTransferLaneModuleResultV1::Accepted(foreign) =
        transition_asset_transfer_lane_module_v1(&foreign_input).unwrap()
    else {
        panic!("internally consistent foreign release must evaluate")
    };
    assert_eq!(
        bind_asset_transfer_lane_output_to_release_route_v1(
            &profile,
            &lanes,
            &coordinators,
            &routes,
            &occurrence,
            &foreign_input,
            &foreign,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module release mismatch")
    );
}

#[test]
fn managed_issue_occurrence_cannot_authorize_a_burn_output() {
    let (profile, lanes, coordinators, routes) = profile();
    let issue_occurrence = occurrence(
        &profile,
        &routes,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        "alice",
        root(6),
    );
    let burn_input = managed_input(
        &profile,
        &lanes,
        &issue_occurrence,
        MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    );
    let ManagedAssetLifecycleLaneModuleResultV1::Accepted(burn) =
        transition_managed_asset_lifecycle_lane_module_v1(&burn_input).unwrap()
    else {
        panic!("valid self-burn must accept")
    };
    assert_eq!(
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            &profile,
            &lanes,
            &coordinators,
            &routes,
            &issue_occurrence,
            &burn_input,
            &burn,
        )
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
    occurrence: EconomicCommandOccurrenceV1,
    input: AssetTransferLaneModuleInputV1,
    accepted: Box<AssetTransferLaneModuleAcceptedV1>,
    verified: VerifiedLaneModuleTransitionV1,
    context: AssetLaneCoordinatorContextV1,
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
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let bound = bind_asset_transfer_lane_output_to_release_route_v1(
        &profile,
        &lanes,
        &coordinators,
        &routes,
        &occurrence,
        &input,
        &accepted,
    )
    .unwrap();
    let verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &profile,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            occurrence: &occurrence,
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
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let bound = bind_asset_transfer_lane_output_to_release_route_v1(
        &profile,
        &lanes,
        &coordinators,
        &routes,
        &occurrence,
        &input,
        &accepted,
    )
    .unwrap();
    let verifier = RecordingModuleReceiptVerifier::default();
    let receipt_bytes = b"succinct-asset-transfer-module-receipt-v1";

    let verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &profile,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            occurrence: &occurrence,
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
        "0xff9d4232a72f8e1039d6afd78ae92052aaca8f29b5d7bd0dd7cf7b6ec50c844f"
    );
    assert_eq!(
        verified.module_journal_digest().as_str(),
        "0x0cf2ba41acceffc7fbaa961960537eb9d55fa2b893c239cfe86960ea63799123"
    );
    assert_eq!(
        verified.receipt_digest().as_str(),
        "0x02506ee4d450a18d7af3b72483d252996ec25283526c04c424d5de64cd42fe05"
    );
}

#[test]
fn managed_module_receipts_gain_release_image_bound_authority() {
    let (profile, lanes, coordinators, routes) = profile();
    for (command_kind, subject_id, grant_root) in [
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", root(6)),
    ] {
        let occurrence = occurrence(&profile, &routes, command_kind, subject_id, grant_root);
        let input = managed_input(&profile, &lanes, &occurrence, command_kind);
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) =
            transition_managed_asset_lifecycle_lane_module_v1(&input).unwrap()
        else {
            panic!("valid managed lifecycle command must accept")
        };
        let bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            &profile,
            &lanes,
            &coordinators,
            &routes,
            &occurrence,
            &input,
            &accepted,
        )
        .unwrap();
        let verifier = RecordingModuleReceiptVerifier::default();

        let verified = verify_managed_asset_lifecycle_lane_module_receipt_v1(
            ManagedAssetLifecycleLaneModuleReceiptCandidateV1 {
                profile: &profile,
                lanes: &lanes,
                coordinators: &coordinators,
                routes: &routes,
                occurrence: &occurrence,
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
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&input).unwrap()
    else {
        panic!("valid transfer must accept")
    };
    let bound = bind_asset_transfer_lane_output_to_release_route_v1(
        &profile,
        &lanes,
        &coordinators,
        &routes,
        &occurrence,
        &input,
        &accepted,
    )
    .unwrap();

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
                    lanes: &lanes,
                    coordinators: &coordinators,
                    routes: &routes,
                    occurrence: &occurrence,
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
                lanes: &lanes,
                coordinators: &coordinators,
                routes: &routes,
                occurrence: &occurrence,
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
        AbiErrorV1::InvalidBinding("lane module structural binding")
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
                lanes: &lanes,
                coordinators: &coordinators,
                routes: &routes,
                occurrence: &occurrence,
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
        "0xee2fd20b3a047f1bb86c014decaaeeca38603fd935af8c2fa7c8a0fd3b97d839"
    );
}

#[test]
fn valid_module_receipt_for_another_journal_rejects() {
    let fixture = verified_asset_lane_fixture();
    let mut substituted_input = fixture.input.clone();
    substituted_input.command.amount_atoms = 29;
    let AssetTransferLaneModuleResultV1::Accepted(substituted) =
        transition_asset_transfer_lane_module_v1(&substituted_input).unwrap()
    else {
        panic!("valid substituted transfer must accept")
    };
    let substituted_bound = bind_asset_transfer_lane_output_to_release_route_v1(
        &fixture.profile,
        &fixture.lanes,
        &fixture.coordinators,
        &fixture.routes,
        &fixture.occurrence,
        &substituted_input,
        &substituted,
    )
    .unwrap();
    let substituted_verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &fixture.profile,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            occurrence: &fixture.occurrence,
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
        "0x9ce2b12b41782f3e1f7ecf5afdc83cc4b3e863de4d62d2efafd6e3770efd6e51"
    );
    assert_eq!(
        verified.binding_root().unwrap().as_str(),
        "0x033c60a4fcf6dbf3c6d9b3893106060bcb344ff0662e149322bfb3ffce8037cb"
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
        "0xe2a86aaaaca9ed4e25fb58a3e11471073ce3c3dc6779033f22d9c0e105522af5"
    );
    assert_eq!(
        verified.binding_root().unwrap().as_str(),
        "0xfc0d847ff20c8a00aef5865eb65d51aca7b7b6ff70246c03b070a8a190d1e817"
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
    occurrences: Vec<EconomicCommandOccurrenceV1>,
    route_journals: Vec<RouteCompositionJournalV1>,
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
            command_occurrences: &self.occurrences,
            route_journals: &self.route_journals,
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
    pre_state_root: RootV1,
    post_state_root: RootV1,
    occurrences: Vec<EconomicCommandOccurrenceV1>,
    route_journals: Vec<RouteCompositionJournalV1>,
    verified_routes: Vec<VerifiedRouteCompositionV1>,
    route_effect_plans: Vec<GlobalEconomicEffectPlanV1>,
}

fn verified_epoch_route_sequence(count: usize) -> VerifiedEpochRouteSequence {
    assert!((1..=64).contains(&count));
    let (profile, lanes, _coordinators, routes) = profile();
    let mut occurrences = Vec::with_capacity(count);
    let mut route_journals = Vec::with_capacity(count);
    let mut verified_routes = Vec::with_capacity(count);
    let mut route_effect_plans = Vec::with_capacity(count);
    let pre_state_root = root(2);
    let mut current_root = pre_state_root.clone();
    let mut module_state = epoch_asset_module_state(&profile, &lanes, &routes);

    for index in 0..count {
        let next_root = root(80_000 + index as u64);
        let fixture = verified_route_composition_fixture_with_state_at(
            index as u64,
            index as u64 + 1,
            current_root,
            next_root.clone(),
            Some(module_state),
        );
        assert_eq!(fixture.base.profile.profile_id, profile.profile_id);
        let route_receipt_bytes = format!("succinct-route-receipt-{index}").into_bytes();
        let verified_route = verify_route_composition_receipt_v1(
            fixture.candidate(ReceiptKindV1::SUCCINCT, &route_receipt_bytes),
            &RecordingRouteReceiptVerifier::default(),
        )
        .expect("route receipt must verify before epoch admission");
        occurrences.push(fixture.base.occurrence.clone());
        route_effect_plans.push(fixture.effect_plan.clone());
        module_state = fixture.base.accepted.post_state.clone();
        route_journals.push(fixture.route_journal);
        verified_routes.push(verified_route);
        current_root = next_root;
    }
    VerifiedEpochRouteSequence {
        pre_state_root,
        post_state_root: current_root,
        occurrences,
        route_journals,
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
        pre_state_root: routes.pre_state_root.clone(),
        post_state_root: routes.post_state_root.clone(),
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
    let (profile, lanes, coordinators, routes) = profile();
    let sequence = verified_epoch_route_sequence(count);
    let (effect_plan, receipt_bytes, certificate) = verified_epoch_statement(&profile, &sequence);

    VerifiedEconomicEpochFixture {
        profile,
        lanes,
        coordinators,
        routes,
        certificate,
        occurrences: sequence.occurrences,
        route_journals: sequence.route_journals,
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
        assert_eq!(verified.certificate(), &fixture.certificate);
        assert_eq!(verified.effect_plan(), &fixture.effect_plan);
        assert_eq!(verified.receipt_digest(), &fixture.certificate.receipt_root);
        assert_eq!(verifier.calls.borrow().len(), 1);
        assert_eq!(verifier.calls.borrow()[0].1, fixture.profile.root_image_id);
        assert_eq!(
            verifier.calls.borrow()[0].2,
            fixture.certificate.canonical_journal_bytes().unwrap()
        );
    }
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
