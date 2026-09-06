// Closed custody semantic selection and custody-release route binding.
//
// The reviewed bundle root selects the custody-complete family only when the
// governed module, coordinator, and single `ASSET_TRANSFER` route lane all
// carry it as their specification root. Every fixture is a coherent governed
// graph: release ids, registry roots, profile id, occurrence, and module
// context are rebuilt from the varied roots. Rejection before the custody
// recomputation is observed through a deterministic seam: the legacy
// acceptance for the same input recomputes differently under the custody
// family, so it is rejected by recomputation when the roots match and by the
// semantic guard when they do not.

use serde_json::json;
use zenodex_global_settlement_abi_v1::*;

const BUNDLE_BYTES: &[u8] =
    include_bytes!("../../../docs/specifications/asset-transfer-custody-semantic-bundle-v1.json");
const SHARED_GOLDEN_BYTES: &[u8] =
    include_bytes!("../../../tests/data/asset_transfer_custody_release_binding_v1_golden.json");
const BUNDLE_DOMAIN: &str = "zenodex/asset-transfer-custody-semantic-bundle/v1";
const BUNDLE_SCHEMA: &str = "zenodex/asset-transfer-custody-semantic-bundle/v1";
const BUNDLE_FAMILY: &str = "CUSTODY_COMPLETE_V1";
const BUNDLE_BYTE_SHA256: &str = "4b16964671cd4e4f4585437ad632eb5aa13fee17a5f49c65a96b59335b43ba72";
const BUNDLE_ROOT: &str = "0x02e297f6d65affbae54509516e6c5816e60e994ef2c674495884072cd0939df1";
const MODULE_SEED: u64 = 116;
const COORDINATOR_SEED: u64 = 316;
const ROUTE_SEED: u64 = 560;

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn bundle_root() -> RootV1 {
    RootV1::parse(
        ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1,
        "reviewed bundle root",
        false,
    )
    .expect("reviewed bundle root must parse")
}

fn unknown_root() -> RootV1 {
    root(0xdead_c0de)
}

fn recomputation_mismatch() -> AbiErrorV1 {
    AbiErrorV1::InvalidBinding("custody-complete supplied acceptance differs from recomputation")
}

fn legacy_recomputation_mismatch() -> AbiErrorV1 {
    AbiErrorV1::InvalidBinding("asset transfer supplied acceptance differs from recomputation")
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

fn custody_rows(amount_atoms: u128) -> Vec<EconomicAmountV1> {
    if amount_atoms == 0 {
        return Vec::new();
    }
    vec![EconomicAmountV1 {
        owner: "vault".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "escrow".to_owned(),
        amount_atoms,
    }]
}

/// Identity one governed role advertises; only `specification_root` selects.
#[derive(Clone)]
struct RoleIdentity {
    specification_root: RootV1,
    semantic_version: String,
    guest_image_id: RootV1,
    source_root: RootV1,
    toolchain_root: RootV1,
}

impl RoleIdentity {
    /// Opaque legacy-style roots that name no reviewed bundle.
    fn opaque(seed: u64) -> Self {
        Self {
            specification_root: root(seed + 2),
            semantic_version: "1.0.0-test".to_owned(),
            guest_image_id: root(seed + 1),
            source_root: root(seed + 3),
            toolchain_root: root(seed + 4),
        }
    }

    /// The reviewed bundle as specification subject over opaque build roots.
    fn bundle(seed: u64) -> Self {
        Self {
            specification_root: bundle_root(),
            ..Self::opaque(seed)
        }
    }
}

/// Fixture knobs; `matching` is the accepted custody-complete governance.
#[derive(Clone)]
struct Options {
    module: RoleIdentity,
    coordinator: RoleIdentity,
    route: RoleIdentity,
    extra_route_lane: bool,
    lane_status: (ReleaseStatusV1, bool),
    route_status: (ReleaseStatusV1, bool),
    profile_status: ProfileStatusV1,
    authority_epoch: u64,
    module_journal_byte_ceiling: u64,
    custody: Vec<EconomicAmountV1>,
}

impl Options {
    fn matching(custody: Vec<EconomicAmountV1>) -> Self {
        Self {
            module: RoleIdentity::bundle(MODULE_SEED),
            coordinator: RoleIdentity::bundle(COORDINATOR_SEED),
            route: RoleIdentity::bundle(ROUTE_SEED),
            extra_route_lane: false,
            lane_status: (ReleaseStatusV1::ACTIVE_NEW, true),
            route_status: (ReleaseStatusV1::ACTIVE_NEW, true),
            profile_status: ProfileStatusV1::ACTIVE,
            authority_epoch: 7,
            module_journal_byte_ceiling: 65_536,
            custody,
        }
    }

    fn opaque(custody: Vec<EconomicAmountV1>) -> Self {
        Self {
            module: RoleIdentity::opaque(MODULE_SEED),
            coordinator: RoleIdentity::opaque(COORDINATOR_SEED),
            route: RoleIdentity::opaque(ROUTE_SEED),
            ..Self::matching(custody)
        }
    }

    fn roles_mut(&mut self) -> [&mut RoleIdentity; 3] {
        [&mut self.module, &mut self.coordinator, &mut self.route]
    }
}

fn lane_release(lane_id: LaneIdV1, ordinal: u64, options: &Options) -> LaneModuleReleaseV1 {
    let selected = lane_id == LaneIdV1::ASSET_TRANSFER;
    let extra = options.extra_route_lane && lane_id == LaneIdV1::SPOT_LIQUIDITY;
    let offset = 100 + ordinal * 16;
    let identity = if selected {
        options.module.clone()
    } else {
        RoleIdentity::opaque(offset)
    };
    let (status, accepts_new_objects) = if selected {
        options.lane_status
    } else if extra {
        (ReleaseStatusV1::ACTIVE_NEW, true)
    } else {
        (ReleaseStatusV1::SHADOW, false)
    };
    let command_variants = if selected || extra {
        vec![ASSET_TRANSFER_COMMAND_KIND_V1.to_owned()]
    } else {
        Vec::new()
    };
    let evidence_statuses = if selected || extra {
        active_evidence()
    } else {
        vec![EvidenceStatusV1::DISABLED_PROVED_NO_WRITER]
    };
    let mut release = LaneModuleReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        release_id: root(1),
        semantic_version: identity.semantic_version,
        state_schema_root: root(offset),
        command_variants,
        terminal_command_variants: Vec::new(),
        guest_image_id: identity.guest_image_id,
        specification_root: identity.specification_root,
        source_root: identity.source_root,
        toolchain_root: identity.toolchain_root,
        terminal_coverage_root: root(offset + 5),
        migration_compatibility_root: root(offset + 6),
        max_cycles: 1_000_000,
        max_journal_bytes: if selected {
            options.module_journal_byte_ceiling
        } else {
            65_536
        },
        status,
        accepts_new_objects,
        evidence_statuses,
    };
    release.release_id = hash_global_v1(
        "global-lane-module-release-content-v1",
        &json!({
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
        }),
    )
    .expect("lane release content must hash");
    release
}

fn coordinator_release(
    lane_id: LaneIdV1,
    ordinal: u64,
    options: &Options,
) -> LaneCoordinatorReleaseV1 {
    let selected = lane_id == LaneIdV1::ASSET_TRANSFER;
    let active = selected || (options.extra_route_lane && lane_id == LaneIdV1::SPOT_LIQUIDITY);
    let offset = 300 + ordinal * 16;
    let identity = if selected {
        options.coordinator.clone()
    } else {
        RoleIdentity::opaque(offset)
    };
    let mut release = LaneCoordinatorReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        coordinator_release_id: root(1),
        semantic_version: identity.semantic_version,
        coordinator_schema_root: root(offset),
        guest_image_id: identity.guest_image_id,
        specification_root: identity.specification_root,
        source_root: identity.source_root,
        toolchain_root: identity.toolchain_root,
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: if active {
            ReleaseStatusV1::ACTIVE_NEW
        } else {
            ReleaseStatusV1::SHADOW
        },
        accepts_new_objects: active,
        evidence_statuses: if active {
            active_evidence()
        } else {
            vec![EvidenceStatusV1::DISABLED_PROVED_NO_WRITER]
        },
    };
    release.coordinator_release_id = hash_global_v1(
        "global-lane-coordinator-release-content-v1",
        &json!({
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "lane_id": release.lane_id,
            "coordinator_schema_root": release.coordinator_schema_root,
            "guest_image_id": release.guest_image_id,
            "specification_root": release.specification_root,
            "source_root": release.source_root,
            "toolchain_root": release.toolchain_root,
            "max_cycles": release.max_cycles,
            "max_journal_bytes": release.max_journal_bytes,
        }),
    )
    .expect("coordinator release content must hash");
    release
}

fn route_release(lanes: &LaneRegistryV1, options: &Options) -> RouteReleaseV1 {
    let mut ordered_lanes = vec![LaneIdV1::ASSET_TRANSFER];
    let mut dependency_roles = vec!["VALUE_OWNER".to_owned()];
    let mut port_schema_roots = vec![root(500)];
    if options.extra_route_lane {
        ordered_lanes.push(LaneIdV1::SPOT_LIQUIDITY);
        dependency_roles.push("LIQUIDITY_MIRROR".to_owned());
        port_schema_roots.push(root(501));
    }
    let module_release_ids: Vec<RootV1> = ordered_lanes
        .iter()
        .map(|lane_id| {
            lanes
                .release_for(*lane_id)
                .expect("route lane release must exist")
                .release_id
                .clone()
        })
        .collect();
    let (status, accepts_new_objects) = options.route_status;
    let identity = options.route.clone();
    let mut route = RouteReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        route_release_id: root(1),
        semantic_version: identity.semantic_version,
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        ordered_lanes,
        module_release_ids,
        dependency_roles,
        port_schema_roots,
        guest_image_id: identity.guest_image_id,
        specification_root: identity.specification_root,
        source_root: identity.source_root,
        toolchain_root: identity.toolchain_root,
        oracle_policy_root: root(510),
        issue_burn_policy_root: root(511),
        max_cycles: 2_000_000,
        max_journal_bytes: 131_072,
        status,
        accepts_new_objects,
        evidence_statuses: active_evidence(),
    };
    route.route_release_id = hash_global_v1(
        "global-route-release-content-v1",
        &json!({
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "command_kind": route.command_kind,
            "ordered_lanes": route.ordered_lanes,
            "module_release_ids": route.module_release_ids,
            "dependency_roles": route.dependency_roles,
            "port_schema_roots": route.port_schema_roots,
            "guest_image_id": route.guest_image_id,
            "specification_root": route.specification_root,
            "source_root": route.source_root,
            "toolchain_root": route.toolchain_root,
            "oracle_policy_root": route.oracle_policy_root,
            "issue_burn_policy_root": route.issue_burn_policy_root,
            "max_cycles": route.max_cycles,
            "max_journal_bytes": route.max_journal_bytes,
        }),
    )
    .expect("route release content must hash");
    route
}

fn asset_policy_registry(module_release_id: &RootV1) -> AssetTransferPolicyRegistryV1 {
    AssetTransferPolicyRegistryV1 {
        schema: ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1.to_owned(),
        module_release_id: module_release_id.clone(),
        policies: vec![AssetTransferPolicyV1 {
            asset: "USD".to_owned(),
            fee_owner: "treasury".to_owned(),
            transfer_fee_atoms: 2,
            enabled: true,
        }],
    }
}

fn policy_registry(registry: &AssetTransferPolicyRegistryV1) -> EconomicPolicyRegistryV1 {
    let binding = |policy_kind: &str, policy_root: RootV1| EconomicPolicyBindingV1 {
        policy_kind: policy_kind.to_owned(),
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        policy_root,
    };
    EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![
            binding(
                ASSET_TRANSFER_ASSET_POLICY_KIND_V1,
                registry.asset_policy_root().expect("asset policy root"),
            ),
            binding(
                ASSET_TRANSFER_FEE_POLICY_KIND_V1,
                registry.fee_policy_root().expect("fee policy root"),
            ),
        ],
    }
}

fn profile_snapshot(
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
    policy_registry_root: RootV1,
    status: ProfileStatusV1,
    authority_epoch: u64,
) -> EconomicProfileSnapshotV1 {
    let lane_registry_root = lanes.registry_root().expect("lane registry must hash");
    let lane_coordinator_registry_root = coordinators
        .registry_root()
        .expect("coordinator registry must hash");
    let route_registry_root = routes.registry_root().expect("route registry must hash");
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "authority_epoch": authority_epoch,
        "lane_registry_root": lane_registry_root,
        "lane_coordinator_registry_root": lane_coordinator_registry_root,
        "route_registry_root": route_registry_root,
        "proof_shape_root": root(520),
        "root_image_id": root(521),
        "verifier_registry_root": root(522),
        "migration_registry_root": root(523),
        "policy_registry_root": policy_registry_root,
        "terminal_registry_root": root(525),
    });
    EconomicProfileSnapshotV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        profile_id: hash_global_v1("global-economic-profile-content-v1", &content)
            .expect("profile content must hash"),
        authority_epoch,
        lane_registry_root,
        lane_coordinator_registry_root,
        route_registry_root,
        proof_shape_root: root(520),
        root_image_id: root(521),
        verifier_registry_root: root(522),
        migration_registry_root: root(523),
        policy_registry_root,
        terminal_registry_root: root(525),
        status,
    }
}

fn command() -> AssetTransferCommandV1 {
    AssetTransferCommandV1 {
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        sender: "alice".to_owned(),
        recipient: "bob".to_owned(),
        amount_atoms: 30,
        max_fee_atoms: 2,
    }
}

fn occurrence(
    profile: &EconomicProfileSnapshotV1,
    route: &RouteReleaseV1,
) -> EconomicCommandOccurrenceV1 {
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-custody-release-test".to_owned(),
        deployment_root: root(1),
        height: 11,
        tx_index: 2,
        op_index: 3,
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        command_body_hash: command().command_body_hash().expect("command must hash"),
        route_release_id: route.route_release_id.clone(),
        subject_id: "alice".to_owned(),
        grant_root: root(7),
        nonce: 9,
        profile_root: profile.profile_id.clone(),
        pre_state_root: root(2),
        consumed_object_ids: Vec::new(),
    }
}

fn module_input(
    profile: &EconomicProfileSnapshotV1,
    release_id: &RootV1,
    occurrence: &EconomicCommandOccurrenceV1,
    custody: Vec<EconomicAmountV1>,
) -> AssetTransferLaneModuleInputV1 {
    let registry = asset_policy_registry(release_id);
    let custodied_atoms: u128 = custody.iter().map(|row| row.amount_atoms).sum();
    let balance = |owner: &str, amount_atoms: u128| EconomicAmountV1 {
        owner: owner.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "accounts".to_owned(),
        amount_atoms,
    };
    AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: occurrence.chain_id.clone(),
            deployment_root: occurrence.deployment_root.clone(),
            profile_root: occurrence.profile_root.clone(),
            writer_epoch: profile.authority_epoch,
            module_release_id: release_id.clone(),
            command_occurrence_id: occurrence.occurrence_id().expect("occurrence must hash"),
            subject_id: occurrence.subject_id.clone(),
            grant_root: occurrence.grant_root.clone(),
        },
        pre_state: AssetTransferStateV1 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: release_id.clone(),
            policies: registry.policies.clone(),
            balances: vec![
                balance("alice", 100),
                balance("bob", 10),
                balance("treasury", 5),
            ],
            supplies: vec![AssetSupplyV1 {
                asset: "USD".to_owned(),
                amount_atoms: 115 + custodied_atoms,
            }],
        },
        command: command(),
        asset_policy_registry_root: registry.asset_policy_root().expect("asset policy root"),
        fee_policy_registry_root: registry.fee_policy_root().expect("fee policy root"),
        custody,
    }
}

/// One coherent governed graph plus the transfer it executes.
struct Governance {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    policy_registry: EconomicPolicyRegistryV1,
    asset_policy_registry: AssetTransferPolicyRegistryV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: AssetTransferLaneModuleInputV1,
}

impl Governance {
    fn build(options: &Options) -> Self {
        let lanes = LaneRegistryV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            releases: ALL_LANE_IDS_V1
                .iter()
                .enumerate()
                .map(|(index, lane_id)| lane_release(*lane_id, index as u64 + 1, options))
                .collect(),
        };
        let coordinators = LaneCoordinatorRegistryV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            releases: ALL_LANE_IDS_V1
                .iter()
                .enumerate()
                .map(|(index, lane_id)| coordinator_release(*lane_id, index as u64 + 1, options))
                .collect(),
        };
        let routes = RouteRegistryV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            routes: vec![route_release(&lanes, options)],
        };
        let release_id = lanes
            .release_for(LaneIdV1::ASSET_TRANSFER)
            .expect("asset release must exist")
            .release_id
            .clone();
        let asset_policy_registry = asset_policy_registry(&release_id);
        let policy_registry = policy_registry(&asset_policy_registry);
        let profile = profile_snapshot(
            &lanes,
            &coordinators,
            &routes,
            policy_registry
                .registry_root()
                .expect("policy registry must hash"),
            options.profile_status,
            options.authority_epoch,
        );
        let occurrence = occurrence(&profile, &routes.routes[0]);
        let module_input =
            module_input(&profile, &release_id, &occurrence, options.custody.clone());
        Self {
            profile,
            lanes,
            coordinators,
            routes,
            policy_registry,
            asset_policy_registry,
            occurrence,
            module_input,
        }
    }

    fn candidate<'a>(
        &'a self,
        accepted: &'a AssetTransferLaneModuleAcceptedV1,
    ) -> AssetTransferReleaseRouteBindingCandidateV1<'a> {
        AssetTransferReleaseRouteBindingCandidateV1 {
            profile: &self.profile,
            policy_registry: &self.policy_registry,
            asset_policy_registry: &self.asset_policy_registry,
            lanes: &self.lanes,
            coordinators: &self.coordinators,
            routes: &self.routes,
            occurrence: &self.occurrence,
            module_input: &self.module_input,
            accepted,
        }
    }

    fn custody_accepted(&self) -> AssetTransferLaneModuleAcceptedV1 {
        match transition_asset_transfer_lane_module_custody_v1(&self.module_input) {
            Ok(AssetTransferLaneModuleResultV1::Accepted(accepted)) => *accepted,
            other => panic!("custody-complete fixture transfer must accept: {other:?}"),
        }
    }

    fn legacy_accepted(&self) -> AssetTransferLaneModuleAcceptedV1 {
        match transition_asset_transfer_lane_module_v1(&self.module_input) {
            Ok(AssetTransferLaneModuleResultV1::Accepted(accepted)) => *accepted,
            other => panic!("legacy fixture transfer must accept: {other:?}"),
        }
    }

    fn semantics(&self) -> AbiResultV1<()> {
        require_asset_transfer_custody_semantics_v1(
            &self.profile,
            &self.lanes,
            &self.coordinators,
            &self.routes,
            &self.occurrence,
        )
    }

    fn bind_custody(
        &self,
        accepted: &AssetTransferLaneModuleAcceptedV1,
    ) -> AbiResultV1<ReleaseRouteBoundLaneTransitionV1> {
        bind_asset_transfer_lane_output_to_custody_release_route_v1(self.candidate(accepted))
    }

    fn bind_legacy(
        &self,
        accepted: &AssetTransferLaneModuleAcceptedV1,
    ) -> AbiResultV1<ReleaseRouteBoundLaneTransitionV1> {
        bind_asset_transfer_lane_output_to_release_route_v1(self.candidate(accepted))
    }

    /// The custody binder's rejection of this graph's own custody-complete output.
    fn custody_rejection(&self) -> AbiErrorV1 {
        self.bind_custody(&self.custody_accepted()).unwrap_err()
    }

    /// The registries, occurrence, and module context all commit this profile.
    fn assert_coherent(&self) {
        self.profile
            .validate_registries(&self.lanes, &self.coordinators, &self.routes)
            .expect("governed registries must bind to the profile");
        assert_eq!(self.occurrence.profile_root, self.profile.profile_id);
        assert_eq!(
            self.module_input.context.profile_root,
            self.profile.profile_id
        );
    }
}

#[test]
fn committed_bundle_bytes_are_canonical_and_domain_separated_root_selects_custody() {
    let bundle: serde_json::Value =
        serde_json::from_slice(BUNDLE_BYTES).expect("committed bundle must be JSON");
    assert_eq!(canonical_bytes_v1(&bundle).unwrap(), BUNDLE_BYTES);
    let measured_byte_sha256 = hash_bytes_sha256_v1(BUNDLE_BYTES);
    assert_eq!(measured_byte_sha256, BUNDLE_BYTE_SHA256);
    let measured_root = hash_global_v1(BUNDLE_DOMAIN, &bundle).unwrap();
    assert_eq!(measured_root.as_str(), BUNDLE_ROOT);
    assert_ne!(measured_root.as_str(), format!("0x{measured_byte_sha256}"));
    assert_eq!(
        measured_root.as_str(),
        ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1
    );
    let mut raw_sha_options = Options::matching(custody_rows(7));
    raw_sha_options.module.specification_root = RootV1::parse(
        format!("0x{BUNDLE_BYTE_SHA256}"),
        "raw bundle byte SHA-256 fixture",
        false,
    )
    .unwrap();
    let raw_sha_governance = Governance::build(&raw_sha_options);
    raw_sha_governance.assert_coherent();
    assert_eq!(
        raw_sha_governance.semantics().unwrap_err(),
        AbiErrorV1::InvalidBinding("custody semantics module specification root")
    );
    assert!(!bundle_root().is_zero());
    assert_eq!(bundle["schema"], BUNDLE_SCHEMA);
    assert_eq!(bundle["family"], BUNDLE_FAMILY);
    assert_eq!(bundle["lane_id"], "ASSET_TRANSFER");
    assert_eq!(bundle["command_kind"], ASSET_TRANSFER_COMMAND_KIND_V1);
    assert_eq!(
        bundle["selection"]["module_coordinator_route_subject"],
        "this_bundle"
    );
    assert_eq!(bundle["selection"]["occurrences_per_route"], 1);
    assert_eq!(
        bundle["selection"]["ordered_lanes"],
        json!(["ASSET_TRANSFER"])
    );
}

#[test]
fn python_produced_custody_binding_vector_decodes_and_binds_without_authority() {
    let vector: serde_json::Value =
        serde_json::from_slice(SHARED_GOLDEN_BYTES).expect("shared vector must be JSON");
    assert_eq!(
        canonical_bytes_v1(&vector).unwrap(),
        SHARED_GOLDEN_BYTES,
        "the vector is production-canonical test data"
    );
    assert_eq!(
        vector["schema"],
        "zenodex/asset-transfer-custody-binding-test-vector/v1"
    );
    assert_eq!(vector["authority"], "NONE");

    let profile: EconomicProfileSnapshotV1 =
        serde_json::from_value(vector["profile"].clone()).expect("exact V1 profile");
    let lanes: LaneRegistryV1 =
        serde_json::from_value(vector["lanes"].clone()).expect("exact V1 lane registry");
    let coordinators: LaneCoordinatorRegistryV1 =
        serde_json::from_value(vector["coordinators"].clone())
            .expect("exact V1 coordinator registry");
    let routes: RouteRegistryV1 =
        serde_json::from_value(vector["routes"].clone()).expect("exact V1 route registry");
    let policy_registry: EconomicPolicyRegistryV1 =
        serde_json::from_value(vector["policy_registry"].clone())
            .expect("exact V1 economic policy registry");
    let asset_policy_registry: AssetTransferPolicyRegistryV1 =
        serde_json::from_value(vector["asset_policy_registry"].clone())
            .expect("exact V1 asset policy registry");
    let occurrence: EconomicCommandOccurrenceV1 =
        serde_json::from_value(vector["occurrence"].clone()).expect("exact V1 occurrence");
    let module_input: AssetTransferLaneModuleInputV1 =
        serde_json::from_value(vector["module_input"].clone()).expect("exact V1 module input");
    let accepted: AssetTransferLaneModuleAcceptedV1 =
        serde_json::from_value(vector["accepted"].clone()).expect("exact V1 accepted output");
    let expected_binding_root: RootV1 = serde_json::from_value(vector["binding_root"].clone())
        .expect("exact V1 expected binding root");

    let bound = bind_asset_transfer_lane_output_to_custody_release_route_v1(
        AssetTransferReleaseRouteBindingCandidateV1 {
            profile: &profile,
            policy_registry: &policy_registry,
            asset_policy_registry: &asset_policy_registry,
            lanes: &lanes,
            coordinators: &coordinators,
            routes: &routes,
            occurrence: &occurrence,
            module_input: &module_input,
            accepted: &accepted,
        },
    )
    .expect("shared Python-produced custody vector must bind");
    assert_eq!(bound.binding_root().unwrap(), expected_binding_root);
}

#[test]
fn matching_roots_and_nonzero_custody_bind_the_custody_output_after_one_recomputation() {
    let governance = Governance::build(&Options::matching(custody_rows(7)));
    governance.assert_coherent();
    governance
        .semantics()
        .expect("matching roots must select the custody family");
    let accepted = governance.custody_accepted();
    let conservation = &accepted.effects.asset_conservation[0];
    assert_eq!(conservation.owned_and_custodied_pre_atoms, 122);
    assert_eq!(conservation.owned_and_custodied_post_atoms, 122);
    assert_eq!(
        recompute_asset_transfer_lane_module_custody_v1(&governance.module_input, &accepted)
            .expect("custody-complete output must recompute"),
        accepted
    );

    let bound = governance
        .bind_custody(&accepted)
        .expect("matching roots with nonzero custody must bind");

    let route = &governance.routes.routes[0];
    let release = governance
        .lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .expect("asset release must exist");
    assert_eq!(bound.profile_id(), &governance.profile.profile_id);
    assert_eq!(bound.route_release_id(), &route.route_release_id);
    assert_eq!(bound.lane_id(), LaneIdV1::ASSET_TRANSFER);
    assert_eq!(bound.module_release_id(), &release.release_id);
    assert_eq!(
        bound.command_occurrence_id(),
        &governance.occurrence.occurrence_id().unwrap()
    );
    assert_eq!(
        bound.module_journal_root(),
        &accepted.module_journal.journal_root().unwrap()
    );
    assert_eq!(
        bound.statement_root(),
        &governance.module_input.statement_root().unwrap()
    );
    assert_eq!(
        bound.producer_module_schema(),
        ASSET_TRANSFER_MODULE_SCHEMA_V1
    );
    assert_eq!(bound.route_lane_index(), 0);
    assert_eq!(bound.port_schema_root(), &route.port_schema_roots[0]);
    let expected_binding_root = hash_global_v1(
        "release-route-bound-lane-transition-v1",
        &json!({
            "schema": RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1,
            "profile_id": bound.profile_id(),
            "route_release_id": bound.route_release_id(),
            "lane_id": bound.lane_id(),
            "module_release_id": bound.module_release_id(),
            "command_occurrence_id": bound.command_occurrence_id(),
            "module_journal_root": bound.module_journal_root(),
            "statement_root": bound.statement_root(),
            "producer_module_schema": bound.producer_module_schema(),
            "route_lane_index": bound.route_lane_index(),
            "port_schema_root": bound.port_schema_root(),
        }),
    )
    .unwrap();
    assert_eq!(bound.binding_root().unwrap(), expected_binding_root);

    // The families differ exactly by their recomputation: the legacy binder
    // rejects the custody-complete output, and the custody binder rejects the
    // legacy output for the same input under the same governance.
    let legacy = governance.legacy_accepted();
    assert_ne!(legacy, accepted);
    assert_eq!(
        governance.bind_legacy(&accepted).unwrap_err(),
        legacy_recomputation_mismatch()
    );
    assert_eq!(
        governance.bind_custody(&legacy).unwrap_err(),
        recomputation_mismatch()
    );
    let legacy_bound = governance
        .bind_legacy(&legacy)
        .expect("the legacy binder ignores the reviewed roots");
    assert_eq!(legacy_bound.statement_root(), bound.statement_root());
    assert_ne!(
        legacy_bound.module_journal_root(),
        bound.module_journal_root()
    );
}

#[test]
fn custody_zero_and_one_bind_and_the_families_coincide_only_without_custody_rows() {
    let zero = Governance::build(&Options::matching(custody_rows(0)));
    let accepted = zero.custody_accepted();
    assert_eq!(accepted, zero.legacy_accepted());
    assert_eq!(
        accepted.effects.asset_conservation[0].owned_and_custodied_post_atoms,
        115
    );
    let bound = zero.bind_custody(&accepted).expect("custody 0 must bind");
    assert_eq!(bound, zero.bind_legacy(&accepted).unwrap());

    let one = Governance::build(&Options::matching(custody_rows(1)));
    let accepted = one.custody_accepted();
    assert_ne!(accepted, one.legacy_accepted());
    assert_eq!(
        accepted.effects.asset_conservation[0].owned_and_custodied_pre_atoms,
        116
    );
    assert_eq!(
        accepted.private_port.post_state.custody,
        one.module_input.custody
    );
    one.bind_custody(&accepted).expect("custody 1 must bind");
    assert_eq!(
        one.bind_legacy(&accepted).unwrap_err(),
        legacy_recomputation_mismatch()
    );

    // A zero-atom custody row is rejected by input validation, never selected.
    let mut zero_row = Governance::build(&Options::matching(custody_rows(1)));
    zero_row.module_input.custody[0].amount_atoms = 0;
    let invalid_custody = AbiErrorV1::InvalidBinding("asset lane custody");
    assert_eq!(
        transition_asset_transfer_lane_module_custody_v1(&zero_row.module_input).unwrap_err(),
        invalid_custody
    );
    assert_eq!(
        zero_row.bind_custody(&accepted).unwrap_err(),
        invalid_custody
    );
}

#[test]
fn each_single_role_root_mismatch_rejects_before_custody_recomputation() {
    let mut module_mismatch = Options::matching(custody_rows(7));
    module_mismatch.module.specification_root = unknown_root();
    let mut coordinator_mismatch = Options::matching(custody_rows(7));
    coordinator_mismatch.coordinator.specification_root = unknown_root();
    let mut route_mismatch = Options::matching(custody_rows(7));
    route_mismatch.route.specification_root = unknown_root();

    for (options, field) in [
        (
            module_mismatch,
            "custody semantics module specification root",
        ),
        (
            coordinator_mismatch,
            "custody semantics coordinator specification root",
        ),
        (route_mismatch, "custody semantics route specification root"),
    ] {
        let governance = Governance::build(&options);
        governance.assert_coherent();
        let expected = AbiErrorV1::InvalidBinding(field);
        assert_eq!(governance.semantics().unwrap_err(), expected);
        assert_eq!(governance.custody_rejection(), expected);
        // Seam: this legacy acceptance fails custody recomputation whenever it
        // is reached (see the matching-roots test); here the root mismatch is
        // what rejects it, so recomputation was never reached.
        let legacy = governance.legacy_accepted();
        assert_eq!(governance.bind_custody(&legacy).unwrap_err(), expected);
        // The retained legacy binder is indifferent to the specification root.
        assert_eq!(
            governance.bind_legacy(&legacy).unwrap().route_lane_index(),
            0
        );
    }
}

#[test]
fn unknown_and_mixed_roots_reject_in_module_coordinator_route_order() {
    let mut all_unknown = Options::matching(custody_rows(7));
    for role in all_unknown.roles_mut() {
        role.specification_root = unknown_root();
    }
    let mut only_module = Options::matching(custody_rows(7));
    only_module.coordinator.specification_root = unknown_root();
    only_module.route.specification_root = unknown_root();
    let mut only_coordinator = Options::matching(custody_rows(7));
    only_coordinator.module.specification_root = unknown_root();
    only_coordinator.route.specification_root = unknown_root();
    let mut only_route = Options::matching(custody_rows(7));
    only_route.module.specification_root = unknown_root();
    only_route.coordinator.specification_root = unknown_root();

    for (options, field) in [
        (all_unknown, "custody semantics module specification root"),
        (
            only_module,
            "custody semantics coordinator specification root",
        ),
        (
            only_coordinator,
            "custody semantics module specification root",
        ),
        (only_route, "custody semantics module specification root"),
        (
            Options::opaque(custody_rows(7)),
            "custody semantics module specification root",
        ),
    ] {
        let governance = Governance::build(&options);
        governance.assert_coherent();
        let expected = AbiErrorV1::InvalidBinding(field);
        assert_eq!(governance.semantics().unwrap_err(), expected);
        assert_eq!(governance.custody_rejection(), expected);
        let legacy = governance.legacy_accepted();
        assert_eq!(governance.bind_custody(&legacy).unwrap_err(), expected);
        governance
            .bind_legacy(&legacy)
            .expect("the legacy binder binds every coherent governance");
    }
}

#[test]
fn semantic_version_image_source_and_toolchain_spoofs_do_not_select_custody() {
    let mut spoofed = Options::matching(custody_rows(7));
    for role in spoofed.roles_mut() {
        role.specification_root = unknown_root();
        role.semantic_version = BUNDLE_FAMILY.to_owned();
        role.guest_image_id = bundle_root();
        role.source_root = bundle_root();
        role.toolchain_root = bundle_root();
    }
    let spoofed = Governance::build(&spoofed);
    spoofed.assert_coherent();
    let expected = AbiErrorV1::InvalidBinding("custody semantics module specification root");
    assert_eq!(spoofed.semantics().unwrap_err(), expected);
    assert_eq!(spoofed.custody_rejection(), expected);

    // Conversely those identities are inert once the specification roots match.
    let mut inert = Options::matching(custody_rows(7));
    for role in inert.roles_mut() {
        role.semantic_version = "0.0.0-legacy".to_owned();
        role.guest_image_id = unknown_root();
        role.source_root = unknown_root();
        role.toolchain_root = unknown_root();
    }
    let inert = Governance::build(&inert);
    inert.assert_coherent();
    inert
        .semantics()
        .expect("identities other than the specification root are inert");
    inert
        .bind_custody(&inert.custody_accepted())
        .expect("matching specification roots bind regardless of version and build identity");
}

#[test]
fn only_the_single_asset_transfer_route_lane_selects_custody() {
    let mut options = Options::matching(custody_rows(7));
    options.extra_route_lane = true;
    let two_lanes = Governance::build(&options);
    two_lanes.assert_coherent();
    assert_eq!(
        two_lanes.routes.routes[0].ordered_lanes,
        [LaneIdV1::ASSET_TRANSFER, LaneIdV1::SPOT_LIQUIDITY]
    );
    let expected =
        AbiErrorV1::InvalidBinding("custody semantics require one ASSET_TRANSFER route lane");
    assert_eq!(two_lanes.semantics().unwrap_err(), expected);
    assert_eq!(two_lanes.custody_rejection(), expected);
    let legacy = two_lanes.legacy_accepted();
    assert_eq!(two_lanes.bind_custody(&legacy).unwrap_err(), expected);
    // The legacy structural binder indexes the wider route instead of refusing it.
    assert_eq!(
        two_lanes.bind_legacy(&legacy).unwrap().route_lane_index(),
        0
    );

    // A route without lanes is not a governed route at all.
    let single = Governance::build(&Options::matching(custody_rows(7)));
    let mut no_lanes = single.routes.clone();
    let route = &mut no_lanes.routes[0];
    route.ordered_lanes.clear();
    route.module_release_ids.clear();
    route.dependency_roles.clear();
    route.port_schema_roots.clear();
    assert_eq!(
        require_asset_transfer_custody_semantics_v1(
            &single.profile,
            &single.lanes,
            &single.coordinators,
            &no_lanes,
            &single.occurrence,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBounds("route module count")
    );
}

#[test]
fn rust_registry_validation_retains_active_release_boundaries() {
    let mut drained_route = Options::matching(custody_rows(7));
    drained_route.route_status = (ReleaseStatusV1::DRAIN_ONLY, false);
    let drained_route = Governance::build(&drained_route);
    let expected = AbiErrorV1::InvalidBinding("active profile route status");
    assert_eq!(drained_route.semantics().unwrap_err(), expected);
    assert_eq!(drained_route.custody_rejection(), expected);

    let mut drained_lane = Options::matching(custody_rows(7));
    drained_lane.lane_status = (ReleaseStatusV1::DRAIN_ONLY, false);
    let drained_lane = Governance::build(&drained_lane);
    let expected = AbiErrorV1::InvalidBinding("active route lane release");
    assert_eq!(drained_lane.semantics().unwrap_err(), expected);
    assert_eq!(drained_lane.custody_rejection(), expected);

    // Flipping either half of the ACTIVE_NEW/accepts_new_objects pair alone
    // leaves an invalid route release.
    let single = Governance::build(&Options::matching(custody_rows(7)));
    for (status, accepts_new_objects) in [
        (ReleaseStatusV1::ACTIVE_NEW, false),
        (ReleaseStatusV1::DRAIN_ONLY, true),
    ] {
        let mut routes = single.routes.clone();
        routes.routes[0].status = status;
        routes.routes[0].accepts_new_objects = accepts_new_objects;
        assert_eq!(
            require_asset_transfer_custody_semantics_v1(
                &single.profile,
                &single.lanes,
                &single.coordinators,
                &routes,
                &single.occurrence,
            )
            .unwrap_err(),
            AbiErrorV1::InvalidBinding("route status")
        );
    }
}

#[test]
fn selector_defers_shadow_profile_and_occurrence_profile_binding_to_structural_binding() {
    let mut shadow_options = Options::matching(custody_rows(7));
    shadow_options.profile_status = ProfileStatusV1::SHADOW;
    let shadow = Governance::build(&shadow_options);
    shadow
        .semantics()
        .expect("well-formed SHADOW profile still selects matching semantics");
    assert_eq!(
        shadow.custody_rejection(),
        AbiErrorV1::InvalidBinding("economic profile is not active")
    );

    let governance = Governance::build(&Options::matching(custody_rows(7)));
    let mut detached_occurrence = governance.occurrence.clone();
    detached_occurrence.profile_root = unknown_root();
    require_asset_transfer_custody_semantics_v1(
        &governance.profile,
        &governance.lanes,
        &governance.coordinators,
        &governance.routes,
        &detached_occurrence,
    )
    .expect("semantic selection defers occurrence-to-profile binding");
    let accepted = governance.custody_accepted();
    assert_eq!(
        bind_asset_transfer_lane_output_to_custody_release_route_v1(
            AssetTransferReleaseRouteBindingCandidateV1 {
                profile: &governance.profile,
                policy_registry: &governance.policy_registry,
                asset_policy_registry: &governance.asset_policy_registry,
                lanes: &governance.lanes,
                coordinators: &governance.coordinators,
                routes: &governance.routes,
                occurrence: &detached_occurrence,
                module_input: &governance.module_input,
                accepted: &accepted,
            },
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module occurrence profile root")
    );
}
