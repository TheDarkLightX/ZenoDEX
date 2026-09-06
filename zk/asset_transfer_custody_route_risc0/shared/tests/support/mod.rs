#![allow(dead_code)]
//! Coherent governed custody-route fixtures. Release ids, registry roots, the
//! profile id, the occurrence, the module context, the coordinator context,
//! and the global state pair are all rebuilt from the varied roots. Fixture
//! statuses and roots grant no authority.

use serde_json::json;
use zenodex_asset_lane_custody_coordinator_risc0_shared::{
    prepare_asset_lane_custody_coordinator_v1, AssetLaneCustodyCoordinatorInputV1,
    ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_SCHEMA_V1,
};
use zenodex_asset_transfer_custody_route_risc0_shared::{
    AssetTransferCustodyRouteInputV1, ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_SCHEMA_V1,
};
use zenodex_global_settlement_abi_v1::*;

pub const MODULE_SEED: u64 = 116;
pub const COORDINATOR_SEED: u64 = 316;
pub const ROUTE_SEED: u64 = 560;
pub const CHAIN_ID: &str = "zeno-custody-route-test";
pub const PREDECESSOR_HEIGHT: u64 = 10;
const UNSELECTED_LANE_ROOT: u64 = 700;
const HISTORY_ROOT: u64 = 701;

pub fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

pub fn bundle_root() -> RootV1 {
    RootV1::parse(
        ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1,
        "reviewed bundle root",
        false,
    )
    .expect("reviewed bundle root must parse")
}

pub fn unknown_root() -> RootV1 {
    root(0xdead_c0de)
}

pub fn custody_rows(amount_atoms: u128) -> Vec<EconomicAmountV1> {
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

/// Identity one governed role advertises; only `specification_root` selects.
#[derive(Clone)]
pub struct RoleIdentity {
    pub specification_root: RootV1,
    pub semantic_version: String,
    pub guest_image_id: RootV1,
    pub source_root: RootV1,
    pub toolchain_root: RootV1,
}

impl RoleIdentity {
    /// Opaque legacy-style roots that name no reviewed bundle.
    pub fn opaque(seed: u64) -> Self {
        Self {
            specification_root: root(seed + 2),
            semantic_version: "1.0.0-test".to_owned(),
            guest_image_id: root(seed + 1),
            source_root: root(seed + 3),
            toolchain_root: root(seed + 4),
        }
    }

    /// The reviewed bundle as specification subject over opaque build roots.
    pub fn bundle(seed: u64) -> Self {
        Self {
            specification_root: bundle_root(),
            ..Self::opaque(seed)
        }
    }
}

/// Fixture knobs; `matching` is the accepted custody-complete governance.
#[derive(Clone)]
pub struct Options {
    pub module: RoleIdentity,
    pub coordinator: RoleIdentity,
    pub route: RoleIdentity,
    pub extra_route_lane: bool,
    pub lane_status: (ReleaseStatusV1, bool),
    pub route_status: (ReleaseStatusV1, bool),
    pub profile_status: ProfileStatusV1,
    pub route_max_journal_bytes: u64,
    pub coordinator_max_journal_bytes: u64,
    pub module_max_journal_bytes: u64,
    pub custody: Vec<EconomicAmountV1>,
}

impl Options {
    pub fn matching(custody: Vec<EconomicAmountV1>) -> Self {
        Self {
            module: RoleIdentity::bundle(MODULE_SEED),
            coordinator: RoleIdentity::bundle(COORDINATOR_SEED),
            route: RoleIdentity::bundle(ROUTE_SEED),
            extra_route_lane: false,
            lane_status: (ReleaseStatusV1::ACTIVE_NEW, true),
            route_status: (ReleaseStatusV1::ACTIVE_NEW, true),
            profile_status: ProfileStatusV1::ACTIVE,
            route_max_journal_bytes: 131_072,
            coordinator_max_journal_bytes: 65_536,
            module_max_journal_bytes: 65_536,
            custody,
        }
    }

    pub fn opaque(custody: Vec<EconomicAmountV1>) -> Self {
        Self {
            module: RoleIdentity::opaque(MODULE_SEED),
            coordinator: RoleIdentity::opaque(COORDINATOR_SEED),
            route: RoleIdentity::opaque(ROUTE_SEED),
            ..Self::matching(custody)
        }
    }

    pub fn roles_mut(&mut self) -> [&mut RoleIdentity; 3] {
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
            options.module_max_journal_bytes
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
        max_journal_bytes: options.coordinator_max_journal_bytes,
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
        max_journal_bytes: options.route_max_journal_bytes,
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
) -> EconomicProfileSnapshotV1 {
    let lane_registry_root = lanes.registry_root().expect("lane registry must hash");
    let lane_coordinator_registry_root = coordinators
        .registry_root()
        .expect("coordinator registry must hash");
    let route_registry_root = routes.registry_root().expect("route registry must hash");
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "authority_epoch": 7,
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
        authority_epoch: 7,
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

/// The occurrence before its pre-state root is bound; `route_input` rebinds it.
fn occurrence(
    profile: &EconomicProfileSnapshotV1,
    route: &RouteReleaseV1,
) -> EconomicCommandOccurrenceV1 {
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: CHAIN_ID.to_owned(),
        deployment_root: root(1),
        height: PREDECESSOR_HEIGHT + 1,
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

fn global_state(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    height: u64,
    projection: &AssetLaneStateProjectionV1,
) -> GlobalEconomicStateV1 {
    GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        writer_epoch: profile.authority_epoch,
        height,
        profile_root: profile.profile_id.clone(),
        lane_roots: ALL_LANE_IDS_V1
            .into_iter()
            .map(|lane_id| {
                let release = lanes
                    .release_for(lane_id)
                    .expect("every lane has a fixture release");
                LaneStateRootV1 {
                    lane_id,
                    module_release_id: release.release_id.clone(),
                    enabled: release.status == ReleaseStatusV1::ACTIVE_NEW
                        && release.accepts_new_objects,
                    state_root: if lane_id == LaneIdV1::ASSET_TRANSFER {
                        projection
                            .state_root()
                            .expect("fixture projection must hash")
                    } else {
                        root(UNSELECTED_LANE_ROOT)
                    },
                }
            })
            .collect(),
        balances: projection.balances.clone(),
        supplies: projection.supplies.clone(),
        custody: projection.custody.clone(),
        liabilities: Vec::new(),
        reserves: Vec::new(),
        oracle_occurrences: Vec::new(),
        replay_state: Vec::new(),
        terminal_obligations: Vec::new(),
        history_root: root(HISTORY_ROOT),
        outbox: Vec::new(),
    }
}

/// One coherent governed graph plus the transfer it executes.
pub struct Governance {
    pub profile: EconomicProfileSnapshotV1,
    pub lanes: LaneRegistryV1,
    pub coordinators: LaneCoordinatorRegistryV1,
    pub routes: RouteRegistryV1,
    pub policy_registry: EconomicPolicyRegistryV1,
    pub asset_policy_registry: AssetTransferPolicyRegistryV1,
    pub occurrence: EconomicCommandOccurrenceV1,
    pub module_input: AssetTransferLaneModuleInputV1,
}

impl Governance {
    pub fn build(options: &Options) -> Self {
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

    /// Bind the occurrence to the exact pre-state root, derive the coordinator
    /// context and the global state pair through the custody coordinator, and
    /// assemble the unchanged V1 route wire value.
    pub fn route_input(self) -> AssetTransferCustodyRouteInputV1 {
        let Self {
            profile,
            lanes,
            coordinators,
            routes,
            policy_registry,
            asset_policy_registry,
            mut occurrence,
            mut module_input,
        } = self;
        let pre_projection = project_asset_transfer_state_v1(
            &module_input.pre_state,
            &module_input.asset_policy_registry_root,
            &module_input.fee_policy_registry_root,
            module_input.custody.clone(),
        )
        .expect("fixture pre-state must project");
        let pre_state = global_state(
            &profile,
            &lanes,
            &occurrence,
            occurrence.height - 1,
            &pre_projection,
        );
        occurrence.pre_state_root = pre_state.state_root().expect("fixture pre state must hash");
        let occurrence_id = occurrence
            .occurrence_id()
            .expect("fixture occurrence must hash");
        module_input.context.command_occurrence_id = occurrence_id.clone();
        let coordinator_release_id = coordinators
            .release_for(LaneIdV1::ASSET_TRANSFER)
            .expect("asset coordinator must exist")
            .coordinator_release_id
            .clone();
        let coordinator_context = AssetLaneCoordinatorContextV1 {
            schema: ASSET_LANE_COORDINATOR_SCHEMA_V1.to_owned(),
            chain_id: occurrence.chain_id.clone(),
            deployment_root: occurrence.deployment_root.clone(),
            profile_root: profile.profile_id.clone(),
            writer_epoch: profile.authority_epoch,
            coordinator_release_id,
            command_occurrence_id: occurrence_id.clone(),
            asset_policy_registry_root: module_input.asset_policy_registry_root.clone(),
            fee_policy_registry_root: module_input.fee_policy_registry_root.clone(),
            compatible_modules: vec![AssetLaneModuleCompatibilityV1 {
                module_release_id: module_input.context.module_release_id.clone(),
                module_schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
            }],
        };
        let lane_input = AssetLaneCustodyCoordinatorInputV1 {
            schema: ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_SCHEMA_V1.to_owned(),
            module_input,
            coordinator_context,
        };
        let lane = prepare_asset_lane_custody_coordinator_v1(lane_input.clone())
            .expect("fixture custody coordinator must prepare");
        let post_projection = &lane.lane_accepted.post_state;
        let mut post_state = pre_state.clone();
        post_state.height = occurrence.height;
        post_state.lane_roots[0].state_root = post_projection
            .state_root()
            .expect("fixture post projection must hash");
        post_state.balances = post_projection.balances.clone();
        post_state.supplies = post_projection.supplies.clone();
        post_state.custody = post_projection.custody.clone();
        post_state.replay_state.push(ReplayStateV1 {
            replay_id: occurrence
                .replay_id()
                .expect("fixture replay id must hash")
                .as_str()
                .to_owned(),
            occurrence_id,
        });
        AssetTransferCustodyRouteInputV1 {
            schema: ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_SCHEMA_V1.to_owned(),
            lane_input,
            profile,
            lanes,
            coordinators,
            routes,
            policy_registry,
            asset_policy_registry,
            occurrence,
            pre_state,
            post_state,
        }
    }
}

pub fn input(options: &Options) -> AssetTransferCustodyRouteInputV1 {
    Governance::build(options).route_input()
}

/// The registries, occurrence, module context, coordinator context, and
/// pre-state all commit the same profile and occurrence.
pub fn assert_coherent(input: &AssetTransferCustodyRouteInputV1) {
    input
        .profile
        .validate_registries(&input.lanes, &input.coordinators, &input.routes)
        .expect("governed registries must bind to the profile");
    assert_eq!(input.occurrence.profile_root, input.profile.profile_id);
    assert_eq!(
        input.lane_input.module_input.context.profile_root,
        input.profile.profile_id
    );
    assert_eq!(
        input.lane_input.coordinator_context.profile_root,
        input.profile.profile_id
    );
    assert_eq!(
        input.occurrence.pre_state_root,
        input.pre_state.state_root().expect("pre state must hash")
    );
    let occurrence_id = input
        .occurrence
        .occurrence_id()
        .expect("occurrence must hash");
    assert_eq!(
        input.lane_input.module_input.context.command_occurrence_id,
        occurrence_id
    );
    assert_eq!(
        input.lane_input.coordinator_context.command_occurrence_id,
        occurrence_id
    );
}
