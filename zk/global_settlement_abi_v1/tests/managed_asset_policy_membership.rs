//! Governed typed policy-registry membership for managed-asset issue and burn.
//!
//! These tests use a synthetic ACTIVE profile solely to exercise fail-closed
//! membership at release-route binding. They grant no release, mount,
//! settlement, or publication authority.

use serde_json::json;
use zenodex_global_settlement_abi_v1::*;

const ISSUE: &str = MANAGED_ASSET_ISSUE_COMMAND_KIND_V1;
const BURN: &str = MANAGED_ASSET_BURN_COMMAND_KIND_V1;
const MEMBER_MISMATCH: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("managed asset state policy is not a governed member");
const RELEASE_MISMATCH: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("managed asset policy registry module release");
const ROUTE_POLICY_ROOT_MISMATCH: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("managed asset route issue/burn policy root");
/// Cross-language vectors: the Python suite asserts the same roots for the same
/// release-bound registries (USD fixture policy row).
const FIXED_RELEASE_REGISTRY_ROOT_V1: &str =
    "0xe9e57192aacf716ec124eabb82fc19ff1382e4a8a60b784b2bed1fb43eac28ba";
const OTHER_RELEASE_REGISTRY_ROOT_V1: &str =
    "0x155c41281d66c0d34d6d1d2443468a264f123801944cab0174b683001c6ce86a";

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn other_release_id() -> RootV1 {
    root(997)
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
        vec![BURN.to_owned(), ISSUE.to_owned()]
    } else {
        vec![]
    };
    let terminal_command_variants = if is_asset_lane {
        vec![BURN.to_owned()]
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
        semantic_version: "1.0.0-managed-policy-test".to_owned(),
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
        semantic_version: "1.0.0-managed-policy-test".to_owned(),
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

fn route(
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
        semantic_version: "1.0.0-managed-policy-test".to_owned(),
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

fn registry_of(
    module_release_id: RootV1,
    policies: Vec<ManagedAssetLifecyclePolicyV1>,
) -> ManagedAssetPolicyRegistryV1 {
    ManagedAssetPolicyRegistryV1 {
        schema: MANAGED_ASSET_POLICY_REGISTRY_SCHEMA_V1.to_owned(),
        module_release_id,
        policies,
    }
}

fn governed_policy_registry(
    asset_policy_registry: &ManagedAssetPolicyRegistryV1,
    command_kinds: &[&str],
) -> EconomicPolicyRegistryV1 {
    let mut bindings = command_kinds
        .iter()
        .map(|command_kind| EconomicPolicyBindingV1 {
            policy_kind: MANAGED_ASSET_POLICY_KIND_V1.to_owned(),
            command_kind: (*command_kind).to_owned(),
            policy_root: asset_policy_registry.registry_root().unwrap(),
        })
        .collect::<Vec<_>>();
    bindings.sort_by(|left, right| {
        (&left.policy_kind, &left.command_kind).cmp(&(&right.policy_kind, &right.command_kind))
    });
    let registry = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings,
    };
    registry
        .validate()
        .expect("test policy registry must validate");
    registry
}

/// One ACTIVE profile whose economic policy registry governs managed assets.
struct Governance {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    policy_registry: EconomicPolicyRegistryV1,
    asset_policy_registry: ManagedAssetPolicyRegistryV1,
}

/// Managed issue and burn routes own the typed registry root as their
/// `issue_burn_policy_root` unless a test overrides it.
fn governance_with(
    policies: Vec<ManagedAssetLifecyclePolicyV1>,
    module_release_id: Option<RootV1>,
    command_kinds: &[&str],
    route_issue_burn_policy_root: Option<RootV1>,
) -> Governance {
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
    let asset_policy_registry = registry_of(
        module_release_id.unwrap_or_else(|| asset_release_id.clone()),
        policies,
    );
    let route_policy_root = route_issue_burn_policy_root
        .unwrap_or_else(|| asset_policy_registry.registry_root().unwrap());
    let routes = RouteRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        routes: [BURN, ISSUE]
            .iter()
            .enumerate()
            .map(|(index, command)| {
                route(
                    command,
                    index as u64,
                    &asset_release_id,
                    route_policy_root.clone(),
                )
            })
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
    let policy_registry = governed_policy_registry(&asset_policy_registry, command_kinds);
    let lane_registry_root = lanes.registry_root().unwrap();
    let lane_coordinator_registry_root = coordinators.registry_root().unwrap();
    let route_registry_root = routes.registry_root().unwrap();
    let policy_registry_root = policy_registry.registry_root().unwrap();
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
        .validate_registries(&lanes, &coordinators, &routes)
        .expect("test profile must bind registries");
    Governance {
        profile,
        lanes,
        coordinators,
        routes,
        policy_registry,
        asset_policy_registry,
    }
}

fn governance() -> Governance {
    governance_with(vec![managed_asset_policy()], None, &[BURN, ISSUE], None)
}

fn asset_release_id(governance: &Governance) -> RootV1 {
    governance
        .lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .unwrap()
        .release_id
        .clone()
}

fn default_authority(command_kind: &str) -> (&'static str, RootV1) {
    if command_kind == ISSUE {
        ("issuer", root(5))
    } else {
        ("alice", root(6))
    }
}

fn occurrence(
    governance: &Governance,
    command_kind: &str,
    subject_id: &str,
    grant_root: RootV1,
) -> EconomicCommandOccurrenceV1 {
    let route = governance
        .routes
        .route_for_command(command_kind, None)
        .expect("test route must exist");
    let command_body_hash = ManagedAssetLifecycleCommandV1 {
        command_kind: command_kind.to_owned(),
        asset: "USD".to_owned(),
        account_owner: "alice".to_owned(),
        amount_atoms: if command_kind == ISSUE { 7 } else { 4 },
    }
    .command_body_hash()
    .expect("test managed command must hash");
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-managed-policy-test".to_owned(),
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
        profile_root: governance.profile.profile_id.clone(),
        pre_state_root: root(2),
        consumed_object_ids: vec![],
    }
}

fn module_input(
    governance: &Governance,
    occurrence: &EconomicCommandOccurrenceV1,
    command_kind: &str,
) -> ManagedAssetLifecycleLaneModuleInputV1 {
    let release_id = asset_release_id(governance);
    ManagedAssetLifecycleLaneModuleInputV1 {
        schema: MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: ManagedAssetLifecycleContextV1 {
            chain_id: occurrence.chain_id.clone(),
            deployment_root: occurrence.deployment_root.clone(),
            profile_root: occurrence.profile_root.clone(),
            writer_epoch: governance.profile.authority_epoch,
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
            amount_atoms: if command_kind == ISSUE { 7 } else { 4 },
        },
        asset_policy_registry_root: governance.asset_policy_registry.registry_root().unwrap(),
        fee_policy_registry_root: root(12),
        custody: vec![],
    }
}

fn accept(
    input: &ManagedAssetLifecycleLaneModuleInputV1,
) -> ManagedAssetLifecycleLaneModuleAcceptedV1 {
    match transition_managed_asset_lifecycle_lane_module_v1(input)
        .expect("typed lifecycle lane module transition must evaluate")
    {
        ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) => *accepted,
        ManagedAssetLifecycleLaneModuleResultV1::Rejected(rejected) => {
            panic!("test transition must accept, got {:?}", rejected.code)
        }
    }
}

struct Executed {
    occurrence: EconomicCommandOccurrenceV1,
    input: ManagedAssetLifecycleLaneModuleInputV1,
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1,
}

fn execute_as(
    governance: &Governance,
    command_kind: &str,
    subject_id: &str,
    grant_root: RootV1,
    edit: impl FnOnce(&mut ManagedAssetLifecycleLaneModuleInputV1),
) -> Executed {
    let occurrence = occurrence(governance, command_kind, subject_id, grant_root);
    let mut input = module_input(governance, &occurrence, command_kind);
    edit(&mut input);
    let accepted = accept(&input);
    Executed {
        occurrence,
        input,
        accepted,
    }
}

fn execute(
    governance: &Governance,
    command_kind: &str,
    edit: impl FnOnce(&mut ManagedAssetLifecycleLaneModuleInputV1),
) -> Executed {
    let (subject_id, grant_root) = default_authority(command_kind);
    execute_as(governance, command_kind, subject_id, grant_root, edit)
}

fn binding_candidate<'a>(
    governance: &'a Governance,
    executed: &'a Executed,
) -> ManagedAssetLifecycleReleaseRouteBindingCandidateV1<'a> {
    ManagedAssetLifecycleReleaseRouteBindingCandidateV1 {
        profile: &governance.profile,
        policy_registry: &governance.policy_registry,
        asset_policy_registry: &governance.asset_policy_registry,
        lanes: &governance.lanes,
        coordinators: &governance.coordinators,
        routes: &governance.routes,
        occurrence: &executed.occurrence,
        module_input: &executed.input,
        accepted: &executed.accepted,
    }
}

fn bind(
    governance: &Governance,
    executed: &Executed,
) -> AbiResultV1<ReleaseRouteBoundLaneTransitionV1> {
    bind_managed_asset_lifecycle_lane_output_to_release_route_v1(binding_candidate(
        governance, executed,
    ))
}

fn with_ungoverned_eur(
    command_asset: &'static str,
) -> impl FnOnce(&mut ManagedAssetLifecycleLaneModuleInputV1) {
    move |input: &mut ManagedAssetLifecycleLaneModuleInputV1| {
        let mut eur = managed_asset_policy();
        eur.asset = "EUR".to_owned();
        input.pre_state.policies.insert(0, eur);
        input.pre_state.supplies.insert(
            0,
            AssetSupplyV1 {
                asset: "EUR".to_owned(),
                amount_atoms: 0,
            },
        );
        input.command.asset = command_asset.to_owned();
    }
}

/// Execute the same command and policy rows under another module release.
fn under_module_release(
    module_release_id: RootV1,
) -> impl FnOnce(&mut ManagedAssetLifecycleLaneModuleInputV1) {
    move |input: &mut ManagedAssetLifecycleLaneModuleInputV1| {
        input.context.module_release_id = module_release_id.clone();
        input.pre_state.module_release_id = module_release_id;
    }
}

#[test]
fn registry_root_is_content_derived_and_member_lookup_is_exact() {
    // Arrange
    let registry = governance().asset_policy_registry;
    let rebuilt = registry.clone();
    let mut disabled = registry.clone();
    disabled.policies[0].enabled = false;

    // Act / Assert
    assert_eq!(
        registry.registry_root().unwrap(),
        rebuilt.registry_root().unwrap()
    );
    assert_ne!(
        registry.registry_root().unwrap(),
        disabled.registry_root().unwrap()
    );
    assert_eq!(registry.policy_for("USD"), Some(&managed_asset_policy()));
    assert_eq!(registry.policy_for("EUR"), None);
}

#[test]
fn registry_root_binds_the_module_release_with_cross_language_vectors() {
    // Arrange: identical policy rows under two module releases.
    let fixed = registry_of(root(3), vec![managed_asset_policy()]);
    let other = registry_of(other_release_id(), vec![managed_asset_policy()]);

    // Act / Assert: the release is part of the root, so rows cannot be replayed.
    assert_eq!(
        fixed.registry_root().unwrap().as_str(),
        FIXED_RELEASE_REGISTRY_ROOT_V1
    );
    assert_eq!(
        other.registry_root().unwrap().as_str(),
        OTHER_RELEASE_REGISTRY_ROOT_V1
    );
    assert_eq!(fixed.policies, other.policies);
    assert_ne!(
        fixed.registry_root().unwrap(),
        other.registry_root().unwrap()
    );
}

#[test]
fn registry_rejects_wrong_schema_zero_release_unsorted_duplicate_and_over_bound_members() {
    let mut wrong_schema = governance().asset_policy_registry;
    wrong_schema.schema = GLOBAL_SETTLEMENT_ABI_V1.to_owned();
    assert_eq!(
        wrong_schema.registry_root().unwrap_err(),
        AbiErrorV1::InvalidSchema
    );

    let zero_release = registry_of(
        RootV1::parse(ZERO_ROOT_V1, "test zero root", true).unwrap(),
        vec![managed_asset_policy()],
    );
    assert_eq!(
        zero_release.registry_root().unwrap_err(),
        AbiErrorV1::InvalidRoot("managed asset policy registry module release")
    );

    let mut eur = managed_asset_policy();
    eur.asset = "EUR".to_owned();
    let unsorted = registry_of(root(3), vec![managed_asset_policy(), eur]);
    assert_eq!(
        unsorted.registry_root().unwrap_err(),
        AbiErrorV1::InvalidOrder("managed asset policy registry")
    );
    let duplicate = registry_of(
        root(3),
        vec![managed_asset_policy(), managed_asset_policy()],
    );
    assert_eq!(
        duplicate.registry_root().unwrap_err(),
        AbiErrorV1::InvalidOrder("managed asset policy registry")
    );

    let policies = |count: usize| {
        (0..count)
            .map(|index| {
                let mut policy = managed_asset_policy();
                policy.asset = format!("A{index:03}");
                policy
            })
            .collect::<Vec<_>>()
    };
    let at_limit = registry_of(root(3), policies(MAX_MANAGED_ASSET_POLICIES_V1));
    assert!(at_limit.registry_root().is_ok());
    let over_limit = registry_of(root(3), policies(MAX_MANAGED_ASSET_POLICIES_V1 + 1));
    assert_eq!(
        over_limit.registry_root().unwrap_err(),
        AbiErrorV1::InvalidBounds("managed asset policy registry")
    );
}

#[test]
fn issue_and_burn_bind_under_governed_membership() {
    let governance = governance();
    for command_kind in [ISSUE, BURN] {
        // Arrange
        let executed = execute(&governance, command_kind, |_| {});

        // Act
        let bound = bind(&governance, &executed).expect("governed member must bind");

        // Assert
        assert_eq!(
            bound.statement_root(),
            &executed.input.statement_root().unwrap()
        );
        assert_eq!(
            bound.route_release_id(),
            &executed.occurrence.route_release_id
        );
        assert_eq!(
            executed.input.asset_policy_registry_root,
            governance.asset_policy_registry.registry_root().unwrap()
        );
        assert_eq!(
            executed.input.context.module_release_id,
            governance.asset_policy_registry.module_release_id
        );
    }
}

#[test]
fn membership_returns_the_exact_governed_member() {
    let governance = governance();
    let executed = execute(&governance, ISSUE, |_| {});

    let member = require_managed_asset_policy_membership_v1(
        &governance.asset_policy_registry,
        &executed.input,
    )
    .expect("governed member must resolve");

    assert_eq!(member, &managed_asset_policy());
}

#[test]
fn policy_registry_outside_the_profile_rejects_before_route_binding() {
    // Arrange: an economic policy registry whose root the profile does not pin.
    let governance = governance();
    let executed = execute(&governance, ISSUE, |_| {});
    let ungoverned = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![],
    };
    let mut candidate = binding_candidate(&governance, &executed);
    candidate.policy_registry = &ungoverned;

    // Act / Assert
    assert_eq!(
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(candidate).unwrap_err(),
        AbiErrorV1::InvalidBinding("managed asset policy registry outside profile")
    );
}

#[test]
fn binding_absent_for_the_command_kind_rejects() {
    // Arrange: the profile governs managed issue only.
    let governance = governance_with(vec![managed_asset_policy()], None, &[ISSUE], None);
    let issue = execute(&governance, ISSUE, |_| {});
    let burn = execute(&governance, BURN, |_| {});

    // Act / Assert
    assert!(bind(&governance, &issue).is_ok());
    assert_eq!(
        bind(&governance, &burn).unwrap_err(),
        AbiErrorV1::InvalidBinding("economic policy binding absent from registry")
    );
}

#[test]
fn typed_registry_root_must_match_the_governed_binding() {
    // Arrange: a registry whose only member differs from the governed one by one root.
    let governance = governance();
    let executed = execute(&governance, BURN, |_| {});
    let mut substituted = governance.asset_policy_registry.clone();
    substituted.policies[0].burn_policy_root = Some(root(66));
    let mut candidate = binding_candidate(&governance, &executed);
    candidate.asset_policy_registry = &substituted;

    // Act / Assert
    assert_eq!(
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(candidate).unwrap_err(),
        AbiErrorV1::InvalidBinding("managed asset policy registry root")
    );
}

#[test]
fn direct_transition_stays_authority_free_and_binding_pins_the_governed_root() {
    // Arrange: the lane statement carries an ungoverned opaque policy registry root.
    let governance = governance();
    let executed = execute(&governance, ISSUE, |input| {
        input.asset_policy_registry_root = root(11);
    });

    // Act / Assert: the direct transition accepted without consulting any registry;
    // only release-route binding pins the governed typed registry root.
    assert_eq!(
        executed
            .accepted
            .private_port
            .pre_state
            .asset_policy_registry_root,
        root(11)
    );
    assert_eq!(
        bind(&governance, &executed).unwrap_err(),
        AbiErrorV1::InvalidBinding("managed asset lane module policy registry root")
    );
}

#[test]
fn same_policy_rows_under_another_module_release_reject_at_membership() {
    let governance = governance();
    for command_kind in [ISSUE, BURN] {
        // Arrange: the module executes the governed rows under a foreign release while
        // advertising the governed registry root.
        let executed = execute(
            &governance,
            command_kind,
            under_module_release(other_release_id()),
        );
        assert_eq!(
            executed.input.asset_policy_registry_root,
            governance.asset_policy_registry.registry_root().unwrap()
        );

        // Act / Assert
        assert_eq!(bind(&governance, &executed).unwrap_err(), RELEASE_MISMATCH);
    }
}

#[test]
fn registry_bound_to_another_release_rejects_the_governed_module() {
    // Arrange: the profile governs rows bound to a foreign release; the module runs
    // under the active release and advertises that governed root.
    let governance = governance_with(
        vec![managed_asset_policy()],
        Some(other_release_id()),
        &[BURN, ISSUE],
        None,
    );
    let executed = execute(&governance, ISSUE, |_| {});
    assert_eq!(
        executed.input.asset_policy_registry_root,
        governance.asset_policy_registry.registry_root().unwrap()
    );

    // Act / Assert
    assert_eq!(bind(&governance, &executed).unwrap_err(), RELEASE_MISMATCH);
    assert_eq!(
        require_managed_asset_policy_membership_v1(
            &governance.asset_policy_registry,
            &executed.input
        )
        .unwrap_err(),
        RELEASE_MISMATCH
    );
}

#[test]
fn route_release_check_remains_independent_of_registry_membership() {
    // Arrange: rows, registry, context, and pre-state all agree on a foreign release
    // that the governed lane registry does not carry.
    let governance = governance_with(
        vec![managed_asset_policy()],
        Some(other_release_id()),
        &[BURN, ISSUE],
        None,
    );
    let executed = execute(&governance, BURN, under_module_release(other_release_id()));

    // Act / Assert: membership passes and the release-route binding still fails closed.
    assert_eq!(
        require_managed_asset_policy_membership_v1(
            &governance.asset_policy_registry,
            &executed.input
        )
        .unwrap(),
        &managed_asset_policy()
    );
    assert_eq!(
        bind(&governance, &executed).unwrap_err(),
        AbiErrorV1::InvalidBinding("lane module release mismatch")
    );
    assert_ne!(asset_release_id(&governance), other_release_id());
}

#[test]
fn ungoverned_issuer_substitution_rejects_at_membership() {
    // Arrange: the state names mallory as issuer and the occurrence matches the state.
    let governance = governance();
    let executed = execute_as(&governance, ISSUE, "mallory", root(55), |input| {
        let policy = &mut input.pre_state.policies[0];
        policy.issue_authority_subject = Some("mallory".to_owned());
        policy.issue_policy_root = Some(root(55));
    });

    // Act / Assert: the module accepted, governed membership does not.
    assert_eq!(bind(&governance, &executed).unwrap_err(), MEMBER_MISMATCH);
}

#[test]
fn state_policy_field_substitutions_reject_at_membership() {
    let governance = governance();
    let cases: [(&str, fn(&mut ManagedAssetLifecyclePolicyV1)); 3] = [
        (BURN, |policy: &mut ManagedAssetLifecyclePolicyV1| {
            policy.issue_authority_subject = Some("mallory".to_owned())
        }),
        (BURN, |policy: &mut ManagedAssetLifecyclePolicyV1| {
            policy.issue_policy_root = Some(root(55))
        }),
        (ISSUE, |policy: &mut ManagedAssetLifecyclePolicyV1| {
            policy.burn_policy_root = Some(root(66))
        }),
    ];
    for (command_kind, mutate) in cases {
        // Arrange: substitute one authority field the executed command does not consult.
        let executed = execute(&governance, command_kind, |input| {
            mutate(&mut input.pre_state.policies[0])
        });

        // Act / Assert
        assert_eq!(bind(&governance, &executed).unwrap_err(), MEMBER_MISMATCH);
    }
}

#[test]
fn command_asset_absent_from_the_governed_registry_rejects() {
    // Arrange: the state carries an ungoverned EUR policy and the command issues EUR.
    let governance = governance();
    let executed = execute(&governance, ISSUE, with_ungoverned_eur("EUR"));

    // Act / Assert
    assert_eq!(
        bind(&governance, &executed).unwrap_err(),
        AbiErrorV1::InvalidBinding("managed asset command asset absent from governed registry")
    );
}

#[test]
fn state_carrying_an_ungoverned_extra_policy_rejects() {
    // Arrange: the command targets the governed USD member, the state also carries EUR.
    let governance = governance();
    let executed = execute(&governance, ISSUE, with_ungoverned_eur("USD"));

    // Act / Assert
    assert_eq!(bind(&governance, &executed).unwrap_err(), MEMBER_MISMATCH);
}

#[test]
fn empty_governed_registry_rejects_every_asset() {
    // Arrange
    let governance = governance_with(vec![], None, &[BURN, ISSUE], None);
    let executed = execute(&governance, ISSUE, |_| {});

    // Act / Assert
    assert_eq!(
        bind(&governance, &executed).unwrap_err(),
        AbiErrorV1::InvalidBinding("managed asset command asset absent from governed registry")
    );
}

#[test]
fn membership_is_content_bound_not_identity_bound() {
    // Arrange
    let governance = governance();
    let executed = execute(&governance, BURN, |_| {});
    let first = bind(&governance, &executed).unwrap();
    let rebuilt = Executed {
        occurrence: executed.occurrence.clone(),
        input: executed.input.clone(),
        accepted: executed.accepted.clone(),
    };

    // Act
    let second = bind(&governance, &rebuilt).unwrap();

    // Assert
    assert_eq!(
        second.binding_root().unwrap(),
        first.binding_root().unwrap()
    );
    assert_eq!(second, first);
}

#[test]
fn governed_routes_own_the_exact_registry_root_and_transfer_kind_is_refused() {
    // Arrange
    let governance = governance();
    let executed = execute(&governance, BURN, |_| {});

    // Act
    let route = require_managed_asset_route_policy_root_v1(
        &governance.routes,
        &executed.occurrence,
        &governance.asset_policy_registry,
    )
    .expect("governed burn route must own the registry root");

    // Assert
    assert_eq!(
        route.issue_burn_policy_root,
        governance.asset_policy_registry.registry_root().unwrap()
    );
    assert_eq!(route.route_release_id, executed.occurrence.route_release_id);
    let mut transfer = executed.occurrence.clone();
    transfer.command_kind = ASSET_TRANSFER_COMMAND_KIND_V1.to_owned();
    assert_eq!(
        require_managed_asset_route_policy_root_v1(
            &governance.routes,
            &transfer,
            &governance.asset_policy_registry
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("managed asset route policy binding requires issue or burn")
    );
}

#[test]
fn wrong_route_issue_burn_policy_root_rejects_before_any_witness() {
    // Arrange: governed rows and membership are exact, but the selected issue and
    // burn routes carry a stale route-owned issue/burn policy root.
    let governance = governance_with(
        vec![managed_asset_policy()],
        None,
        &[BURN, ISSUE],
        Some(root(511)),
    );
    for command_kind in [ISSUE, BURN] {
        let executed = execute(&governance, command_kind, |_| {});
        assert!(require_managed_asset_policy_membership_v1(
            &governance.asset_policy_registry,
            &executed.input
        )
        .is_ok());

        // Act / Assert
        assert_eq!(
            bind(&governance, &executed).unwrap_err(),
            ROUTE_POLICY_ROOT_MISMATCH
        );
        assert_eq!(
            require_managed_asset_route_policy_root_v1(
                &governance.routes,
                &executed.occurrence,
                &governance.asset_policy_registry
            )
            .unwrap_err(),
            ROUTE_POLICY_ROOT_MISMATCH
        );
    }
}
