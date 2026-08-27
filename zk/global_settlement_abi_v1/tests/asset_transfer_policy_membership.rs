//! Governed typed policy-registry membership for asset transfer.
//!
//! These tests use a synthetic ACTIVE profile solely to exercise fail-closed
//! membership at release-route binding. They grant no release, mount,
//! settlement, or publication authority. Receipt-path precedence for the
//! same policy is exercised by the route-binding suite, which owns the
//! authentication fixtures.

use serde_json::json;
use zenodex_global_settlement_abi_v1::*;

const TRANSFER: &str = ASSET_TRANSFER_COMMAND_KIND_V1;
const ASSET_KIND: &str = ASSET_TRANSFER_ASSET_POLICY_KIND_V1;
const FEE_KIND: &str = ASSET_TRANSFER_FEE_POLICY_KIND_V1;
const BOTH_KINDS: &[&str] = &[ASSET_KIND, FEE_KIND];
const MEMBER_MISMATCH: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("asset transfer state policy is not a governed member");
const MEMBER_ABSENT: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("asset transfer command asset absent from governed registry");
const RELEASE_MISMATCH: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("asset transfer policy registry module release");
const NOT_PROFILE_SELECTED: AbiErrorV1 = AbiErrorV1::InvalidBinding(
    "asset transfer policy registry module release is not profile-selected",
);
const ASSET_ROOT_MISMATCH: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("asset transfer lane module asset policy root");
const FEE_ROOT_MISMATCH: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("asset transfer lane module fee policy root");
const BINDING_ABSENT: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("economic policy binding absent from registry");
const OUTSIDE_PROFILE: AbiErrorV1 =
    AbiErrorV1::InvalidBinding("asset transfer policy registry outside profile");
/// Cross-language vectors: the Python suite asserts the same domain-separated
/// roots for the same release-bound registries (USD/treasury/2/enabled row).
const FIXED_RELEASE_ASSET_POLICY_ROOT_V1: &str =
    "0xddf8513d14116e9f5ef0060c3d93ea37ea8ae68e831f78d36a16726cdbb6d3f5";
const FIXED_RELEASE_FEE_POLICY_ROOT_V1: &str =
    "0xb4c242d46f2974c7cea8ca99e54112881631264bdc7e1ba32ee8cb20ece1e62f";
const OTHER_RELEASE_ASSET_POLICY_ROOT_V1: &str =
    "0x841cd037837f1f6542639456083dd48bab63ac9060ca21da092be93df461a49b";
const OTHER_RELEASE_FEE_POLICY_ROOT_V1: &str =
    "0xeaacbb1844aa90baaf68c76b8710c0aa4d7f05bd0d174d9bb17186a850a0e907";

type InputEdit = fn(&mut AssetTransferLaneModuleInputV1);

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
        vec![TRANSFER.to_owned()]
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
        "terminal_command_variants": Vec::<String>::new(),
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
        semantic_version: "1.0.0-transfer-policy-test".to_owned(),
        state_schema_root,
        command_variants,
        terminal_command_variants: vec![],
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
        semantic_version: "1.0.0-transfer-policy-test".to_owned(),
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

fn transfer_route(release_id: &RootV1) -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::ASSET_TRANSFER];
    let module_release_ids = vec![release_id.clone()];
    let dependency_roles = vec!["VALUE_OWNER".to_owned()];
    let port_schema_roots = vec![root(500)];
    let guest_image_id = root(520);
    let specification_root = root(530);
    let source_root = root(540);
    let toolchain_root = root(550);
    let oracle_policy_root = root(510);
    let issue_burn_policy_root = root(511);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "command_kind": TRANSFER,
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
        semantic_version: "1.0.0-transfer-policy-test".to_owned(),
        command_kind: TRANSFER.to_owned(),
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

fn transfer_policy() -> AssetTransferPolicyV1 {
    AssetTransferPolicyV1 {
        asset: "USD".to_owned(),
        fee_owner: "treasury".to_owned(),
        transfer_fee_atoms: 2,
        enabled: true,
    }
}

fn policy_with(fee_owner: &str, transfer_fee_atoms: u128, enabled: bool) -> AssetTransferPolicyV1 {
    AssetTransferPolicyV1 {
        asset: "USD".to_owned(),
        fee_owner: fee_owner.to_owned(),
        transfer_fee_atoms,
        enabled,
    }
}

fn registry_of(
    module_release_id: RootV1,
    policies: Vec<AssetTransferPolicyV1>,
) -> AssetTransferPolicyRegistryV1 {
    AssetTransferPolicyRegistryV1 {
        schema: ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1.to_owned(),
        module_release_id,
        policies,
    }
}

fn governed_policy_registry(
    asset_policy_registry: &AssetTransferPolicyRegistryV1,
    kinds: &[&str],
) -> EconomicPolicyRegistryV1 {
    let mut bindings = kinds
        .iter()
        .map(|kind| EconomicPolicyBindingV1 {
            policy_kind: (*kind).to_owned(),
            command_kind: TRANSFER.to_owned(),
            policy_root: if *kind == ASSET_KIND {
                asset_policy_registry.asset_policy_root().unwrap()
            } else {
                asset_policy_registry.fee_policy_root().unwrap()
            },
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

fn profile_for(
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

/// One ACTIVE profile whose economic policy registry governs transfers.
struct Governance {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    policy_registry: EconomicPolicyRegistryV1,
    asset_policy_registry: AssetTransferPolicyRegistryV1,
}

fn governance_with(
    policies: Vec<AssetTransferPolicyV1>,
    module_release_id: Option<RootV1>,
    kinds: &[&str],
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
    let routes = RouteRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        routes: vec![transfer_route(&asset_release_id)],
    };
    let coordinators = LaneCoordinatorRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane)| coordinator_release(*lane, index as u64 + 1))
            .collect(),
    };
    let policy_registry = governed_policy_registry(&asset_policy_registry, kinds);
    let profile = profile_for(
        &lanes,
        &coordinators,
        &routes,
        policy_registry.registry_root().unwrap(),
    );
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
    governance_with(vec![transfer_policy()], None, BOTH_KINDS)
}

fn asset_release_id(governance: &Governance) -> RootV1 {
    governance
        .lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .unwrap()
        .release_id
        .clone()
}

fn command() -> AssetTransferCommandV1 {
    AssetTransferCommandV1 {
        command_kind: TRANSFER.to_owned(),
        asset: "USD".to_owned(),
        sender: "alice".to_owned(),
        recipient: "bob".to_owned(),
        amount_atoms: 30,
        max_fee_atoms: 2,
    }
}

fn amount(owner: &str, asset: &str, amount_atoms: u128) -> EconomicAmountV1 {
    EconomicAmountV1 {
        owner: owner.to_owned(),
        asset: asset.to_owned(),
        custody_domain: "accounts".to_owned(),
        amount_atoms,
    }
}

fn supply(asset: &str, amount_atoms: u128) -> AssetSupplyV1 {
    AssetSupplyV1 {
        asset: asset.to_owned(),
        amount_atoms,
    }
}

fn default_balances() -> Vec<EconomicAmountV1> {
    vec![
        amount("alice", "USD", 100),
        amount("bob", "USD", 10),
        amount("treasury", "USD", 5),
    ]
}

/// Occurrence whose body hash is the exact canonical command payload.
fn occurrence(
    governance: &Governance,
    command: &AssetTransferCommandV1,
) -> EconomicCommandOccurrenceV1 {
    let route = governance
        .routes
        .route_for_command(TRANSFER, None)
        .expect("test route must exist");
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-transfer-policy-test".to_owned(),
        deployment_root: root(1),
        height: 11,
        tx_index: 2,
        op_index: 3,
        command_kind: TRANSFER.to_owned(),
        command_body_hash: command.command_body_hash().expect("test command must hash"),
        route_release_id: route.route_release_id.clone(),
        subject_id: command.sender.clone(),
        grant_root: root(7),
        nonce: 9,
        profile_root: governance.profile.profile_id.clone(),
        pre_state_root: root(2),
        consumed_object_ids: vec![],
    }
}

/// Transfer input whose rows and opaque roots come from the governed registry.
fn module_input(
    governance: &Governance,
    occurrence: &EconomicCommandOccurrenceV1,
    command: AssetTransferCommandV1,
    balances: Vec<EconomicAmountV1>,
    supplies: Vec<AssetSupplyV1>,
) -> AssetTransferLaneModuleInputV1 {
    let release_id = asset_release_id(governance);
    let registry = &governance.asset_policy_registry;
    AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: occurrence.chain_id.clone(),
            deployment_root: occurrence.deployment_root.clone(),
            profile_root: occurrence.profile_root.clone(),
            writer_epoch: governance.profile.authority_epoch,
            module_release_id: release_id.clone(),
            command_occurrence_id: occurrence.occurrence_id().unwrap(),
            subject_id: occurrence.subject_id.clone(),
            grant_root: occurrence.grant_root.clone(),
        },
        pre_state: AssetTransferStateV1 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: release_id,
            policies: registry.policies.clone(),
            balances,
            supplies,
        },
        command,
        asset_policy_registry_root: registry.asset_policy_root().unwrap(),
        fee_policy_registry_root: registry.fee_policy_root().unwrap(),
        custody: vec![],
    }
}

fn accept(input: &AssetTransferLaneModuleInputV1) -> AssetTransferLaneModuleAcceptedV1 {
    match transition_asset_transfer_lane_module_v1(input)
        .expect("typed transfer lane module transition must evaluate")
    {
        AssetTransferLaneModuleResultV1::Accepted(accepted) => *accepted,
        AssetTransferLaneModuleResultV1::Rejected(rejected) => {
            panic!("test transition must accept, got {:?}", rejected.code)
        }
    }
}

fn reject(input: &AssetTransferLaneModuleInputV1) -> AssetTransferRejectedV1 {
    match transition_asset_transfer_lane_module_v1(input)
        .expect("typed transfer lane module transition must evaluate")
    {
        AssetTransferLaneModuleResultV1::Accepted(_) => panic!("test transition must reject"),
        AssetTransferLaneModuleResultV1::Rejected(rejected) => *rejected,
    }
}

struct Executed {
    occurrence: EconomicCommandOccurrenceV1,
    input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
}

fn execute_command(
    governance: &Governance,
    command: AssetTransferCommandV1,
    balances: Vec<EconomicAmountV1>,
    supplies: Vec<AssetSupplyV1>,
    edit: impl FnOnce(&mut AssetTransferLaneModuleInputV1),
) -> Executed {
    let occurrence = occurrence(governance, &command);
    let mut input = module_input(governance, &occurrence, command, balances, supplies);
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
    edit: impl FnOnce(&mut AssetTransferLaneModuleInputV1),
) -> Executed {
    execute_command(
        governance,
        command(),
        default_balances(),
        vec![supply("USD", 115)],
        edit,
    )
}

fn binding_candidate<'a>(
    governance: &'a Governance,
    executed: &'a Executed,
) -> AssetTransferReleaseRouteBindingCandidateV1<'a> {
    AssetTransferReleaseRouteBindingCandidateV1 {
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
    bind_asset_transfer_lane_output_to_release_route_v1(binding_candidate(governance, executed))
}

fn membership<'a>(
    governance: &'a Governance,
    executed: &Executed,
) -> AbiResultV1<&'a AssetTransferPolicyV1> {
    require_asset_transfer_policy_membership_v1(&governance.asset_policy_registry, &executed.input)
}

fn with_state_policy(
    policy: AssetTransferPolicyV1,
) -> impl FnOnce(&mut AssetTransferLaneModuleInputV1) {
    move |input: &mut AssetTransferLaneModuleInputV1| {
        input.pre_state.policies = vec![policy];
    }
}

fn with_ungoverned_eur(
    command_asset: &'static str,
) -> impl FnOnce(&mut AssetTransferLaneModuleInputV1) {
    move |input: &mut AssetTransferLaneModuleInputV1| {
        let mut eur = transfer_policy();
        eur.asset = "EUR".to_owned();
        input.pre_state.policies.insert(0, eur);
        input
            .pre_state
            .balances
            .insert(0, amount("alice", "EUR", 100));
        input.pre_state.supplies.insert(0, supply("EUR", 100));
        input.command.asset = command_asset.to_owned();
    }
}

/// Execute the same command and policy rows under another module release.
fn under_module_release(
    module_release_id: RootV1,
) -> impl FnOnce(&mut AssetTransferLaneModuleInputV1) {
    move |input: &mut AssetTransferLaneModuleInputV1| {
        input.context.module_release_id = module_release_id.clone();
        input.pre_state.module_release_id = module_release_id;
    }
}

fn with_roots(
    asset_root: RootV1,
    fee_root: RootV1,
) -> impl FnOnce(&mut AssetTransferLaneModuleInputV1) {
    move |input: &mut AssetTransferLaneModuleInputV1| {
        input.asset_policy_registry_root = asset_root;
        input.fee_policy_registry_root = fee_root;
    }
}

#[test]
fn registry_roots_are_content_derived_domain_separated_and_lookup_is_exact() {
    // Arrange
    let registry = governance().asset_policy_registry;
    let rebuilt = registry.clone();
    let mut disabled = registry.clone();
    disabled.policies[0].enabled = false;
    let mut repriced = registry.clone();
    repriced.policies[0].transfer_fee_atoms = 1;
    let mut reowned = registry.clone();
    reowned.policies[0].fee_owner = "mallory".to_owned();

    // Act / Assert: each root commits exactly its projected columns.
    assert_eq!(
        registry.asset_policy_root().unwrap(),
        rebuilt.asset_policy_root().unwrap()
    );
    assert_eq!(
        registry.fee_policy_root().unwrap(),
        rebuilt.fee_policy_root().unwrap()
    );
    assert_ne!(
        registry.asset_policy_root().unwrap(),
        registry.fee_policy_root().unwrap()
    );
    assert_ne!(
        disabled.asset_policy_root().unwrap(),
        registry.asset_policy_root().unwrap()
    );
    assert_eq!(
        disabled.fee_policy_root().unwrap(),
        registry.fee_policy_root().unwrap()
    );
    assert_eq!(
        repriced.asset_policy_root().unwrap(),
        registry.asset_policy_root().unwrap()
    );
    assert_ne!(
        repriced.fee_policy_root().unwrap(),
        registry.fee_policy_root().unwrap()
    );
    assert_eq!(
        reowned.asset_policy_root().unwrap(),
        registry.asset_policy_root().unwrap()
    );
    assert_ne!(
        reowned.fee_policy_root().unwrap(),
        registry.fee_policy_root().unwrap()
    );
    assert_ne!(
        reowned.fee_policy_root().unwrap(),
        repriced.fee_policy_root().unwrap()
    );
    assert_eq!(registry.policy_for("USD"), Some(&transfer_policy()));
    assert_eq!(registry.policy_for("EUR"), None);
}

#[test]
fn registry_roots_bind_the_module_release_with_cross_language_vectors() {
    // Arrange: identical policy rows under two module releases.
    let fixed = registry_of(root(3), vec![transfer_policy()]);
    let other = registry_of(other_release_id(), vec![transfer_policy()]);

    // Act / Assert: the release is part of both roots, so rows cannot be replayed.
    assert_eq!(
        fixed.asset_policy_root().unwrap().as_str(),
        FIXED_RELEASE_ASSET_POLICY_ROOT_V1
    );
    assert_eq!(
        fixed.fee_policy_root().unwrap().as_str(),
        FIXED_RELEASE_FEE_POLICY_ROOT_V1
    );
    assert_eq!(
        other.asset_policy_root().unwrap().as_str(),
        OTHER_RELEASE_ASSET_POLICY_ROOT_V1
    );
    assert_eq!(
        other.fee_policy_root().unwrap().as_str(),
        OTHER_RELEASE_FEE_POLICY_ROOT_V1
    );
    assert_eq!(fixed.policies, other.policies);
}

#[test]
fn registry_rejects_wrong_schema_zero_release_unsorted_duplicate_and_over_bound_members() {
    let mut wrong_schema = governance().asset_policy_registry;
    wrong_schema.schema = GLOBAL_SETTLEMENT_ABI_V1.to_owned();
    assert_eq!(
        wrong_schema.asset_policy_root().unwrap_err(),
        AbiErrorV1::InvalidSchema
    );
    assert_eq!(
        wrong_schema.fee_policy_root().unwrap_err(),
        AbiErrorV1::InvalidSchema
    );

    let zero_release = registry_of(
        RootV1::parse(ZERO_ROOT_V1, "test zero root", true).unwrap(),
        vec![transfer_policy()],
    );
    assert_eq!(
        zero_release.asset_policy_root().unwrap_err(),
        AbiErrorV1::InvalidRoot("asset transfer policy registry module release")
    );

    let mut eur = transfer_policy();
    eur.asset = "EUR".to_owned();
    let unsorted = registry_of(root(3), vec![transfer_policy(), eur.clone()]);
    assert_eq!(
        unsorted.asset_policy_root().unwrap_err(),
        AbiErrorV1::InvalidOrder("asset transfer policy registry")
    );
    let duplicate = registry_of(root(3), vec![transfer_policy(), transfer_policy()]);
    assert_eq!(
        duplicate.fee_policy_root().unwrap_err(),
        AbiErrorV1::InvalidOrder("asset transfer policy registry")
    );
    let sorted = registry_of(root(3), vec![eur, transfer_policy()]);
    assert!(sorted.asset_policy_root().is_ok());

    let empty_token = registry_of(root(3), vec![policy_with("", 2, true)]);
    assert_eq!(
        empty_token.fee_policy_root().unwrap_err(),
        AbiErrorV1::InvalidToken("asset transfer policy fee owner")
    );

    let policies = |count: usize| {
        (0..count)
            .map(|index| {
                let mut policy = transfer_policy();
                policy.asset = format!("A{index:03}");
                policy
            })
            .collect::<Vec<_>>()
    };
    let empty = registry_of(root(3), policies(0));
    assert!(empty.asset_policy_root().is_ok());
    assert_eq!(empty.policy_for("A000"), None);
    let single = registry_of(root(3), policies(1));
    assert!(single.fee_policy_root().is_ok());
    let at_limit = registry_of(root(3), policies(MAX_ASSET_TRANSFER_POLICIES_V1));
    assert!(at_limit.asset_policy_root().is_ok());
    assert_ne!(
        at_limit.asset_policy_root().unwrap(),
        single.asset_policy_root().unwrap()
    );
    let over_limit = registry_of(root(3), policies(MAX_ASSET_TRANSFER_POLICIES_V1 + 1));
    assert_eq!(
        over_limit.asset_policy_root().unwrap_err(),
        AbiErrorV1::InvalidBounds("asset transfer policy registry")
    );
    assert_eq!(MAX_ASSET_TRANSFER_POLICIES_V1, 256);
}

#[test]
fn registry_decode_rejects_unknown_fields() {
    let decoded = serde_json::from_value::<AssetTransferPolicyRegistryV1>(json!({
        "schema": ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1,
        "module_release_id": root(3),
        "policies": [transfer_policy()],
        "extra": 1,
    }));
    assert!(decoded.is_err());
    let exact = serde_json::from_value::<AssetTransferPolicyRegistryV1>(json!({
        "schema": ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1,
        "module_release_id": root(3),
        "policies": [transfer_policy()],
    }))
    .expect("exact registry decodes");
    assert_eq!(
        exact.asset_policy_root().unwrap().as_str(),
        FIXED_RELEASE_ASSET_POLICY_ROOT_V1
    );
}

#[test]
fn governed_member_binds_and_pins_both_roots_and_the_selected_release() {
    // Arrange
    let governance = governance();
    let executed = execute(&governance, |_| {});

    // Act
    let bound = bind(&governance, &executed).expect("governed member must bind");

    // Assert
    let registry = &governance.asset_policy_registry;
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
        registry.asset_policy_root().unwrap()
    );
    assert_eq!(
        executed.input.fee_policy_registry_root,
        registry.fee_policy_root().unwrap()
    );
    assert_eq!(
        executed.input.context.module_release_id,
        registry.module_release_id
    );
    assert_eq!(
        governance.policy_registry.registry_root().unwrap(),
        governance.profile.policy_registry_root
    );
    assert_eq!(
        governance
            .policy_registry
            .require_binding(ASSET_KIND, TRANSFER)
            .unwrap()
            .policy_root,
        registry.asset_policy_root().unwrap()
    );
    assert_eq!(
        governance
            .policy_registry
            .require_binding(FEE_KIND, TRANSFER)
            .unwrap()
            .policy_root,
        registry.fee_policy_root().unwrap()
    );
}

#[test]
fn membership_returns_the_exact_governed_member() {
    let governance = governance();
    let executed = execute(&governance, |_| {});

    let member = membership(&governance, &executed).expect("governed member must resolve");

    assert_eq!(member, &transfer_policy());
}

#[test]
fn direct_transition_stays_authority_free_and_binding_pins_both_roots() {
    let governance = governance();
    let asset_root = governance
        .asset_policy_registry
        .asset_policy_root()
        .unwrap();
    let fee_root = governance.asset_policy_registry.fee_policy_root().unwrap();
    let cases = [
        (root(11), fee_root.clone(), ASSET_ROOT_MISMATCH),
        (asset_root.clone(), root(12), FEE_ROOT_MISMATCH),
        (fee_root, asset_root, ASSET_ROOT_MISMATCH),
    ];
    for (advertised_asset_root, advertised_fee_root, expected) in cases {
        // Arrange: the lane statement carries ungoverned or swapped opaque roots.
        let executed = execute(
            &governance,
            with_roots(advertised_asset_root.clone(), advertised_fee_root.clone()),
        );

        // Act / Assert: the direct transition accepted without consulting any
        // registry; only release-route binding pins both typed registry roots.
        let projected = &executed.accepted.private_port.pre_state;
        assert_eq!(projected.asset_policy_registry_root, advertised_asset_root);
        assert_eq!(projected.fee_policy_registry_root, advertised_fee_root);
        assert_eq!(bind(&governance, &executed).unwrap_err(), expected);
    }
}

#[test]
fn policy_registry_outside_the_profile_rejects_before_route_binding() {
    // Arrange: an economic policy registry whose root the profile does not pin.
    let governance = governance();
    let executed = execute(&governance, |_| {});
    let ungoverned = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![],
    };
    let mut candidate = binding_candidate(&governance, &executed);
    candidate.policy_registry = &ungoverned;

    // Act / Assert
    assert_eq!(
        bind_asset_transfer_lane_output_to_release_route_v1(candidate).unwrap_err(),
        OUTSIDE_PROFILE
    );
}

#[test]
fn omitting_either_binding_rejects_before_any_witness() {
    for retained in [ASSET_KIND, FEE_KIND] {
        // Arrange: the profile governs only one of the two transfer policy kinds.
        let governance = governance_with(vec![transfer_policy()], None, &[retained]);
        let executed = execute(&governance, |_| {});

        // Act / Assert: one binding is never enough.
        assert_eq!(bind(&governance, &executed).unwrap_err(), BINDING_ABSENT);
    }
}

#[test]
fn swapped_asset_and_fee_roots_reject_at_governed_binding() {
    // Arrange: a profile whose asset binding carries the fee root and whose fee
    // binding carries the asset root of the same typed registry.
    let governance = governance();
    let registry = &governance.asset_policy_registry;
    let mut swapped = governance.policy_registry.clone();
    for binding in &mut swapped.bindings {
        binding.policy_root = if binding.policy_kind == ASSET_KIND {
            registry.fee_policy_root().unwrap()
        } else {
            registry.asset_policy_root().unwrap()
        };
    }
    let swapped_profile = profile_for(
        &governance.lanes,
        &governance.coordinators,
        &governance.routes,
        swapped.registry_root().unwrap(),
    );
    let swapped_governance = Governance {
        profile: swapped_profile,
        lanes: governance.lanes.clone(),
        coordinators: governance.coordinators.clone(),
        routes: governance.routes.clone(),
        policy_registry: swapped,
        asset_policy_registry: registry.clone(),
    };
    let executed = execute(&swapped_governance, |_| {});

    // Act / Assert: domain separation makes the swap observable.
    assert_eq!(
        bind(&swapped_governance, &executed).unwrap_err(),
        AbiErrorV1::InvalidBinding("asset transfer asset policy root")
    );
    assert_eq!(
        require_governed_asset_transfer_policy_registry_v1(
            &swapped_governance.profile,
            &swapped_governance.lanes,
            &swapped_governance.policy_registry,
            &executed.occurrence,
            registry,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("asset transfer asset policy root")
    );
}

#[test]
fn governed_binding_requires_the_transfer_command_kind_and_the_profile_lanes() {
    let governance = governance();
    let executed = execute(&governance, |_| {});
    let mut foreign_kind = executed.occurrence.clone();
    foreign_kind.command_kind = MANAGED_ASSET_ISSUE_COMMAND_KIND_V1.to_owned();
    assert_eq!(
        require_governed_asset_transfer_policy_registry_v1(
            &governance.profile,
            &governance.lanes,
            &governance.policy_registry,
            &foreign_kind,
            &governance.asset_policy_registry,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding(
            "asset transfer policy binding requires an asset transfer command"
        )
    );

    let foreign_lanes = LaneRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane)| lane_release(*lane, index as u64 + 9))
            .collect(),
    };
    assert_eq!(
        require_governed_asset_transfer_policy_registry_v1(
            &governance.profile,
            &foreign_lanes,
            &governance.policy_registry,
            &executed.occurrence,
            &governance.asset_policy_registry,
        )
        .unwrap_err(),
        AbiErrorV1::InvalidBinding("asset transfer policy lane registry outside profile")
    );
}

#[test]
fn same_policy_rows_under_another_module_release_reject_at_membership() {
    // Arrange: the module executes the governed rows under a foreign release while
    // advertising both governed registry roots.
    let governance = governance();
    let executed = execute(&governance, under_module_release(other_release_id()));
    let registry = &governance.asset_policy_registry;
    assert_eq!(
        executed.input.asset_policy_registry_root,
        registry.asset_policy_root().unwrap()
    );
    assert_eq!(
        executed.input.fee_policy_registry_root,
        registry.fee_policy_root().unwrap()
    );

    // Act / Assert
    assert_eq!(bind(&governance, &executed).unwrap_err(), RELEASE_MISMATCH);
}

#[test]
fn registry_bound_to_another_release_rejects_at_governed_binding() {
    // Arrange: the profile governs rows bound to a foreign release; the module runs
    // under the active release and advertises that governed registry's roots.
    let governance = governance_with(
        vec![transfer_policy()],
        Some(other_release_id()),
        BOTH_KINDS,
    );
    let executed = execute(&governance, |_| {});

    // Act / Assert: the registry release is not the profile-selected release.
    assert_eq!(
        bind(&governance, &executed).unwrap_err(),
        NOT_PROFILE_SELECTED
    );
    assert_eq!(
        membership(&governance, &executed).unwrap_err(),
        RELEASE_MISMATCH
    );
}

#[test]
fn route_release_check_remains_independent_of_registry_membership() {
    // Arrange: rows, registry, context, and pre-state all agree on a foreign release
    // that the governed lane registry does not carry.
    let governance = governance_with(
        vec![transfer_policy()],
        Some(other_release_id()),
        BOTH_KINDS,
    );
    let executed = execute(&governance, under_module_release(other_release_id()));

    // Act / Assert: membership passes on its own and governed binding still
    // fails closed on the profile-selected release.
    assert_eq!(
        membership(&governance, &executed).unwrap(),
        &transfer_policy()
    );
    assert_eq!(
        bind(&governance, &executed).unwrap_err(),
        NOT_PROFILE_SELECTED
    );
    assert_ne!(asset_release_id(&governance), other_release_id());
}

#[test]
fn fee_owner_and_fee_atoms_state_mutations_reject_at_membership() {
    let governance = governance();
    let rogues = [
        policy_with("mallory", 2, true),
        policy_with("treasury", 1, true),
        policy_with("mallory", 1, true),
        policy_with("treasury", 0, true),
    ];
    for rogue in rogues {
        // Arrange: the executed state row differs from the governed member in one
        // fee column while both opaque roots stay governed.
        let executed = execute(&governance, with_state_policy(rogue));

        // Act / Assert: the module accepted, governed membership does not.
        assert_eq!(bind(&governance, &executed).unwrap_err(), MEMBER_MISMATCH);
        assert_eq!(
            membership(&governance, &executed).unwrap_err(),
            MEMBER_MISMATCH
        );
    }
}

#[test]
fn enablement_mutation_rejects_at_membership() {
    // Arrange: governance disabled USD; the module executes an enabled row while
    // advertising the disabled registry's roots.
    let governance = governance_with(vec![policy_with("treasury", 2, false)], None, BOTH_KINDS);
    let executed = execute(&governance, with_state_policy(transfer_policy()));

    // Act / Assert
    assert_eq!(bind(&governance, &executed).unwrap_err(), MEMBER_MISMATCH);
}

#[test]
fn disabled_governed_member_admits_no_transfer() {
    // Arrange: governance disabled USD and the state row agrees.
    let governance = governance_with(vec![policy_with("treasury", 2, false)], None, BOTH_KINDS);
    let command = command();
    let occurrence = occurrence(&governance, &command);
    let input = module_input(
        &governance,
        &occurrence,
        command,
        default_balances(),
        vec![supply("USD", 115)],
    );

    // Act / Assert: membership is exact and the transition rejects as a no-op.
    assert_eq!(
        require_asset_transfer_policy_membership_v1(&governance.asset_policy_registry, &input)
            .unwrap(),
        &policy_with("treasury", 2, false)
    );
    let rejected = reject(&input);
    assert_eq!(rejected.code, AssetTransferRejectCodeV1::DISABLED_ASSET);
    assert_eq!(
        rejected.post_state_root,
        input.pre_state.state_root().unwrap()
    );
    assert!(rejected.effects.rows.is_empty());
}

#[test]
fn command_asset_absent_from_the_governed_registry_rejects() {
    // Arrange: the state carries an ungoverned EUR row and the command moves EUR.
    let governance = governance();
    let executed = execute(&governance, with_ungoverned_eur("EUR"));

    // Act / Assert
    assert_eq!(bind(&governance, &executed).unwrap_err(), MEMBER_ABSENT);
}

#[test]
fn state_carrying_an_ungoverned_extra_policy_rejects() {
    // Arrange: the command targets the governed USD member, the state also carries EUR.
    let governance = governance();
    let executed = execute(&governance, with_ungoverned_eur("USD"));

    // Act / Assert
    assert_eq!(bind(&governance, &executed).unwrap_err(), MEMBER_MISMATCH);
}

#[test]
fn state_omitting_the_governed_command_policy_rejects_at_membership() {
    // Arrange: the registry governs USD, the pre-state carries no USD row.
    let governance = governance();
    let command = command();
    let occurrence = occurrence(&governance, &command);
    let mut input = module_input(&governance, &occurrence, command, vec![], vec![]);
    input.pre_state.policies.clear();

    // Act / Assert: membership rejects before any transition consultation, and
    // the direct transition cannot accept such a state either.
    assert_eq!(
        require_asset_transfer_policy_membership_v1(&governance.asset_policy_registry, &input)
            .unwrap_err(),
        AbiErrorV1::InvalidBinding("asset transfer state omits the governed command policy")
    );
    assert_eq!(
        reject(&input).code,
        AssetTransferRejectCodeV1::UNKNOWN_ASSET
    );
}

#[test]
fn empty_governed_registry_rejects_every_asset() {
    // Arrange: governance commits an empty registry; the module still executes
    // its own USD row while advertising the empty registry's roots.
    let governance = governance_with(vec![], None, BOTH_KINDS);
    let executed = execute(&governance, |input| {
        input.pre_state.policies = vec![transfer_policy()];
    });

    // Act / Assert
    assert_eq!(bind(&governance, &executed).unwrap_err(), MEMBER_ABSENT);
}

#[test]
fn stale_roots_after_policy_rotation_reject_before_any_witness() {
    let old = governance();
    let executed = execute(&old, |_| {});
    let rotations = [
        (policy_with("vault", 2, true), FEE_ROOT_MISMATCH),
        (policy_with("treasury", 3, true), FEE_ROOT_MISMATCH),
        (policy_with("treasury", 2, false), ASSET_ROOT_MISMATCH),
    ];
    for (rotated, expected) in rotations {
        // Arrange: governance rotated one policy column; an output executed under
        // the old registry roots is presented to the rotated profile.
        let new = governance_with(vec![rotated], None, BOTH_KINDS);
        assert_ne!(new.profile.profile_id, old.profile.profile_id);

        // Act / Assert: the stale roots reject at membership, before the old
        // occurrence or witness is compared.
        assert_eq!(bind(&new, &executed).unwrap_err(), expected);
    }
}

#[test]
fn membership_is_content_bound_not_identity_bound() {
    // Arrange
    let governance = governance();
    let executed = execute(&governance, |_| {});
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
fn coherent_foreign_output_rejects_at_recomputation_after_governed_checks() {
    // Arrange: a coherent amount+1 output whose public statement is rebound to
    // the honest input; governed checks pass and recomputation must reject.
    let governance = governance();
    let executed = execute(&governance, |_| {});
    let mut foreign_input = executed.input.clone();
    foreign_input.command.amount_atoms += 1;
    let mut forged = accept(&foreign_input);
    forged.statement_root = executed.input.statement_root().unwrap();
    forged.module_journal.receipt_root = hash_global_v1(
        "asset-transfer-lane-module-receipt-v1",
        &json!({
            "statement_root": forged.statement_root,
            "pre_state_root": forged.module_journal.pre_lane_root,
            "post_state_root": forged.module_journal.post_lane_root,
            "effect_plan_root": forged.effects.effect_plan_root().unwrap(),
            "private_port_root": forged.private_port.port_root().unwrap(),
            "terminal_obligations_root": forged.private_port.terminal_obligations_root,
        }),
    )
    .unwrap();
    forged
        .validate()
        .expect("forged output remains structurally self-consistent");
    let forged_executed = Executed {
        occurrence: executed.occurrence.clone(),
        input: executed.input.clone(),
        accepted: forged,
    };

    // Act / Assert: trusting the supplied acceptance is never an option.
    assert_eq!(
        bind(&governance, &forged_executed).unwrap_err(),
        AbiErrorV1::InvalidBinding("asset transfer supplied acceptance differs from recomputation")
    );
}

#[test]
fn governed_binding_preserves_fee_boundaries() {
    for transfer_fee_atoms in [0_u128, 1_u128] {
        // Arrange: governance rows at the zero and one-atom fee boundaries.
        let governance = governance_with(
            vec![policy_with("treasury", transfer_fee_atoms, true)],
            None,
            BOTH_KINDS,
        );
        let mut command = command();
        command.max_fee_atoms = transfer_fee_atoms;
        let executed = execute_command(
            &governance,
            command,
            vec![amount("alice", "USD", 100), amount("bob", "USD", 10)],
            vec![supply("USD", 110)],
            |_| {},
        );

        // Act
        let bound = bind(&governance, &executed).expect("governed fee boundary must bind");

        // Assert: the typed economic transition is preserved under governance.
        let post_state = &executed.accepted.post_state;
        assert_eq!(
            bound.statement_root(),
            &executed.input.statement_root().unwrap()
        );
        assert_eq!(
            post_state.balance_atoms("alice", "USD"),
            100 - 30 - transfer_fee_atoms
        );
        assert_eq!(
            post_state.balance_atoms("treasury", "USD"),
            transfer_fee_atoms
        );
        assert_eq!(
            executed.accepted.effects.fee_conservation.len(),
            usize::from(transfer_fee_atoms != 0)
        );
    }
}

#[test]
fn governed_binding_preserves_signed_effect_overflow_neighbors() {
    // Arrange: a zero-fee governed row with the exact i128 magnitude neighbors.
    let governance = governance_with(vec![policy_with("treasury", 0, true)], None, BOTH_KINDS);
    let representable: u128 = (1_u128 << 127) - 1;
    let overflowing: u128 = 1_u128 << 127;
    let mut command = command();
    command.amount_atoms = representable;
    command.max_fee_atoms = 0;
    let executed = execute_command(
        &governance,
        command,
        vec![amount("alice", "USD", representable)],
        vec![supply("USD", representable)],
        |_| {},
    );
    let mut overflow_command = self::command();
    overflow_command.amount_atoms = overflowing;
    overflow_command.max_fee_atoms = 0;
    let overflow_occurrence = occurrence(&governance, &overflow_command);
    let overflow_input = module_input(
        &governance,
        &overflow_occurrence,
        overflow_command,
        vec![amount("alice", "USD", overflowing)],
        vec![supply("USD", overflowing)],
    );

    // Act / Assert: the representable neighbor binds; the overflowing neighbor
    // is a typed no-op rejection with nothing to bind.
    let bound = bind(&governance, &executed).expect("representable neighbor must bind");
    assert_eq!(
        bound.statement_root(),
        &executed.input.statement_root().unwrap()
    );
    assert_eq!(
        executed.accepted.post_state.balance_atoms("bob", "USD"),
        representable
    );
    assert_eq!(
        executed.accepted.post_state.balance_atoms("alice", "USD"),
        0
    );
    let rejected = reject(&overflow_input);
    assert_eq!(
        rejected.code,
        AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW
    );
    assert!(rejected.effects.rows.is_empty());
}

#[test]
fn governed_binding_preserves_fee_owner_alias_aggregation() {
    for (fee_owner, alice_atoms, bob_atoms, owner_delta) in
        [("alice", 70_u128, 40_u128, -30_i128), ("bob", 68, 42, 32)]
    {
        // Arrange: the governed fee owner aliases the sender or the recipient.
        let governance = governance_with(vec![policy_with(fee_owner, 2, true)], None, BOTH_KINDS);
        let executed = execute_command(
            &governance,
            command(),
            vec![amount("alice", "USD", 100), amount("bob", "USD", 10)],
            vec![supply("USD", 110)],
            |_| {},
        );

        // Act
        let bound = bind(&governance, &executed).expect("aliased fee owner must bind");

        // Assert
        let post_state = &executed.accepted.post_state;
        assert_eq!(
            bound.statement_root(),
            &executed.input.statement_root().unwrap()
        );
        assert_eq!(post_state.balance_atoms("alice", "USD"), alice_atoms);
        assert_eq!(post_state.balance_atoms("bob", "USD"), bob_atoms);
        let owner_row = executed
            .accepted
            .effects
            .rows
            .iter()
            .find(|row| {
                row.kind == EconomicEffectKindV1::ACCOUNT_MOVEMENT && row.principal == fee_owner
            })
            .expect("fee owner movement row must exist");
        assert_eq!(owner_row.delta_atoms, owner_delta);
    }
}

#[test]
fn governed_binding_preserves_first_credit_and_zero_row_removal() {
    // Arrange: Alice is fully debited (amount plus fee) into Carol's first credit.
    let governance = governance();
    let mut command = command();
    command.recipient = "carol".to_owned();
    let executed = execute_command(
        &governance,
        command,
        vec![amount("alice", "USD", 32), amount("treasury", "USD", 5)],
        vec![supply("USD", 37)],
        |_| {},
    );

    // Act
    let bound = bind(&governance, &executed).expect("first credit must bind");

    // Assert: the absent recipient gains its first row and the zero row is removed.
    let post_state = &executed.accepted.post_state;
    assert_eq!(
        bound.statement_root(),
        &executed.input.statement_root().unwrap()
    );
    assert_eq!(
        post_state
            .balances
            .iter()
            .map(|row| (row.owner.as_str(), row.amount_atoms))
            .collect::<Vec<_>>(),
        vec![("carol", 30), ("treasury", 7)]
    );
    assert_eq!(post_state.balance_atoms("alice", "USD"), 0);
    assert_eq!(
        executed.accepted.effects.asset_conservation[0].owned_and_custodied_post_atoms,
        37
    );
}

#[test]
fn governed_binding_rejection_precedence_is_exact() {
    // Arrange: candidates carrying two defects each; the earlier check wins.
    let governance = governance();
    let one_binding = governance_with(vec![transfer_policy()], None, &[ASSET_KIND]);
    let ungoverned = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![],
    };
    let absent_and_extra = execute(&governance, with_ungoverned_eur("EUR"));
    let stale_roots_one_binding = execute(&one_binding, with_roots(root(11), root(12)));
    let stale_and_foreign_release = execute(&governance, |input| {
        under_module_release(other_release_id())(input);
        input.asset_policy_registry_root = root(11);
    });
    let foreign_release_absent_member = execute(&governance, |input| {
        under_module_release(other_release_id())(input);
        with_ungoverned_eur("EUR")(input);
    });
    let mut outside_profile = binding_candidate(&governance, &absent_and_extra);
    outside_profile.policy_registry = &ungoverned;

    // Act / Assert
    assert_eq!(
        bind_asset_transfer_lane_output_to_release_route_v1(outside_profile).unwrap_err(),
        OUTSIDE_PROFILE,
        "outside profile precedes absent member"
    );
    assert_eq!(
        bind(&one_binding, &stale_roots_one_binding).unwrap_err(),
        BINDING_ABSENT,
        "absent binding precedes stale roots"
    );
    assert_eq!(
        bind(&governance, &stale_and_foreign_release).unwrap_err(),
        ASSET_ROOT_MISMATCH,
        "stale root precedes foreign release"
    );
    assert_eq!(
        bind(&governance, &foreign_release_absent_member).unwrap_err(),
        RELEASE_MISMATCH,
        "foreign release precedes absent member"
    );
}

#[test]
fn input_edit_alias_type_is_exercised() {
    // The closure alias keeps the edit-shaped helpers exhaustive for readers.
    let edits: [InputEdit; 1] = [|input| input.custody.clear()];
    let governance = governance();
    let executed = execute(&governance, edits[0]);
    assert!(bind(&governance, &executed).is_ok());
}
