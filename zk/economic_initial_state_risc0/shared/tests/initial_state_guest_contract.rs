use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_economic_initial_state_risc0_shared::{
    canonical_economic_initial_state_guest_input_bytes_v1,
    prepare_economic_initial_state_from_canonical_bytes_v1, prepare_economic_initial_state_v1,
    EconomicInitialStateGuestErrorV1, EconomicInitialStateGuestInputV1,
    ECONOMIC_INITIAL_STATE_GUEST_INPUT_SCHEMA_V1,
};
use zenodex_global_settlement_abi_v1::{
    derive_economic_initial_state_atom_occurrences_v1,
    derive_economic_initial_state_outbox_continuity_root_v1,
    derive_economic_initial_state_replay_continuity_root_v1,
    derive_economic_initial_state_terminal_continuity_root_v1,
    economic_initial_state_atom_coverage_policy_binding_v1, EconomicAmountV1,
    EconomicInitialStateAtomClassificationV1, EconomicInitialStateAtomSourceV1,
    EconomicInitialStateJournalV1, EconomicInitialStateKindV1,
    EconomicInitialStateSourceManifestV1, EconomicPolicyBindingV1, EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1, GlobalEconomicStateV1, OutboxStateV1, OutboxStatusV1, ReplayStateV1,
    RootV1, GLOBAL_SETTLEMENT_ABI_V1, M6_ASSET_PRECISION_POLICY_KIND_V1,
    M6_ASSET_PRECISION_POLICY_ROOT_V1, M6_ASSET_PRECISION_PROFILE_COMMAND_KIND_V1,
    M6_CAPABILITY_MANIFEST_ROOT_V1, M6_CAPABILITY_POLICY_KIND_V1,
    M6_CAPABILITY_PROFILE_COMMAND_KIND_V1, MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "initial-state guest test root",
        false,
    )
    .unwrap()
}

fn fixture_vector(name: &str) -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("tests/data/global_settlement_abi_v1_golden.json");
    let fixture: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    fixture["vectors"][name]["canonical"].clone()
}

fn fixture() -> EconomicInitialStateGuestInputV1 {
    let mut profile: EconomicProfileSnapshotV1 =
        serde_json::from_value(fixture_vector("economic_profile")).unwrap();
    let mut state: GlobalEconomicStateV1 =
        serde_json::from_value(fixture_vector("global_state")).unwrap();
    let source_manifest = EconomicInitialStateSourceManifestV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind: EconomicInitialStateKindV1::MIGRATION,
        rows: derive_economic_initial_state_atom_occurrences_v1(&state)
            .unwrap()
            .into_iter()
            .enumerate()
            .map(|(index, occurrence)| EconomicInitialStateAtomSourceV1 {
                occurrence,
                classification: EconomicInitialStateAtomClassificationV1::MigratedTarget,
                source_authorization_root: root(1_000 + u64::try_from(index).unwrap()),
            })
            .collect(),
    };
    let policy_registry = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![
            EconomicPolicyBindingV1 {
                policy_kind: M6_ASSET_PRECISION_POLICY_KIND_V1.to_owned(),
                command_kind: M6_ASSET_PRECISION_PROFILE_COMMAND_KIND_V1.to_owned(),
                policy_root: RootV1::parse(
                    M6_ASSET_PRECISION_POLICY_ROOT_V1,
                    "precision policy root",
                    false,
                )
                .unwrap(),
            },
            EconomicPolicyBindingV1 {
                policy_kind: M6_CAPABILITY_POLICY_KIND_V1.to_owned(),
                command_kind: M6_CAPABILITY_PROFILE_COMMAND_KIND_V1.to_owned(),
                policy_root: RootV1::parse(
                    M6_CAPABILITY_MANIFEST_ROOT_V1,
                    "capability policy root",
                    false,
                )
                .unwrap(),
            },
            economic_initial_state_atom_coverage_policy_binding_v1(&source_manifest).unwrap(),
        ],
    };
    profile.policy_registry_root = policy_registry.registry_root().unwrap();
    let profile_content = serde_json::json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "authority_epoch": profile.authority_epoch,
        "lane_registry_root": profile.lane_registry_root,
        "lane_coordinator_registry_root": profile.lane_coordinator_registry_root,
        "route_registry_root": profile.route_registry_root,
        "proof_shape_root": profile.proof_shape_root,
        "root_image_id": profile.root_image_id,
        "verifier_registry_root": profile.verifier_registry_root,
        "migration_registry_root": profile.migration_registry_root,
        "policy_registry_root": profile.policy_registry_root,
        "terminal_registry_root": profile.terminal_registry_root,
    });
    profile.profile_id = zenodex_global_settlement_abi_v1::hash_global_v1(
        "global-economic-profile-content-v1",
        &profile_content,
    )
    .unwrap();
    let mut predecessor_state = state.clone();
    predecessor_state.profile_root = root(2_001);
    predecessor_state.writer_epoch = state.writer_epoch.checked_sub(1).unwrap();
    predecessor_state.height = state.height.checked_sub(1).unwrap();
    state.profile_root = profile.profile_id.clone();
    let statement = EconomicInitialStateJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind: EconomicInitialStateKindV1::MIGRATION,
        chain_id: state.chain_id.clone(),
        deployment_root: state.deployment_root.clone(),
        profile_root: profile.profile_id.clone(),
        writer_epoch: state.writer_epoch,
        height: state.height,
        state_root: state.state_root().unwrap(),
        source_profile_root: root(2_001),
        source_state_root: predecessor_state.state_root().unwrap(),
        source_writer_epoch: predecessor_state.writer_epoch,
        source_height: predecessor_state.height,
        state_atom_coverage_root: source_manifest.manifest_root().unwrap(),
        lane_object_coverage_root: root(2_003),
        replay_continuity_root: derive_economic_initial_state_replay_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            &state,
            Some(&predecessor_state),
        )
        .unwrap(),
        terminal_continuity_root: derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            &state,
            Some(&predecessor_state),
        )
        .unwrap(),
        outbox_continuity_root: derive_economic_initial_state_outbox_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            &state,
            Some(&predecessor_state),
        )
        .unwrap(),
        source_manifest_root: root(2_007),
        toolchain_manifest_root: root(2_008),
        root_image_id: profile.root_image_id.clone(),
    };
    EconomicInitialStateGuestInputV1 {
        schema: ECONOMIC_INITIAL_STATE_GUEST_INPUT_SCHEMA_V1.to_owned(),
        profile,
        policy_registry,
        state,
        predecessor_state: Some(predecessor_state),
        source_manifest,
        statement,
    }
}

#[test]
fn exact_profile_state_manifest_statement_prepares_the_committed_journal() {
    // Arrange
    let input = fixture();
    let expected_journal = input.statement.canonical_bytes().unwrap();

    // Act
    let prepared = prepare_economic_initial_state_v1(input).unwrap();

    // Assert
    assert_eq!(prepared.journal_bytes(), expected_journal);
}

#[test]
fn state_or_source_substitution_rejects_before_any_receipt_exists() {
    // Arrange
    let input = fixture();
    let mut changed_state = input.clone();
    changed_state.state.balances[0].amount_atoms += 1;
    let mut changed_source = input;
    changed_source.source_manifest.rows[0].source_authorization_root = root(9_001);

    // Act / Assert
    assert!(matches!(
        prepare_economic_initial_state_v1(changed_state),
        Err(EconomicInitialStateGuestErrorV1::StatementBinding)
    ));
    assert!(matches!(
        prepare_economic_initial_state_v1(changed_source),
        Err(EconomicInitialStateGuestErrorV1::StatementBinding)
    ));
}

#[test]
fn predecessor_substitution_or_absence_rejects_before_any_receipt_exists() {
    // Arrange
    let input = fixture();
    let mut changed_predecessor = input.clone();
    changed_predecessor
        .predecessor_state
        .as_mut()
        .unwrap()
        .balances[0]
        .amount_atoms += 1;
    let mut missing_predecessor = input;
    missing_predecessor.predecessor_state = None;
    let mut changed_replay_root = fixture();
    changed_replay_root.statement.replay_continuity_root = root(9_002);
    let mut changed_outbox_root = fixture();
    changed_outbox_root.statement.outbox_continuity_root = root(9_004);
    let mut changed_terminal_root = fixture();
    changed_terminal_root.statement.terminal_continuity_root = root(9_005);
    let mut deleted_replay = fixture();
    deleted_replay
        .predecessor_state
        .as_mut()
        .unwrap()
        .replay_state = vec![ReplayStateV1 {
        replay_id: "source-replay-1".to_owned(),
        occurrence_id: root(9_003),
    }];
    deleted_replay.statement.source_state_root = deleted_replay
        .predecessor_state
        .as_ref()
        .unwrap()
        .state_root()
        .unwrap();

    // Act / Assert
    assert!(matches!(
        prepare_economic_initial_state_v1(changed_predecessor),
        Err(EconomicInitialStateGuestErrorV1::StatementBinding)
    ));
    assert!(matches!(
        prepare_economic_initial_state_v1(missing_predecessor),
        Err(EconomicInitialStateGuestErrorV1::StatementBinding)
    ));
    assert!(matches!(
        prepare_economic_initial_state_v1(changed_replay_root),
        Err(EconomicInitialStateGuestErrorV1::StatementBinding)
    ));
    assert!(matches!(
        prepare_economic_initial_state_v1(changed_outbox_root),
        Err(EconomicInitialStateGuestErrorV1::StatementBinding)
    ));
    assert!(matches!(
        prepare_economic_initial_state_v1(changed_terminal_root),
        Err(EconomicInitialStateGuestErrorV1::StatementBinding)
    ));
    assert!(matches!(
        prepare_economic_initial_state_v1(deleted_replay),
        Err(EconomicInitialStateGuestErrorV1::StatementBinding)
    ));
}

#[test]
fn noncanonical_wire_bytes_reject_before_statement_execution() {
    // Arrange
    let input = fixture();
    let mut bytes = canonical_economic_initial_state_guest_input_bytes_v1(&input).unwrap();
    bytes.push(b'\n');

    // Act / Assert
    assert!(matches!(
        prepare_economic_initial_state_from_canonical_bytes_v1(&bytes),
        Err(EconomicInitialStateGuestErrorV1::NonCanonicalInput)
    ));
}

#[test]
fn guest_rejects_4097_rows_before_validating_the_hostile_first_row() {
    // Arrange
    let mut input = fixture();
    input.state.balances = (0..4_097)
        .map(|index| EconomicAmountV1 {
            owner: format!("owner-{index:04}"),
            asset: "ZDEX".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: u128::try_from(index).unwrap(),
        })
        .collect();
    input.state.balances[0].owner = "invalid unicode ☃".to_owned();
    input.state.supplies.clear();

    // Act / Assert
    assert!(matches!(
        prepare_economic_initial_state_v1(input),
        Err(EconomicInitialStateGuestErrorV1::ExplicitRowCount)
    ));
}

#[test]
fn canonical_wire_decoder_maps_oversized_nested_state_to_decode() {
    let mut input = fixture();
    let row = input.state.balances[0].clone();
    input.state.balances = vec![row; MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1 + 1];
    let bytes = serde_json::to_vec(&input).unwrap();

    assert!(matches!(
        prepare_economic_initial_state_from_canonical_bytes_v1(&bytes),
        Err(EconomicInitialStateGuestErrorV1::Decode)
    ));
}

#[test]
fn guest_rejects_4097_predecessor_rows_before_validating_the_hostile_first_row() {
    // Arrange
    let mut input = fixture();
    let predecessor = input.predecessor_state.as_mut().unwrap();
    predecessor.balances = (0..4_097)
        .map(|index| EconomicAmountV1 {
            owner: format!("owner-{index:04}"),
            asset: "ZDEX".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: u128::try_from(index).unwrap(),
        })
        .collect();
    predecessor.balances[0].owner = "invalid unicode ☃".to_owned();
    predecessor.supplies.clear();

    // Act / Assert
    assert!(matches!(
        prepare_economic_initial_state_v1(input),
        Err(EconomicInitialStateGuestErrorV1::ExplicitRowCount)
    ));
}

fn oversized_outbox() -> Vec<OutboxStateV1> {
    let mut rows: Vec<_> = (0..4_097)
        .map(|index| OutboxStateV1 {
            effect_id: root(20_000 + index),
            destination_id: "bridge:test".to_owned(),
            payload_hash: root(30_000 + index),
            commit_id: root(40_000 + index),
            status: OutboxStatusV1::PENDING,
        })
        .collect();
    rows[0].destination_id = "invalid unicode ☃".to_owned();
    rows
}

#[test]
fn guest_preflights_4097_target_outbox_rows_before_row_validation() {
    // Arrange
    let mut input = fixture();
    input.state.outbox = oversized_outbox();

    // Act / Assert
    assert!(matches!(
        prepare_economic_initial_state_v1(input),
        Err(EconomicInitialStateGuestErrorV1::OutboxRowCount)
    ));
}

#[test]
fn guest_preflights_4097_predecessor_outbox_rows_before_row_validation() {
    // Arrange
    let mut input = fixture();
    input.predecessor_state.as_mut().unwrap().outbox = oversized_outbox();

    // Act / Assert
    assert!(matches!(
        prepare_economic_initial_state_v1(input),
        Err(EconomicInitialStateGuestErrorV1::OutboxRowCount)
    ));
}
