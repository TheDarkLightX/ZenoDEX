use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    derive_economic_initial_state_atom_occurrences_v1,
    derive_economic_initial_state_outbox_continuity_root_v1,
    derive_economic_initial_state_replay_continuity_root_v1,
    derive_economic_initial_state_terminal_continuity_root_v1,
    economic_initial_state_atom_coverage_policy_binding_v1, hash_bytes_sha256_v1, hash_global_v1,
    validate_economic_initial_state_bindings_v1,
    validate_economic_initial_state_statement_bindings_v1, AbiErrorV1, EconomicAmountV1,
    EconomicInitialStateAtomClassificationV1, EconomicInitialStateAtomSourceV1,
    EconomicInitialStateCertificateV1, EconomicInitialStateKindV1,
    EconomicInitialStateSourceManifestV1, EconomicPolicyBindingV1, EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1, GlobalEconomicStateV1, OutboxStateV1, OutboxStatusV1,
    ProfileStatusV1, ReceiptKindV1, ReplayStateV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
    M6_ASSET_PRECISION_POLICY_KIND_V1, M6_ASSET_PRECISION_POLICY_ROOT_V1,
    M6_ASSET_PRECISION_PROFILE_COMMAND_KIND_V1, M6_CAPABILITY_MANIFEST_ROOT_V1,
    M6_CAPABILITY_POLICY_KIND_V1, M6_CAPABILITY_PROFILE_COMMAND_KIND_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "initial state test root", false).unwrap()
}

fn fixture_vector(name: &str) -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_settlement_abi_v1_golden.json");
    let fixture: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    fixture["vectors"][name]["canonical"].clone()
}

fn source_manifest(
    state: &GlobalEconomicStateV1,
    kind: EconomicInitialStateKindV1,
) -> EconomicInitialStateSourceManifestV1 {
    let classification = match kind {
        EconomicInitialStateKindV1::GENESIS => {
            EconomicInitialStateAtomClassificationV1::GenesisAllocation
        }
        EconomicInitialStateKindV1::MIGRATION => {
            EconomicInitialStateAtomClassificationV1::MigratedTarget
        }
    };
    EconomicInitialStateSourceManifestV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind,
        rows: derive_economic_initial_state_atom_occurrences_v1(state)
            .unwrap()
            .into_iter()
            .enumerate()
            .map(|(index, occurrence)| EconomicInitialStateAtomSourceV1 {
                occurrence,
                classification,
                source_authorization_root: root(1_000 + u64::try_from(index).unwrap()),
            })
            .collect(),
    }
}

fn policy_registry(
    source_manifest: &EconomicInitialStateSourceManifestV1,
) -> EconomicPolicyRegistryV1 {
    EconomicPolicyRegistryV1 {
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
            economic_initial_state_atom_coverage_policy_binding_v1(source_manifest).unwrap(),
        ],
    }
}

fn profile_and_state(
    kind: EconomicInitialStateKindV1,
) -> (
    EconomicProfileSnapshotV1,
    EconomicPolicyRegistryV1,
    GlobalEconomicStateV1,
    EconomicInitialStateSourceManifestV1,
) {
    let mut profile: EconomicProfileSnapshotV1 =
        serde_json::from_value(fixture_vector("economic_profile")).unwrap();
    let mut state: GlobalEconomicStateV1 =
        serde_json::from_value(fixture_vector("global_state")).unwrap();
    let source_manifest = source_manifest(&state, kind);
    let policy_registry = policy_registry(&source_manifest);
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
    profile.profile_id =
        hash_global_v1("global-economic-profile-content-v1", &profile_content).unwrap();
    state.profile_root = profile.profile_id.clone();
    (profile, policy_registry, state, source_manifest)
}

fn migration_certificate(
    profile: &EconomicProfileSnapshotV1,
    state: &GlobalEconomicStateV1,
    predecessor_state: &GlobalEconomicStateV1,
    source_manifest: &EconomicInitialStateSourceManifestV1,
    receipt_bytes: &[u8],
) -> EconomicInitialStateCertificateV1 {
    let mut certificate = EconomicInitialStateCertificateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind: EconomicInitialStateKindV1::MIGRATION,
        chain_id: state.chain_id.clone(),
        deployment_root: state.deployment_root.clone(),
        profile_root: profile.profile_id.clone(),
        writer_epoch: state.writer_epoch,
        height: state.height,
        state_root: state.state_root().unwrap(),
        source_profile_root: predecessor_state.profile_root.clone(),
        source_state_root: predecessor_state.state_root().unwrap(),
        source_writer_epoch: predecessor_state.writer_epoch,
        source_height: predecessor_state.height,
        state_atom_coverage_root: source_manifest.manifest_root().unwrap(),
        lane_object_coverage_root: root(33),
        replay_continuity_root: derive_economic_initial_state_replay_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            state,
            Some(predecessor_state),
        )
        .unwrap(),
        terminal_continuity_root: derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            state,
            Some(predecessor_state),
        )
        .unwrap(),
        outbox_continuity_root: derive_economic_initial_state_outbox_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            state,
            Some(predecessor_state),
        )
        .unwrap(),
        source_manifest_root: root(37),
        toolchain_manifest_root: root(38),
        root_image_id: profile.root_image_id.clone(),
        receipt_root: RootV1::parse(
            format!("0x{}", hash_bytes_sha256_v1(receipt_bytes)),
            "initial state receipt root",
            false,
        )
        .unwrap(),
        receipt_kind: ReceiptKindV1::SUCCINCT,
        journal_bytes: 1,
        cycle_budget: 1_000_000,
    };
    certificate.journal_bytes =
        u64::try_from(certificate.canonical_journal_bytes().unwrap().len()).unwrap();
    certificate
}

fn migration_predecessor(state: &GlobalEconomicStateV1) -> GlobalEconomicStateV1 {
    let mut predecessor = state.clone();
    predecessor.profile_root = root(30);
    predecessor.writer_epoch = state.writer_epoch.checked_sub(1).unwrap();
    predecessor.height = state.height.checked_sub(1).unwrap();
    predecessor
}

fn genesis_certificate() -> EconomicInitialStateCertificateV1 {
    let receipt_bytes = b"initial-golden";
    let mut certificate = EconomicInitialStateCertificateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        kind: EconomicInitialStateKindV1::GENESIS,
        chain_id: "tau-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        height: 0,
        state_root: root(3),
        source_profile_root: RootV1::parse(
            "0x0000000000000000000000000000000000000000000000000000000000000000",
            "zero source profile",
            true,
        )
        .unwrap(),
        source_state_root: RootV1::parse(
            "0x0000000000000000000000000000000000000000000000000000000000000000",
            "zero source state",
            true,
        )
        .unwrap(),
        source_writer_epoch: 0,
        source_height: 0,
        state_atom_coverage_root: root(4),
        lane_object_coverage_root: root(5),
        replay_continuity_root: root(6),
        terminal_continuity_root: root(7),
        outbox_continuity_root: root(8),
        source_manifest_root: root(9),
        toolchain_manifest_root: root(10),
        root_image_id: root(11),
        receipt_root: RootV1::parse(
            format!("0x{}", hash_bytes_sha256_v1(receipt_bytes)),
            "genesis receipt root",
            false,
        )
        .unwrap(),
        receipt_kind: ReceiptKindV1::SUCCINCT,
        journal_bytes: 1,
        cycle_budget: 1_000_000,
    };
    certificate.journal_bytes =
        u64::try_from(certificate.canonical_journal_bytes().unwrap().len()).unwrap();
    certificate
}

#[test]
fn genesis_certificate_matches_python_golden_roots() {
    let certificate = genesis_certificate();

    assert_eq!(certificate.journal_bytes, 1_336);
    assert_eq!(
        hash_bytes_sha256_v1(&certificate.canonical_journal_bytes().unwrap()),
        "eaa2444864e429f494f61220afecb9610e0d6195aa1d4cb59f34b9193ca5dd88"
    );
    assert_eq!(
        certificate.certificate_root().unwrap().as_str(),
        "0xaad3f289eaa13fc2e96451aa051437c6a91955bd6d026ee3d15517b392c9d809"
    );
}

#[test]
fn genesis_predecessor_binding_requires_absence() {
    // Arrange
    let (profile, policy_registry, mut state, source_manifest) =
        profile_and_state(EconomicInitialStateKindV1::GENESIS);
    state.height = 0;
    let mut certificate = genesis_certificate();
    certificate.chain_id = state.chain_id.clone();
    certificate.deployment_root = state.deployment_root.clone();
    certificate.profile_root = profile.profile_id.clone();
    certificate.writer_epoch = state.writer_epoch;
    certificate.state_root = state.state_root().unwrap();
    certificate.state_atom_coverage_root = source_manifest.manifest_root().unwrap();
    certificate.replay_continuity_root = derive_economic_initial_state_replay_continuity_root_v1(
        EconomicInitialStateKindV1::GENESIS,
        &state,
        None,
    )
    .unwrap();
    certificate.terminal_continuity_root =
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1::GENESIS,
            &state,
            None,
        )
        .unwrap();
    certificate.outbox_continuity_root = derive_economic_initial_state_outbox_continuity_root_v1(
        EconomicInitialStateKindV1::GENESIS,
        &state,
        None,
    )
    .unwrap();
    certificate.root_image_id = profile.root_image_id.clone();
    let statement = certificate.journal();

    // Act / Assert
    validate_economic_initial_state_statement_bindings_v1(
        &profile,
        &policy_registry,
        &state,
        None,
        &source_manifest,
        &statement,
    )
    .unwrap();
    assert_eq!(
        validate_economic_initial_state_statement_bindings_v1(
            &profile,
            &policy_registry,
            &state,
            Some(&state),
            &source_manifest,
            &statement,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "genesis initial state predecessor"
        ))
    );
    let mut genesis_with_replay = state.clone();
    genesis_with_replay.replay_state = vec![ReplayStateV1 {
        replay_id: "genesis-replay-1".to_owned(),
        occurrence_id: root(8_102),
    }];
    assert_eq!(
        derive_economic_initial_state_replay_continuity_root_v1(
            EconomicInitialStateKindV1::GENESIS,
            &genesis_with_replay,
            None,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "genesis replay state must be empty"
        ))
    );
}

#[test]
fn migration_certificate_binds_profile_state_lineage_and_receipt() {
    let (profile, policy_registry, state, source_manifest) =
        profile_and_state(EconomicInitialStateKindV1::MIGRATION);
    let predecessor_state = migration_predecessor(&state);
    let receipt_bytes = b"economic-initial-state-receipt";
    let certificate = migration_certificate(
        &profile,
        &state,
        &predecessor_state,
        &source_manifest,
        receipt_bytes,
    );

    validate_economic_initial_state_bindings_v1(
        &profile,
        &policy_registry,
        &state,
        Some(&predecessor_state),
        &source_manifest,
        &certificate,
        receipt_bytes,
    )
    .unwrap();
    assert!(!certificate.certificate_root().unwrap().is_zero());
}

#[test]
fn initialization_statement_binds_exact_profile_state_and_manifest_without_receipt_metadata() {
    // Arrange
    let (profile, policy_registry, state, source_manifest) =
        profile_and_state(EconomicInitialStateKindV1::MIGRATION);
    let predecessor_state = migration_predecessor(&state);
    let certificate = migration_certificate(
        &profile,
        &state,
        &predecessor_state,
        &source_manifest,
        b"statement-seam-receipt",
    );
    let statement = certificate.journal();

    // Act
    let accepted = validate_economic_initial_state_statement_bindings_v1(
        &profile,
        &policy_registry,
        &state,
        Some(&predecessor_state),
        &source_manifest,
        &statement,
    );

    // Assert
    accepted.unwrap();
    let mut changed_statement = statement.clone();
    changed_statement.state_atom_coverage_root = root(8_001);
    assert!(validate_economic_initial_state_statement_bindings_v1(
        &profile,
        &policy_registry,
        &state,
        Some(&predecessor_state),
        &source_manifest,
        &changed_statement,
    )
    .is_err());
    let mut changed_replay_root = changed_statement;
    changed_replay_root.state_atom_coverage_root = source_manifest.manifest_root().unwrap();
    changed_replay_root.replay_continuity_root = root(8_002);
    assert_eq!(
        validate_economic_initial_state_statement_bindings_v1(
            &profile,
            &policy_registry,
            &state,
            Some(&predecessor_state),
            &source_manifest,
            &changed_replay_root,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "initial state replay continuity root"
        ))
    );
    let mut changed_outbox_root = statement;
    changed_outbox_root.outbox_continuity_root = root(8_003);
    assert_eq!(
        validate_economic_initial_state_statement_bindings_v1(
            &profile,
            &policy_registry,
            &state,
            Some(&predecessor_state),
            &source_manifest,
            &changed_outbox_root,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "initial state outbox continuity root"
        ))
    );
    let mut changed_terminal_root = certificate.journal();
    changed_terminal_root.terminal_continuity_root = root(8_004);
    assert_eq!(
        validate_economic_initial_state_statement_bindings_v1(
            &profile,
            &policy_registry,
            &state,
            Some(&predecessor_state),
            &source_manifest,
            &changed_terminal_root,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "initial state terminal continuity root"
        ))
    );
}

#[test]
fn migration_statement_rejects_missing_or_substituted_predecessor_state() {
    // Arrange
    let (profile, policy_registry, state, source_manifest) =
        profile_and_state(EconomicInitialStateKindV1::MIGRATION);
    let predecessor_state = migration_predecessor(&state);
    let statement = migration_certificate(
        &profile,
        &state,
        &predecessor_state,
        &source_manifest,
        b"predecessor-binding-receipt",
    )
    .journal();

    // Act / Assert: removing the witness or changing covered content rejects.
    assert_eq!(
        validate_economic_initial_state_statement_bindings_v1(
            &profile,
            &policy_registry,
            &state,
            None,
            &source_manifest,
            &statement,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "migration initial state predecessor"
        ))
    );

    let mut predecessor_with_unpreserved_replay = predecessor_state.clone();
    predecessor_with_unpreserved_replay.replay_state = vec![ReplayStateV1 {
        replay_id: "source-replay-1".to_owned(),
        occurrence_id: root(8_203),
    }];
    let mut rebound_replay_statement = statement.clone();
    rebound_replay_statement.source_state_root =
        predecessor_with_unpreserved_replay.state_root().unwrap();
    assert_eq!(
        validate_economic_initial_state_statement_bindings_v1(
            &profile,
            &policy_registry,
            &state,
            Some(&predecessor_with_unpreserved_replay),
            &source_manifest,
            &rebound_replay_statement,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "migration replay predecessor preservation"
        ))
    );

    let mut predecessor_with_unpreserved_outbox = predecessor_state.clone();
    predecessor_with_unpreserved_outbox.outbox = vec![OutboxStateV1 {
        effect_id: root(8_204),
        destination_id: "bridge:test".to_owned(),
        payload_hash: root(8_205),
        commit_id: root(8_206),
        status: OutboxStatusV1::PENDING,
    }];
    let mut rebound_outbox_statement = statement.clone();
    rebound_outbox_statement.source_state_root =
        predecessor_with_unpreserved_outbox.state_root().unwrap();
    rebound_outbox_statement.replay_continuity_root =
        derive_economic_initial_state_replay_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            &state,
            Some(&predecessor_with_unpreserved_outbox),
        )
        .unwrap();
    rebound_outbox_statement.terminal_continuity_root =
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            &state,
            Some(&predecessor_with_unpreserved_outbox),
        )
        .unwrap();
    assert_eq!(
        validate_economic_initial_state_statement_bindings_v1(
            &profile,
            &policy_registry,
            &state,
            Some(&predecessor_with_unpreserved_outbox),
            &source_manifest,
            &rebound_outbox_statement,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "migration outbox predecessor preservation"
        ))
    );
    let mut changed_balance = predecessor_state.clone();
    changed_balance.balances[0].amount_atoms += 1;
    assert_eq!(
        validate_economic_initial_state_statement_bindings_v1(
            &profile,
            &policy_registry,
            &state,
            Some(&changed_balance),
            &source_manifest,
            &statement,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "economic initial state predecessor content"
        ))
    );

    // Rebind the root while leaving each independently committed coordinate stale.
    let substitutions = [
        {
            let mut value = predecessor_state.clone();
            value.chain_id = "other-chain".to_owned();
            value
        },
        {
            let mut value = predecessor_state.clone();
            value.deployment_root = root(8_201);
            value
        },
        {
            let mut value = predecessor_state.clone();
            value.profile_root = root(8_202);
            value
        },
        {
            let mut value = predecessor_state.clone();
            value.writer_epoch += 1;
            value
        },
        {
            let mut value = predecessor_state.clone();
            value.height += 1;
            value
        },
    ];
    for substituted in substitutions {
        let mut rebound_statement = statement.clone();
        rebound_statement.source_state_root = substituted.state_root().unwrap();
        assert_eq!(
            validate_economic_initial_state_statement_bindings_v1(
                &profile,
                &policy_registry,
                &state,
                Some(&substituted),
                &source_manifest,
                &rebound_statement,
            ),
            Err(AbiErrorV1::InvalidBinding(
                "economic initial state predecessor content"
            ))
        );
    }
}

#[test]
fn migration_statement_rejects_4097_predecessor_rows_before_row_validation() {
    // Arrange
    let (profile, policy_registry, state, source_manifest) =
        profile_and_state(EconomicInitialStateKindV1::MIGRATION);
    let predecessor_state = migration_predecessor(&state);
    let statement = migration_certificate(
        &profile,
        &state,
        &predecessor_state,
        &source_manifest,
        b"predecessor-row-bound-receipt",
    )
    .journal();
    let mut oversized_predecessor = predecessor_state;
    oversized_predecessor.balances = (0..4_097)
        .map(|index| EconomicAmountV1 {
            owner: format!("owner-{index:04}"),
            asset: "ZDEX".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: u128::try_from(index).unwrap(),
        })
        .collect();
    oversized_predecessor.balances[0].owner = "invalid unicode ☃".to_owned();
    oversized_predecessor.supplies.clear();

    // Act / Assert: the direct ABI guard runs before row validation or hashing.
    assert_eq!(
        validate_economic_initial_state_statement_bindings_v1(
            &profile,
            &policy_registry,
            &state,
            Some(&oversized_predecessor),
            &source_manifest,
            &statement,
        ),
        Err(AbiErrorV1::InvalidBounds(
            "initial state explicit value rows"
        ))
    );
}

#[test]
fn migration_certificate_rejects_skipped_lineage_and_crossed_state() {
    let (profile, policy_registry, state, source_manifest) =
        profile_and_state(EconomicInitialStateKindV1::MIGRATION);
    let predecessor_state = migration_predecessor(&state);
    let receipt_bytes = b"economic-initial-state-receipt";
    let certificate = migration_certificate(
        &profile,
        &state,
        &predecessor_state,
        &source_manifest,
        receipt_bytes,
    );

    let mut skipped = certificate.clone();
    skipped.source_writer_epoch -= 1;
    assert!(skipped.validate().is_err());

    let mut crossed = certificate;
    crossed.state_root = root(99);
    assert!(validate_economic_initial_state_bindings_v1(
        &profile,
        &policy_registry,
        &state,
        Some(&predecessor_state),
        &source_manifest,
        &crossed,
        receipt_bytes,
    )
    .is_err());

    let mut substituted_manifest = source_manifest.clone();
    substituted_manifest.rows[0].source_authorization_root = root(98);
    assert!(validate_economic_initial_state_bindings_v1(
        &profile,
        &policy_registry,
        &state,
        Some(&predecessor_state),
        &substituted_manifest,
        &migration_certificate(
            &profile,
            &state,
            &predecessor_state,
            &substituted_manifest,
            receipt_bytes,
        ),
        receipt_bytes,
    )
    .is_err());

    let mut wrong_coverage_root = migration_certificate(
        &profile,
        &state,
        &predecessor_state,
        &source_manifest,
        receipt_bytes,
    );
    wrong_coverage_root.state_atom_coverage_root = root(97);
    wrong_coverage_root.journal_bytes =
        u64::try_from(wrong_coverage_root.canonical_journal_bytes().unwrap().len()).unwrap();
    assert!(validate_economic_initial_state_bindings_v1(
        &profile,
        &policy_registry,
        &state,
        Some(&predecessor_state),
        &source_manifest,
        &wrong_coverage_root,
        receipt_bytes,
    )
    .is_err());

    let mut inactive = profile;
    inactive.status = ProfileStatusV1::SHADOW;
    assert!(validate_economic_initial_state_bindings_v1(
        &inactive,
        &policy_registry,
        &state,
        Some(&predecessor_state),
        &source_manifest,
        &migration_certificate(
            &inactive,
            &state,
            &predecessor_state,
            &source_manifest,
            receipt_bytes,
        ),
        receipt_bytes,
    )
    .is_err());
}
