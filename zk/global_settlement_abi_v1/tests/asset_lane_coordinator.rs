use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, compose_asset_lane_single_v1, hash_bytes_sha256_v1,
    project_asset_transfer_state_v1, transition_asset_transfer_v1,
    transition_managed_asset_lifecycle_lane_module_v1, AssetLaneCompositionResultV1,
    AssetLaneCoordinatorContextV1, AssetLaneCoordinatorRejectCodeV1,
    AssetLaneModuleCompatibilityV1, AssetLanePrivatePortV1, AssetSupplyV1, AssetTransferCommandV1,
    AssetTransferContextV1, AssetTransferPolicyV1, AssetTransferResultV1, AssetTransferStateV1,
    EconomicAmountV1, EconomicEffectKindV1, EconomicEffectRowV1, ExternalOutboxEnqueueV1,
    GlobalEconomicEffectPlanV1, LaneIdV1, LaneWriteV1, ManagedAssetClassV1,
    ManagedAssetLifecycleCommandV1, ManagedAssetLifecycleContextV1,
    ManagedAssetLifecycleLaneModuleInputV1, ManagedAssetLifecycleLaneModuleResultV1,
    ManagedAssetLifecyclePolicyV1, ManagedAssetLifecycleStateV1, RootV1,
    ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1, GLOBAL_SETTLEMENT_ABI_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1, ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).unwrap()
}

fn fixture() -> (
    AssetTransferStateV1,
    zenodex_global_settlement_abi_v1::AssetTransferAcceptedV1,
) {
    let context = AssetTransferContextV1 {
        chain_id: "zeno-asset-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        module_release_id: root(3),
        command_occurrence_id: root(4),
        subject_id: "alice".to_owned(),
        grant_root: root(5),
    };
    let state = AssetTransferStateV1 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(3),
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
    };
    let command = AssetTransferCommandV1 {
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        sender: "alice".to_owned(),
        recipient: "bob".to_owned(),
        amount_atoms: 30,
        max_fee_atoms: 2,
    };
    let AssetTransferResultV1::Accepted(accepted) =
        transition_asset_transfer_v1(&context, &state, &command).unwrap()
    else {
        panic!("fixture transfer must accept")
    };
    (state, *accepted)
}

fn private_port(
    state: &AssetTransferStateV1,
    accepted: &zenodex_global_settlement_abi_v1::AssetTransferAcceptedV1,
) -> AssetLanePrivatePortV1 {
    AssetLanePrivatePortV1 {
        schema: "zenodex/asset-lane-private-port/v1".to_owned(),
        producer_module_schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(3),
        command_occurrence_id: root(4),
        pre_state: project_asset_transfer_state_v1(state, &root(11), &root(12), vec![]).unwrap(),
        post_state: project_asset_transfer_state_v1(
            &accepted.post_state,
            &root(11),
            &root(12),
            vec![],
        )
        .unwrap(),
        module_effect_plan_root: accepted.effects.effect_plan_root().unwrap(),
        terminal_obligations_root: RootV1::parse(ZERO_ROOT_V1, "terminal root", true).unwrap(),
    }
}

fn coordinator_context() -> AssetLaneCoordinatorContextV1 {
    AssetLaneCoordinatorContextV1 {
        schema: "zenodex/asset-lane-coordinator/v1".to_owned(),
        chain_id: "zeno-asset-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        coordinator_release_id: root(10),
        command_occurrence_id: root(4),
        asset_policy_registry_root: root(11),
        fee_policy_registry_root: root(12),
        compatible_modules: vec![AssetLaneModuleCompatibilityV1 {
            module_release_id: root(3),
            module_schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        }],
    }
}

fn bound_journal(
    accepted: &zenodex_global_settlement_abi_v1::AssetTransferAcceptedV1,
    port: &AssetLanePrivatePortV1,
    effects: &GlobalEconomicEffectPlanV1,
) -> zenodex_global_settlement_abi_v1::LaneModuleTransitionJournalV1 {
    let mut journal = accepted.module_journal.clone();
    journal.private_port_root = port.port_root().unwrap();
    journal.effect_plan_root = effects.effect_plan_root().unwrap();
    journal.receipt_root = root(30);
    journal
}

fn reject_code(
    context: &AssetLaneCoordinatorContextV1,
    journal: &zenodex_global_settlement_abi_v1::LaneModuleTransitionJournalV1,
    port: &AssetLanePrivatePortV1,
    effects: &GlobalEconomicEffectPlanV1,
) -> AssetLaneCoordinatorRejectCodeV1 {
    let result = compose_asset_lane_single_v1(context, journal, port, effects)
        .expect("typed coordinator must evaluate");
    let AssetLaneCompositionResultV1::Rejected(rejected) = result else {
        panic!("mutated composition unexpectedly accepted")
    };
    assert_eq!(rejected.pre_lane_root, rejected.post_lane_root);
    assert!(rejected.effects.is_empty());
    rejected.code
}

#[test]
fn zero_private_port_is_an_exact_composition_noop() {
    let (state, accepted) = fixture();
    let port = private_port(&state, &accepted);
    let context = coordinator_context();
    let result =
        compose_asset_lane_single_v1(&context, &accepted.module_journal, &port, &accepted.effects)
            .expect("typed coordinator must evaluate");
    let AssetLaneCompositionResultV1::Rejected(rejected) = result else {
        panic!("zero-port journal must reject")
    };
    assert_eq!(
        rejected.code,
        AssetLaneCoordinatorRejectCodeV1::PRIVATE_PORT_UNBOUND
    );
    assert_eq!(rejected.pre_lane_root, rejected.post_lane_root);
    assert!(rejected.effects.is_empty());
    assert_eq!(rejected.effects.schema, GLOBAL_SETTLEMENT_ABI_V1);
}

#[test]
fn structurally_bound_transfer_normalizes_the_common_lane_write() {
    let (state, accepted) = fixture();
    let port = private_port(&state, &accepted);
    let journal = bound_journal(&accepted, &port, &accepted.effects);
    let result =
        compose_asset_lane_single_v1(&coordinator_context(), &journal, &port, &accepted.effects)
            .unwrap();
    let AssetLaneCompositionResultV1::Accepted(composed) = result else {
        panic!("bound transfer must compose")
    };
    assert_eq!(composed.post_state, port.post_state);
    assert_eq!(composed.effects.rows, accepted.effects.rows);
    assert_eq!(
        composed.effects.lane_writes[0].pre_root,
        port.pre_state.state_root().unwrap()
    );
    assert_eq!(
        composed.effects.lane_writes[0].post_root,
        port.post_state.state_root().unwrap()
    );
    assert_eq!(
        composed.lane_journal.effect_plan_root,
        composed.effects.effect_plan_root().unwrap()
    );

    let byte_hashes = [
        hash_bytes_sha256_v1(&canonical_bytes_v1(&port.pre_state).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&port.post_state).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&port).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&coordinator_context()).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&journal).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&composed.effects).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&composed.lane_journal).unwrap()),
    ];
    assert_eq!(
        byte_hashes,
        [
            "e3d707bb1405aa0cdc1ce6873bc78c87c1b2527605c4c501655a09c5ae9adf2c",
            "be1346724e8ccd7d5e30dcc9feb4684ad4ac7640abc87d4e16a2bccb76d88d82",
            "bc41b6785d2d62544860f4d669c8ddaf7668df77c9b76a9cb7cc5ef34ad55120",
            "7a45cb769cc2dcd79593ba75fb059cef2bceeade7cceca8c3c90cb34ae8f3a21",
            "737322036412e7f7a4db7c4e4ba33ec61784a7186bcfef57be660734427d4af1",
            "3a57907a25d5b75e5fc15f86c15050011e22fdc7592b83b68d9d48f73667ca50",
            "2b1386422d0060876b2c0580db1676d45c73e2287395dba3ba63f905fa4e6251",
        ]
    );
    assert_eq!(
        [
            port.pre_state.state_root().unwrap().to_string(),
            port.post_state.state_root().unwrap().to_string(),
            port.port_root().unwrap().to_string(),
            journal.journal_root().unwrap().to_string(),
            composed.effects.effect_plan_root().unwrap().to_string(),
            composed.lane_journal.journal_root().unwrap().to_string(),
        ],
        [
            "0x9fe0b7f2c601e9628e368e60c494a0624393571c01389b87f1f0d3e827f9205f",
            "0xb67fa23250a7e61a5b181a55528413d2f992f7ce0b2ac141d92b0d785c4e8b80",
            "0x8bf6e49619c76a0c271d2b63cf5ca26cfb4b70114e9cfcaaf205aaf518984289",
            "0xfcf64b40761d25671159759b49f31314d8bc243a01cfffcb5509308bc88e0dc3",
            "0xd93b0a7c00f40c21bb12b9904ef6ce8d7609b441c4fe71d4c56c832259827ea3",
            "0xa4c9b98bfa0cd955b0fd74e34bb4b5c91508bc94e2fee229eacb5f3e4a13319d",
        ]
    );
}

#[test]
fn lifecycle_issue_uses_the_same_complete_lane_projection() {
    let context = ManagedAssetLifecycleContextV1 {
        chain_id: "zeno-asset-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        module_release_id: root(6),
        command_occurrence_id: root(7),
        subject_id: "issuer".to_owned(),
        grant_root: root(8),
    };
    let state = ManagedAssetLifecycleStateV1 {
        schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(6),
        policies: vec![ManagedAssetLifecyclePolicyV1 {
            asset: "USD".to_owned(),
            asset_class: ManagedAssetClassV1::REGISTERED_ORDINARY_TOKEN,
            issue_authority_subject: Some("issuer".to_owned()),
            issue_policy_root: Some(root(8)),
            burn_policy_root: Some(root(9)),
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
            amount_atoms: 15,
        }],
    };
    let command = ManagedAssetLifecycleCommandV1 {
        command_kind: MANAGED_ASSET_ISSUE_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        account_owner: "alice".to_owned(),
        amount_atoms: 7,
    };
    let custody = vec![EconomicAmountV1 {
        owner: "escrow".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "strategy_escrow".to_owned(),
        amount_atoms: 5,
    }];
    let module_input = ManagedAssetLifecycleLaneModuleInputV1 {
        schema: MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context,
        pre_state: state,
        command,
        asset_policy_registry_root: root(11),
        fee_policy_registry_root: root(12),
        custody,
    };
    let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) =
        transition_managed_asset_lifecycle_lane_module_v1(&module_input).unwrap()
    else {
        panic!("fixture issue must accept")
    };
    let mut coordinator = coordinator_context();
    coordinator.command_occurrence_id = root(7);
    coordinator.compatible_modules = vec![AssetLaneModuleCompatibilityV1 {
        module_release_id: root(6),
        module_schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1.to_owned(),
    }];
    let result = compose_asset_lane_single_v1(
        &coordinator,
        &accepted.module_journal,
        &accepted.private_port,
        &accepted.effects,
    )
    .unwrap();
    let AssetLaneCompositionResultV1::Accepted(composed) = result else {
        panic!("bound issue must compose")
    };
    assert_eq!(composed.post_state.supply_atoms("USD").unwrap(), 22);
    assert_eq!(
        composed.effects.asset_conservation[0].owned_and_custodied_pre_atoms,
        15
    );
    assert_eq!(
        composed.effects.asset_conservation[0].owned_and_custodied_post_atoms,
        22
    );
    assert_eq!(
        composed.effects.asset_conservation[0].authorized_issue_atoms,
        7
    );
}

#[test]
fn binding_mutations_reject_with_exact_noop_results() {
    let (state, accepted) = fixture();
    let base_port = private_port(&state, &accepted);
    let base_context = coordinator_context();
    let base_journal = bound_journal(&accepted, &base_port, &accepted.effects);

    let mut journal = base_journal.clone();
    journal.chain_id = "other-chain".to_owned();
    assert_eq!(
        reject_code(&base_context, &journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::CHAIN_MISMATCH
    );
    journal = base_journal.clone();
    journal.deployment_root = root(99);
    assert_eq!(
        reject_code(&base_context, &journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::DEPLOYMENT_MISMATCH
    );
    journal = base_journal.clone();
    journal.profile_root = root(99);
    assert_eq!(
        reject_code(&base_context, &journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::PROFILE_MISMATCH
    );
    journal = base_journal.clone();
    journal.writer_epoch = 99;
    assert_eq!(
        reject_code(&base_context, &journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::WRITER_EPOCH_MISMATCH
    );
    journal = base_journal.clone();
    journal.lane_id = LaneIdV1::SPOT_LIQUIDITY;
    assert_eq!(
        reject_code(&base_context, &journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::WRONG_LANE
    );

    let mut context = base_context.clone();
    context.compatible_modules[0].module_release_id = root(99);
    assert_eq!(
        reject_code(&context, &base_journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::MODULE_NOT_REGISTERED
    );
    let mut port = base_port.clone();
    port.producer_module_schema = "zenodex/unknown-module/v1".to_owned();
    journal = base_journal.clone();
    journal.private_port_root = port.port_root().unwrap();
    assert_eq!(
        reject_code(&base_context, &journal, &port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::MODULE_SCHEMA_MISMATCH
    );
    port = base_port.clone();
    port.module_release_id = root(99);
    journal = base_journal.clone();
    journal.private_port_root = port.port_root().unwrap();
    assert_eq!(
        reject_code(&base_context, &journal, &port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::MODULE_RELEASE_MISMATCH
    );
    journal = base_journal.clone();
    journal.command_occurrence_id = root(99);
    assert_eq!(
        reject_code(&base_context, &journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::OCCURRENCE_MISMATCH
    );
    journal = base_journal.clone();
    journal.private_port_root = root(99);
    assert_eq!(
        reject_code(&base_context, &journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::PRIVATE_PORT_ROOT_MISMATCH
    );
    journal = base_journal.clone();
    journal.effect_plan_root = root(99);
    assert_eq!(
        reject_code(&base_context, &journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::EFFECT_PLAN_MISMATCH
    );
    journal = base_journal.clone();
    journal.terminal_obligations_root = root(99);
    assert_eq!(
        reject_code(&base_context, &journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::TERMINAL_OBLIGATION_MISMATCH
    );
    context = base_context.clone();
    context.asset_policy_registry_root = root(99);
    assert_eq!(
        reject_code(&context, &base_journal, &base_port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::POLICY_ROOT_MISMATCH
    );
}

#[test]
fn economic_projection_mutations_reject_with_exact_noop_results() {
    let (state, accepted) = fixture();
    let context = coordinator_context();
    let base_port = private_port(&state, &accepted);

    let mut effects = accepted.effects.clone();
    effects.occurrence_consumptions = vec![root(99)];
    let mut port = base_port.clone();
    port.module_effect_plan_root = effects.effect_plan_root().unwrap();
    let journal = bound_journal(&accepted, &port, &effects);
    assert_eq!(
        reject_code(&context, &journal, &port, &effects),
        AssetLaneCoordinatorRejectCodeV1::OCCURRENCE_EFFECT_MISMATCH
    );

    effects = accepted.effects.clone();
    effects.lane_writes = vec![LaneWriteV1 {
        lane_id: LaneIdV1::ASSET_TRANSFER,
        pre_root: accepted.module_journal.pre_lane_root.clone(),
        post_root: root(99),
    }];
    port = base_port.clone();
    port.module_effect_plan_root = effects.effect_plan_root().unwrap();
    let journal = bound_journal(&accepted, &port, &effects);
    assert_eq!(
        reject_code(&context, &journal, &port, &effects),
        AssetLaneCoordinatorRejectCodeV1::LANE_WRITE_SHAPE_MISMATCH
    );

    effects = accepted.effects.clone();
    effects.rows.push(EconomicEffectRowV1 {
        kind: EconomicEffectKindV1::LIABILITY,
        principal: "alice".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "liability:test".to_owned(),
        delta_atoms: 1,
    });
    effects.rows.sort_by_key(|row| {
        (
            format!("{:?}", row.kind),
            row.asset.clone(),
            row.principal.clone(),
            row.custody_domain.clone(),
        )
    });
    port = base_port.clone();
    port.module_effect_plan_root = effects.effect_plan_root().unwrap();
    let journal = bound_journal(&accepted, &port, &effects);
    assert_eq!(
        reject_code(&context, &journal, &port, &effects),
        AssetLaneCoordinatorRejectCodeV1::EFFECT_KIND_FORBIDDEN
    );

    effects = accepted.effects.clone();
    effects.asset_conservation.clear();
    port = base_port.clone();
    port.module_effect_plan_root = effects.effect_plan_root().unwrap();
    let journal = bound_journal(&accepted, &port, &effects);
    assert_eq!(
        reject_code(&context, &journal, &port, &effects),
        AssetLaneCoordinatorRejectCodeV1::CONSERVATION_COVERAGE_MISMATCH
    );

    port = base_port.clone();
    port.post_state.balances[0].amount_atoms += 1;
    port.post_state.supplies[0].amount_atoms += 1;
    let journal = bound_journal(&accepted, &port, &accepted.effects);
    assert_eq!(
        reject_code(&context, &journal, &port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::CONSERVATION_STATE_MISMATCH
    );

    port = base_port.clone();
    port.post_state.balances[0].amount_atoms += 1;
    port.post_state.balances[1].amount_atoms -= 1;
    let journal = bound_journal(&accepted, &port, &accepted.effects);
    assert_eq!(
        reject_code(&context, &journal, &port, &accepted.effects),
        AssetLaneCoordinatorRejectCodeV1::STATE_EFFECT_MISMATCH
    );

    effects = accepted.effects.clone();
    effects.external_outbox_enqueue = vec![ExternalOutboxEnqueueV1 {
        effect_id: root(40),
        destination_id: "external:test".to_owned(),
        payload_hash: root(41),
        adapter_profile_root: root(42),
    }];
    port = base_port;
    port.module_effect_plan_root = effects.effect_plan_root().unwrap();
    let journal = bound_journal(&accepted, &port, &effects);
    assert_eq!(
        reject_code(&context, &journal, &port, &effects),
        AssetLaneCoordinatorRejectCodeV1::EXTERNAL_OUTBOX_FORBIDDEN
    );
}
