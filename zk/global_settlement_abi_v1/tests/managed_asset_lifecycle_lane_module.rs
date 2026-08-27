use zenodex_global_settlement_abi_v1::{
    compose_asset_lane_single_v1, transition_managed_asset_lifecycle_lane_module_v1, AbiErrorV1,
    AssetLaneCompositionResultV1, AssetLaneCoordinatorContextV1, AssetLaneModuleCompatibilityV1,
    AssetSupplyV1, EconomicAmountV1, ManagedAssetClassV1, ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1, ManagedAssetLifecycleLaneModuleInputV1,
    ManagedAssetLifecycleLaneModuleResultV1, ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleRejectCodeV1, ManagedAssetLifecycleStateV1, RootV1,
    ASSET_LANE_COORDINATOR_SCHEMA_V1, MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1, MAX_ASSET_CUSTODY_ROWS_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn module_input(command_kind: &str) -> ManagedAssetLifecycleLaneModuleInputV1 {
    let is_issue = command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1;
    ManagedAssetLifecycleLaneModuleInputV1 {
        schema: MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: ManagedAssetLifecycleContextV1 {
            chain_id: "zeno-asset-test".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 7,
            module_release_id: root(3),
            command_occurrence_id: root(4),
            subject_id: if is_issue { "issuer" } else { "alice" }.to_owned(),
            grant_root: root(if is_issue { 5 } else { 6 }),
        },
        pre_state: ManagedAssetLifecycleStateV1 {
            schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: root(3),
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

fn coordinator_context() -> AssetLaneCoordinatorContextV1 {
    AssetLaneCoordinatorContextV1 {
        schema: ASSET_LANE_COORDINATOR_SCHEMA_V1.to_owned(),
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
            module_schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1.to_owned(),
        }],
    }
}

#[test]
fn issue_and_burn_outputs_own_ports_and_compose_without_fixture_rebinding() {
    for command_kind in [
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    ] {
        let input = module_input(command_kind);
        let result = transition_managed_asset_lifecycle_lane_module_v1(&input)
            .expect("typed lifecycle lane module transition must evaluate");
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) = result else {
            panic!("valid lifecycle lane module transition must accept")
        };
        assert!(!accepted.module_journal.private_port_root.is_zero());
        assert_eq!(
            accepted.module_journal.private_port_root,
            accepted.private_port.port_root().unwrap()
        );
        let composed = compose_asset_lane_single_v1(
            &coordinator_context(),
            &accepted.module_journal,
            &accepted.private_port,
            &accepted.effects,
        )
        .expect("typed coordinator must evaluate");
        let AssetLaneCompositionResultV1::Accepted(composed) = composed else {
            panic!("bound lifecycle output must compose")
        };
        assert_eq!(composed.post_state, accepted.private_port.post_state);
    }
}

#[test]
fn zero_issue_rejects_without_port_effects_or_state_change() {
    let mut input = module_input(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1);
    input.command.amount_atoms = 0;
    let result = transition_managed_asset_lifecycle_lane_module_v1(&input)
        .expect("typed lifecycle lane module rejection must evaluate");
    let ManagedAssetLifecycleLaneModuleResultV1::Rejected(rejected) = result else {
        panic!("zero issue must reject")
    };
    assert_eq!(
        rejected.code,
        ManagedAssetLifecycleRejectCodeV1::ZERO_AMOUNT
    );
    assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    assert!(rejected.effects.is_empty());
}

#[test]
fn custody_row_bound_accepts_maximum_and_rejects_next_neighbor() {
    // Arrange
    let mut at_limit = module_input(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1);
    at_limit.custody = (0..MAX_ASSET_CUSTODY_ROWS_V1)
        .map(|index| EconomicAmountV1 {
            owner: format!("escrow-{index:04}"),
            asset: "USD".to_owned(),
            custody_domain: "strategy_escrow".to_owned(),
            amount_atoms: 1,
        })
        .collect();
    at_limit.pre_state.supplies[0].amount_atoms += MAX_ASSET_CUSTODY_ROWS_V1 as u128;

    // Act / Assert
    assert!(matches!(
        transition_managed_asset_lifecycle_lane_module_v1(&at_limit).unwrap(),
        ManagedAssetLifecycleLaneModuleResultV1::Accepted(_)
    ));

    let mut over_limit = at_limit;
    over_limit.custody.push(EconomicAmountV1 {
        owner: "escrow-over".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "strategy_escrow".to_owned(),
        amount_atoms: 1,
    });
    over_limit.pre_state.supplies[0].amount_atoms += 1;
    assert_eq!(
        transition_managed_asset_lifecycle_lane_module_v1(&over_limit).unwrap_err(),
        AbiErrorV1::InvalidBounds("managed asset lane module custody rows")
    );
}

#[test]
fn python_rust_issue_and_burn_bound_output_roots_match() {
    let vectors = [
        (
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
            [
                "0xed74cca83c0741c453e63bc08e78b3a86154ad149663bb08cb00e1e85dd3b480",
                "0x66381e30c5c4d8edf53f39a1bf5e163cdfc9fd5054b96ce7259da4a2a36de3fe",
                "0x02c6aa0f8e3a1d5657c83b5841ea58b7b921b4db6856d6c5079de628f61f287c",
                "0x755516a651edbe44851ab1123a59622f6a3742154a9522b3e4be3a15cef4d6d3",
                "0x1e3e9fd97bf8133ee48d8f1b5e3a715820f0dc936e7250b91b18060c37985602",
                "0x0e616a7f30f6270fe549109acdccc81a97fbcfab60b9176b8874b563929d2ae3",
            ],
        ),
        (
            MANAGED_ASSET_BURN_COMMAND_KIND_V1,
            [
                "0x92d8f7897877bedb7e24d5e5df09fbca6d28e7db2447e31a615f39b711e41072",
                "0x66381e30c5c4d8edf53f39a1bf5e163cdfc9fd5054b96ce7259da4a2a36de3fe",
                "0x7290cb1923b417e0b9a9f8b8c05489e6f8928a2fe5753a6d1af924951441a3f5",
                "0x734d22c6e56a8860fb564184163dbab501b6d533434f5050eb683b03acc01ebf",
                "0xc6222f0a74796f6fc1006d3638844c38cdb6885cbd85f705cf53a53835feda9b",
                "0xa3ae2a5d391489ed88fbc2327a38b43f5aa5712f7948fc789cee1e5bc80bf123",
            ],
        ),
    ];
    for (command_kind, expected) in vectors {
        let input = module_input(command_kind);
        let mut changed_policy = input.clone();
        changed_policy.fee_policy_registry_root = root(13);
        assert_ne!(
            input.statement_root().unwrap(),
            changed_policy.statement_root().unwrap()
        );
        let result = transition_managed_asset_lifecycle_lane_module_v1(&input).unwrap();
        let ManagedAssetLifecycleLaneModuleResultV1::Accepted(accepted) = result else {
            panic!("valid lifecycle lane module transition must accept")
        };
        let roots = [
            input.statement_root().unwrap(),
            accepted.private_port.pre_state.state_root().unwrap(),
            accepted.private_port.post_state.state_root().unwrap(),
            accepted.private_port.port_root().unwrap(),
            accepted.receipt_root().clone(),
            accepted.module_journal.journal_root().unwrap(),
        ];
        assert_eq!(roots.map(|value| value.to_string()), expected);
    }
}
