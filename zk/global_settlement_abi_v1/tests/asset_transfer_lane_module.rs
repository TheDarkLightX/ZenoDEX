use zenodex_global_settlement_abi_v1::{
    compose_asset_lane_single_v1, transition_asset_transfer_lane_module_v1,
    AssetLaneCompositionResultV1, AssetLaneCoordinatorContextV1, AssetLaneModuleCompatibilityV1,
    AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1, AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleResultV1, AssetTransferPolicyV1, AssetTransferRejectCodeV1,
    AssetTransferStateV1, EconomicAmountV1, RootV1, ASSET_LANE_COORDINATOR_SCHEMA_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1, ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn module_input(amount_atoms: u128) -> AssetTransferLaneModuleInputV1 {
    AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: "zeno-asset-test".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 7,
            module_release_id: root(3),
            command_occurrence_id: root(4),
            subject_id: "alice".to_owned(),
            grant_root: root(5),
        },
        pre_state: AssetTransferStateV1 {
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
        },
        command: AssetTransferCommandV1 {
            command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
            asset: "USD".to_owned(),
            sender: "alice".to_owned(),
            recipient: "bob".to_owned(),
            amount_atoms,
            max_fee_atoms: 2,
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
            module_schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        }],
    }
}

#[test]
fn accepted_output_owns_bound_port_and_composes_without_fixture_rebinding() {
    let input = module_input(30);
    let result = transition_asset_transfer_lane_module_v1(&input)
        .expect("typed lane module transition must evaluate");
    let AssetTransferLaneModuleResultV1::Accepted(accepted) = result else {
        panic!("valid lane module transition must accept")
    };

    assert!(!accepted.module_journal.private_port_root.is_zero());
    assert_eq!(
        accepted.module_journal.private_port_root,
        accepted.private_port.port_root().unwrap()
    );
    assert_eq!(
        accepted.module_journal.effect_plan_root,
        accepted.effects.effect_plan_root().unwrap()
    );
    let composed = compose_asset_lane_single_v1(
        &coordinator_context(),
        &accepted.module_journal,
        &accepted.private_port,
        &accepted.effects,
    )
    .expect("typed coordinator must evaluate");
    let AssetLaneCompositionResultV1::Accepted(composed) = composed else {
        panic!("bound module output must compose")
    };
    assert_eq!(composed.post_state, accepted.private_port.post_state);
}

#[test]
fn rejection_has_no_port_and_is_exact_no_op() {
    let input = module_input(0);
    let result = transition_asset_transfer_lane_module_v1(&input)
        .expect("typed lane module rejection must evaluate");
    let AssetTransferLaneModuleResultV1::Rejected(rejected) = result else {
        panic!("zero-amount lane module transition must reject")
    };

    assert_eq!(rejected.code, AssetTransferRejectCodeV1::ZERO_AMOUNT);
    assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    assert!(rejected.effects.is_empty());
}

#[test]
fn python_rust_bound_output_roots_match() {
    let input = module_input(30);
    let mut changed_policy = input.clone();
    changed_policy.fee_policy_registry_root = root(13);
    assert_ne!(
        input.statement_root().unwrap(),
        changed_policy.statement_root().unwrap()
    );

    let result = transition_asset_transfer_lane_module_v1(&input)
        .expect("typed lane module transition must evaluate");
    let AssetTransferLaneModuleResultV1::Accepted(accepted) = result else {
        panic!("valid lane module transition must accept")
    };
    let roots = [
        input.statement_root().unwrap(),
        accepted.private_port.pre_state.state_root().unwrap(),
        accepted.private_port.post_state.state_root().unwrap(),
        accepted.private_port.port_root().unwrap(),
        accepted.receipt_root().clone(),
        accepted.module_journal.journal_root().unwrap(),
    ];
    assert_eq!(
        roots.map(|value| value.to_string()),
        [
            "0x9c9426e4c8c3f2047417815f76a91588a754fe4e692af165dcabbc9be8c8ab32",
            "0x9fe0b7f2c601e9628e368e60c494a0624393571c01389b87f1f0d3e827f9205f",
            "0xb67fa23250a7e61a5b181a55528413d2f992f7ce0b2ac141d92b0d785c4e8b80",
            "0x8bf6e49619c76a0c271d2b63cf5ca26cfb4b70114e9cfcaaf205aaf518984289",
            "0x3f9e60c18c0293971123a3da2b703ba3da574ba58704696519dc24d4a97121f7",
            "0x709acd06e9bf22c0f4791b9eb7d8c48a01cc07bc8b66ea8df52dd964a72c2af8",
        ]
    );
    assert_ne!(
        accepted.module_journal.private_port_root.as_str(),
        ZERO_ROOT_V1
    );
}
