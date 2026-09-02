use zenodex_global_settlement_abi_v1::{
    transition_asset_transfer_v1, transition_managed_asset_lifecycle_v1, AssetSupplyV1,
    AssetTransferCommandV1, AssetTransferContextV1, AssetTransferPolicyV1,
    AssetTransferRejectCodeV1, AssetTransferResultV1, AssetTransferStateV1, EconomicAmountV1,
    ManagedAssetClassV1, ManagedAssetLifecycleCommandV1, ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1, ManagedAssetLifecycleRejectCodeV1,
    ManagedAssetLifecycleResultV1, ManagedAssetLifecycleStateV1, RootV1, ACCOUNT_CUSTODY_DOMAIN_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
    MAX_ASSET_BALANCE_ROWS_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn transfer_state(row_count: usize) -> AssetTransferStateV1 {
    AssetTransferStateV1 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(3),
        policies: vec![AssetTransferPolicyV1 {
            asset: "USD".to_owned(),
            fee_owner: "acct-000000".to_owned(),
            transfer_fee_atoms: 0,
            enabled: true,
        }],
        balances: (0..row_count)
            .map(|index| EconomicAmountV1 {
                owner: format!("acct-{index:06}"),
                asset: "USD".to_owned(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 10,
            })
            .collect(),
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: 10 * row_count as u128,
        }],
    }
}

fn transfer_context() -> AssetTransferContextV1 {
    AssetTransferContextV1 {
        chain_id: "resource-bound-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 1,
        module_release_id: root(3),
        command_occurrence_id: root(4),
        subject_id: "acct-000001".to_owned(),
        grant_root: root(5),
    }
}

fn transfer_command() -> AssetTransferCommandV1 {
    AssetTransferCommandV1 {
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        sender: "acct-000001".to_owned(),
        recipient: "brand-new-owner".to_owned(),
        amount_atoms: 1,
        max_fee_atoms: 0,
    }
}

fn managed_state(row_count: usize) -> ManagedAssetLifecycleStateV1 {
    ManagedAssetLifecycleStateV1 {
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
        balances: (0..row_count)
            .map(|index| EconomicAmountV1 {
                owner: format!("acct-{index:06}"),
                asset: "USD".to_owned(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 1,
            })
            .collect(),
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: row_count as u128,
        }],
    }
}

fn managed_context() -> ManagedAssetLifecycleContextV1 {
    ManagedAssetLifecycleContextV1 {
        chain_id: "resource-bound-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 1,
        module_release_id: root(3),
        command_occurrence_id: root(4),
        subject_id: "issuer".to_owned(),
        grant_root: root(5),
    }
}

fn managed_issue() -> ManagedAssetLifecycleCommandV1 {
    ManagedAssetLifecycleCommandV1 {
        command_kind: MANAGED_ASSET_ISSUE_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        account_owner: "brand-new-owner".to_owned(),
        amount_atoms: 1,
    }
}

#[test]
fn asset_transfer_can_grow_to_exact_balance_row_ceiling() {
    let pre_state = transfer_state(MAX_ASSET_BALANCE_ROWS_V1 - 1);
    let result = transition_asset_transfer_v1(&transfer_context(), &pre_state, &transfer_command())
        .expect("typed transition must evaluate");
    let AssetTransferResultV1::Accepted(accepted) = result else {
        panic!("growth to the exact ceiling must accept");
    };
    assert_eq!(
        accepted.post_state.balances.len(),
        MAX_ASSET_BALANCE_ROWS_V1
    );
}

#[test]
fn asset_transfer_growth_past_ceiling_is_closed_typed_noop() {
    let pre_state = transfer_state(MAX_ASSET_BALANCE_ROWS_V1);
    let pre_root = pre_state.state_root().expect("valid pre-state must hash");
    let result = transition_asset_transfer_v1(&transfer_context(), &pre_state, &transfer_command())
        .expect("resource exhaustion must remain a typed transition result");
    let AssetTransferResultV1::Rejected(rejected) = result else {
        panic!("growth past the ceiling must reject");
    };
    assert_eq!(
        rejected.code,
        AssetTransferRejectCodeV1::POST_STATE_RESOURCE_BOUND_EXCEEDED
    );
    assert_eq!(rejected.pre_state_root, pre_root);
    assert_eq!(rejected.post_state_root, pre_root);
    assert!(rejected.effects.is_empty());
}

#[test]
fn managed_asset_issue_can_grow_to_exact_balance_row_ceiling() {
    let pre_state = managed_state(MAX_ASSET_BALANCE_ROWS_V1 - 1);
    let result =
        transition_managed_asset_lifecycle_v1(&managed_context(), &pre_state, &managed_issue())
            .expect("typed transition must evaluate");
    let ManagedAssetLifecycleResultV1::Accepted(accepted) = result else {
        panic!("growth to the exact ceiling must accept");
    };
    assert_eq!(
        accepted.post_state.balances.len(),
        MAX_ASSET_BALANCE_ROWS_V1
    );
}

#[test]
fn managed_asset_issue_growth_past_ceiling_is_closed_typed_noop() {
    let pre_state = managed_state(MAX_ASSET_BALANCE_ROWS_V1);
    let pre_root = pre_state.state_root().expect("valid pre-state must hash");
    let result =
        transition_managed_asset_lifecycle_v1(&managed_context(), &pre_state, &managed_issue())
            .expect("resource exhaustion must remain a typed transition result");
    let ManagedAssetLifecycleResultV1::Rejected(rejected) = result else {
        panic!("growth past the ceiling must reject");
    };
    assert_eq!(
        rejected.code,
        ManagedAssetLifecycleRejectCodeV1::POST_STATE_RESOURCE_BOUND_EXCEEDED
    );
    assert_eq!(rejected.pre_state_root, pre_root);
    assert_eq!(rejected.post_state_root, pre_root);
    assert!(rejected.effects.is_empty());
}
