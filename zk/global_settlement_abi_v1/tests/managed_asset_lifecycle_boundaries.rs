use zenodex_global_settlement_abi_v1::{
    transition_managed_asset_lifecycle_v1, AssetSupplyV1, EconomicAmountV1, EconomicEffectKindV1,
    ManagedAssetClassV1, ManagedAssetLifecycleCommandV1, ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1, ManagedAssetLifecycleRejectCodeV1,
    ManagedAssetLifecycleResultV1, ManagedAssetLifecycleStateV1, RootV1, ACCOUNT_CUSTODY_DOMAIN_V1,
    MANAGED_ASSET_BURN_COMMAND_KIND_V1, MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
};

const I128_MIN_MAGNITUDE: u128 = 1_u128 << 127;
const I128_MAX_MAGNITUDE: u128 = I128_MIN_MAGNITUDE - 1;

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn policy() -> ManagedAssetLifecyclePolicyV1 {
    ManagedAssetLifecyclePolicyV1 {
        asset: "USD".to_owned(),
        asset_class: ManagedAssetClassV1::REGISTERED_ORDINARY_TOKEN,
        issue_authority_subject: Some("issuer".to_owned()),
        issue_policy_root: Some(root(5)),
        burn_policy_root: Some(root(6)),
        enabled: true,
    }
}

fn state(account_atoms: u128, supply_atoms: u128) -> ManagedAssetLifecycleStateV1 {
    ManagedAssetLifecycleStateV1 {
        schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(3),
        policies: vec![policy()],
        balances: (account_atoms != 0)
            .then(|| EconomicAmountV1 {
                owner: "alice".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: account_atoms,
            })
            .into_iter()
            .collect(),
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: supply_atoms,
        }],
    }
}

fn context(issue: bool) -> ManagedAssetLifecycleContextV1 {
    ManagedAssetLifecycleContextV1 {
        chain_id: "zeno-asset-boundary".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        module_release_id: root(3),
        command_occurrence_id: root(4),
        subject_id: if issue { "issuer" } else { "alice" }.to_owned(),
        grant_root: root(if issue { 5 } else { 6 }),
    }
}

fn command(issue: bool, amount_atoms: u128) -> ManagedAssetLifecycleCommandV1 {
    ManagedAssetLifecycleCommandV1 {
        command_kind: if issue {
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
        } else {
            MANAGED_ASSET_BURN_COMMAND_KIND_V1
        }
        .to_owned(),
        asset: "USD".to_owned(),
        account_owner: "alice".to_owned(),
        amount_atoms,
    }
}

#[test]
fn full_burn_accepts_exact_i128_min_effect_and_removes_zero_rows() {
    let pre_state = state(I128_MIN_MAGNITUDE, I128_MIN_MAGNITUDE);

    let result = transition_managed_asset_lifecycle_v1(
        &context(false),
        &pre_state,
        &command(false, I128_MIN_MAGNITUDE),
    )
    .expect("typed boundary transition must evaluate");

    let ManagedAssetLifecycleResultV1::Accepted(accepted) = result else {
        panic!("exact i128::MIN burn must accept")
    };
    assert!(accepted.post_state.balances.is_empty());
    assert_eq!(accepted.post_state.supply_atoms("USD").unwrap(), 0);
    assert!(accepted.effects.rows.iter().all(|row| {
        matches!(
            row.kind,
            EconomicEffectKindV1::ACCOUNT_MOVEMENT | EconomicEffectKindV1::BURN
        ) && row.delta_atoms == i128::MIN
    }));
}

#[test]
fn issue_and_burn_accept_exact_i128_max_effects() {
    for issue in [true, false] {
        let pre_atoms = if issue { 0 } else { I128_MAX_MAGNITUDE };
        let result = transition_managed_asset_lifecycle_v1(
            &context(issue),
            &state(pre_atoms, pre_atoms),
            &command(issue, I128_MAX_MAGNITUDE),
        )
        .expect("typed signed-maximum transition must evaluate");
        let ManagedAssetLifecycleResultV1::Accepted(accepted) = result else {
            panic!("exact i128::MAX issue or burn must accept")
        };
        let expected = if issue { I128_MAX_MAGNITUDE } else { 0 };
        assert_eq!(accepted.post_state.balance_atoms("alice", "USD"), expected);
        assert_eq!(accepted.post_state.supply_atoms("USD").unwrap(), expected);
    }
}

#[test]
fn directional_effect_width_rejects_first_invalid_neighbors_as_noops() {
    for (issue, amount_atoms) in [(true, I128_MIN_MAGNITUDE), (false, I128_MIN_MAGNITUDE + 1)] {
        let pre_state = state(I128_MIN_MAGNITUDE + 1, I128_MIN_MAGNITUDE + 1);
        let result = transition_managed_asset_lifecycle_v1(
            &context(issue),
            &pre_state,
            &command(issue, amount_atoms),
        )
        .expect("typed boundary rejection must evaluate");
        let ManagedAssetLifecycleResultV1::Rejected(rejected) = result else {
            panic!("first invalid directional neighbor must reject")
        };
        assert_eq!(
            rejected.code,
            ManagedAssetLifecycleRejectCodeV1::EFFECT_DELTA_OVERFLOW
        );
        assert_eq!(rejected.pre_state_root, rejected.post_state_root);
        assert!(rejected.effects.is_empty());
    }
}

#[test]
fn state_allows_supply_atoms_held_in_other_accounting_locations() {
    let state = state(10, 15);

    state
        .validate()
        .expect("other accounting locations may complete the supply total");
    assert_eq!(state.balance_atoms("alice", "USD"), 10);
    assert_eq!(state.supply_atoms("USD").unwrap(), 15);
}

#[test]
fn burn_rejects_when_selected_account_is_short_even_if_supply_is_sufficient() {
    let pre_state = state(5, 10);

    let result =
        transition_managed_asset_lifecycle_v1(&context(false), &pre_state, &command(false, 6))
            .expect("typed owner-underflow transition must evaluate");

    let ManagedAssetLifecycleResultV1::Rejected(rejected) = result else {
        panic!("selected owner underflow must reject")
    };
    assert_eq!(
        rejected.code,
        ManagedAssetLifecycleRejectCodeV1::INSUFFICIENT_BALANCE
    );
    assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    assert!(rejected.effects.is_empty());
}

#[test]
fn explicit_validation_rejects_empty_accepted_effects_and_nonempty_rejected_effects() {
    let accepted_result =
        transition_managed_asset_lifecycle_v1(&context(true), &state(0, 0), &command(true, 1))
            .expect("typed issue must evaluate");
    let ManagedAssetLifecycleResultV1::Accepted(mut accepted) = accepted_result else {
        panic!("valid issue must accept")
    };
    let rejected_result =
        transition_managed_asset_lifecycle_v1(&context(true), &state(0, 0), &command(true, 0))
            .expect("typed zero issue must evaluate");
    let ManagedAssetLifecycleResultV1::Rejected(mut rejected) = rejected_result else {
        panic!("zero issue must reject")
    };

    accepted.effects = rejected.effects.clone();
    accepted.module_journal.effect_plan_root = accepted.effects.effect_plan_root().unwrap();
    assert_eq!(
        accepted.validate().unwrap_err(),
        zenodex_global_settlement_abi_v1::AbiErrorV1::InvalidBinding(
            "managed asset accepted effects empty"
        )
    );

    let accepted_result =
        transition_managed_asset_lifecycle_v1(&context(true), &state(0, 0), &command(true, 1))
            .expect("typed issue must evaluate");
    let ManagedAssetLifecycleResultV1::Accepted(accepted) = accepted_result else {
        panic!("valid issue must accept")
    };
    rejected.effects = accepted.effects;
    assert_eq!(
        rejected.validate().unwrap_err(),
        zenodex_global_settlement_abi_v1::AbiErrorV1::InvalidBinding(
            "managed asset rejected transition no-op"
        )
    );
}

#[test]
fn explicit_validation_rejects_rejected_state_root_change() {
    // Arrange
    let rejected_result =
        transition_managed_asset_lifecycle_v1(&context(true), &state(0, 0), &command(true, 0))
            .expect("typed zero issue must evaluate");
    let ManagedAssetLifecycleResultV1::Rejected(mut rejected) = rejected_result else {
        panic!("zero issue must reject")
    };
    rejected.post_state_root = root(99);

    // Act / Assert
    assert_eq!(
        rejected.validate().unwrap_err(),
        zenodex_global_settlement_abi_v1::AbiErrorV1::InvalidBinding(
            "managed asset rejected transition no-op"
        )
    );
}
