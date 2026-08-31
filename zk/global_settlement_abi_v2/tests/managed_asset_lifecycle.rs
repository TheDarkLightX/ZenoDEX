use zenodex_global_settlement_abi_v2::{
    transition_managed_asset_lifecycle_v2, AssetClassV2, AssetSupplyV2, EconomicAmountV2,
    EconomicCommandOccurrenceV2, ManagedAssetLifecycleAcceptedV2, ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleContextV2, ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2, ManagedAssetLifecycleRejectedV2,
    ManagedAssetLifecycleResultV2, ManagedAssetLifecycleStateV2, RootV2, ACCOUNT_CUSTODY_DOMAIN_V2,
    ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2, ASSET_ATOM_DECIMALS_V2, GLOBAL_SETTLEMENT_ABI_V2,
    MANAGED_ASSET_BURN_COMMAND_KIND_V2, MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2, MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2,
};

fn root(value: u8) -> RootV2 {
    RootV2::parse(format!("0x{value:064x}"), "test root", false).expect("nonzero test root")
}

fn policy() -> ManagedAssetLifecyclePolicyV2 {
    ManagedAssetLifecyclePolicyV2 {
        asset: "USD".to_owned(),
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
        asset_origin_root: Some(root(6)),
        atom_decimals: ASSET_ATOM_DECIMALS_V2,
        issue_authority_subject: Some("issuer".to_owned()),
        issue_authorization_root: Some(root(5)),
        burn_authorization_root: Some(root(4)),
        enabled: true,
    }
}

fn state_with(
    policy: ManagedAssetLifecyclePolicyV2,
    balance_atoms: Option<u128>,
    supply_atoms: u128,
) -> ManagedAssetLifecycleStateV2 {
    ManagedAssetLifecycleStateV2 {
        schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: root(3),
        policies: vec![policy],
        balances: balance_atoms
            .into_iter()
            .map(|amount_atoms| EconomicAmountV2 {
                owner: "alice".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
                amount_atoms,
            })
            .collect(),
        supplies: vec![AssetSupplyV2 {
            asset: "USD".to_owned(),
            amount_atoms: supply_atoms,
        }],
    }
}

fn command(
    command_kind: &str,
    amount_atoms: u128,
    authorization_root: Option<RootV2>,
) -> ManagedAssetLifecycleCommandV2 {
    ManagedAssetLifecycleCommandV2 {
        command_kind: command_kind.to_owned(),
        asset: "USD".to_owned(),
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
        asset_origin_root: Some(root(6)),
        atom_decimals: ASSET_ATOM_DECIMALS_V2,
        authorization_root,
        account_owner: "alice".to_owned(),
        amount_atoms,
    }
}

fn context(
    state: &ManagedAssetLifecycleStateV2,
    command: &ManagedAssetLifecycleCommandV2,
    subject: &str,
    grant_root: RootV2,
) -> ManagedAssetLifecycleContextV2 {
    ManagedAssetLifecycleContextV2 {
        writer_epoch: 7,
        module_release_id: state.module_release_id.clone(),
        global_pre_state_root: root(7),
        occurrence: Some(EconomicCommandOccurrenceV2 {
            schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
            chain_id: "zeno-v2-managed-test".to_owned(),
            deployment_root: root(1),
            height: 42,
            tx_index: 2,
            op_index: 1,
            command_kind: command.command_kind.clone(),
            command_body_hash: command.command_body_hash().expect("command hash"),
            route_release_id: root(2),
            subject_id: subject.to_owned(),
            grant_root,
            nonce: 9,
            profile_root: root(8),
            pre_state_root: root(7),
            consumed_object_ids: Vec::new(),
        }),
    }
}

fn accepted(result: ManagedAssetLifecycleResultV2) -> Box<ManagedAssetLifecycleAcceptedV2> {
    let ManagedAssetLifecycleResultV2::Accepted(accepted) = result else {
        panic!("expected managed-asset acceptance");
    };
    accepted.validate().expect("acceptance bindings must close");
    assert_eq!(
        accepted.production_authority(),
        MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2
    );
    accepted
}

fn rejected(
    result: ManagedAssetLifecycleResultV2,
    expected: ManagedAssetLifecycleRejectCodeV2,
    state: &ManagedAssetLifecycleStateV2,
) -> Box<ManagedAssetLifecycleRejectedV2> {
    let ManagedAssetLifecycleResultV2::Rejected(rejected) = result else {
        panic!("expected managed-asset rejection");
    };
    assert_eq!(rejected.code, expected);
    let root = state.state_root().expect("pre-state root");
    assert_eq!(rejected.pre_state_root, root);
    assert_eq!(rejected.post_state_root, root);
    assert!(rejected.effects.is_empty());
    assert!(rejected.terminal_obligations_root().is_zero());
    assert!(rejected.oracle_occurrence_plan_root().is_zero());
    assert_eq!(
        rejected.production_authority(),
        MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2
    );
    rejected
        .validate()
        .expect("rejection must be an exact no-op");
    rejected
}

#[test]
fn issue_and_self_burn_match_the_python_state_and_effect_semantics() {
    let issue = command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, 7, Some(root(5)));
    let issue_state = state_with(policy(), Some(10), 10);
    let issued = accepted(
        transition_managed_asset_lifecycle_v2(
            &context(&issue_state, &issue, "issuer", root(5)),
            &issue_state,
            &issue,
        )
        .expect("typed issue transition"),
    );
    assert_eq!(issued.post_state.balance_atoms("alice", "USD"), 17);
    assert_eq!(issued.post_state.supply_atoms("USD").expect("supply"), 17);
    assert_eq!(issued.effects.rows.len(), 2);
    assert_eq!(
        issued.effects.asset_conservation[0].authorized_issue_atoms,
        7
    );
    assert_eq!(
        issued.effects.asset_conservation[0].authorized_burn_atoms,
        0
    );

    let burn = command(MANAGED_ASSET_BURN_COMMAND_KIND_V2, 4, Some(root(4)));
    let burn_state = state_with(policy(), Some(10), 10);
    let burned = accepted(
        transition_managed_asset_lifecycle_v2(
            &context(&burn_state, &burn, "alice", root(4)),
            &burn_state,
            &burn,
        )
        .expect("typed burn transition"),
    );
    assert_eq!(burned.post_state.balance_atoms("alice", "USD"), 6);
    assert_eq!(burned.post_state.supply_atoms("USD").expect("supply"), 6);
    assert_eq!(
        burned.effects.asset_conservation[0].authorized_issue_atoms,
        0
    );
    assert_eq!(
        burned.effects.asset_conservation[0].authorized_burn_atoms,
        4
    );
}

#[test]
fn burn_disabled_and_owner_insufficiency_are_exact_noops() {
    let burn = command(MANAGED_ASSET_BURN_COMMAND_KIND_V2, 2, Some(root(4)));

    let mut disabled_policy = policy();
    disabled_policy.burn_authorization_root = None;
    let disabled_state = state_with(disabled_policy, Some(10), 10);
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&disabled_state, &burn, "alice", root(4)),
            &disabled_state,
            &burn,
        )
        .expect("typed disabled burn"),
        ManagedAssetLifecycleRejectCodeV2::BURN_DISABLED,
        &disabled_state,
    );

    let insufficient_state = state_with(policy(), Some(1), 10);
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&insufficient_state, &burn, "alice", root(4)),
            &insufficient_state,
            &burn,
        )
        .expect("typed insufficient burn"),
        ManagedAssetLifecycleRejectCodeV2::INSUFFICIENT_BALANCE,
        &insufficient_state,
    );
}

#[test]
fn reachable_protocol_rejects_follow_python_precedence_and_are_noops() {
    let issue = command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, 7, Some(root(5)));
    let base_state = state_with(policy(), Some(10), 10);

    let mut missing = context(&base_state, &issue, "issuer", root(5));
    missing.occurrence = None;
    missing.module_release_id = root(9);
    rejected(
        transition_managed_asset_lifecycle_v2(&missing, &base_state, &issue)
            .expect("missing occurrence"),
        ManagedAssetLifecycleRejectCodeV2::MISSING_OCCURRENCE,
        &base_state,
    );

    let mut binding = context(&base_state, &issue, "issuer", root(5));
    binding.global_pre_state_root = root(9);
    binding.module_release_id = root(10);
    rejected(
        transition_managed_asset_lifecycle_v2(&binding, &base_state, &issue)
            .expect("occurrence binding"),
        ManagedAssetLifecycleRejectCodeV2::OCCURRENCE_BINDING_MISMATCH,
        &base_state,
    );

    let mut release = context(&base_state, &issue, "issuer", root(5));
    release.module_release_id = root(9);
    rejected(
        transition_managed_asset_lifecycle_v2(&release, &base_state, &issue)
            .expect("release mismatch"),
        ManagedAssetLifecycleRejectCodeV2::RELEASE_MISMATCH,
        &base_state,
    );

    let unknown_command = command("unknown_managed_command", 7, Some(root(5)));
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&base_state, &unknown_command, "issuer", root(5)),
            &base_state,
            &unknown_command,
        )
        .expect("unknown command"),
        ManagedAssetLifecycleRejectCodeV2::UNKNOWN_COMMAND,
        &base_state,
    );

    let mut occurrence_mismatch = context(&base_state, &issue, "issuer", root(5));
    occurrence_mismatch
        .occurrence
        .as_mut()
        .expect("occurrence")
        .command_body_hash = root(9);
    rejected(
        transition_managed_asset_lifecycle_v2(&occurrence_mismatch, &base_state, &issue)
            .expect("occurrence command mismatch"),
        ManagedAssetLifecycleRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH,
        &base_state,
    );

    let mut unknown_asset = issue.clone();
    unknown_asset.asset = "EUR".to_owned();
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&base_state, &unknown_asset, "issuer", root(5)),
            &base_state,
            &unknown_asset,
        )
        .expect("unknown asset"),
        ManagedAssetLifecycleRejectCodeV2::UNKNOWN_ASSET,
        &base_state,
    );

    let mut disabled_policy = policy();
    disabled_policy.enabled = false;
    let disabled_state = state_with(disabled_policy, Some(10), 10);
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&disabled_state, &issue, "issuer", root(5)),
            &disabled_state,
            &issue,
        )
        .expect("disabled asset"),
        ManagedAssetLifecycleRejectCodeV2::DISABLED_ASSET,
        &disabled_state,
    );

    let mut wrong_class = issue.clone();
    wrong_class.asset_class = AssetClassV2::LpShare;
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&base_state, &wrong_class, "issuer", root(5)),
            &base_state,
            &wrong_class,
        )
        .expect("class mismatch"),
        ManagedAssetLifecycleRejectCodeV2::ASSET_CLASS_MISMATCH,
        &base_state,
    );

    let mut unregistered_policy = policy();
    unregistered_policy.asset_origin_root = None;
    let unregistered_state = state_with(unregistered_policy, Some(10), 10);
    let mut unregistered_command = issue.clone();
    unregistered_command.asset_origin_root = None;
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(
                &unregistered_state,
                &unregistered_command,
                "issuer",
                root(5),
            ),
            &unregistered_state,
            &unregistered_command,
        )
        .expect("unregistered asset"),
        ManagedAssetLifecycleRejectCodeV2::UNREGISTERED_ASSET,
        &unregistered_state,
    );

    let mut wrong_origin = issue.clone();
    wrong_origin.asset_origin_root = Some(root(9));
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&base_state, &wrong_origin, "issuer", root(5)),
            &base_state,
            &wrong_origin,
        )
        .expect("origin mismatch"),
        ManagedAssetLifecycleRejectCodeV2::ASSET_ORIGIN_MISMATCH,
        &base_state,
    );

    let protocol_state = ManagedAssetLifecycleStateV2 {
        schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: root(3),
        policies: vec![ManagedAssetLifecyclePolicyV2 {
            asset: "TAU".to_owned(),
            asset_class: AssetClassV2::TauNativeCoin,
            asset_origin_root: Some(root(6)),
            atom_decimals: ASSET_ATOM_DECIMALS_V2,
            issue_authority_subject: None,
            issue_authorization_root: None,
            burn_authorization_root: None,
            enabled: true,
        }],
        balances: Vec::new(),
        supplies: vec![AssetSupplyV2 {
            asset: "TAU".to_owned(),
            amount_atoms: 0,
        }],
    };
    let mut protocol_command = issue.clone();
    protocol_command.asset = "TAU".to_owned();
    protocol_command.asset_class = AssetClassV2::TauNativeCoin;
    protocol_command.authorization_root = None;
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&protocol_state, &protocol_command, "issuer", root(5)),
            &protocol_state,
            &protocol_command,
        )
        .expect("generic authority forbidden"),
        ManagedAssetLifecycleRejectCodeV2::GENERIC_AUTHORITY_FORBIDDEN,
        &protocol_state,
    );

    let mut issue_disabled_policy = policy();
    issue_disabled_policy.issue_authority_subject = None;
    issue_disabled_policy.issue_authorization_root = None;
    let issue_disabled_state = state_with(issue_disabled_policy, Some(10), 10);
    let mut issue_disabled_command = issue.clone();
    issue_disabled_command.authorization_root = None;
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(
                &issue_disabled_state,
                &issue_disabled_command,
                "issuer",
                root(5),
            ),
            &issue_disabled_state,
            &issue_disabled_command,
        )
        .expect("issue disabled"),
        ManagedAssetLifecycleRejectCodeV2::ISSUE_DISABLED,
        &issue_disabled_state,
    );

    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&base_state, &issue, "mallory", root(5)),
            &base_state,
            &issue,
        )
        .expect("unauthorized subject"),
        ManagedAssetLifecycleRejectCodeV2::UNAUTHORIZED_SUBJECT,
        &base_state,
    );

    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&base_state, &issue, "issuer", root(9)),
            &base_state,
            &issue,
        )
        .expect("authorization mismatch"),
        ManagedAssetLifecycleRejectCodeV2::AUTHORIZATION_ROOT_MISMATCH,
        &base_state,
    );

    let zero = command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, 0, Some(root(5)));
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&base_state, &zero, "issuer", root(5)),
            &base_state,
            &zero,
        )
        .expect("zero amount"),
        ManagedAssetLifecycleRejectCodeV2::ZERO_AMOUNT,
        &base_state,
    );
}

#[test]
fn signed_delta_boundaries_and_supply_first_precedence_match_python() {
    let issue_max = command(
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
        i128::MAX as u128,
        Some(root(5)),
    );
    let empty_state = state_with(policy(), None, 0);
    let issued = accepted(
        transition_managed_asset_lifecycle_v2(
            &context(&empty_state, &issue_max, "issuer", root(5)),
            &empty_state,
            &issue_max,
        )
        .expect("maximum signed issue"),
    );
    assert_eq!(
        issued.post_state.balance_atoms("alice", "USD"),
        i128::MAX as u128
    );

    let issue_too_wide = command(
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
        (i128::MAX as u128) + 1,
        Some(root(5)),
    );
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&empty_state, &issue_too_wide, "issuer", root(5)),
            &empty_state,
            &issue_too_wide,
        )
        .expect("oversize issue rejection"),
        ManagedAssetLifecycleRejectCodeV2::EFFECT_DELTA_OVERFLOW,
        &empty_state,
    );

    let burn_min = command(
        MANAGED_ASSET_BURN_COMMAND_KIND_V2,
        1_u128 << 127,
        Some(root(4)),
    );
    let burn_state = state_with(policy(), Some(1_u128 << 127), 1_u128 << 127);
    let burned = accepted(
        transition_managed_asset_lifecycle_v2(
            &context(&burn_state, &burn_min, "alice", root(4)),
            &burn_state,
            &burn_min,
        )
        .expect("minimum signed burn"),
    );
    assert_eq!(burned.post_state.balance_atoms("alice", "USD"), 0);
    assert_eq!(burned.effects.rows[0].delta_atoms, i128::MIN);

    let full_state = state_with(policy(), Some(u128::MAX), u128::MAX);
    let issue_one = command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, 1, Some(root(5)));
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&full_state, &issue_one, "issuer", root(5)),
            &full_state,
            &issue_one,
        )
        .expect("full supply rejection"),
        ManagedAssetLifecycleRejectCodeV2::SUPPLY_OVERFLOW,
        &full_state,
    );
}

#[test]
fn reject_registry_is_exact_and_reserved_codes_are_honestly_unreachable() {
    let expected = [
        "MISSING_OCCURRENCE",
        "OCCURRENCE_BINDING_MISMATCH",
        "RELEASE_MISMATCH",
        "UNKNOWN_COMMAND",
        "OCCURRENCE_COMMAND_MISMATCH",
        "UNKNOWN_ASSET",
        "DISABLED_ASSET",
        "ASSET_CLASS_MISMATCH",
        "ASSET_DECIMALS_MISMATCH",
        "UNREGISTERED_ASSET",
        "ASSET_ORIGIN_MISMATCH",
        "GENERIC_AUTHORITY_FORBIDDEN",
        "ISSUE_DISABLED",
        "BURN_DISABLED",
        "UNAUTHORIZED_SUBJECT",
        "AUTHORIZATION_ROOT_MISMATCH",
        "ZERO_AMOUNT",
        "EFFECT_DELTA_OVERFLOW",
        "INSUFFICIENT_BALANCE",
        "BALANCE_OVERFLOW",
        "SUPPLY_OVERFLOW",
    ];
    assert_eq!(
        ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2.map(|code| code.as_str()),
        expected
    );
    for code in ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2 {
        assert_eq!(
            serde_json::to_value(code).expect("reject code wire value"),
            serde_json::Value::String(code.as_str().to_owned())
        );
    }

    let mut invalid_decimals = command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, 1, Some(root(5)));
    invalid_decimals.atom_decimals = 7;
    assert!(invalid_decimals.validate().is_err());

    // A valid state enforces balance <= supply and the transition updates supply
    // before balance. A positive balance overflow therefore rejects as supply
    // overflow first; BALANCE_OVERFLOW remains a closed reserved wire code.
    let full_state = state_with(policy(), Some(u128::MAX), u128::MAX);
    let issue_one = command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, 1, Some(root(5)));
    rejected(
        transition_managed_asset_lifecycle_v2(
            &context(&full_state, &issue_one, "issuer", root(5)),
            &full_state,
            &issue_one,
        )
        .expect("full supply rejection"),
        ManagedAssetLifecycleRejectCodeV2::SUPPLY_OVERFLOW,
        &full_state,
    );
}
