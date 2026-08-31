use zenodex_global_settlement_abi_v2::{
    transition_asset_transfer_v2, AssetClassV2, AssetSupplyV2, AssetTransferAcceptedV2,
    AssetTransferCommandV2, AssetTransferContextV2, AssetTransferPolicyV2,
    AssetTransferRejectCodeV2, AssetTransferRejectedV2, AssetTransferResultV2,
    AssetTransferStateV2, EconomicAmountV2, EconomicCommandOccurrenceV2, RootV2,
    ACCOUNT_CUSTODY_DOMAIN_V2, ASSET_ATOM_DECIMALS_V2, ASSET_TRANSFER_COMMAND_KIND_V2,
    ASSET_TRANSFER_MODULE_SCHEMA_V2, GLOBAL_SETTLEMENT_ABI_V2,
};

fn root(value: u8) -> RootV2 {
    RootV2::parse(format!("0x{value:064x}"), "test root", false).expect("nonzero test root")
}

fn command(asset: &str, amount_atoms: u128, max_fee_atoms: u128) -> AssetTransferCommandV2 {
    AssetTransferCommandV2 {
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V2.to_owned(),
        asset: asset.to_owned(),
        sender: "alice".to_owned(),
        recipient: "bob".to_owned(),
        amount_atoms,
        max_fee_atoms,
        asset_origin_root: Some(root(6)),
    }
}

fn policy(asset: &str, fee_owner: &str, fee_atoms: u128) -> AssetTransferPolicyV2 {
    AssetTransferPolicyV2 {
        asset: asset.to_owned(),
        fee_owner: fee_owner.to_owned(),
        transfer_fee_atoms: fee_atoms,
        enabled: true,
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
        asset_origin_root: Some(root(6)),
        atom_decimals: ASSET_ATOM_DECIMALS_V2,
    }
}

fn state_with(policy: AssetTransferPolicyV2, alice_atoms: u128) -> AssetTransferStateV2 {
    AssetTransferStateV2 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: root(3),
        balances: vec![EconomicAmountV2 {
            owner: "alice".to_owned(),
            asset: policy.asset.clone(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            amount_atoms: alice_atoms,
        }],
        supplies: vec![AssetSupplyV2 {
            asset: policy.asset.clone(),
            amount_atoms: alice_atoms,
        }],
        policies: vec![policy],
    }
}

fn context(
    state: &AssetTransferStateV2,
    command: &AssetTransferCommandV2,
) -> AssetTransferContextV2 {
    AssetTransferContextV2 {
        writer_epoch: 5,
        module_release_id: state.module_release_id.clone(),
        global_pre_state_root: root(7),
        occurrence: Some(EconomicCommandOccurrenceV2 {
            schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
            chain_id: "zeno-test".to_owned(),
            deployment_root: root(1),
            height: 7,
            tx_index: 3,
            op_index: 1,
            command_kind: command.command_kind.clone(),
            command_body_hash: command.command_body_hash().expect("command hash"),
            route_release_id: root(2),
            subject_id: command.sender.clone(),
            grant_root: root(4),
            nonce: 11,
            profile_root: root(5),
            pre_state_root: root(7),
            consumed_object_ids: Vec::new(),
        }),
    }
}

fn rejected(
    result: AssetTransferResultV2,
    expected: AssetTransferRejectCodeV2,
    state: &AssetTransferStateV2,
) -> Box<AssetTransferRejectedV2> {
    let AssetTransferResultV2::Rejected(rejected) = result else {
        panic!("expected typed V2 rejection");
    };
    assert_eq!(rejected.code, expected);
    let state_root = state.state_root().expect("pre-state root");
    assert_eq!(rejected.pre_state_root, state_root);
    assert_eq!(rejected.post_state_root, state_root);
    assert!(rejected.effects.is_empty());
    rejected
        .validate()
        .expect("rejection must be an exact no-op");
    rejected
}

fn accepted(result: AssetTransferResultV2) -> Box<AssetTransferAcceptedV2> {
    let AssetTransferResultV2::Accepted(accepted) = result else {
        panic!("expected typed V2 acceptance");
    };
    accepted.validate().expect("acceptance bindings must close");
    accepted
}

#[test]
fn occurrence_release_command_asset_and_policy_reject_precedence_is_exact() {
    let base_policy = policy("USD", "treasury", 2);
    let base_state = state_with(base_policy.clone(), 1_000);
    let base_command = command("USD", 100, 2);

    let mut missing = context(&base_state, &base_command);
    missing.occurrence = None;
    missing.module_release_id = root(8);
    rejected(
        transition_asset_transfer_v2(&missing, &base_state, &base_command)
            .expect("typed transition"),
        AssetTransferRejectCodeV2::MISSING_OCCURRENCE,
        &base_state,
    );

    let mut binding = context(&base_state, &base_command);
    binding.global_pre_state_root = root(8);
    binding.module_release_id = root(9);
    rejected(
        transition_asset_transfer_v2(&binding, &base_state, &base_command)
            .expect("typed transition"),
        AssetTransferRejectCodeV2::OCCURRENCE_BINDING_MISMATCH,
        &base_state,
    );

    let mut consumed = context(&base_state, &base_command);
    consumed
        .occurrence
        .as_mut()
        .expect("occurrence")
        .consumed_object_ids = vec!["already-consumed".to_owned()];
    rejected(
        transition_asset_transfer_v2(&consumed, &base_state, &base_command)
            .expect("typed transition"),
        AssetTransferRejectCodeV2::OCCURRENCE_BINDING_MISMATCH,
        &base_state,
    );

    let mut release = context(&base_state, &base_command);
    release.module_release_id = root(8);
    let mut unknown_command = base_command.clone();
    unknown_command.command_kind = "unknown_transfer".to_owned();
    rejected(
        transition_asset_transfer_v2(&release, &base_state, &unknown_command)
            .expect("typed transition"),
        AssetTransferRejectCodeV2::RELEASE_MISMATCH,
        &base_state,
    );

    rejected(
        transition_asset_transfer_v2(
            &context(&base_state, &base_command),
            &base_state,
            &unknown_command,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::UNKNOWN_COMMAND,
        &base_state,
    );

    let mut command_mismatch = context(&base_state, &base_command);
    command_mismatch
        .occurrence
        .as_mut()
        .expect("occurrence")
        .command_body_hash = root(8);
    let other_asset = command("OTHER", 100, 2);
    rejected(
        transition_asset_transfer_v2(&command_mismatch, &base_state, &other_asset)
            .expect("typed transition"),
        AssetTransferRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH,
        &base_state,
    );

    rejected(
        transition_asset_transfer_v2(
            &context(&base_state, &other_asset),
            &base_state,
            &other_asset,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::UNKNOWN_ASSET,
        &base_state,
    );

    let mut disabled_policy = base_policy;
    disabled_policy.enabled = false;
    let disabled_state = state_with(disabled_policy, 1_000);
    rejected(
        transition_asset_transfer_v2(
            &context(&disabled_state, &base_command),
            &disabled_state,
            &base_command,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::DISABLED_ASSET,
        &disabled_state,
    );
}

#[test]
fn origin_native_subject_and_transfer_guards_are_fail_closed_no_ops() {
    let base_command = command("USD", 100, 2);

    let relabelled_protocol_asset = policy("ZDEX", "treasury", 2);
    assert!(relabelled_protocol_asset.validate().is_err());

    let mut unregistered_policy = policy("USD", "treasury", 2);
    unregistered_policy.asset_origin_root = None;
    let unregistered_state = state_with(unregistered_policy, 1_000);
    rejected(
        transition_asset_transfer_v2(
            &context(&unregistered_state, &base_command),
            &unregistered_state,
            &base_command,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::UNREGISTERED_ASSET,
        &unregistered_state,
    );

    let base_state = state_with(policy("USD", "treasury", 2), 1_000);
    let mut missing_command_origin = base_command.clone();
    missing_command_origin.asset_origin_root = None;
    rejected(
        transition_asset_transfer_v2(
            &context(&base_state, &missing_command_origin),
            &base_state,
            &missing_command_origin,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::UNREGISTERED_ASSET,
        &base_state,
    );

    let mut wrong_origin = base_command.clone();
    wrong_origin.asset_origin_root = Some(root(8));
    rejected(
        transition_asset_transfer_v2(
            &context(&base_state, &wrong_origin),
            &base_state,
            &wrong_origin,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::ASSET_ORIGIN_MISMATCH,
        &base_state,
    );

    let mut native_policy = policy("TAU", "treasury", 2);
    native_policy.asset_class = AssetClassV2::TauNativeCoin;
    let native_state = state_with(native_policy, 1_000);
    let native_command = command("TAU", 100, 2);
    rejected(
        transition_asset_transfer_v2(
            &context(&native_state, &native_command),
            &native_state,
            &native_command,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
        &native_state,
    );

    let mut unauthorized = context(&base_state, &base_command);
    unauthorized
        .occurrence
        .as_mut()
        .expect("occurrence")
        .subject_id = "mallory".to_owned();
    rejected(
        transition_asset_transfer_v2(&unauthorized, &base_state, &base_command)
            .expect("typed transition"),
        AssetTransferRejectCodeV2::UNAUTHORIZED_SUBJECT,
        &base_state,
    );

    let mut self_transfer = base_command.clone();
    self_transfer.recipient = "alice".to_owned();
    rejected(
        transition_asset_transfer_v2(
            &context(&base_state, &self_transfer),
            &base_state,
            &self_transfer,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::SELF_TRANSFER,
        &base_state,
    );

    let zero = command("USD", 0, 2);
    rejected(
        transition_asset_transfer_v2(&context(&base_state, &zero), &base_state, &zero)
            .expect("typed transition"),
        AssetTransferRejectCodeV2::ZERO_AMOUNT,
        &base_state,
    );

    let fee_limit = command("USD", 100, 1);
    rejected(
        transition_asset_transfer_v2(&context(&base_state, &fee_limit), &base_state, &fee_limit)
            .expect("typed transition"),
        AssetTransferRejectCodeV2::FEE_LIMIT_EXCEEDED,
        &base_state,
    );
}

#[test]
fn signed_delta_boundary_and_balance_failure_match_python() {
    let maximum = i128::MAX as u128;
    let max_state = state_with(policy("USD", "treasury", 0), maximum);
    let max_command = command("USD", maximum, 0);
    let max_accept = accepted(
        transition_asset_transfer_v2(&context(&max_state, &max_command), &max_state, &max_command)
            .expect("typed transition"),
    );
    assert_eq!(max_accept.post_state.balance_atoms("alice", "USD"), 0);
    assert_eq!(max_accept.post_state.balance_atoms("bob", "USD"), maximum);

    let overflow_amount = maximum + 1;
    let overflow_state = state_with(policy("USD", "treasury", 0), overflow_amount);
    let overflow_command = command("USD", overflow_amount, 0);
    rejected(
        transition_asset_transfer_v2(
            &context(&overflow_state, &overflow_command),
            &overflow_state,
            &overflow_command,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::EFFECT_DELTA_OVERFLOW,
        &overflow_state,
    );

    let insufficient_state = state_with(policy("USD", "treasury", 2), 1_000);
    let insufficient_command = command("USD", 1_001, 2);
    rejected(
        transition_asset_transfer_v2(
            &context(&insufficient_state, &insufficient_command),
            &insufficient_state,
            &insufficient_command,
        )
        .expect("typed transition"),
        AssetTransferRejectCodeV2::INSUFFICIENT_BALANCE,
        &insufficient_state,
    );
}

#[test]
fn fee_owner_aliasing_preserves_supply_and_python_delta_semantics() {
    let sender_fee_state = state_with(policy("USD", "alice", 2), 1_000);
    let transfer = command("USD", 100, 2);
    let sender_fee_accept = accepted(
        transition_asset_transfer_v2(
            &context(&sender_fee_state, &transfer),
            &sender_fee_state,
            &transfer,
        )
        .expect("typed transition"),
    );
    assert_eq!(
        sender_fee_accept.post_state.balance_atoms("alice", "USD"),
        900
    );
    assert_eq!(
        sender_fee_accept.post_state.balance_atoms("bob", "USD"),
        100
    );

    let recipient_fee_state = state_with(policy("USD", "bob", 2), 1_000);
    let recipient_fee_accept = accepted(
        transition_asset_transfer_v2(
            &context(&recipient_fee_state, &transfer),
            &recipient_fee_state,
            &transfer,
        )
        .expect("typed transition"),
    );
    assert_eq!(
        recipient_fee_accept
            .post_state
            .balance_atoms("alice", "USD"),
        898
    );
    assert_eq!(
        recipient_fee_accept.post_state.balance_atoms("bob", "USD"),
        102
    );
    assert_eq!(
        recipient_fee_accept
            .post_state
            .balances
            .iter()
            .map(|row| row.amount_atoms)
            .sum::<u128>(),
        1_000
    );
}

#[test]
fn accepted_leaf_rejects_forged_external_commitment_roots() {
    let base_state = state_with(policy("USD", "treasury", 2), 1_000);
    let transfer = command("USD", 100, 2);
    let honest = accepted(
        transition_asset_transfer_v2(&context(&base_state, &transfer), &base_state, &transfer)
            .expect("typed transition"),
    );

    for field in ["private", "terminal", "oracle"] {
        let mut forged = (*honest).clone();
        match field {
            "private" => forged.module_journal.private_port_root = root(8),
            "terminal" => forged.module_journal.terminal_obligations_root = root(8),
            "oracle" => forged.module_journal.oracle_occurrence_plan_root = root(8),
            _ => unreachable!("closed test field"),
        }
        assert!(
            forged.validate().is_err(),
            "forged {field} root was accepted"
        );
    }
}
