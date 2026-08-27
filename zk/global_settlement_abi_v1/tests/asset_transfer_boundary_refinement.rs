use zenodex_global_settlement_abi_v1::{
    transition_asset_transfer_v1, AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1,
    AssetTransferPolicyV1, AssetTransferRejectCodeV1, AssetTransferResultV1, AssetTransferStateV1,
    EconomicAmountV1, RootV1, ACCOUNT_CUSTODY_DOMAIN_V1, ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn context(subject: &str) -> AssetTransferContextV1 {
    AssetTransferContextV1 {
        chain_id: "zeno-asset-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        module_release_id: root(3),
        command_occurrence_id: root(4),
        subject_id: subject.to_owned(),
        grant_root: root(5),
    }
}

fn state(
    fee_owner: &str,
    fee_atoms: u128,
    balances: Vec<EconomicAmountV1>,
    supply_atoms: u128,
) -> AssetTransferStateV1 {
    AssetTransferStateV1 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(3),
        policies: vec![AssetTransferPolicyV1 {
            asset: "USD".to_owned(),
            fee_owner: fee_owner.to_owned(),
            transfer_fee_atoms: fee_atoms,
            enabled: true,
        }],
        balances,
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: supply_atoms,
        }],
    }
}

fn balance(owner: &str, amount_atoms: u128) -> EconomicAmountV1 {
    EconomicAmountV1 {
        owner: owner.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
        amount_atoms,
    }
}

fn command(
    sender: &str,
    recipient: &str,
    amount_atoms: u128,
    max_fee_atoms: u128,
) -> AssetTransferCommandV1 {
    AssetTransferCommandV1 {
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        sender: sender.to_owned(),
        recipient: recipient.to_owned(),
        amount_atoms,
        max_fee_atoms,
    }
}

fn reject_code(
    context: &AssetTransferContextV1,
    state: &AssetTransferStateV1,
    command: &AssetTransferCommandV1,
) -> AssetTransferRejectCodeV1 {
    match transition_asset_transfer_v1(context, state, command)
        .expect("typed transition must evaluate")
    {
        AssetTransferResultV1::Rejected(rejected) => {
            assert_eq!(rejected.pre_state_root, rejected.post_state_root);
            assert!(rejected.effects.is_empty());
            rejected.code
        }
        AssetTransferResultV1::Accepted(_) => panic!("test command unexpectedly accepted"),
    }
}

#[test]
fn sender_insufficiency_precedes_credit_overflow_independent_of_principal_order() {
    for (sender, recipient) in [("z_sender", "a_recipient"), ("a_sender", "z_recipient")] {
        // Arrange: both balance failures are reachable, with lexical role order
        // reversed by the second case.
        let pre_state = state(
            "treasury",
            0,
            vec![balance(recipient, u128::MAX)],
            u128::MAX,
        );
        let transfer_context = context(sender);
        let transfer_command = command(sender, recipient, 1, 0);

        // Act.
        let code = reject_code(&transfer_context, &pre_state, &transfer_command);

        // Assert.
        assert_eq!(code, AssetTransferRejectCodeV1::INSUFFICIENT_BALANCE);
    }
}

#[test]
fn distinct_fee_owner_accepts_the_exact_i128_min_sender_delta() {
    // Arrange.
    let max_i128_atoms = i128::MAX as u128;
    let debit_atoms = 1_u128 << 127;
    let pre_state = state(
        "treasury",
        1,
        vec![balance("alice", debit_atoms)],
        debit_atoms,
    );
    let transfer_command = command("alice", "bob", max_i128_atoms, 1);

    // Act.
    let result = transition_asset_transfer_v1(&context("alice"), &pre_state, &transfer_command)
        .expect("typed transition must evaluate");

    // Assert.
    let AssetTransferResultV1::Accepted(accepted) = result else {
        panic!("exact i128::MIN debit must be representable");
    };
    assert_eq!(accepted.post_state.balance_atoms("alice", "USD"), 0);
    assert_eq!(
        accepted.post_state.balance_atoms("bob", "USD"),
        max_i128_atoms
    );
    assert_eq!(accepted.post_state.balance_atoms("treasury", "USD"), 1);
    assert_eq!(accepted.effects.rows[0].delta_atoms, i128::MIN);
}

#[test]
fn sender_owned_fee_is_aggregated_before_debit_width_validation() {
    // Arrange.
    let max_i128_atoms = i128::MAX as u128;
    let pre_state = state(
        "alice",
        max_i128_atoms,
        vec![balance("alice", max_i128_atoms)],
        max_i128_atoms,
    );
    let transfer_command = command("alice", "bob", max_i128_atoms, max_i128_atoms);

    // Act.
    let result = transition_asset_transfer_v1(&context("alice"), &pre_state, &transfer_command)
        .expect("typed transition must evaluate");

    // Assert.
    let AssetTransferResultV1::Accepted(accepted) = result else {
        panic!("final alias-aggregated effects are representable");
    };
    assert_eq!(accepted.post_state.balance_atoms("alice", "USD"), 0);
    assert_eq!(
        accepted.post_state.balance_atoms("bob", "USD"),
        max_i128_atoms
    );
    assert_eq!(accepted.effects.rows[0].delta_atoms, -i128::MAX);
    assert_eq!(accepted.effects.rows[2].delta_atoms, i128::MAX);
}

#[test]
fn distinct_debit_one_atom_beyond_i128_min_rejects() {
    // Arrange.
    let max_i128_atoms = i128::MAX as u128;
    let debit_atoms = (1_u128 << 127) + 1;
    let pre_state = state(
        "treasury",
        2,
        vec![balance("alice", debit_atoms)],
        debit_atoms,
    );
    let transfer_command = command("alice", "bob", max_i128_atoms, 2);

    // Act and assert.
    assert_eq!(
        reject_code(&context("alice"), &pre_state, &transfer_command),
        AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW
    );
}

#[test]
fn sender_owned_fee_one_atom_beyond_i128_max_rejects() {
    // Arrange.
    let too_wide_fee = 1_u128 << 127;
    let pre_state = state("alice", too_wide_fee, vec![balance("alice", 1)], 1);
    let transfer_command = command("alice", "bob", 1, too_wide_fee);

    // Act and assert.
    assert_eq!(
        reject_code(&context("alice"), &pre_state, &transfer_command),
        AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW
    );
}

#[test]
fn recipient_owned_credit_one_atom_beyond_i128_max_rejects() {
    // Arrange.
    let max_i128_atoms = i128::MAX as u128;
    let sender_atoms = 1_u128 << 127;
    let pre_state = state("bob", 1, vec![balance("alice", sender_atoms)], sender_atoms);
    let transfer_command = command("alice", "bob", max_i128_atoms, 1);

    // Act and assert.
    assert_eq!(
        reject_code(&context("alice"), &pre_state, &transfer_command),
        AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW
    );
}
