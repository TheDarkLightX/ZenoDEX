use zenodex_zrpf_protocol_v3::{
    decode_exact_asset_transfer_leaf_input_v1, encode_asset_transfer_leaf_input_v1,
    execute_asset_transfer_leaf_v1, AssetTransferAccountIdV1, AssetTransferAssetIdV1,
    AssetTransferBalanceInputV1, AssetTransferBalanceV1, AssetTransferCommandInputV1,
    AssetTransferCommandV1, AssetTransferErrorV1, AssetTransferLeafInputV1,
    AssetTransferLeafOutcomeV1, AssetTransferRejectCodeV1, AssetTransferStateInputV1,
    AssetTransferStateRootV1, AssetTransferStateV1, AuthorizationSubjectIdV1, EconomicLaneIdV1,
    GlobalEconomicEffectKindV1, MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1,
    MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1, MAX_ASSET_TRANSFER_STATE_ENTRIES_V1,
};

fn account(tag: u8) -> AssetTransferAccountIdV1 {
    AssetTransferAccountIdV1::new([tag; 32]).unwrap()
}

fn numbered_account(value: u16) -> AssetTransferAccountIdV1 {
    let mut bytes = [0_u8; 32];
    bytes[..2].copy_from_slice(&value.to_be_bytes());
    bytes[31] = 1;
    AssetTransferAccountIdV1::new(bytes).unwrap()
}

fn asset(tag: u8) -> AssetTransferAssetIdV1 {
    AssetTransferAssetIdV1::new([tag; 32]).unwrap()
}

fn balance(
    account_id: AssetTransferAccountIdV1,
    asset_id: AssetTransferAssetIdV1,
    amount_atoms: u128,
) -> AssetTransferBalanceV1 {
    AssetTransferBalanceV1::new(AssetTransferBalanceInputV1 {
        account_id,
        asset_id,
        amount_atoms,
    })
    .unwrap()
}

fn state(entries: Vec<AssetTransferBalanceV1>) -> AssetTransferStateV1 {
    AssetTransferStateV1::new(AssetTransferStateInputV1 { balances: entries }).unwrap()
}

fn command(
    source_account_id: AssetTransferAccountIdV1,
    destination_account_id: AssetTransferAccountIdV1,
    asset_id: AssetTransferAssetIdV1,
    amount_atoms: u128,
) -> AssetTransferCommandV1 {
    AssetTransferCommandV1::new(AssetTransferCommandInputV1 {
        source_account_id,
        destination_account_id,
        asset_id,
        amount_atoms,
    })
    .unwrap()
}

fn authorized_input(
    pre_state: AssetTransferStateV1,
    command: AssetTransferCommandV1,
) -> AssetTransferLeafInputV1 {
    let expected_pre_state_root = pre_state.state_root();
    let expected_command_hash = command.canonical_hash().unwrap();
    let expected_authorization_subject_id =
        AuthorizationSubjectIdV1::new(command.source_account_id().into_bytes()).unwrap();
    AssetTransferLeafInputV1::new(
        pre_state,
        command,
        expected_pre_state_root,
        expected_command_hash,
        expected_authorization_subject_id,
    )
    .unwrap()
}

fn accepted(
    outcome: AssetTransferLeafOutcomeV1,
) -> zenodex_zrpf_protocol_v3::AssetTransferAcceptedV1 {
    match outcome {
        AssetTransferLeafOutcomeV1::Accepted(value) => value,
        AssetTransferLeafOutcomeV1::Rejected(code) => panic!("unexpected reject: {code:?}"),
    }
}

#[test]
fn one_atom_transfer_derives_exact_state_and_global_movement() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let pre = state(vec![balance(alice, token, 2)]);
    let operation = command(alice, bob, token, 1);

    let result =
        accepted(execute_asset_transfer_leaf_v1(&authorized_input(pre, operation)).unwrap());

    assert_eq!(result.post_state().balance_of(alice, token), 1);
    assert_eq!(result.post_state().balance_of(bob, token), 1);
    assert_eq!(result.pre_asset_total_atoms(), 2);
    assert_eq!(result.post_asset_total_atoms(), 2);
    assert_eq!(result.movement().source_account_id(), alice);
    assert_eq!(result.movement().destination_account_id(), bob);
    assert_eq!(result.movement().asset_id(), token);
    assert_eq!(result.movement().amount_atoms(), 1);
    let row = result.movement().to_global_effect_row().unwrap();
    assert_eq!(row.kind(), GlobalEconomicEffectKindV1::AccountMovement);
    assert_eq!(row.lane_id(), Some(EconomicLaneIdV1::AssetTransfer));
}

#[test]
fn exact_balance_transfer_removes_the_zero_sender_cell() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let pre = state(vec![balance(alice, token, 5)]);
    let operation = command(alice, bob, token, 5);

    let result =
        accepted(execute_asset_transfer_leaf_v1(&authorized_input(pre, operation)).unwrap());

    assert_eq!(result.post_state().balance_of(alice, token), 0);
    assert_eq!(result.post_state().balance_of(bob, token), 5);
    assert_eq!(result.post_state().balances().len(), 1);
}

#[test]
fn insufficient_precedes_recipient_overflow_and_reject_has_no_candidate() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let pre = state(vec![
        balance(alice, token, 4),
        balance(bob, token, MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1),
    ]);
    let operation = command(alice, bob, token, 5);

    let result = execute_asset_transfer_leaf_v1(&authorized_input(pre.clone(), operation)).unwrap();

    assert_eq!(
        result,
        AssetTransferLeafOutcomeV1::Rejected(AssetTransferRejectCodeV1::InsufficientBalance)
    );
    assert_eq!(pre.balance_of(alice, token), 4);
    assert_eq!(
        pre.balance_of(bob, token),
        MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1
    );
}

#[test]
fn recipient_maximum_plus_one_rejects_without_post_state() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let pre = state(vec![
        balance(alice, token, 1),
        balance(bob, token, MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1),
    ]);
    let operation = command(alice, bob, token, 1);

    let result = execute_asset_transfer_leaf_v1(&authorized_input(pre, operation)).unwrap();

    assert_eq!(
        result,
        AssetTransferLeafOutcomeV1::Rejected(AssetTransferRejectCodeV1::BalanceOverflow)
    );
}

#[test]
fn maximum_amount_moves_to_an_empty_recipient() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let pre = state(vec![balance(
        alice,
        token,
        MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1,
    )]);
    let operation = command(alice, bob, token, MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1);

    let result =
        accepted(execute_asset_transfer_leaf_v1(&authorized_input(pre, operation)).unwrap());

    assert_eq!(result.post_state().balance_of(alice, token), 0);
    assert_eq!(
        result.post_state().balance_of(bob, token),
        MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1
    );
}

#[test]
fn statement_root_command_and_subject_mismatches_are_distinct_noop_rejects() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let pre = state(vec![balance(alice, token, 10)]);
    let operation = command(alice, bob, token, 3);
    let valid = authorized_input(pre.clone(), operation.clone());

    let wrong_root = AssetTransferLeafInputV1::new(
        pre.clone(),
        operation.clone(),
        state(vec![balance(alice, token, 11)]).state_root(),
        operation.canonical_hash().unwrap(),
        AuthorizationSubjectIdV1::new(alice.into_bytes()).unwrap(),
    )
    .unwrap();
    let wrong_command = AssetTransferLeafInputV1::new(
        pre.clone(),
        operation.clone(),
        pre.state_root(),
        command(alice, bob, token, 4).canonical_hash().unwrap(),
        AuthorizationSubjectIdV1::new(alice.into_bytes()).unwrap(),
    )
    .unwrap();
    let wrong_subject = AssetTransferLeafInputV1::new(
        pre.clone(),
        operation,
        pre.state_root(),
        valid.expected_command_hash(),
        AuthorizationSubjectIdV1::new(bob.into_bytes()).unwrap(),
    )
    .unwrap();

    assert_eq!(
        execute_asset_transfer_leaf_v1(&wrong_root).unwrap(),
        AssetTransferLeafOutcomeV1::Rejected(AssetTransferRejectCodeV1::PreStateRootMismatch)
    );
    assert_eq!(
        execute_asset_transfer_leaf_v1(&wrong_command).unwrap(),
        AssetTransferLeafOutcomeV1::Rejected(AssetTransferRejectCodeV1::CommandHashMismatch)
    );
    assert_eq!(
        execute_asset_transfer_leaf_v1(&wrong_subject).unwrap(),
        AssetTransferLeafOutcomeV1::Rejected(
            AssetTransferRejectCodeV1::AuthorizationSubjectMismatch
        )
    );
    assert_eq!(pre.balance_of(alice, token), 10);
    assert_eq!(pre.balance_of(bob, token), 0);
}

#[test]
fn command_constructor_enforces_zero_one_max_and_self_transfer_boundaries() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let build = |destination_account_id, amount_atoms| {
        AssetTransferCommandV1::new(AssetTransferCommandInputV1 {
            source_account_id: alice,
            destination_account_id,
            asset_id: token,
            amount_atoms,
        })
    };

    assert_eq!(build(bob, 0), Err(AssetTransferErrorV1::InvalidAmount));
    assert!(build(bob, 1).is_ok());
    assert!(build(bob, MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1).is_ok());
    assert_eq!(
        build(bob, MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1 + 1),
        Err(AssetTransferErrorV1::InvalidAmount)
    );
    assert_eq!(build(alice, 1), Err(AssetTransferErrorV1::SelfTransfer));
    assert_eq!(
        AssetTransferAccountIdV1::new([0; 32]),
        Err(AssetTransferErrorV1::ZeroIdentifier(
            "asset_transfer_account_id"
        ))
    );
    assert_eq!(
        AssetTransferAssetIdV1::new([0; 32]),
        Err(AssetTransferErrorV1::ZeroIdentifier(
            "asset_transfer_asset_id"
        ))
    );
    assert_eq!(
        AssetTransferStateRootV1::new([0; 32]),
        Err(AssetTransferErrorV1::ZeroIdentifier(
            "asset_transfer_state_root"
        ))
    );
}

#[test]
fn state_constructor_canonicalizes_and_rejects_duplicate_or_invalid_balances() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let canonical = state(vec![balance(bob, token, 2), balance(alice, token, 1)]);

    assert_eq!(canonical.balances()[0].account_id(), alice);
    assert_eq!(canonical.balances()[1].account_id(), bob);
    assert_eq!(
        AssetTransferBalanceV1::new(AssetTransferBalanceInputV1 {
            account_id: alice,
            asset_id: token,
            amount_atoms: 0,
        }),
        Err(AssetTransferErrorV1::InvalidStoredBalance)
    );
    assert_eq!(
        AssetTransferBalanceV1::new(AssetTransferBalanceInputV1 {
            account_id: alice,
            asset_id: token,
            amount_atoms: MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1 + 1,
        }),
        Err(AssetTransferErrorV1::InvalidStoredBalance)
    );
    assert_eq!(
        AssetTransferStateV1::new(AssetTransferStateInputV1 {
            balances: vec![balance(alice, token, 1), balance(alice, token, 2)],
        }),
        Err(AssetTransferErrorV1::DuplicateBalanceKey)
    );
}

#[test]
fn state_count_accepts_maximum_and_rejects_maximum_plus_one() {
    let token = asset(9);
    let entries = (1..=MAX_ASSET_TRANSFER_STATE_ENTRIES_V1)
        .map(|value| balance(numbered_account(value as u16), token, 1))
        .collect::<Vec<_>>();
    let mut excess = entries.clone();
    excess.push(balance(
        numbered_account((MAX_ASSET_TRANSFER_STATE_ENTRIES_V1 + 1) as u16),
        token,
        1,
    ));

    assert!(AssetTransferStateV1::new(AssetTransferStateInputV1 { balances: entries }).is_ok());
    assert_eq!(
        AssetTransferStateV1::new(AssetTransferStateInputV1 { balances: excess }),
        Err(AssetTransferErrorV1::TooManyBalances {
            actual: MAX_ASSET_TRANSFER_STATE_ENTRIES_V1 + 1,
            maximum: MAX_ASSET_TRANSFER_STATE_ENTRIES_V1,
        })
    );
}

#[test]
fn transition_rejects_a_new_cell_when_the_bounded_state_is_full() {
    let token = asset(9);
    let alice = numbered_account(1);
    let bob = numbered_account(600);
    let entries = (1..=MAX_ASSET_TRANSFER_STATE_ENTRIES_V1)
        .map(|value| {
            let amount = if value == 1 { 2 } else { 1 };
            balance(numbered_account(value as u16), token, amount)
        })
        .collect::<Vec<_>>();
    let pre = state(entries);
    let operation = command(alice, bob, token, 1);

    let result = execute_asset_transfer_leaf_v1(&authorized_input(pre, operation)).unwrap();

    assert_eq!(
        result,
        AssetTransferLeafOutcomeV1::Rejected(AssetTransferRejectCodeV1::StateCapacityExceeded)
    );
}

#[test]
fn bounded_exhaustive_oracle_checks_acceptance_rejects_and_conservation() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    for source_atoms in 0_u128..=8 {
        for destination_atoms in 0_u128..=8 {
            for amount_atoms in 1_u128..=9 {
                let mut entries = Vec::new();
                if source_atoms > 0 {
                    entries.push(balance(alice, token, source_atoms));
                }
                if destination_atoms > 0 {
                    entries.push(balance(bob, token, destination_atoms));
                }
                let pre = state(entries);
                let operation = command(alice, bob, token, amount_atoms);
                let result =
                    execute_asset_transfer_leaf_v1(&authorized_input(pre, operation)).unwrap();

                if source_atoms < amount_atoms {
                    assert_eq!(
                        result,
                        AssetTransferLeafOutcomeV1::Rejected(
                            AssetTransferRejectCodeV1::InsufficientBalance
                        )
                    );
                } else {
                    let value = accepted(result);
                    assert_eq!(
                        value.post_state().balance_of(alice, token),
                        source_atoms - amount_atoms
                    );
                    assert_eq!(
                        value.post_state().balance_of(bob, token),
                        destination_atoms + amount_atoms
                    );
                    assert_eq!(
                        value.pre_asset_total_atoms(),
                        source_atoms + destination_atoms
                    );
                    assert_eq!(
                        value.post_asset_total_atoms(),
                        source_atoms + destination_atoms
                    );
                }
            }
        }
    }
}

#[test]
fn transfer_preserves_unrelated_accounts_and_assets() {
    let (alice, bob, carol, token_x, token_y) =
        (account(1), account(2), account(3), asset(9), asset(10));
    let pre = state(vec![
        balance(alice, token_x, 10),
        balance(bob, token_x, 2),
        balance(carol, token_x, 7),
        balance(alice, token_y, 11),
    ]);
    let operation = command(alice, bob, token_x, 3);

    let result =
        accepted(execute_asset_transfer_leaf_v1(&authorized_input(pre, operation)).unwrap());

    assert_eq!(result.post_state().balance_of(carol, token_x), 7);
    assert_eq!(result.post_state().balance_of(alice, token_y), 11);
}

#[test]
fn input_permutation_has_identical_root_command_and_outcome() {
    let (alice, bob, carol, token) = (account(1), account(2), account(3), asset(9));
    let first = state(vec![
        balance(carol, token, 7),
        balance(alice, token, 10),
        balance(bob, token, 2),
    ]);
    let second = state(vec![
        balance(bob, token, 2),
        balance(carol, token, 7),
        balance(alice, token, 10),
    ]);
    let operation = command(alice, bob, token, 3);

    let first_outcome =
        execute_asset_transfer_leaf_v1(&authorized_input(first.clone(), operation.clone()))
            .unwrap();
    let second_outcome =
        execute_asset_transfer_leaf_v1(&authorized_input(second.clone(), operation)).unwrap();

    assert_eq!(first.state_root(), second.state_root());
    assert_eq!(first_outcome, second_outcome);
}

#[test]
fn leaf_input_codec_is_exact_bounded_and_self_validating() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let input = authorized_input(
        state(vec![balance(alice, token, 10)]),
        command(alice, bob, token, 3),
    );
    let bytes = encode_asset_transfer_leaf_input_v1(&input).unwrap();

    assert_eq!(
        decode_exact_asset_transfer_leaf_input_v1(&bytes).unwrap(),
        input
    );
    assert_eq!(
        decode_exact_asset_transfer_leaf_input_v1(&[]),
        Err(AssetTransferErrorV1::EmptyInput)
    );
    let mut trailing = bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_asset_transfer_leaf_input_v1(&trailing),
        Err(AssetTransferErrorV1::TrailingBytes)
    );
    assert_eq!(
        decode_exact_asset_transfer_leaf_input_v1(&vec![
            0;
            MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1 + 1
        ]),
        Err(AssetTransferErrorV1::InputTooLarge {
            actual: MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1 + 1,
            maximum: MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1,
        })
    );
}

#[test]
fn leaf_json_rejects_unknown_fields_and_mutated_nested_versions() {
    let (alice, bob, token) = (account(1), account(2), asset(9));
    let input = authorized_input(
        state(vec![balance(alice, token, 10)]),
        command(alice, bob, token, 3),
    );
    let mut document = serde_json::to_value(&input).unwrap();

    document["unknown"] = serde_json::json!(1);
    assert!(serde_json::from_value::<AssetTransferLeafInputV1>(document).is_err());

    let mut command_version = serde_json::to_value(&input).unwrap();
    command_version["command"]["command_version"] = serde_json::json!(2);
    assert!(serde_json::from_value::<AssetTransferLeafInputV1>(command_version).is_err());

    let mut state_version = serde_json::to_value(&input).unwrap();
    state_version["pre_state"]["state_version"] = serde_json::json!(2);
    assert!(serde_json::from_value::<AssetTransferLeafInputV1>(state_version).is_err());

    let mut command_hash = serde_json::to_value(&input).unwrap();
    command_hash["command"]["command_hash"] = serde_json::to_value([7_u8; 32]).unwrap();
    assert!(serde_json::from_value::<AssetTransferLeafInputV1>(command_hash).is_err());

    let mut state_root = serde_json::to_value(&input).unwrap();
    state_root["pre_state"]["state_root"] = serde_json::to_value([8_u8; 32]).unwrap();
    assert!(serde_json::from_value::<AssetTransferLeafInputV1>(state_root).is_err());

    let ordered = authorized_input(
        state(vec![balance(alice, token, 10), balance(bob, token, 1)]),
        command(alice, bob, token, 3),
    );
    let mut reordered = serde_json::to_value(ordered).unwrap();
    reordered["pre_state"]["balances"]
        .as_array_mut()
        .unwrap()
        .swap(0, 1);
    assert!(serde_json::from_value::<AssetTransferLeafInputV1>(reordered).is_err());
}

#[test]
fn command_hash_and_receipt_bind_each_semantic_field() {
    let (alice, bob, carol, token_x, token_y) =
        (account(1), account(2), account(3), asset(9), asset(10));
    let baseline = command(alice, bob, token_x, 3);
    let baseline_hash = baseline.canonical_hash().unwrap();

    for variant in [
        command(alice, carol, token_x, 3),
        command(alice, bob, token_y, 3),
        command(alice, bob, token_x, 4),
    ] {
        assert_ne!(variant.canonical_hash().unwrap(), baseline_hash);
    }

    let first = accepted(
        execute_asset_transfer_leaf_v1(&authorized_input(
            state(vec![balance(alice, token_x, 10)]),
            baseline.clone(),
        ))
        .unwrap(),
    );
    let second = accepted(
        execute_asset_transfer_leaf_v1(&authorized_input(
            state(vec![balance(alice, token_x, 11)]),
            baseline,
        ))
        .unwrap(),
    );
    assert_ne!(first.receipt_hash(), second.receipt_hash());
}

#[test]
fn reject_codes_are_stable_nonzero_lane_module_codes() {
    assert_eq!(
        AssetTransferRejectCodeV1::PreStateRootMismatch.code(),
        1_001
    );
    assert_eq!(AssetTransferRejectCodeV1::CommandHashMismatch.code(), 1_002);
    assert_eq!(
        AssetTransferRejectCodeV1::AuthorizationSubjectMismatch.code(),
        1_003
    );
    assert_eq!(AssetTransferRejectCodeV1::InsufficientBalance.code(), 1_004);
    assert_eq!(AssetTransferRejectCodeV1::BalanceOverflow.code(), 1_005);
    assert_eq!(
        AssetTransferRejectCodeV1::StateCapacityExceeded.code(),
        1_006
    );
    for code in AssetTransferRejectCodeV1::ALL {
        assert_eq!(
            code.to_lane_module_reject_code().unwrap().get(),
            code.code()
        );
    }
}
