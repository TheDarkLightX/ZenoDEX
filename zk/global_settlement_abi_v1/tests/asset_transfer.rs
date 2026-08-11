use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, hash_bytes_sha256_v1, transition_asset_transfer_v1, AssetSupplyV1,
    AssetTransferAcceptedV1, AssetTransferCommandV1, AssetTransferContextV1, AssetTransferPolicyV1,
    AssetTransferRejectCodeV1, AssetTransferResultV1, AssetTransferStateV1, EconomicAmountV1,
    EconomicEffectKindV1, LaneIdV1, RootV1, ACCOUNT_CUSTODY_DOMAIN_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1, ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn context() -> AssetTransferContextV1 {
    AssetTransferContextV1 {
        chain_id: "zeno-asset-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        module_release_id: root(3),
        command_occurrence_id: root(4),
        subject_id: "alice".to_owned(),
        grant_root: root(5),
    }
}

fn state(enabled: bool, fee_atoms: u128) -> AssetTransferStateV1 {
    state_with_fee_owner(enabled, fee_atoms, "treasury")
}

fn state_with_fee_owner(enabled: bool, fee_atoms: u128, fee_owner: &str) -> AssetTransferStateV1 {
    AssetTransferStateV1 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(3),
        policies: vec![AssetTransferPolicyV1 {
            asset: "USD".to_owned(),
            fee_owner: fee_owner.to_owned(),
            transfer_fee_atoms: fee_atoms,
            enabled,
        }],
        balances: vec![
            EconomicAmountV1 {
                owner: "alice".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 100,
            },
            EconomicAmountV1 {
                owner: "bob".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 10,
            },
            EconomicAmountV1 {
                owner: "treasury".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
                amount_atoms: 5,
            },
        ],
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: 115,
        }],
    }
}

fn command() -> AssetTransferCommandV1 {
    AssetTransferCommandV1 {
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        sender: "alice".to_owned(),
        recipient: "bob".to_owned(),
        amount_atoms: 30,
        max_fee_atoms: 2,
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

fn assert_canonical_vector(
    context: &AssetTransferContextV1,
    command: &AssetTransferCommandV1,
    pre_state: &AssetTransferStateV1,
    accepted: &AssetTransferAcceptedV1,
) {
    let byte_hashes = [
        hash_bytes_sha256_v1(&canonical_bytes_v1(context).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(command).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(pre_state).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&accepted.post_state).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&accepted.effects).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&accepted.module_journal).unwrap()),
    ];
    assert_eq!(
        byte_hashes,
        [
            "4629858b2b5d24a68a564c2f413fbe9dd1b0499b50cf7c5e71a871ebb7f6786a",
            "1404382098da29fbcf5facf9fe4ecf5d0cd67a04eaec0c0cb89f6d78f17d1bc6",
            "ffd49e8969de8b04cd1059ecd22ff422f4c1442c41ddf673342811ef32dbb274",
            "8620254b8374262d59dfb7b24cdfdecb385e0409f65343990951bed2cdc25a63",
            "34243fd329cf76b63cbaa433505f4cb5ed11c40ba80146426041b21e20bd0db5",
            "4cec50ca78d33c8e3d4c09359523ffcd6c2eb700c2dd0c441d8a31e609139c78",
        ]
    );
    let roots = [
        pre_state.state_root().unwrap(),
        accepted.post_state.state_root().unwrap(),
        accepted.effects.effect_plan_root().unwrap(),
        accepted.receipt_root().clone(),
        accepted.module_journal.journal_root().unwrap(),
    ];
    assert_eq!(
        roots.map(|value| value.to_string()),
        [
            "0x2e153465fca81b1035f8823db8368022c5ee4393b8bcdff136a2e4ec5de74ca8",
            "0xbdb2605d119cc52da0f883c15e5979a9c8be98d728fc2f53e1c2af44d25de758",
            "0xb1b9e0b5c0078d0f90dbacce439026ac062c8d393f80533a1f9c1215c1f9e9fc",
            "0x80ed14647f235e94982788fd932e7b63a933b9cb2f41505dbed0815c8c6a7cfb",
            "0x9c1fdc428aa5b38e698620f4bf93306fef83e3b469acaff9046ad7d8976977f3",
        ]
    );
}

#[test]
fn transfer_accepts_with_canonical_fee_and_conservation_effects() {
    let context = context();
    let pre_state = state(true, 2);
    let command = command();
    let result = transition_asset_transfer_v1(&context, &pre_state, &command)
        .expect("typed transfer must evaluate");
    let AssetTransferResultV1::Accepted(accepted) = result else {
        panic!("valid transfer must accept");
    };
    assert_eq!(accepted.post_state.balance_atoms("alice", "USD"), 68);
    assert_eq!(accepted.post_state.balance_atoms("bob", "USD"), 40);
    assert_eq!(accepted.post_state.balance_atoms("treasury", "USD"), 7);
    assert_eq!(accepted.post_state.supply_atoms("USD").unwrap(), 115);
    assert_eq!(accepted.effects.rows.len(), 4);
    assert_eq!(
        accepted.effects.rows[0].kind,
        EconomicEffectKindV1::ACCOUNT_MOVEMENT
    );
    assert_eq!(accepted.effects.rows[0].principal, "alice");
    assert_eq!(accepted.effects.rows[0].delta_atoms, -32);
    assert_eq!(
        accepted.effects.rows[3].kind,
        EconomicEffectKindV1::FEE_ALLOCATION
    );
    assert_eq!(accepted.effects.fee_conservation[0].fee_charged_atoms, 2);
    assert!(accepted.effects.external_outbox_enqueue.is_empty());
    assert_eq!(accepted.module_journal.lane_id, LaneIdV1::ASSET_TRANSFER);
    assert_eq!(
        accepted.module_journal.private_port_root.as_str(),
        ZERO_ROOT_V1
    );
    assert_eq!(
        accepted.module_journal.terminal_obligations_root.as_str(),
        ZERO_ROOT_V1
    );
    assert_canonical_vector(&context, &command, &pre_state, &accepted);
}

#[test]
fn rejection_precedence_is_typed_and_exact_no_op() {
    let mut wrong_release = context();
    wrong_release.module_release_id = root(99);
    assert_eq!(
        reject_code(&wrong_release, &state(true, 2), &command()),
        AssetTransferRejectCodeV1::RELEASE_MISMATCH
    );

    let mut unknown = command();
    unknown.command_kind = "unknown".to_owned();
    assert_eq!(
        reject_code(&context(), &state(true, 2), &unknown),
        AssetTransferRejectCodeV1::UNKNOWN_COMMAND
    );
    let mut unknown_asset = command();
    unknown_asset.asset = "EUR".to_owned();
    assert_eq!(
        reject_code(&context(), &state(true, 2), &unknown_asset),
        AssetTransferRejectCodeV1::UNKNOWN_ASSET
    );
    assert_eq!(
        reject_code(&context(), &state(false, 2), &command()),
        AssetTransferRejectCodeV1::DISABLED_ASSET
    );

    let mut unauthorized = context();
    unauthorized.subject_id = "mallory".to_owned();
    assert_eq!(
        reject_code(&unauthorized, &state(true, 2), &command()),
        AssetTransferRejectCodeV1::UNAUTHORIZED_SUBJECT
    );

    let mut self_transfer = command();
    self_transfer.recipient = "alice".to_owned();
    assert_eq!(
        reject_code(&context(), &state(true, 2), &self_transfer),
        AssetTransferRejectCodeV1::SELF_TRANSFER
    );

    let mut zero = command();
    zero.amount_atoms = 0;
    assert_eq!(
        reject_code(&context(), &state(true, 2), &zero),
        AssetTransferRejectCodeV1::ZERO_AMOUNT
    );

    let mut fee_limit = command();
    fee_limit.max_fee_atoms = 1;
    assert_eq!(
        reject_code(&context(), &state(true, 2), &fee_limit),
        AssetTransferRejectCodeV1::FEE_LIMIT_EXCEEDED
    );

    let mut insufficient = command();
    insufficient.amount_atoms = 99;
    assert_eq!(
        reject_code(&context(), &state(true, 2), &insufficient),
        AssetTransferRejectCodeV1::INSUFFICIENT_BALANCE
    );
}

#[test]
fn transfer_rejects_effect_width_before_balance_mutation() {
    let amount_atoms = 1_u128 << 127;
    let mut wide_state = state(true, 0);
    wide_state.balances = vec![EconomicAmountV1 {
        owner: "alice".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
        amount_atoms,
    }];
    wide_state.supplies[0].amount_atoms = amount_atoms;
    let mut wide_command = command();
    wide_command.amount_atoms = amount_atoms;
    wide_command.max_fee_atoms = 0;

    assert_eq!(
        reject_code(&context(), &wide_state, &wide_command),
        AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW
    );
}

#[test]
fn zero_fee_split_and_merged_transfers_reach_the_same_state_root() {
    let pre_state = state(true, 0);
    let mut merged_command = command();
    merged_command.max_fee_atoms = 0;
    let AssetTransferResultV1::Accepted(merged) =
        transition_asset_transfer_v1(&context(), &pre_state, &merged_command).unwrap()
    else {
        panic!("merged transfer must accept");
    };
    let mut first_command = merged_command.clone();
    first_command.amount_atoms = 10;
    let AssetTransferResultV1::Accepted(first) =
        transition_asset_transfer_v1(&context(), &pre_state, &first_command).unwrap()
    else {
        panic!("first split transfer must accept");
    };
    let mut second_context = context();
    second_context.command_occurrence_id = root(6);
    let mut second_command = merged_command;
    second_command.amount_atoms = 20;
    let AssetTransferResultV1::Accepted(second) =
        transition_asset_transfer_v1(&second_context, &first.post_state, &second_command).unwrap()
    else {
        panic!("second split transfer must accept");
    };
    assert_eq!(
        merged.post_state.state_root().unwrap(),
        second.post_state.state_root().unwrap()
    );
    assert!(merged.effects.fee_conservation.is_empty());
    assert!(second.effects.fee_conservation.is_empty());
}

#[test]
fn fee_owner_alias_is_aggregated_before_effect_projection() {
    let AssetTransferResultV1::Accepted(sender_owned) = transition_asset_transfer_v1(
        &context(),
        &state_with_fee_owner(true, 2, "alice"),
        &command(),
    )
    .unwrap() else {
        panic!("sender-owned fee transfer must accept");
    };
    assert_eq!(sender_owned.post_state.balance_atoms("alice", "USD"), 70);
    assert_eq!(sender_owned.effects.rows[0].delta_atoms, -30);

    let AssetTransferResultV1::Accepted(recipient_owned) = transition_asset_transfer_v1(
        &context(),
        &state_with_fee_owner(true, 2, "bob"),
        &command(),
    )
    .unwrap() else {
        panic!("recipient-owned fee transfer must accept");
    };
    assert_eq!(recipient_owned.post_state.balance_atoms("bob", "USD"), 42);
    assert_eq!(recipient_owned.effects.rows[1].delta_atoms, 32);
}

#[test]
fn accepted_result_rejects_a_parallel_journal_binding_mutation() {
    let AssetTransferResultV1::Accepted(mut accepted) =
        transition_asset_transfer_v1(&context(), &state(true, 2), &command()).unwrap()
    else {
        panic!("valid transfer must accept");
    };
    accepted.module_journal.post_lane_root = root(99);
    assert!(accepted.validate().is_err());
}

#[test]
fn strict_decode_rejects_unknown_transfer_fields() {
    let mut value = serde_json::to_value(command()).expect("command must encode");
    value
        .as_object_mut()
        .expect("command must be an object")
        .insert("opaque_authority".to_owned(), serde_json::Value::Bool(true));
    assert!(serde_json::from_value::<AssetTransferCommandV1>(value).is_err());
}
