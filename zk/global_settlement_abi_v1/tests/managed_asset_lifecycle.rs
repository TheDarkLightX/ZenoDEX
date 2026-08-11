use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, hash_bytes_sha256_v1, transition_managed_asset_lifecycle_v1, AssetSupplyV1,
    EconomicAmountV1, EconomicEffectKindV1, LaneIdV1, ManagedAssetClassV1,
    ManagedAssetLifecycleAcceptedV1, ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1, ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleRejectCodeV1, ManagedAssetLifecycleResultV1, ManagedAssetLifecycleStateV1,
    RootV1, ACCOUNT_CUSTODY_DOMAIN_V1, MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1, MAX_ATOMS_V1,
    ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("test root must parse")
}

fn context(subject: &str, grant: u64) -> ManagedAssetLifecycleContextV1 {
    ManagedAssetLifecycleContextV1 {
        chain_id: "zeno-asset-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        module_release_id: root(3),
        command_occurrence_id: root(4),
        subject_id: subject.to_owned(),
        grant_root: root(grant),
    }
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

fn state() -> ManagedAssetLifecycleStateV1 {
    ManagedAssetLifecycleStateV1 {
        schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(3),
        policies: vec![policy()],
        balances: vec![EconomicAmountV1 {
            owner: "alice".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            amount_atoms: 10,
        }],
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: 10,
        }],
    }
}

fn command(kind: &str, amount_atoms: u128) -> ManagedAssetLifecycleCommandV1 {
    ManagedAssetLifecycleCommandV1 {
        command_kind: kind.to_owned(),
        asset: "USD".to_owned(),
        account_owner: "alice".to_owned(),
        amount_atoms,
    }
}

fn reject_code(
    context: &ManagedAssetLifecycleContextV1,
    state: &ManagedAssetLifecycleStateV1,
    command: &ManagedAssetLifecycleCommandV1,
) -> ManagedAssetLifecycleRejectCodeV1 {
    match transition_managed_asset_lifecycle_v1(context, state, command)
        .expect("typed lifecycle transition must evaluate")
    {
        ManagedAssetLifecycleResultV1::Rejected(rejected) => {
            assert_eq!(rejected.pre_state_root, rejected.post_state_root);
            assert!(rejected.effects.is_empty());
            rejected.code
        }
        ManagedAssetLifecycleResultV1::Accepted(_) => {
            panic!("test lifecycle command unexpectedly accepted")
        }
    }
}

fn assert_canonical_vector(
    context: &ManagedAssetLifecycleContextV1,
    command: &ManagedAssetLifecycleCommandV1,
    pre_state: &ManagedAssetLifecycleStateV1,
    accepted: &ManagedAssetLifecycleAcceptedV1,
    expected_bytes: [&str; 6],
    expected_roots: [&str; 5],
) {
    let byte_hashes = [
        hash_bytes_sha256_v1(&canonical_bytes_v1(context).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(command).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(pre_state).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&accepted.post_state).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&accepted.effects).unwrap()),
        hash_bytes_sha256_v1(&canonical_bytes_v1(&accepted.module_journal).unwrap()),
    ];
    assert_eq!(byte_hashes, expected_bytes);
    let roots = [
        pre_state.state_root().unwrap(),
        accepted.post_state.state_root().unwrap(),
        accepted.effects.effect_plan_root().unwrap(),
        accepted.receipt_root().clone(),
        accepted.module_journal.journal_root().unwrap(),
    ];
    assert_eq!(roots.map(|value| value.to_string()), expected_roots);
}

#[test]
fn named_issue_profile_increases_account_and_supply_exactly() {
    let context = context("issuer", 5);
    let pre_state = state();
    let command = command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, 7);
    let result = transition_managed_asset_lifecycle_v1(&context, &pre_state, &command)
        .expect("typed issue must evaluate");
    let ManagedAssetLifecycleResultV1::Accepted(accepted) = result else {
        panic!("valid issue must accept");
    };
    assert_eq!(accepted.post_state.balance_atoms("alice", "USD"), 17);
    assert_eq!(accepted.post_state.supply_atoms("USD").unwrap(), 17);
    assert_eq!(
        accepted.effects.asset_conservation[0].authorized_issue_atoms,
        7
    );
    assert_eq!(
        accepted.effects.asset_conservation[0].authorized_burn_atoms,
        0
    );
    assert_eq!(accepted.effects.rows.len(), 2);
    assert!(accepted
        .effects
        .rows
        .iter()
        .any(|row| row.kind == EconomicEffectKindV1::ISSUE && row.delta_atoms == 7));
    assert!(accepted.effects.external_outbox_enqueue.is_empty());
    assert_eq!(accepted.module_journal.lane_id, LaneIdV1::ASSET_TRANSFER);
    assert_eq!(
        accepted.module_journal.private_port_root.as_str(),
        ZERO_ROOT_V1
    );
    assert_canonical_vector(
        &context,
        &command,
        &pre_state,
        &accepted,
        [
            "3d38eaec45656db314443ff15bad0bae45f6211558055eff91f949143b3f09d6",
            "533e6782f4d1151184bf2454c1bd831cbce2faf15b659085e185c34880437afa",
            "96cb14644957c04ecfc3b26cb54bcb4273bf7b6a46d2d0160db2bade4ef45855",
            "0a15c9a3e825509148bbccf33ad798babc1e2adceed9f0dab24721e381b22e7c",
            "53c3029c697e5f6568e974b1a7dbcf38d5a1a4c184affd496ea33217473d97b6",
            "2ee98dc3179f173e7e398f9b6c7dee68fd8e43a55c7c6b27bb45a5090f01a71b",
        ],
        [
            "0x3c026d5b4b479df83144ff80809160e085a53d83ef66ecf448262d75ad9a7781",
            "0x5d4e148902614b6ed22fbe8d64885aa0f8237fde1da1f12843f28466640e8dee",
            "0x41af9589b39f6d7219aadfa5089718ca0f2787caa406a68b9e2706cfc3efd80e",
            "0xdfd3e45ee519617a1c62c21181c64e8cc4d8180cbffd7c4330cdd13c8963e627",
            "0x5f3bd854e4fce48fe9a9b1c9eca948186fd488b86addaf4dcf2c2bfa91025d77",
        ],
    );
}

#[test]
fn profile_bound_self_burn_decreases_account_and_supply_exactly() {
    let context = context("alice", 6);
    let pre_state = state();
    let command = command(MANAGED_ASSET_BURN_COMMAND_KIND_V1, 4);
    let result = transition_managed_asset_lifecycle_v1(&context, &pre_state, &command)
        .expect("typed burn must evaluate");
    let ManagedAssetLifecycleResultV1::Accepted(accepted) = result else {
        panic!("valid burn must accept");
    };
    assert_eq!(accepted.post_state.balance_atoms("alice", "USD"), 6);
    assert_eq!(accepted.post_state.supply_atoms("USD").unwrap(), 6);
    assert_eq!(
        accepted.effects.asset_conservation[0].authorized_issue_atoms,
        0
    );
    assert_eq!(
        accepted.effects.asset_conservation[0].authorized_burn_atoms,
        4
    );
    assert!(accepted
        .effects
        .rows
        .iter()
        .any(|row| row.kind == EconomicEffectKindV1::BURN && row.delta_atoms == -4));
    assert_canonical_vector(
        &context,
        &command,
        &pre_state,
        &accepted,
        [
            "6d3753828ecb423b1ca432de1dc5883a01381dfd2b906d10613d3c696afa1108",
            "12f79d91a9f827df793cbaa85265483f26067777fdec27ce56e8e7db03bf735f",
            "96cb14644957c04ecfc3b26cb54bcb4273bf7b6a46d2d0160db2bade4ef45855",
            "04932c1497458a8135e758abf37404756ed8cea48e6243637028ca94a3aec7b5",
            "22ef496d1bbf7763a4f1c80b15bab5ad4f78dd7fd1c6a64402712959dc27833e",
            "04a20ecc71d22da70a66d17a6dde6fb7f3ac8784135fcacdec3e9f118897ab6c",
        ],
        [
            "0x3c026d5b4b479df83144ff80809160e085a53d83ef66ecf448262d75ad9a7781",
            "0xba9ac989411ad9af4653b3b1bfd7b0fd0b41f0c752747a56c0d629b240a49b1b",
            "0x8f2e19f92b2ce7c1117b8656bdaedbad779ffb3100f90e226a5fb1aad8deed24",
            "0xd24649608ef33d62efd81bf6740beb5aeba4015e9a8f1daf7b443821eed4581e",
            "0xa0f0f5709d2e3a205ea09737bfce98b96baef5bfa0ad9f9755c27c77cbff4191",
        ],
    );
}

#[test]
fn protocol_managed_assets_reject_generic_supply_authority() {
    let managed_classes = [
        ManagedAssetClassV1::TAU_NATIVE_COIN,
        ManagedAssetClassV1::CANONICAL_ZUSD,
        ManagedAssetClassV1::LP_SHARE,
        ManagedAssetClassV1::ZDEX_PROTOCOL_TOKEN,
        ManagedAssetClassV1::SEALED_BID_PAYMENT_OR_INVENTORY,
    ];
    for asset_class in managed_classes {
        let mut managed_state = state();
        managed_state.policies[0].asset_class = asset_class;
        managed_state.policies[0].issue_authority_subject = None;
        managed_state.policies[0].issue_policy_root = None;
        managed_state.policies[0].burn_policy_root = None;
        assert_eq!(
            reject_code(
                &context("issuer", 5),
                &managed_state,
                &command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, 1),
            ),
            ManagedAssetLifecycleRejectCodeV1::GENERIC_AUTHORITY_FORBIDDEN
        );
        assert_eq!(
            reject_code(
                &context("alice", 6),
                &managed_state,
                &command(MANAGED_ASSET_BURN_COMMAND_KIND_V1, 1),
            ),
            ManagedAssetLifecycleRejectCodeV1::GENERIC_AUTHORITY_FORBIDDEN
        );
    }
}

#[test]
fn rejection_precedence_is_typed_and_exact_noop() {
    let mut wrong_release = context("issuer", 5);
    wrong_release.module_release_id = root(99);
    assert_eq!(
        reject_code(
            &wrong_release,
            &state(),
            &command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, 1)
        ),
        ManagedAssetLifecycleRejectCodeV1::RELEASE_MISMATCH
    );

    let mut wrong_subject = context("mallory", 5);
    assert_eq!(
        reject_code(
            &wrong_subject,
            &state(),
            &command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, 1)
        ),
        ManagedAssetLifecycleRejectCodeV1::UNAUTHORIZED_SUBJECT
    );
    wrong_subject.subject_id = "issuer".to_owned();
    wrong_subject.grant_root = root(99);
    assert_eq!(
        reject_code(
            &wrong_subject,
            &state(),
            &command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, 1)
        ),
        ManagedAssetLifecycleRejectCodeV1::AUTHORITY_PROFILE_MISMATCH
    );

    assert_eq!(
        reject_code(
            &context("alice", 6),
            &state(),
            &command(MANAGED_ASSET_BURN_COMMAND_KIND_V1, 11)
        ),
        ManagedAssetLifecycleRejectCodeV1::INSUFFICIENT_BALANCE
    );
    assert_eq!(
        reject_code(
            &context("issuer", 5),
            &state(),
            &command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, 1_u128 << 127)
        ),
        ManagedAssetLifecycleRejectCodeV1::EFFECT_DELTA_OVERFLOW
    );
}

#[test]
fn full_supply_rejects_issue_without_mutation() {
    let mut full = state();
    full.balances[0].owner = "bob".to_owned();
    full.balances[0].amount_atoms = MAX_ATOMS_V1;
    full.supplies[0].amount_atoms = MAX_ATOMS_V1;
    assert_eq!(
        reject_code(
            &context("issuer", 5),
            &full,
            &command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, 1)
        ),
        ManagedAssetLifecycleRejectCodeV1::SUPPLY_OVERFLOW
    );
}

#[test]
fn strict_decode_rejects_unknown_lifecycle_fields() {
    let mut value = serde_json::to_value(command(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, 1))
        .expect("command must encode");
    value
        .as_object_mut()
        .expect("command must be an object")
        .insert("opaque_authority".to_owned(), serde_json::Value::Bool(true));
    assert!(serde_json::from_value::<ManagedAssetLifecycleCommandV1>(value).is_err());
}
