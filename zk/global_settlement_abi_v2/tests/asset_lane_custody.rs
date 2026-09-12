#[path = "support/asset_lane_coordinator.rs"]
mod support;

use zenodex_global_settlement_abi_v2::{
    asset_transfer_policy_root_v2, canonical_bytes_v2, decode_canonical_v2, hash_global_v2,
    managed_asset_policy_root_v2, transition_asset_lane_custody_v2, AbiErrorV2, AssetClassV2,
    AssetLaneCommandV2, AssetLaneContextV2, AssetLaneCoordinatorRejectCodeV2,
    AssetLaneCustodyAcceptedV2, AssetLaneCustodyResultV2, AssetLaneCustodyStateV2,
    AssetLaneRejectCodeV2, AssetLaneResultV2, AssetLaneRouteV2, AssetLaneStateV2,
    AssetOriginKindV2, AssetOriginRecordV2, AssetOriginRegistrationPolicyV2,
    AssetOriginRegistryStateV2, AssetSupplyV2, AssetTransferCommandV2, AssetTransferPolicyV2,
    AssetTransferRejectCodeV2, AssetTransferStateV2, EconomicAmountV2,
    ManagedAssetLifecycleCommandV2, ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2, RootV2, ACCOUNT_CUSTODY_DOMAIN_V2, ASSET_ATOM_DECIMALS_V2,
    ASSET_LANE_CUSTODY_STATE_SCHEMA_V2, ASSET_ORIGIN_REGISTRY_SCHEMA_V2,
    ASSET_TRANSFER_MODULE_SCHEMA_V2, MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, MAX_ASSET_LANE_CUSTODY_ROWS_V2,
};

fn account_row(owner: &str, amount_atoms: u128) -> EconomicAmountV2 {
    EconomicAmountV2 {
        owner: owner.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
        amount_atoms,
    }
}

fn custody_row(owner: &str, domain: &str, amount_atoms: u128) -> EconomicAmountV2 {
    EconomicAmountV2 {
        owner: owner.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: domain.to_owned(),
        amount_atoms,
    }
}

fn state_with_split(
    case_name: &str,
    account_atoms: u128,
    custody_atoms: u128,
    supply: u128,
) -> AssetLaneCustodyStateV2 {
    let fixture = support::fixture();
    let case = &fixture.accepted[case_name];
    let aggregate: AssetLaneStateV2 = support::typed_vector(&case.vectors, "pre_state");
    let mut transfer_state = aggregate.transfer_leaf_state();
    transfer_state.balances = (account_atoms != 0)
        .then(|| account_row("alice", account_atoms))
        .into_iter()
        .collect();
    transfer_state.supplies = vec![AssetSupplyV2 {
        asset: "USD".to_owned(),
        amount_atoms: supply,
    }];
    AssetLaneCustodyStateV2 {
        schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
        transfer_state,
        origin_registry: aggregate.origin_registry,
        managed_policies: aggregate.managed_policies,
        custody: (custody_atoms != 0)
            .then(|| custody_row("vault", "vault:primary", custody_atoms))
            .into_iter()
            .collect(),
    }
}

fn transfer_subject() -> (
    AssetLaneContextV2,
    AssetLaneCustodyStateV2,
    AssetLaneCommandV2,
) {
    let fixture = support::fixture();
    let case = &fixture.accepted["transfer"];
    let mut context: AssetLaneContextV2 = support::typed_vector(&case.vectors, "context");
    let mut command: AssetTransferCommandV2 = support::typed_vector(&case.vectors, "command");
    command.amount_atoms = 10;
    context
        .occurrence
        .as_mut()
        .expect("transfer occurrence")
        .command_body_hash = command.command_body_hash().expect("transfer body hash");
    (
        context,
        state_with_split("transfer", 80, 20, 100),
        AssetLaneCommandV2::Transfer(command),
    )
}

fn managed_subject(
    burn: bool,
    account_atoms: u128,
    custody_atoms: u128,
    supply: u128,
) -> (
    AssetLaneContextV2,
    AssetLaneCustodyStateV2,
    AssetLaneCommandV2,
) {
    let fixture = support::fixture();
    let case = &fixture.accepted["managed_issue"];
    let mut context: AssetLaneContextV2 = support::typed_vector(&case.vectors, "context");
    let mut command: ManagedAssetLifecycleCommandV2 =
        support::typed_vector(&case.vectors, "command");
    command.amount_atoms = 10;
    if burn {
        let burn_root = state_with_split("managed_issue", 80, 20, 100).managed_policies[0]
            .burn_authorization_root
            .clone()
            .expect("burn root");
        command.command_kind = MANAGED_ASSET_BURN_COMMAND_KIND_V2.to_owned();
        command.authorization_root = Some(burn_root.clone());
        let occurrence = context.occurrence.as_mut().expect("managed occurrence");
        occurrence.command_kind = MANAGED_ASSET_BURN_COMMAND_KIND_V2.to_owned();
        occurrence.subject_id = command.account_owner.clone();
        occurrence.grant_root = burn_root;
    }
    context
        .occurrence
        .as_mut()
        .expect("managed occurrence")
        .command_body_hash = command.command_body_hash().expect("managed body hash");
    (
        context,
        state_with_split("managed_issue", account_atoms, custody_atoms, supply),
        AssetLaneCommandV2::ManagedLifecycle(command),
    )
}

const MULTIASSET_ASSETS: [&str; 7] = ["AUD", "EUR", "GBP", "JPY", "USD", "VND", "ZZZ"];
const MULTIASSET_MANAGED_ASSETS: [&str; 2] = ["GBP", "USD"];

fn multiasset_root(label: &str) -> RootV2 {
    hash_global_v2(
        "asset-lane-coordinator-test-v2",
        &serde_json::json!({"label": label}),
    )
    .expect("multiasset test root")
}

fn multiasset_transfer_policy(asset: &str) -> AssetTransferPolicyV2 {
    AssetTransferPolicyV2 {
        asset: asset.to_owned(),
        fee_owner: "treasury".to_owned(),
        transfer_fee_atoms: 0,
        enabled: true,
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
        asset_origin_root: Some(multiasset_root(&format!("origin:{asset}"))),
        atom_decimals: ASSET_ATOM_DECIMALS_V2,
    }
}

fn multiasset_managed_policy(asset: &str) -> ManagedAssetLifecyclePolicyV2 {
    ManagedAssetLifecyclePolicyV2 {
        asset: asset.to_owned(),
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
        asset_origin_root: Some(multiasset_root(&format!("origin:{asset}"))),
        atom_decimals: ASSET_ATOM_DECIMALS_V2,
        issue_authority_subject: Some("issuer".to_owned()),
        issue_authorization_root: Some(multiasset_root(&format!("issue:{asset}"))),
        burn_authorization_root: Some(multiasset_root(&format!("burn:{asset}"))),
        enabled: true,
    }
}

fn multiasset_balance_rows(rows: &[(&str, &str, u128)]) -> Vec<EconomicAmountV2> {
    rows.iter()
        .map(|(asset, owner, amount_atoms)| EconomicAmountV2 {
            owner: (*owner).to_owned(),
            asset: (*asset).to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            amount_atoms: *amount_atoms,
        })
        .collect()
}

fn multiasset_supply_rows(rows: &[(&str, u128)]) -> Vec<AssetSupplyV2> {
    rows.iter()
        .map(|(asset, amount_atoms)| AssetSupplyV2 {
            asset: (*asset).to_owned(),
            amount_atoms: *amount_atoms,
        })
        .collect()
}

fn multiasset_state() -> AssetLaneCustodyStateV2 {
    let transfer_policies = MULTIASSET_ASSETS
        .into_iter()
        .map(multiasset_transfer_policy)
        .collect::<Vec<_>>();
    let managed_policies = MULTIASSET_MANAGED_ASSETS
        .into_iter()
        .map(multiasset_managed_policy)
        .collect::<Vec<_>>();
    let origin_registry = AssetOriginRegistryStateV2 {
        schema: ASSET_ORIGIN_REGISTRY_SCHEMA_V2.to_owned(),
        module_release_id: multiasset_root("module-release"),
        policy: AssetOriginRegistrationPolicyV2 {
            authority_subject: "governance".to_owned(),
            authority_grant_root: multiasset_root("governance-grant"),
            allow_native: true,
            allow_tau_originated: true,
        },
        assets: transfer_policies
            .iter()
            .map(|policy| {
                let issue_policy_root = managed_policies
                    .iter()
                    .find(|managed| managed.asset == policy.asset)
                    .map(|managed| managed_asset_policy_root_v2(managed).expect("managed root"))
                    .unwrap_or_else(RootV2::zero);
                AssetOriginRecordV2 {
                    asset: policy.asset.clone(),
                    origin_kind: AssetOriginKindV2::TAU_ORIGINATED,
                    origin_root: policy
                        .asset_origin_root
                        .clone()
                        .expect("ordinary asset origin"),
                    transfer_policy_root: asset_transfer_policy_root_v2(policy)
                        .expect("transfer root"),
                    issue_policy_root,
                    decimals: u64::from(policy.atom_decimals),
                    asset_class: policy.asset_class,
                }
            })
            .collect(),
    };
    let module_release_id = origin_registry.module_release_id.clone();
    AssetLaneCustodyStateV2 {
        schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
        transfer_state: AssetTransferStateV2 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V2.to_owned(),
            module_release_id,
            policies: transfer_policies,
            balances: multiasset_balance_rows(&[
                ("EUR", "carol", 7),
                ("GBP", "dana", 3),
                ("JPY", "erin", 5),
                ("VND", "frank", 11),
            ]),
            supplies: multiasset_supply_rows(&[
                ("AUD", 0),
                ("EUR", 9),
                ("GBP", 3),
                ("JPY", 5),
                ("USD", 0),
                ("VND", 11),
                ("ZZZ", 0),
            ]),
        },
        origin_registry,
        managed_policies,
        custody: vec![EconomicAmountV2 {
            owner: "vault".to_owned(),
            asset: "EUR".to_owned(),
            custody_domain: "escrow".to_owned(),
            amount_atoms: 2,
        }],
    }
}

fn multiasset_managed_subject(
    command_kind: &str,
    account_owner: &str,
    amount_atoms: u128,
    subject_id: &str,
    nonce: u64,
) -> (AssetLaneContextV2, AssetLaneCommandV2) {
    let fixture = support::fixture();
    let case = &fixture.accepted["managed_issue"];
    let mut context: AssetLaneContextV2 = support::typed_vector(&case.vectors, "context");
    let mut command: ManagedAssetLifecycleCommandV2 =
        support::typed_vector(&case.vectors, "command");
    context.writer_epoch = 4;
    context.module_release_id = multiasset_root("module-release");
    let global_pre_state_root = multiasset_root(&format!("global-pre:{nonce}"));
    context.global_pre_state_root = global_pre_state_root.clone();
    let authorization_root = if command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2 {
        multiasset_root("issue:USD")
    } else {
        multiasset_root("burn:USD")
    };
    command.command_kind = command_kind.to_owned();
    command.account_owner = account_owner.to_owned();
    command.amount_atoms = amount_atoms;
    command.asset_origin_root = Some(multiasset_root("origin:USD"));
    command.authorization_root = Some(authorization_root.clone());
    let occurrence = context.occurrence.as_mut().expect("managed occurrence");
    occurrence.chain_id = "asset-lane-v2-test".to_owned();
    occurrence.deployment_root = multiasset_root("deployment");
    occurrence.pre_state_root = global_pre_state_root;
    occurrence.command_kind = command.command_kind.clone();
    occurrence.subject_id = subject_id.to_owned();
    occurrence.grant_root = authorization_root;
    occurrence.height = 8 + nonce;
    occurrence.tx_index = 0;
    occurrence.op_index = 0;
    occurrence.route_release_id = multiasset_root("route-release");
    occurrence.nonce = nonce;
    occurrence.profile_root = multiasset_root("profile");
    occurrence.command_body_hash = command.command_body_hash().expect("managed body hash");
    (context, AssetLaneCommandV2::ManagedLifecycle(command))
}

fn assert_multiasset_accepted(
    accepted: &AssetLaneCustodyAcceptedV2,
    source: &AssetLaneCustodyStateV2,
    expected_balances: &[EconomicAmountV2],
    expected_supplies: &[AssetSupplyV2],
) {
    let post = accepted.post_state();
    assert_eq!(accepted.route(), AssetLaneRouteV2::MANAGED_LIFECYCLE);
    assert_eq!(post.transfer_state.balances.as_slice(), expected_balances);
    assert_eq!(post.transfer_state.supplies.as_slice(), expected_supplies);
    assert_eq!(
        post.transfer_state
            .policies
            .iter()
            .map(|policy| policy.asset.as_str())
            .collect::<Vec<_>>(),
        MULTIASSET_ASSETS.to_vec()
    );
    assert_eq!(
        post.origin_registry
            .assets
            .iter()
            .map(|record| record.asset.as_str())
            .collect::<Vec<_>>(),
        MULTIASSET_ASSETS.to_vec()
    );
    assert_eq!(
        post.managed_policies
            .iter()
            .map(|policy| policy.asset.as_str())
            .collect::<Vec<_>>(),
        MULTIASSET_MANAGED_ASSETS.to_vec()
    );
    assert_eq!(
        post.transfer_state.module_release_id,
        source.transfer_state.module_release_id
    );
    assert_eq!(post.transfer_state.policies, source.transfer_state.policies);
    assert_eq!(post.origin_registry, source.origin_registry);
    assert_eq!(post.managed_policies, source.managed_policies);
    assert_eq!(
        post.custody,
        vec![EconomicAmountV2 {
            owner: "vault".to_owned(),
            asset: "EUR".to_owned(),
            custody_domain: "escrow".to_owned(),
            amount_atoms: 2,
        }]
    );
    assert_eq!(post.custody, source.custody);
    assert_eq!(accepted.production_authority(), "NONE");
    assert_eq!(accepted.profile_authentication(), "SHADOW");
}

fn assert_source_unchanged(source: &AssetLaneCustodyStateV2, bytes: &[u8], root: &RootV2) {
    assert_eq!(&canonical_bytes_v2(source).expect("source bytes"), bytes);
    assert_eq!(&source.state_root().expect("source root"), root);
}

fn total(rows: &[EconomicAmountV2], asset: &str) -> u128 {
    rows.iter()
        .filter(|row| row.asset == asset)
        .map(|row| row.amount_atoms)
        .sum()
}

fn expect_accepted(
    result: AssetLaneCustodyResultV2,
) -> Box<zenodex_global_settlement_abi_v2::AssetLaneCustodyAcceptedV2> {
    let AssetLaneCustodyResultV2::Accepted(accepted) = result else {
        panic!("custody successor unexpectedly rejected")
    };
    accepted
}

#[test]
fn managed_multiasset_history_keeps_complete_rows_and_rejects_unauthorized_burn() {
    let source = multiasset_state();
    source
        .validate()
        .expect("complete multiasset source is valid");
    let source_bytes = canonical_bytes_v2(&source).expect("source bytes");
    let source_root = source.state_root().expect("source root");

    let (issue_context, issue_command) =
        multiasset_managed_subject(MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, "alice", 2, "issuer", 1);
    let issued = expect_accepted(
        transition_asset_lane_custody_v2(&issue_context, &source, &issue_command)
            .expect("USD issue executes in the multiasset state"),
    );
    assert_multiasset_accepted(
        &issued,
        &source,
        &multiasset_balance_rows(&[
            ("EUR", "carol", 7),
            ("GBP", "dana", 3),
            ("JPY", "erin", 5),
            ("USD", "alice", 2),
            ("VND", "frank", 11),
        ]),
        &multiasset_supply_rows(&[
            ("AUD", 0),
            ("EUR", 9),
            ("GBP", 3),
            ("JPY", 5),
            ("USD", 2),
            ("VND", 11),
            ("ZZZ", 0),
        ]),
    );
    assert_source_unchanged(&source, &source_bytes, &source_root);

    let middle = issued.post_state().clone();
    let middle_bytes = canonical_bytes_v2(&middle).expect("middle bytes");
    let middle_root = middle.state_root().expect("middle root");
    let (unauthorized_context, unauthorized_command) =
        multiasset_managed_subject(MANAGED_ASSET_BURN_COMMAND_KIND_V2, "alice", 2, "mallory", 2);
    let AssetLaneCustodyResultV2::Rejected(rejected) =
        transition_asset_lane_custody_v2(&unauthorized_context, &middle, &unauthorized_command)
            .expect("unauthorized burn is a typed result")
    else {
        panic!("unauthorized burn unexpectedly accepted")
    };
    assert_eq!(rejected.route(), AssetLaneRouteV2::MANAGED_LIFECYCLE);
    assert_eq!(
        rejected.code(),
        AssetLaneRejectCodeV2::ManagedLifecycle(
            ManagedAssetLifecycleRejectCodeV2::UNAUTHORIZED_SUBJECT,
        )
    );
    assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
    assert_eq!(rejected.pre_state_root(), &middle_root);
    assert!(rejected.effects().is_empty());
    assert_source_unchanged(&middle, &middle_bytes, &middle_root);

    let (burn_context, burn_command) =
        multiasset_managed_subject(MANAGED_ASSET_BURN_COMMAND_KIND_V2, "alice", 2, "alice", 3);
    let burned = expect_accepted(
        transition_asset_lane_custody_v2(&burn_context, &middle, &burn_command)
            .expect("authorized USD burn executes in the middle state"),
    );
    assert_multiasset_accepted(
        &burned,
        &middle,
        &multiasset_balance_rows(&[
            ("EUR", "carol", 7),
            ("GBP", "dana", 3),
            ("JPY", "erin", 5),
            ("VND", "frank", 11),
        ]),
        &multiasset_supply_rows(&[
            ("AUD", 0),
            ("EUR", 9),
            ("GBP", 3),
            ("JPY", 5),
            ("USD", 0),
            ("VND", 11),
            ("ZZZ", 0),
        ]),
    );
    assert_source_unchanged(&middle, &middle_bytes, &middle_root);

    let burned_source = burned.post_state().clone();
    let burned_source_bytes = canonical_bytes_v2(&burned_source).expect("burned source bytes");
    let burned_source_root = burned_source.state_root().expect("burned source root");
    let (reissue_context, reissue_command) =
        multiasset_managed_subject(MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, "bob", 1, "issuer", 4);
    let reissued = expect_accepted(
        transition_asset_lane_custody_v2(&reissue_context, &burned_source, &reissue_command)
            .expect("USD reissue executes after the full burn"),
    );
    assert_multiasset_accepted(
        &reissued,
        &burned_source,
        &multiasset_balance_rows(&[
            ("EUR", "carol", 7),
            ("GBP", "dana", 3),
            ("JPY", "erin", 5),
            ("USD", "bob", 1),
            ("VND", "frank", 11),
        ]),
        &multiasset_supply_rows(&[
            ("AUD", 0),
            ("EUR", 9),
            ("GBP", 3),
            ("JPY", 5),
            ("USD", 1),
            ("VND", 11),
            ("ZZZ", 0),
        ]),
    );
    assert_source_unchanged(&burned_source, &burned_source_bytes, &burned_source_root);
}

#[test]
fn lawful_account_transfer_preserves_vault_and_completes_physical_conservation() {
    let (context, pre_state, command) = transfer_subject();
    pre_state
        .validate()
        .expect("80 account + 20 vault must represent supply 100");
    let first = transition_asset_lane_custody_v2(&context, &pre_state, &command)
        .expect("custody transfer executes");
    let second = transition_asset_lane_custody_v2(&context, &pre_state, &command)
        .expect("custody transfer replay executes");
    assert_eq!(first, second);
    let accepted = expect_accepted(first);

    assert_eq!(accepted.route(), AssetLaneRouteV2::TRANSFER);
    assert_eq!(accepted.post_state().custody, pre_state.custody);
    assert_eq!(
        accepted
            .post_state()
            .transfer_state
            .balance_atoms("alice", "USD"),
        68
    );
    assert_eq!(
        accepted
            .post_state()
            .transfer_state
            .balance_atoms("bob", "USD"),
        10
    );
    assert_eq!(
        accepted
            .post_state()
            .transfer_state
            .balance_atoms("treasury", "USD"),
        2
    );
    assert_eq!(
        total(&accepted.post_state().transfer_state.balances, "USD"),
        80
    );
    assert_eq!(total(&accepted.post_state().custody, "USD"), 20);

    let conservation = &accepted.effects().asset_conservation;
    assert_eq!(conservation.len(), 1);
    assert_eq!(conservation[0].owned_and_custodied_pre_atoms, 100);
    assert_eq!(conservation[0].owned_and_custodied_post_atoms, 100);
    assert_eq!(conservation[0].supply_pre_atoms, 100);
    assert_eq!(conservation[0].supply_post_atoms, 100);
    assert_eq!(accepted.effects().rows.len(), 4);
    assert_eq!(accepted.effects().fee_conservation.len(), 1);
    assert!(accepted.effects().external_outbox_enqueue.is_empty());
    assert_eq!(
        accepted.module_journal().pre_lane_root,
        pre_state.state_root().unwrap()
    );
    assert_eq!(
        accepted.module_journal().post_lane_root,
        accepted.post_state().state_root().unwrap()
    );
    assert_ne!(accepted.source_leaf_receipt_root(), accepted.receipt_root());
    assert_eq!(accepted.production_authority(), "NONE");
    assert_eq!(accepted.profile_authentication(), "SHADOW");
    accepted
        .validate()
        .expect("returned acceptance remains self-consistent");
}

#[test]
fn managed_issue_and_burn_preserve_custody_and_replace_only_physical_totals() {
    for (burn, expected_account, expected_supply, issue, burned) in
        [(false, 90, 110, 10, 0), (true, 70, 90, 0, 10)]
    {
        let (context, pre_state, command) = managed_subject(burn, 80, 20, 100);
        let accepted = expect_accepted(
            transition_asset_lane_custody_v2(&context, &pre_state, &command)
                .expect("managed custody transition executes"),
        );
        assert_eq!(accepted.route(), AssetLaneRouteV2::MANAGED_LIFECYCLE);
        assert_eq!(accepted.post_state().custody, pre_state.custody);
        assert_eq!(
            accepted
                .post_state()
                .transfer_state
                .balance_atoms("alice", "USD"),
            expected_account
        );
        assert_eq!(
            accepted
                .post_state()
                .transfer_state
                .supply_atoms("USD")
                .unwrap(),
            expected_supply
        );
        let row = &accepted.effects().asset_conservation[0];
        assert_eq!(row.owned_and_custodied_pre_atoms, 100);
        assert_eq!(row.owned_and_custodied_post_atoms, expected_supply);
        assert_eq!(row.supply_pre_atoms, 100);
        assert_eq!(row.supply_post_atoms, expected_supply);
        assert_eq!(row.authorized_issue_atoms, issue);
        assert_eq!(row.authorized_burn_atoms, burned);
        assert!(accepted.effects().external_outbox_enqueue.is_empty());
    }
}

#[test]
fn account_domain_cannot_masquerade_as_external_custody() {
    let mut state = state_with_split("transfer", 80, 20, 100);
    state.custody[0].custody_domain = ACCOUNT_CUSTODY_DOMAIN_V2.to_owned();
    assert_eq!(
        state.validate(),
        Err(AbiErrorV2::InvalidBinding("asset lane custody row"))
    );
}

#[test]
fn physical_conservation_and_u128_overflow_fail_closed() {
    let state = state_with_split("transfer", 80, 21, 100);
    assert_eq!(
        state.validate(),
        Err(AbiErrorV2::Conservation(
            "asset lane physical total differs from supply"
        ))
    );

    let mut overflow = state_with_split("transfer", u128::MAX, 1, u128::MAX);
    overflow.transfer_state.balances = vec![account_row("alice", u128::MAX)];
    assert_eq!(
        overflow.validate(),
        Err(AbiErrorV2::Conservation(
            "asset lane physical total overflow"
        ))
    );
}

#[test]
fn custody_row_ceiling_precedes_inner_validation_and_accepts_exact_boundary() {
    let mut state = state_with_split("transfer", 0, 0, MAX_ASSET_LANE_CUSTODY_ROWS_V2 as u128);
    state.custody = (0..MAX_ASSET_LANE_CUSTODY_ROWS_V2)
        .map(|index| custody_row(&format!("vault-{index:04}"), "vault:primary", 1))
        .collect();
    state
        .validate()
        .expect("exact custody row ceiling must remain representable");

    state.custody.push(EconomicAmountV2 {
        owner: String::new(),
        asset: String::new(),
        custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
        amount_atoms: 0,
    });
    assert_eq!(
        state.validate(),
        Err(AbiErrorV2::StateResourceLimit("asset lane custody rows"))
    );
}

#[test]
fn dormant_zero_supply_key_is_retained_and_can_be_issued() {
    let (context, state, command) = managed_subject(false, 0, 0, 0);
    state
        .validate()
        .expect("registered dormant zero supply must be valid");
    assert_eq!(state.transfer_state.supplies.len(), 1);
    assert_eq!(state.transfer_state.supplies[0].amount_atoms, 0);
    let accepted = expect_accepted(
        transition_asset_lane_custody_v2(&context, &state, &command)
            .expect("issue from dormant supply executes"),
    );
    assert_eq!(accepted.post_state().transfer_state.supplies.len(), 1);
    assert_eq!(
        accepted.post_state().transfer_state.supplies[0].amount_atoms,
        10
    );
    let row = &accepted.effects().asset_conservation[0];
    assert_eq!(
        (row.owned_and_custodied_pre_atoms, row.supply_pre_atoms),
        (0, 0)
    );
    assert_eq!(
        (row.owned_and_custodied_post_atoms, row.supply_post_atoms),
        (10, 10)
    );
}

#[test]
fn origin_membership_rejects_before_leaf_dispatch() {
    let (mut context, mut state, command) = transfer_subject();
    state.transfer_state.policies[0].fee_owner = "mallory".to_owned();
    context.occurrence = None;
    state
        .validate()
        .expect("structural state remains valid before origin membership");

    let AssetLaneCustodyResultV2::Rejected(rejected) =
        transition_asset_lane_custody_v2(&context, &state, &command)
            .expect("origin mismatch is a typed rejection")
    else {
        panic!("origin mismatch unexpectedly accepted")
    };
    assert_eq!(rejected.route(), AssetLaneRouteV2::COORDINATOR);
    assert_eq!(
        rejected.code(),
        AssetLaneRejectCodeV2::Coordinator(
            AssetLaneCoordinatorRejectCodeV2::REGISTRY_BINDING_MISMATCH
        )
    );
    assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
    assert!(rejected.effects().is_empty());
}

#[test]
fn registry_identity_mismatch_is_typed_before_leaf_dispatch() {
    let (mut context, mut state, command) = transfer_subject();
    let wrong_origin = hash_global_v2("asset-lane-custody-test-root-v2", &"wrong-origin").unwrap();
    state.transfer_state.policies[0].asset_origin_root = Some(wrong_origin.clone());
    state.managed_policies[0].asset_origin_root = Some(wrong_origin);
    context.occurrence = None;

    let AssetLaneCustodyResultV2::Rejected(rejected) =
        transition_asset_lane_custody_v2(&context, &state, &command)
            .expect("registry identity mismatch is a typed rejection")
    else {
        panic!("registry identity mismatch unexpectedly accepted")
    };
    assert_eq!(rejected.route(), AssetLaneRouteV2::COORDINATOR);
    assert_eq!(
        rejected.code(),
        AssetLaneRejectCodeV2::Coordinator(
            AssetLaneCoordinatorRejectCodeV2::REGISTRY_BINDING_MISMATCH
        )
    );
    assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
    assert!(rejected.effects().is_empty());
}

#[test]
fn wrong_occurrence_binding_is_a_route_owned_exact_noop() {
    let (mut context, state, command) = transfer_subject();
    context.global_pre_state_root =
        hash_global_v2("asset-lane-custody-test-root-v2", &"wrong-pre").unwrap();

    let AssetLaneCustodyResultV2::Rejected(rejected) =
        transition_asset_lane_custody_v2(&context, &state, &command)
            .expect("wrong occurrence binding is a typed rejection")
    else {
        panic!("wrong occurrence binding unexpectedly accepted")
    };
    assert_eq!(rejected.route(), AssetLaneRouteV2::TRANSFER);
    assert_eq!(
        rejected.code(),
        AssetLaneRejectCodeV2::Transfer(AssetTransferRejectCodeV2::OCCURRENCE_BINDING_MISMATCH)
    );
    assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
    assert_eq!(rejected.pre_state_root(), &state.state_root().unwrap());
    assert!(rejected.effects().is_empty());
}

#[test]
fn historical_asset_lane_decoder_rejects_successor_state_bytes() {
    let (_, state, _) = transfer_subject();
    let bytes = canonical_bytes_v2(&state).expect("successor canonical bytes");
    let decoded: AssetLaneCustodyStateV2 =
        decode_canonical_v2(&bytes).expect("successor decoder accepts its state");
    assert_eq!(decoded, state);
    assert!(decode_canonical_v2::<AssetLaneStateV2>(&bytes).is_err());
}

#[test]
fn old_account_only_result_type_remains_distinct() {
    let fixture = support::fixture();
    let case = &fixture.accepted["transfer"];
    let context: AssetLaneContextV2 = support::typed_vector(&case.vectors, "context");
    let state: AssetLaneStateV2 = support::typed_vector(&case.vectors, "pre_state");
    let command = support::command(&case.vectors, &case.command_type);
    assert!(matches!(
        zenodex_global_settlement_abi_v2::transition_asset_lane_v2(&context, &state, &command)
            .expect("historical account-only transition remains valid"),
        AssetLaneResultV2::Accepted(_)
    ));
}

#[test]
fn successor_state_root_is_domain_separated_from_leaf_root() {
    let (_, state, _) = transfer_subject();
    let successor = state.state_root().expect("successor root");
    let leaf = state.transfer_state.state_root().expect("leaf root");
    assert_ne!(successor, leaf);
    assert_ne!(successor, RootV2::zero());
}
