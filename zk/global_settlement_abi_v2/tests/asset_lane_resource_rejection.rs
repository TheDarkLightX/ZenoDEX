#[path = "support/asset_lane_coordinator.rs"]
mod support;

use support::{fixture, typed_vector};
use zenodex_global_settlement_abi_v2::{
    asset_transfer_policy_root_v2, canonical_bytes_v2, canonical_wire_bytes_v2,
    decode_canonical_v2, transition_asset_lane_v2, transition_asset_transfer_v2,
    transition_managed_asset_lifecycle_v2, validate_asset_state_asset_count_v2,
    validate_asset_state_balance_row_count_v2, validate_consumed_object_id_count_v2,
    validate_consumed_occurrence_count_v2, validate_rootable_asset_state_canonical_bytes_v2,
    AbiErrorV2, AssetClassV2, AssetLaneCommandV2, AssetLaneContextV2,
    AssetLaneCoordinatorRejectCodeV2, AssetLaneRejectCodeV2, AssetLaneRejectedWireV2,
    AssetLaneResultV2, AssetLaneRouteV2, AssetLaneStateV2, AssetOriginKindV2, AssetSupplyV2,
    AssetTransferCommandV2, AssetTransferRejectCodeV2, AssetTransferResultV2, EconomicAmountV2,
    GlobalEconomicEffectPlanV2, ManagedAssetLifecycleCommandV2, ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleResultV2, RootV2, MAX_ASSETS_PER_ASSET_STATE_V2,
    MAX_ASSET_LANE_BALANCE_ROWS_V2, MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
};

fn root(value: u64) -> RootV2 {
    RootV2::parse(
        format!("0x{value:064x}"),
        "resource rejection test root",
        false,
    )
    .expect("test root is canonical")
}

fn managed_subject() -> (
    AssetLaneContextV2,
    AssetLaneStateV2,
    ManagedAssetLifecycleCommandV2,
) {
    let fixture = fixture();
    let case = &fixture.accepted["managed_issue"];
    (
        typed_vector(&case.vectors, "context"),
        typed_vector(&case.vectors, "pre_state"),
        typed_vector(&case.vectors, "command"),
    )
}

fn rebind_context(
    mut context: AssetLaneContextV2,
    command_kind: &str,
    command_body_hash: RootV2,
    subject: &str,
    grant_root: RootV2,
    nonce: u64,
    pre_state_root: RootV2,
) -> AssetLaneContextV2 {
    context.global_pre_state_root = pre_state_root.clone();
    let occurrence = context.occurrence.as_mut().expect("fixture occurrence");
    occurrence.pre_state_root = pre_state_root;
    occurrence.command_kind = command_kind.to_owned();
    occurrence.command_body_hash = command_body_hash;
    occurrence.subject_id = subject.to_owned();
    occurrence.grant_root = grant_root;
    occurrence.nonce = nonce;
    context
}

fn managed_command(
    command_kind: &str,
    account_owner: &str,
    amount_atoms: u128,
    authorization_root: RootV2,
) -> ManagedAssetLifecycleCommandV2 {
    let (_, _, mut command) = managed_subject();
    command.command_kind = command_kind.to_owned();
    command.account_owner = account_owner.to_owned();
    command.amount_atoms = amount_atoms;
    command.authorization_root = Some(authorization_root);
    command
}

fn managed_context(
    command: &ManagedAssetLifecycleCommandV2,
    subject: &str,
    grant_root: RootV2,
    nonce: u64,
    state: &AssetLaneStateV2,
) -> AssetLaneContextV2 {
    let (context, _, _) = managed_subject();
    rebind_context(
        context,
        &command.command_kind,
        command.command_body_hash().expect("managed command hash"),
        subject,
        grant_root,
        nonce,
        state.state_root().expect("managed context state root"),
    )
}

fn transfer_command(
    asset: &str,
    asset_origin_root: RootV2,
    sender: &str,
    recipient: &str,
    amount_atoms: u128,
) -> AssetTransferCommandV2 {
    let fixture = fixture();
    let case = &fixture.accepted["transfer"];
    let mut command: AssetTransferCommandV2 = typed_vector(&case.vectors, "command");
    command.asset = asset.to_owned();
    command.asset_origin_root = Some(asset_origin_root);
    command.sender = sender.to_owned();
    command.recipient = recipient.to_owned();
    command.amount_atoms = amount_atoms;
    command.max_fee_atoms = 0;
    command
}

fn transfer_context(
    command: &AssetTransferCommandV2,
    subject: &str,
    nonce: u64,
    state: &AssetLaneStateV2,
) -> AssetLaneContextV2 {
    let (context, _, _) = managed_subject();
    rebind_context(
        context,
        &command.command_kind,
        command.command_body_hash().expect("transfer command hash"),
        subject,
        root(5),
        nonce,
        state.state_root().expect("transfer context state root"),
    )
}

fn lane_state(
    eur_rows: usize,
    eur_first_atoms: u128,
    usd_rows: &[(String, u128)],
) -> AssetLaneStateV2 {
    let (_, mut state, _) = managed_subject();
    let eur_origin = root(100);
    let mut eur_policy = state.transfer_policies[0].clone();
    eur_policy.asset = "EUR".to_owned();
    eur_policy.transfer_fee_atoms = 0;
    eur_policy.asset_origin_root = Some(eur_origin.clone());
    let eur_policy_root = asset_transfer_policy_root_v2(&eur_policy).expect("EUR policy root");

    let mut eur_record = state.origin_registry.assets[0].clone();
    eur_record.asset = "EUR".to_owned();
    eur_record.origin_kind = AssetOriginKindV2::TAU_ORIGINATED;
    eur_record.origin_root = eur_origin;
    eur_record.transfer_policy_root = eur_policy_root;
    eur_record.issue_policy_root = RootV2::zero();
    eur_record.asset_class = AssetClassV2::RegisteredOrdinaryToken;

    state.transfer_policies.push(eur_policy);
    state
        .transfer_policies
        .sort_by(|left, right| left.asset.cmp(&right.asset));
    state.origin_registry.assets.push(eur_record);
    state
        .origin_registry
        .assets
        .sort_by(|left, right| left.asset.cmp(&right.asset));

    let mut balances = Vec::with_capacity(eur_rows + usd_rows.len());
    let mut eur_total = 0_u128;
    for index in 0..eur_rows {
        let amount_atoms = if index == 0 { eur_first_atoms } else { 1 };
        eur_total += amount_atoms;
        balances.push(EconomicAmountV2 {
            owner: format!("holder{index:04}"),
            asset: "EUR".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms,
        });
    }
    let mut usd_total = 0_u128;
    for (owner, amount_atoms) in usd_rows {
        usd_total += *amount_atoms;
        balances.push(EconomicAmountV2 {
            owner: owner.clone(),
            asset: "USD".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: *amount_atoms,
        });
    }
    balances.sort_by(|left, right| {
        (
            left.asset.as_str(),
            left.owner.as_str(),
            left.custody_domain.as_str(),
        )
            .cmp(&(
                right.asset.as_str(),
                right.owner.as_str(),
                right.custody_domain.as_str(),
            ))
    });
    state.balances = balances;
    state.supplies = vec![
        AssetSupplyV2 {
            asset: "EUR".to_owned(),
            amount_atoms: eur_total,
        },
        AssetSupplyV2 {
            asset: "USD".to_owned(),
            amount_atoms: usd_total,
        },
    ];
    state.validate().expect("resource test state is valid");
    state
}

fn assert_lane_noop(
    result: AssetLaneResultV2,
    state: &AssetLaneStateV2,
    route: AssetLaneRouteV2,
    code: AssetLaneRejectCodeV2,
) {
    let AssetLaneResultV2::Rejected(rejected) = result else {
        panic!("resource-limited transition unexpectedly accepted")
    };
    assert_eq!(rejected.route(), route);
    assert_eq!(rejected.code(), code);
    let root = state.state_root().expect("pre-state root");
    assert_eq!(rejected.pre_state_root(), &root);
    assert_eq!(rejected.post_state_root(), &root);
    assert!(rejected.effects().is_empty());
    assert!(rejected.effects().rows.is_empty());
    assert!(rejected.effects().lane_writes.is_empty());
    assert!(rejected.effects().occurrence_consumptions.is_empty());
    assert!(rejected.effects().external_outbox_enqueue.is_empty());
    assert_eq!(rejected.production_authority(), "NONE");
    assert_eq!(rejected.profile_authentication(), "SHADOW");
}

fn holder_rows(count: usize) -> Vec<(String, u128)> {
    (0..count)
        .map(|index| (format!("holder{index:04}"), 1))
        .collect()
}

const REAL_BYTE_BOUNDARY_OWNER_V2: &str = "ali\"ce\\x";
const REAL_BYTE_BOUNDARY_ROW_SKELETON_V2: &[u8] =
    br#"{"amount_atoms":1,"asset":"EUR","custody_domain":"accounts","owner":""}"#;
// This local chunk controls the sizing search; it is not a protocol bound.
const REAL_BYTE_BOUNDARY_MAX_EXTRA_PER_ROW_V2: usize = 300;

fn escaped_size_v2(value: &str) -> usize {
    value.len()
        + value
            .bytes()
            .filter(|byte| matches!(byte, b'"' | b'\\'))
            .count()
}

fn real_byte_boundary_state_v2(headroom: usize, funded: bool) -> AssetLaneStateV2 {
    assert_eq!(MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2, 1_048_576);
    let usd_rows = if funded {
        vec![(REAL_BYTE_BOUNDARY_OWNER_V2.to_owned(), 9)]
    } else {
        Vec::new()
    };
    let empty = lane_state(0, 1, &usd_rows);
    let base_size = canonical_bytes_v2(&empty)
        .expect("empty boundary state canonicalizes")
        .len();
    let target = MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
        .checked_sub(headroom)
        .expect("boundary headroom fits the limit");
    let min_row_size = REAL_BYTE_BOUNDARY_ROW_SKELETON_V2.len() + 10;
    let count =
        (target - base_size) / (min_row_size + REAL_BYTE_BOUNDARY_MAX_EXTRA_PER_ROW_V2 + 1) + 1;
    let first_comma_correction = if funded { 0 } else { 1 };
    let extra = target - base_size - (count.to_string().len() - 1) - count * (min_row_size + 1)
        + first_comma_correction;
    assert!(
        extra <= REAL_BYTE_BOUNDARY_MAX_EXTRA_PER_ROW_V2 * count,
        "sizing search produced too much owner padding"
    );
    assert!(
        count + usd_rows.len() < MAX_ASSET_LANE_BALANCE_ROWS_V2,
        "boundary state remains below the row ceiling"
    );

    let mut balances = Vec::with_capacity(count + usd_rows.len());
    let mut remaining = extra;
    for index in 0..count {
        let contribution = remaining.min(REAL_BYTE_BOUNDARY_MAX_EXTRA_PER_ROW_V2);
        remaining -= contribution;
        let mut owner = format!("holder{index:04}");
        owner.push_str(&"\\".repeat(contribution / 2));
        if contribution % 2 == 1 {
            owner.push('x');
        }
        balances.push(EconomicAmountV2 {
            owner,
            asset: "EUR".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: 1,
        });
    }
    assert_eq!(remaining, 0);
    balances.extend(empty.balances.iter().cloned());
    balances.sort_by(|left, right| {
        (
            left.asset.as_str(),
            left.owner.as_str(),
            left.custody_domain.as_str(),
        )
            .cmp(&(
                right.asset.as_str(),
                right.owner.as_str(),
                right.custody_domain.as_str(),
            ))
    });

    let mut state = empty;
    state.balances = balances;
    for supply in &mut state.supplies {
        supply.amount_atoms = match supply.asset.as_str() {
            "EUR" => count as u128,
            "USD" => {
                if funded {
                    9
                } else {
                    0
                }
            }
            _ => supply.amount_atoms,
        };
    }
    state.validate().expect("real boundary state is valid");
    assert_eq!(
        canonical_bytes_v2(&state)
            .expect("real boundary state canonicalizes")
            .len(),
        target
    );
    state
}

fn expected_real_byte_boundary_post_state_v2(
    pre_state: &AssetLaneStateV2,
    managed_post_state: &zenodex_global_settlement_abi_v2::ManagedAssetLifecycleStateV2,
) -> AssetLaneStateV2 {
    let mut post_state = pre_state.clone();
    post_state.balances.retain(|row| row.asset != "USD");
    post_state
        .balances
        .extend(managed_post_state.balances.iter().cloned());
    post_state.balances.sort_by(|left, right| {
        (
            left.asset.as_str(),
            left.owner.as_str(),
            left.custody_domain.as_str(),
        )
            .cmp(&(
                right.asset.as_str(),
                right.owner.as_str(),
                right.custody_domain.as_str(),
            ))
    });
    post_state.supplies.retain(|row| row.asset != "USD");
    post_state
        .supplies
        .extend(managed_post_state.supplies.iter().cloned());
    post_state
        .supplies
        .sort_by(|left, right| left.asset.cmp(&right.asset));
    post_state
}

fn check_real_byte_boundary_v2(funded: bool, excess: usize) {
    let added_bytes = if funded {
        assert_eq!(REAL_BYTE_BOUNDARY_OWNER_V2.len(), 8);
        assert_eq!(escaped_size_v2(REAL_BYTE_BOUNDARY_OWNER_V2), 10);
        2
    } else {
        REAL_BYTE_BOUNDARY_ROW_SKELETON_V2.len() + escaped_size_v2(REAL_BYTE_BOUNDARY_OWNER_V2) + 1
    };
    let headroom = added_bytes - excess;
    let state = real_byte_boundary_state_v2(headroom, funded);
    let command = managed_command(
        "managed_asset_issue",
        REAL_BYTE_BOUNDARY_OWNER_V2,
        1,
        root(5),
    );
    let context = managed_context(&command, "issuer", root(5), 20 + excess as u64, &state);
    let occurrence_id = context
        .occurrence
        .as_ref()
        .expect("boundary context occurrence")
        .occurrence_id()
        .expect("boundary occurrence id");
    let pre_bytes = canonical_bytes_v2(&state).expect("pre-state canonical bytes");
    let pre_root = state.state_root().expect("pre-state root");
    assert_eq!(
        pre_bytes.len(),
        MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2 - headroom
    );

    let leaf = transition_managed_asset_lifecycle_v2(
        &context.managed_context(),
        &state.managed_leaf_state(),
        &command,
    )
    .expect("managed leaf must remain within its own small state");
    let ManagedAssetLifecycleResultV2::Accepted(leaf) = leaf else {
        panic!("managed leaf boundary control unexpectedly rejected")
    };
    assert_eq!(
        leaf.post_state
            .balance_atoms(REAL_BYTE_BOUNDARY_OWNER_V2, "USD"),
        if funded { 10 } else { 1 }
    );
    assert_eq!(
        leaf.post_state.supply_atoms("USD").expect("USD supply"),
        if funded { 10 } else { 1 }
    );

    let expected_post_state = expected_real_byte_boundary_post_state_v2(&state, &leaf.post_state);
    let expected_post_bytes =
        canonical_bytes_v2(&expected_post_state).expect("expected recomposed state canonicalizes");
    assert_eq!(expected_post_bytes.len(), pre_bytes.len() + added_bytes);

    let result = transition_asset_lane_v2(
        &context,
        &state,
        &AssetLaneCommandV2::ManagedLifecycle(command),
    )
    .expect("aggregate byte boundary must be a typed result");
    if excess == 0 {
        let AssetLaneResultV2::Accepted(accepted) = result else {
            panic!("exact byte ceiling positive control rejected")
        };
        let post_bytes = canonical_bytes_v2(accepted.post_state())
            .expect("accepted full boundary state canonicalizes");
        assert_eq!(post_bytes, expected_post_bytes);
        assert_eq!(
            post_bytes.len(),
            MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
        );
        assert_eq!(
            accepted.post_state().balances.len(),
            state.balances.len() + usize::from(!funded)
        );
        assert_eq!(accepted.route(), AssetLaneRouteV2::MANAGED_LIFECYCLE);
        assert_eq!(
            accepted.effects().occurrence_consumptions,
            vec![occurrence_id.clone()]
        );
        assert_eq!(
            accepted.module_journal().command_occurrence_id,
            occurrence_id
        );
        assert_eq!(accepted.production_authority(), "NONE");
        assert_eq!(accepted.profile_authentication(), "SHADOW");
        assert_eq!(
            accepted
                .post_state()
                .balance_atoms(REAL_BYTE_BOUNDARY_OWNER_V2, "USD")
                .expect("accepted USD balance"),
            if funded { 10 } else { 1 }
        );
        assert_eq!(
            accepted
                .post_state()
                .supply_atoms("USD")
                .expect("accepted USD supply"),
            if funded { 10 } else { 1 }
        );
        if funded {
            assert_eq!(accepted.post_state().balances.len(), state.balances.len());
        }
    } else {
        assert_eq!(excess, 1);
        assert_eq!(
            expected_post_bytes.len(),
            MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2 + 1
        );
        assert_lane_noop(
            result,
            &state,
            AssetLaneRouteV2::COORDINATOR,
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::STATE_RESOURCE_LIMIT,
            ),
        );
    }
    assert_eq!(
        canonical_bytes_v2(&state).expect("pre-state remains canonical"),
        pre_bytes
    );
    assert_eq!(
        state.state_root().expect("pre-state root remains stable"),
        pre_root
    );
}

#[test]
fn real_byte_ceiling_counts_escaped_new_owner_and_array_separator() {
    for excess in [0, 1] {
        check_real_byte_boundary_v2(false, excess);
    }
}

#[test]
fn real_byte_ceiling_counts_balance_and_supply_digit_growth_without_new_rows() {
    for excess in [0, 1] {
        check_real_byte_boundary_v2(true, excess);
    }
}

#[test]
fn aggregate_row_overflow_is_coordinator_owned_and_replay_is_a_noop() {
    let state = lane_state(MAX_ASSET_LANE_BALANCE_ROWS_V2, 1, &[]);
    let issue = managed_command("managed_asset_issue", "alice", 1, root(5));
    let context = managed_context(&issue, "issuer", root(5), 1, &state);
    let leaf = transition_managed_asset_lifecycle_v2(
        &context.managed_context(),
        &state.managed_leaf_state(),
        &issue,
    )
    .expect("managed leaf must fit before aggregate admission");
    let ManagedAssetLifecycleResultV2::Accepted(leaf) = leaf else {
        panic!("managed leaf unexpectedly rejected")
    };
    assert_eq!(leaf.post_state.balances.len(), 1);

    let before = state.state_root().expect("pre-state root");
    let first = transition_asset_lane_v2(
        &context,
        &state,
        &AssetLaneCommandV2::ManagedLifecycle(issue.clone()),
    )
    .expect("aggregate resource rejection must be typed");
    let second = transition_asset_lane_v2(
        &context,
        &state,
        &AssetLaneCommandV2::ManagedLifecycle(issue),
    )
    .expect("replayed aggregate resource rejection must be typed");
    assert_eq!(first, second);
    assert_lane_noop(
        first,
        &state,
        AssetLaneRouteV2::COORDINATOR,
        AssetLaneRejectCodeV2::Coordinator(AssetLaneCoordinatorRejectCodeV2::STATE_RESOURCE_LIMIT),
    );
    assert_eq!(
        state.state_root().expect("state root remains stable"),
        before
    );
    assert_eq!(state.balances.len(), MAX_ASSET_LANE_BALANCE_ROWS_V2);
}

#[test]
fn direct_transfer_growth_keeps_the_transfer_owner_and_exact_noop() {
    let state = lane_state(MAX_ASSET_LANE_BALANCE_ROWS_V2, 5, &[]);
    let command = transfer_command("EUR", root(100), "holder0000", "alice", 1);
    let context = transfer_context(&command, "holder0000", 2, &state);
    let leaf = transition_asset_transfer_v2(
        &context.transfer_context(),
        &state.transfer_leaf_state(),
        &command,
    )
    .expect("direct transfer resource rejection must be typed");
    let AssetTransferResultV2::Rejected(leaf) = leaf else {
        panic!("transfer leaf unexpectedly accepted a 4097th row")
    };
    assert_eq!(leaf.code, AssetTransferRejectCodeV2::STATE_RESOURCE_LIMIT);
    assert_eq!(leaf.pre_state_root, leaf.post_state_root);
    assert!(leaf.effects.is_empty());
    assert!(leaf.effects.occurrence_consumptions.is_empty());

    let result = transition_asset_lane_v2(&context, &state, &AssetLaneCommandV2::Transfer(command))
        .expect("coordinated transfer resource rejection must be typed");
    assert_lane_noop(
        result,
        &state,
        AssetLaneRouteV2::TRANSFER,
        AssetLaneRejectCodeV2::Transfer(AssetTransferRejectCodeV2::STATE_RESOURCE_LIMIT),
    );
}

#[test]
fn direct_managed_growth_keeps_the_managed_owner_and_exact_noop() {
    let usd_rows = holder_rows(MAX_ASSET_LANE_BALANCE_ROWS_V2);
    let state = lane_state(0, 1, &usd_rows);
    let command = managed_command("managed_asset_issue", "alice", 1, root(5));
    let context = managed_context(&command, "issuer", root(5), 3, &state);
    let leaf = transition_managed_asset_lifecycle_v2(
        &context.managed_context(),
        &state.managed_leaf_state(),
        &command,
    )
    .expect("direct managed resource rejection must be typed");
    let ManagedAssetLifecycleResultV2::Rejected(leaf) = leaf else {
        panic!("managed leaf unexpectedly accepted a 4097th row")
    };
    assert_eq!(
        leaf.code,
        ManagedAssetLifecycleRejectCodeV2::STATE_RESOURCE_LIMIT
    );
    assert_eq!(leaf.pre_state_root, leaf.post_state_root);
    assert!(leaf.effects.is_empty());
    assert!(leaf.effects.occurrence_consumptions.is_empty());

    let result = transition_asset_lane_v2(
        &context,
        &state,
        &AssetLaneCommandV2::ManagedLifecycle(command),
    )
    .expect("coordinated managed resource rejection must be typed");
    assert_lane_noop(
        result,
        &state,
        AssetLaneRouteV2::MANAGED_LIFECYCLE,
        AssetLaneRejectCodeV2::ManagedLifecycle(
            ManagedAssetLifecycleRejectCodeV2::STATE_RESOURCE_LIMIT,
        ),
    );
}

#[test]
fn row_boundary_accepts_4095_to_4096_and_full_row_transfer() {
    let below = lane_state(MAX_ASSET_LANE_BALANCE_ROWS_V2 - 1, 1, &[]);
    let issue = managed_command("managed_asset_issue", "alice", 1, root(5));
    let issued = transition_asset_lane_v2(
        &managed_context(&issue, "issuer", root(5), 4, &below),
        &below,
        &AssetLaneCommandV2::ManagedLifecycle(issue),
    )
    .expect("4095-to-4096 issue should fit");
    let AssetLaneResultV2::Accepted(issued) = issued else {
        panic!("row boundary positive control rejected")
    };
    assert_eq!(
        issued.post_state().balances.len(),
        MAX_ASSET_LANE_BALANCE_ROWS_V2
    );
    assert_eq!(
        issued
            .post_state()
            .balance_atoms("alice", "USD")
            .expect("alice balance"),
        1
    );
    assert_eq!(
        issued.post_state().supply_atoms("USD").expect("USD supply"),
        1
    );
    assert_eq!(issued.route(), AssetLaneRouteV2::MANAGED_LIFECYCLE);
    assert_eq!(issued.production_authority(), "NONE");
    assert_eq!(issued.profile_authentication(), "SHADOW");

    let at_ceiling = lane_state(MAX_ASSET_LANE_BALANCE_ROWS_V2, 5, &[]);
    let transfer = transfer_command("EUR", root(100), "holder0000", "holder0001", 1);
    let accepted = transition_asset_lane_v2(
        &transfer_context(&transfer, "holder0000", 5, &at_ceiling),
        &at_ceiling,
        &AssetLaneCommandV2::Transfer(transfer),
    )
    .expect("full-row transfer should fit");
    let AssetLaneResultV2::Accepted(accepted) = accepted else {
        panic!("full-row transfer positive control rejected")
    };
    assert_eq!(accepted.route(), AssetLaneRouteV2::TRANSFER);
    assert_eq!(
        accepted.post_state().balances.len(),
        MAX_ASSET_LANE_BALANCE_ROWS_V2
    );
    assert_eq!(
        accepted
            .post_state()
            .balance_atoms("holder0000", "EUR")
            .expect("sender balance"),
        4
    );
    assert_eq!(
        accepted
            .post_state()
            .balance_atoms("holder0001", "EUR")
            .expect("recipient balance"),
        2
    );
}

#[test]
fn final_capacity_allows_credit_before_full_sender_deletion() {
    let state = lane_state(MAX_ASSET_LANE_BALANCE_ROWS_V2, 1, &[]);
    let command = transfer_command("EUR", root(100), "holder0000", "alice", 1);
    let context = transfer_context(&command, "holder0000", 8, &state);
    let occurrence_id = context
        .occurrence
        .as_ref()
        .expect("fixture occurrence")
        .occurrence_id()
        .expect("occurrence id");
    let before = canonical_bytes_v2(&state).expect("pre-state bytes");
    assert_eq!(state.balances.len(), 4096);
    assert!(command.recipient < command.sender);
    let result = transition_asset_lane_v2(&context, &state, &AssetLaneCommandV2::Transfer(command))
        .expect("final state at capacity is valid");
    let AssetLaneResultV2::Accepted(accepted) = result else {
        panic!("temporary extra credit row must not reject a final table that fits")
    };
    let mut expected = state.balances.clone();
    assert_eq!(expected[0].owner, "holder0000");
    expected[0].owner = "alice".to_owned();
    assert_eq!(accepted.post_state().balances, expected);
    assert_eq!(accepted.post_state().supplies, state.supplies);
    assert_eq!(accepted.route(), AssetLaneRouteV2::TRANSFER);
    assert_eq!(
        accepted.effects().occurrence_consumptions,
        vec![occurrence_id]
    );
    assert_eq!(
        canonical_bytes_v2(&state).expect("unchanged pre-state bytes"),
        before
    );
}

#[test]
fn transfer_counts_both_new_recipient_and_fee_collector_rows() {
    assert_eq!(MAX_ASSET_LANE_BALANCE_ROWS_V2, 4096);
    for pre_count in [4094, 4095] {
        let mut state = lane_state(pre_count, 9, &[]);
        let policy = state
            .transfer_policies
            .iter_mut()
            .find(|policy| policy.asset == "EUR")
            .expect("EUR policy");
        policy.transfer_fee_atoms = 2;
        policy.fee_owner = "collector".to_owned();
        let policy_root = asset_transfer_policy_root_v2(policy).expect("updated fee policy root");
        state
            .origin_registry
            .assets
            .iter_mut()
            .find(|record| record.asset == "EUR")
            .expect("EUR registration")
            .transfer_policy_root = policy_root;
        state.validate().expect("two-credit PRE is admitted");
        let before = canonical_bytes_v2(&state).expect("PRE bytes");
        let mut command = transfer_command("EUR", root(100), "holder0000", "alice", 3);
        command.max_fee_atoms = 2;
        let context = transfer_context(&command, "holder0000", 30, &state);
        let occurrence_id = context
            .occurrence
            .as_ref()
            .expect("occurrence")
            .occurrence_id()
            .expect("occurrence id");
        let mut expected = state.balances.clone();
        assert_eq!(expected[0].owner, "holder0000");
        expected[0].amount_atoms = 4;
        expected.insert(
            0,
            EconomicAmountV2 {
                owner: "collector".to_owned(),
                asset: "EUR".to_owned(),
                custody_domain: "accounts".to_owned(),
                amount_atoms: 2,
            },
        );
        expected.insert(
            0,
            EconomicAmountV2 {
                owner: "alice".to_owned(),
                asset: "EUR".to_owned(),
                custody_domain: "accounts".to_owned(),
                amount_atoms: 3,
            },
        );
        assert_eq!(expected.len(), pre_count + 2);
        let result =
            transition_asset_lane_v2(&context, &state, &AssetLaneCommandV2::Transfer(command))
                .expect("capacity outcome is typed");
        if pre_count == 4094 {
            let AssetLaneResultV2::Accepted(accepted) = result else {
                panic!("two new credits fit exactly at 4096 rows")
            };
            assert_eq!(accepted.post_state().balances, expected);
            assert_eq!(accepted.post_state().supplies, state.supplies);
            assert_eq!(
                accepted.post_state().transfer_policies,
                state.transfer_policies
            );
            assert_eq!(accepted.route(), AssetLaneRouteV2::TRANSFER);
            assert_eq!(
                accepted.effects().occurrence_consumptions,
                vec![occurrence_id]
            );
        } else {
            assert_lane_noop(
                result,
                &state,
                AssetLaneRouteV2::TRANSFER,
                AssetLaneRejectCodeV2::Transfer(AssetTransferRejectCodeV2::STATE_RESOURCE_LIMIT),
            );
        }
        assert_eq!(
            canonical_bytes_v2(&state).expect("unchanged PRE bytes"),
            before
        );
    }
}

#[test]
fn rejected_issue_then_terminal_burn_frees_a_row_for_retry() {
    let state = lane_state(
        MAX_ASSET_LANE_BALANCE_ROWS_V2 - 1,
        1,
        &[(String::from("bob"), 3)],
    );
    let issue = managed_command("managed_asset_issue", "alice", 1, root(5));
    let issue_context = managed_context(&issue, "issuer", root(5), 6, &state);
    let first = transition_asset_lane_v2(
        &issue_context,
        &state,
        &AssetLaneCommandV2::ManagedLifecycle(issue.clone()),
    )
    .expect("issue overflow must be typed");
    let retry = transition_asset_lane_v2(
        &issue_context,
        &state,
        &AssetLaneCommandV2::ManagedLifecycle(issue.clone()),
    )
    .expect("issue retry must be typed");
    assert_eq!(first, retry);
    assert_lane_noop(
        first,
        &state,
        AssetLaneRouteV2::COORDINATOR,
        AssetLaneRejectCodeV2::Coordinator(AssetLaneCoordinatorRejectCodeV2::STATE_RESOURCE_LIMIT),
    );

    let burn = managed_command("managed_asset_burn", "bob", 3, root(4));
    let burn_context = managed_context(&burn, "bob", root(4), 7, &state);
    let burned = transition_asset_lane_v2(
        &burn_context,
        &state,
        &AssetLaneCommandV2::ManagedLifecycle(burn),
    )
    .expect("terminal burn must free the row");
    let AssetLaneResultV2::Accepted(burned) = burned else {
        panic!("terminal burn unexpectedly rejected")
    };
    assert_eq!(
        burned.post_state().balances.len(),
        MAX_ASSET_LANE_BALANCE_ROWS_V2 - 1
    );
    assert_eq!(
        burned.post_state().supply_atoms("USD").expect("USD supply"),
        0
    );

    let admitted_context = managed_context(&issue, "issuer", root(5), 8, burned.post_state());
    let admitted = transition_asset_lane_v2(
        &admitted_context,
        burned.post_state(),
        &AssetLaneCommandV2::ManagedLifecycle(issue),
    )
    .expect("retry after terminal burn must fit");
    let AssetLaneResultV2::Accepted(admitted) = admitted else {
        panic!("freed-row issue unexpectedly rejected")
    };
    assert_eq!(
        admitted.post_state().balances.len(),
        MAX_ASSET_LANE_BALANCE_ROWS_V2
    );
    assert_eq!(
        admitted
            .post_state()
            .balance_atoms("alice", "USD")
            .expect("alice balance"),
        1
    );
    assert_eq!(
        admitted
            .post_state()
            .supply_atoms("USD")
            .expect("USD supply"),
        1
    );
}

#[test]
fn resource_error_boundaries_are_distinct_and_pre_state_stays_an_abi_error() {
    assert_eq!(
        validate_asset_state_asset_count_v2(MAX_ASSETS_PER_ASSET_STATE_V2, "asset count"),
        Ok(())
    );
    assert_eq!(
        validate_asset_state_asset_count_v2(MAX_ASSETS_PER_ASSET_STATE_V2 + 1, "asset count"),
        Err(AbiErrorV2::StateResourceLimit("asset count"))
    );
    assert_eq!(
        validate_asset_state_balance_row_count_v2(MAX_ASSET_LANE_BALANCE_ROWS_V2 + 1, "rows"),
        Err(AbiErrorV2::StateResourceLimit("rows"))
    );
    assert_eq!(
        validate_rootable_asset_state_canonical_bytes_v2(
            MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
            "bytes",
        ),
        Ok(())
    );
    assert_eq!(
        validate_rootable_asset_state_canonical_bytes_v2(
            MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2 + 1,
            "bytes",
        ),
        Err(AbiErrorV2::StateResourceLimit("bytes"))
    );
    assert_eq!(
        validate_consumed_object_id_count_v2(65, "object ids"),
        Err(AbiErrorV2::InvalidBounds("object ids"))
    );
    assert_eq!(
        validate_consumed_occurrence_count_v2(65, "occurrences"),
        Err(AbiErrorV2::InvalidBounds("occurrences"))
    );

    let mut oversized = lane_state(MAX_ASSET_LANE_BALANCE_ROWS_V2, 1, &[]);
    let issue = managed_command("managed_asset_issue", "alice", 1, root(5));
    let admitted_context = managed_context(&issue, "issuer", root(5), 9, &oversized);
    oversized.balances.push(EconomicAmountV2 {
        owner: "zzzz".to_owned(),
        asset: "EUR".to_owned(),
        custody_domain: "accounts".to_owned(),
        amount_atoms: 1,
    });
    assert_eq!(
        oversized.validate(),
        Err(AbiErrorV2::StateResourceLimit("asset lane balances"))
    );
    assert_eq!(
        transition_asset_lane_v2(
            &admitted_context,
            &oversized,
            &AssetLaneCommandV2::ManagedLifecycle(issue),
        ),
        Err(AbiErrorV2::StateResourceLimit("asset lane balances")),
    );
    let mut unrelated = lane_state(0, 1, &[]);
    unrelated.supplies[1].amount_atoms = 1;
    assert_eq!(
        unrelated.validate(),
        Err(AbiErrorV2::Conservation(
            "asset lane owned account total differs from supply"
        ))
    );
    let canonical = canonical_bytes_v2(&unrelated).expect("malformed state still encodes");
    assert!(!canonical.is_empty());
}

#[test]
fn state_resource_limit_wire_records_preserve_route_owned_code_types() {
    let root = root(999);
    let cases = [
        (
            AssetLaneRouteV2::TRANSFER,
            AssetLaneRejectCodeV2::Transfer(AssetTransferRejectCodeV2::STATE_RESOURCE_LIMIT),
        ),
        (
            AssetLaneRouteV2::MANAGED_LIFECYCLE,
            AssetLaneRejectCodeV2::ManagedLifecycle(
                ManagedAssetLifecycleRejectCodeV2::STATE_RESOURCE_LIMIT,
            ),
        ),
        (
            AssetLaneRouteV2::COORDINATOR,
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::STATE_RESOURCE_LIMIT,
            ),
        ),
    ];

    for (route, code) in cases {
        let wire = AssetLaneRejectedWireV2 {
            route,
            code: code.as_str().to_owned(),
            pre_state_root: root.clone(),
            post_state_root: root.clone(),
            effects: GlobalEconomicEffectPlanV2::empty(),
            production_authority: "NONE".to_owned(),
            profile_authentication: "SHADOW".to_owned(),
        };
        let bytes = canonical_wire_bytes_v2(&wire).expect("route-owned rejection encodes");
        let decoded: AssetLaneRejectedWireV2 =
            decode_canonical_v2(&bytes).expect("route-owned rejection decodes");
        assert_eq!(decoded, wire);
        assert_eq!(
            canonical_wire_bytes_v2(&decoded).expect("wire re-encodes"),
            bytes
        );
    }
}

#[test]
fn authorization_and_arithmetic_rejections_precede_post_resource_checks() {
    let state = lane_state(MAX_ASSET_LANE_BALANCE_ROWS_V2, 1, &[]);
    let issue = managed_command("managed_asset_issue", "alice", 1, root(5));
    let unauthorized = transition_asset_lane_v2(
        &managed_context(&issue, "mallory", root(5), 10, &state),
        &state,
        &AssetLaneCommandV2::ManagedLifecycle(issue),
    )
    .expect("unauthorized command is a typed no-op");
    assert_lane_noop(
        unauthorized,
        &state,
        AssetLaneRouteV2::MANAGED_LIFECYCLE,
        AssetLaneRejectCodeV2::ManagedLifecycle(
            ManagedAssetLifecycleRejectCodeV2::UNAUTHORIZED_SUBJECT,
        ),
    );
    let transfer = transfer_command("EUR", root(100), "holder0000", "alice", 2);
    let insufficient = transition_asset_lane_v2(
        &transfer_context(&transfer, "holder0000", 11, &state),
        &state,
        &AssetLaneCommandV2::Transfer(transfer),
    )
    .expect("insufficient balance is a typed no-op");
    assert_lane_noop(
        insufficient,
        &state,
        AssetLaneRouteV2::TRANSFER,
        AssetLaneRejectCodeV2::Transfer(AssetTransferRejectCodeV2::INSUFFICIENT_BALANCE),
    );
}
