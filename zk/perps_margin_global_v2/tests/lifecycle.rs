use serde::Serialize;
use zenodex_global_settlement_abi_v1::{
    PerpsMarginAccountStatusV1, PerpsMarginCommandV1, PerpsMarginMarketStatusV1,
    PerpsMarginRejectCodeV1, PerpsMarginStateV1, RootV1, PERPS_MARGIN_MODULE_SCHEMA_V1,
};
use zenodex_global_settlement_abi_v2::{
    asset_transfer_policy_root_v2, AssetClassV2, AssetLaneCustodyStateV2, AssetOriginKindV2,
    AssetOriginRecordV2, AssetOriginRegistrationPolicyV2, AssetOriginRegistryStateV2,
    AssetSupplyV2, AssetTransferPolicyV2, AssetTransferStateV2, EconomicAmountV2,
    EconomicCommandOccurrenceV2, GlobalEconomicStateV2, LaneIdV2, LaneStateRootV2, RootV2,
    TerminalObligationStatusV2, ACCOUNT_CUSTODY_DOMAIN_V2, ALL_LANE_IDS_V2, ASSET_ATOM_DECIMALS_V2,
    ASSET_LANE_CUSTODY_STATE_SCHEMA_V2, ASSET_ORIGIN_REGISTRY_SCHEMA_V2,
    ASSET_TRANSFER_MODULE_SCHEMA_V2, GLOBAL_SETTLEMENT_ABI_V2,
};
use zenodex_perps_margin_global_v2::{
    margin_claim_id_v2, prepare_perps_margin_global_from_frame_v2,
    transition_perps_margin_global_v2, PerpsMarginClaimBindingV2, PerpsMarginGlobalFrameErrorV2,
    PerpsMarginGlobalRejectCodeV2, PerpsMarginGlobalRejectKindV2, PerpsMarginGlobalResultV2,
    PerpsMarginStateV2, PERPS_MARGIN_FRAME_MAGIC_V2, PERPS_MARGIN_GLOBAL_STATEMENT_SCHEMA_V2,
    PERPS_MARGIN_REQUEST_SCHEMA_V2,
};

const MARKET: &str = "perp-btc-usd";
const ASSET: &str = "USD";
const OWNER: &str = "alice";
const DOMAIN: &str = "perps_margin";

fn root(value: u64) -> RootV2 {
    RootV2::parse(format!("0x{value:064x}"), "test root", false).expect("canonical root")
}

fn root_v1(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test V1 root", false).expect("V1 root")
}

fn account(
    owner: &str,
    account_id: &str,
    collateral: u128,
    nonce: u64,
) -> zenodex_global_settlement_abi_v1::PerpsMarginAccountV1 {
    zenodex_global_settlement_abi_v1::PerpsMarginAccountV1 {
        account_id: account_id.to_owned(),
        owner: owner.to_owned(),
        position_base: 0,
        entry_price_e8: 0,
        collateral_atoms: collateral,
        nonce,
        status: PerpsMarginAccountStatusV1::OPEN,
    }
}

fn margin_state(
    accounts: Vec<zenodex_global_settlement_abi_v1::PerpsMarginAccountV1>,
) -> PerpsMarginStateV2 {
    PerpsMarginStateV2::new(
        PerpsMarginStateV1 {
            schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: root_v1(20),
            market_id: MARKET.to_owned(),
            collateral_asset: ASSET.to_owned(),
            index_price_e8: 100_000_000,
            maintenance_margin_bps: 1_000,
            depeg_buffer_bps: 0,
            max_position_abs: 100,
            market_status: PerpsMarginMarketStatusV1::ACTIVE,
            accounts,
        },
        Vec::new(),
    )
    .expect("valid V2 margin state")
}

fn asset_frame(account_atoms: u128, custody_atoms: u128) -> AssetLaneCustodyStateV2 {
    let origin = root(30);
    let policy = AssetTransferPolicyV2 {
        asset: ASSET.to_owned(),
        fee_owner: "fees".to_owned(),
        transfer_fee_atoms: 0,
        enabled: true,
        asset_class: AssetClassV2::RegisteredOrdinaryToken,
        asset_origin_root: Some(origin.clone()),
        atom_decimals: ASSET_ATOM_DECIMALS_V2,
    };
    let registry = AssetOriginRegistryStateV2 {
        schema: ASSET_ORIGIN_REGISTRY_SCHEMA_V2.to_owned(),
        module_release_id: root(20),
        policy: AssetOriginRegistrationPolicyV2 {
            authority_subject: "governance".to_owned(),
            authority_grant_root: root(31),
            allow_native: false,
            allow_tau_originated: true,
        },
        assets: vec![AssetOriginRecordV2 {
            asset: ASSET.to_owned(),
            origin_kind: AssetOriginKindV2::TAU_ORIGINATED,
            origin_root: origin,
            transfer_policy_root: asset_transfer_policy_root_v2(&policy).expect("policy root"),
            issue_policy_root: RootV2::zero(),
            decimals: 8,
            asset_class: AssetClassV2::RegisteredOrdinaryToken,
        }],
    };
    AssetLaneCustodyStateV2 {
        schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
        transfer_state: AssetTransferStateV2 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V2.to_owned(),
            module_release_id: root(20),
            policies: vec![policy],
            balances: (account_atoms > 0)
                .then(|| EconomicAmountV2 {
                    owner: OWNER.to_owned(),
                    asset: ASSET.to_owned(),
                    custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
                    amount_atoms: account_atoms,
                })
                .into_iter()
                .collect(),
            supplies: vec![AssetSupplyV2 {
                asset: ASSET.to_owned(),
                amount_atoms: account_atoms + custody_atoms,
            }],
        },
        origin_registry: registry,
        managed_policies: Vec::new(),
        custody: (custody_atoms > 0)
            .then(|| EconomicAmountV2 {
                owner: "margin-a".to_owned(),
                asset: ASSET.to_owned(),
                custody_domain: DOMAIN.to_owned(),
                amount_atoms: custody_atoms,
            })
            .into_iter()
            .collect(),
    }
}

fn global_state(
    assets: &AssetLaneCustodyStateV2,
    margin: &PerpsMarginStateV2,
) -> GlobalEconomicStateV2 {
    let asset_root = assets.state_root().expect("asset root");
    let margin_root = margin.state_root().expect("margin root");
    let lanes = ALL_LANE_IDS_V2
        .iter()
        .copied()
        .enumerate()
        .map(|(index, lane_id)| match lane_id {
            LaneIdV2::ASSET_TRANSFER => LaneStateRootV2 {
                lane_id,
                module_release_id: root(20),
                enabled: true,
                state_root: asset_root.clone(),
            },
            LaneIdV2::PERPS_MARKET => LaneStateRootV2 {
                lane_id,
                module_release_id: root(20),
                enabled: true,
                state_root: margin_root.clone(),
            },
            _ => LaneStateRootV2 {
                lane_id,
                module_release_id: root(100 + index as u64),
                enabled: false,
                state_root: RootV2::zero(),
            },
        })
        .collect();
    GlobalEconomicStateV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: "test-chain".to_owned(),
        deployment_root: root(40),
        writer_epoch: 7,
        height: 0,
        profile_root: root(41),
        lane_roots: lanes,
        balances: assets.balances().to_vec(),
        supplies: assets
            .supplies()
            .iter()
            .filter(|row| row.amount_atoms > 0)
            .cloned()
            .collect(),
        custody: assets.custody.clone(),
        liabilities: Vec::new(),
        reserves: Vec::new(),
        oracle_occurrences: Vec::new(),
        replay_state: Vec::new(),
        terminal_obligations: Vec::new(),
        history_root: RootV2::zero(),
        outbox: Vec::new(),
    }
}

fn command(kind: &str, account_id: &str, amount: u128, nonce: u64) -> PerpsMarginCommandV1 {
    PerpsMarginCommandV1 {
        command_kind: kind.to_owned(),
        account_id: account_id.to_owned(),
        market_id: MARKET.to_owned(),
        owner: OWNER.to_owned(),
        asset: ASSET.to_owned(),
        amount_atoms: amount,
        nonce,
    }
}

fn make_occurrence(
    state: &GlobalEconomicStateV2,
    command: &PerpsMarginCommandV1,
    nonce: u64,
) -> EconomicCommandOccurrenceV2 {
    EconomicCommandOccurrenceV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: state.chain_id.clone(),
        deployment_root: state.deployment_root.clone(),
        height: state.height + 1,
        tx_index: 0,
        op_index: 0,
        command_kind: command.command_kind.clone(),
        command_body_hash: zenodex_global_settlement_abi_v2::hash_economic_command_body_v2(
            &command.command_kind,
            command,
        )
        .expect("body hash"),
        route_release_id: root(50),
        subject_id: OWNER.to_owned(),
        grant_root: root(51),
        nonce,
        profile_root: state.profile_root.clone(),
        pre_state_root: state.state_root().expect("state root"),
        consumed_object_ids: Vec::new(),
    }
}

#[derive(Serialize)]
struct ExactPerpsMarginRequestV2<'a> {
    schema: &'static str,
    command: &'a PerpsMarginCommandV1,
    occurrence: &'a EconomicCommandOccurrenceV2,
    oracle: Option<()>,
}

fn exact_zdpm2_frame(
    assets: &AssetLaneCustodyStateV2,
    margin: &PerpsMarginStateV2,
    state: &GlobalEconomicStateV2,
    command: &PerpsMarginCommandV1,
    occurrence: &EconomicCommandOccurrenceV2,
) -> Vec<u8> {
    let components = [
        zenodex_global_settlement_abi_v2::canonical_bytes_v2(assets).expect("asset bytes"),
        margin.canonical_bytes().expect("margin bytes"),
        zenodex_global_settlement_abi_v2::canonical_bytes_v2(state).expect("state bytes"),
        zenodex_global_settlement_abi_v2::canonical_bytes_v2(&ExactPerpsMarginRequestV2 {
            schema: PERPS_MARGIN_REQUEST_SCHEMA_V2,
            command,
            occurrence,
            oracle: None,
        })
        .expect("request bytes"),
    ];
    let mut frame = PERPS_MARGIN_FRAME_MAGIC_V2.to_vec();
    for component in components {
        let length = u32::try_from(component.len()).expect("bounded test component");
        frame.extend_from_slice(&length.to_le_bytes());
        frame.extend_from_slice(&component);
    }
    frame
}

fn step(
    assets: &AssetLaneCustodyStateV2,
    margin: &PerpsMarginStateV2,
    state: &GlobalEconomicStateV2,
    command: &PerpsMarginCommandV1,
    outer_nonce: u64,
) -> (
    AssetLaneCustodyStateV2,
    PerpsMarginStateV2,
    GlobalEconomicStateV2,
) {
    let occurrence = make_occurrence(state, command, outer_nonce);
    let result =
        transition_perps_margin_global_v2(assets, margin, state, command, &occurrence, None)
            .expect("typed transition");
    let PerpsMarginGlobalResultV2::Accepted(accepted) = result else {
        panic!("expected accepted transition")
    };
    (
        accepted.post_assets().clone(),
        accepted.post_margin().clone(),
        accepted.post_state().clone(),
    )
}

#[test]
fn connected_deposit_drain_refill_close_preserves_terminal_history() {
    let mut assets = asset_frame(100, 0);
    let mut margin = margin_state(Vec::new());
    let mut state = global_state(&assets, &margin);

    (assets, margin, state) = step(
        &assets,
        &margin,
        &state,
        &command("perps_margin_deposit", "margin-a", 40, 1),
        1,
    );
    let first_claim = margin.claim_id("margin-a").expect("lookup").expect("claim");
    assert_eq!(state.terminal_obligations.len(), 1);
    assert_eq!(
        state.terminal_obligations[0].status,
        TerminalObligationStatusV2::OPEN
    );

    (assets, margin, state) = step(
        &assets,
        &margin,
        &state,
        &command("perps_margin_withdraw", "margin-a", 10, 2),
        2,
    );
    assert_eq!(state.terminal_obligations[0].amount_atoms, 30);
    assert_eq!(
        margin.claim_id("margin-a").expect("lookup"),
        Some(first_claim.clone())
    );

    (assets, margin, state) = step(
        &assets,
        &margin,
        &state,
        &command("perps_margin_withdraw", "margin-a", 30, 3),
        3,
    );
    assert_eq!(
        state.terminal_obligations[0].status,
        TerminalObligationStatusV2::DRAINED
    );
    assert_eq!(state.terminal_obligations[0].amount_atoms, 30);
    assert_eq!(margin.claim_id("margin-a").expect("lookup"), None);

    (assets, margin, state) = step(
        &assets,
        &margin,
        &state,
        &command("perps_margin_deposit", "margin-a", 20, 4),
        4,
    );
    let refill_claim = margin
        .claim_id("margin-a")
        .expect("lookup")
        .expect("refill claim");
    assert_ne!(refill_claim, first_claim);
    assert_eq!(state.terminal_obligations.len(), 2);
    assert!(state
        .terminal_obligations
        .iter()
        .any(|row| row.obligation_id == first_claim
            && row.status == TerminalObligationStatusV2::DRAINED));

    (assets, margin, state) = step(
        &assets,
        &margin,
        &state,
        &command("perps_margin_withdraw", "margin-a", 20, 5),
        5,
    );
    assert_eq!(margin.claim_id("margin-a").expect("lookup"), None);
    (assets, margin, state) = step(
        &assets,
        &margin,
        &state,
        &command("perps_margin_close", "margin-a", 0, 6),
        6,
    );
    assert_eq!(
        margin.economic_state.accounts[0].status,
        PerpsMarginAccountStatusV1::CLOSED
    );
    assert_eq!(state.terminal_obligations.len(), 2);
    assert!(state
        .terminal_obligations
        .iter()
        .all(|row| row.status == TerminalObligationStatusV2::DRAINED));
    assert!(assets.validate().is_ok());
}

#[test]
fn same_owner_accounts_have_independent_occurrence_claims() {
    let assets = asset_frame(100, 0);
    let margin = margin_state(Vec::new());
    let state = global_state(&assets, &margin);
    let (assets, margin, state) = step(
        &assets,
        &margin,
        &state,
        &command("perps_margin_deposit", "margin-a", 20, 1),
        1,
    );
    let command_b = command("perps_margin_deposit", "margin-b", 20, 1);
    let occurrence = make_occurrence(&state, &command_b, 2);
    let result =
        transition_perps_margin_global_v2(&assets, &margin, &state, &command_b, &occurrence, None)
            .expect("typed transition");
    let PerpsMarginGlobalResultV2::Accepted(accepted) = result else {
        panic!("second account deposit must accept")
    };
    let ids = accepted
        .post_margin()
        .active_claims
        .iter()
        .map(|binding| binding.obligation_id.clone())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(ids.len(), 2);
    assert_eq!(accepted.post_margin().economic_state.accounts[1].nonce, 1);
}

#[test]
fn malformed_command_binding_and_unowned_consumption_are_exact_no_ops() {
    let assets = asset_frame(100, 0);
    let margin = margin_state(Vec::new());
    let state = global_state(&assets, &margin);
    let command = command("perps_margin_deposit", "margin-a", 40, 1);
    let mut occurrence = make_occurrence(&state, &command, 1);
    occurrence.command_kind = "wrong-kind".to_owned();
    let result =
        transition_perps_margin_global_v2(&assets, &margin, &state, &command, &occurrence, None)
            .expect("typed rejection");
    let PerpsMarginGlobalResultV2::Rejected(rejected) = result else {
        panic!("wrong body must reject")
    };
    assert_eq!(
        rejected.code,
        PerpsMarginGlobalRejectCodeV2::Global(
            PerpsMarginGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH
        )
    );
    assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    assert!(rejected.effects().is_empty());

    let mut replayed = make_occurrence(&state, &command, 1);
    replayed.consumed_object_ids.push("object".to_owned());
    let result =
        transition_perps_margin_global_v2(&assets, &margin, &state, &command, &replayed, None)
            .expect("typed rejection");
    let PerpsMarginGlobalResultV2::Rejected(rejected) = result else {
        panic!("consumed object must reject")
    };
    assert_eq!(
        rejected.code,
        PerpsMarginGlobalRejectCodeV2::Global(
            PerpsMarginGlobalRejectKindV2::OCCURRENCE_COMMAND_MISMATCH
        )
    );
}

#[test]
fn v2_state_root_and_claim_id_are_distinct_from_v1_bytes() {
    let economic = PerpsMarginStateV1 {
        schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root_v1(20),
        market_id: MARKET.to_owned(),
        collateral_asset: ASSET.to_owned(),
        index_price_e8: 100_000_000,
        maintenance_margin_bps: 1_000,
        depeg_buffer_bps: 0,
        max_position_abs: 100,
        market_status: PerpsMarginMarketStatusV1::ACTIVE,
        accounts: vec![account(OWNER, "margin-a", 7, 1)],
    };
    let opening = root(60);
    let claim = margin_claim_id_v2(&economic, "margin-a", &opening).expect("claim id");
    let state = PerpsMarginStateV2::new(
        economic,
        vec![PerpsMarginClaimBindingV2::new("margin-a", claim.to_string()).expect("binding")],
    )
    .expect("state");
    let canonical = String::from_utf8(state.canonical_bytes().expect("canonical")).expect("utf8");
    assert!(canonical.contains("zenodex/perps-margin-module/v2"));
    assert!(!canonical.contains("zenodex/perps-margin-module/v1"));
    assert_ne!(
        state.state_root().expect("V2 root").as_str(),
        state.economic_state.state_root().expect("V1 root").as_str()
    );
}

#[test]
fn v1_margin_rejection_is_preserved_as_a_typed_global_rejection() {
    let assets = asset_frame(100, 0);
    let margin = margin_state(vec![account(OWNER, "margin-a", 0, 1)]);
    let state = global_state(&assets, &margin);
    let command = command("perps_margin_withdraw", "margin-a", 1, 2);
    let occurrence = make_occurrence(&state, &command, 1);
    let result =
        transition_perps_margin_global_v2(&assets, &margin, &state, &command, &occurrence, None)
            .expect("typed rejection");
    let PerpsMarginGlobalResultV2::Rejected(rejected) = result else {
        panic!("withdraw on empty account must reject")
    };
    assert_eq!(
        rejected.code,
        PerpsMarginGlobalRejectCodeV2::Margin(PerpsMarginRejectCodeV1::INSUFFICIENT_COLLATERAL)
    );
}

#[test]
fn maximum_height_rejects_without_effects_before_replay_or_body_checks() {
    let assets = asset_frame(100, 0);
    let margin = margin_state(Vec::new());
    let mut state = global_state(&assets, &margin);
    let command = command("perps_margin_deposit", "margin-a", 1, 1);
    let original = make_occurrence(&state, &command, 1);
    state.height = u64::MAX;
    let pre_root = state
        .state_root()
        .expect("maximum height remains representable");
    for height in [0, u64::MAX - 1, u64::MAX] {
        let mut occurrence = original.clone();
        occurrence.height = height;
        occurrence.pre_state_root = pre_root.clone();
        // Context failure must retain precedence even with a mismatched body.
        occurrence.command_body_hash = root(999);
        let result = transition_perps_margin_global_v2(
            &assets,
            &margin,
            &state,
            &command,
            &occurrence,
            None,
        )
        .expect("maximum-height input must return a typed economic rejection");
        let PerpsMarginGlobalResultV2::Rejected(rejected) = result else {
            panic!("unrepresentable successor height must reject")
        };
        assert_eq!(rejected.code.as_str(), "OCCURRENCE_CONTEXT_MISMATCH");
        assert_eq!(rejected.pre_state_root, pre_root);
        assert_eq!(rejected.post_state_root, pre_root);
        assert!(rejected.effects().is_empty());
        assert!(rejected.terminal_plan().deltas.is_empty());
        assert!(rejected.oracle_plan().deltas.is_empty());
    }
}

#[test]
fn exact_zdpm2_bridge_commits_only_the_existing_two_root_statement() {
    let assets = asset_frame(100, 0);
    let margin = margin_state(Vec::new());
    let state = global_state(&assets, &margin);
    let deposit = command("perps_margin_deposit", "margin-a", 40, 1);
    let occurrence = make_occurrence(&state, &deposit, 1);
    let frame = exact_zdpm2_frame(&assets, &margin, &state, &deposit, &occurrence);

    let prepared = prepare_perps_margin_global_from_frame_v2(&frame).expect("accepted frame");
    let result =
        transition_perps_margin_global_v2(&assets, &margin, &state, &deposit, &occurrence, None)
            .expect("typed transition");
    let PerpsMarginGlobalResultV2::Accepted(accepted) = result else {
        panic!("expected accepted deposit");
    };
    let expected_journal = format!(
        "{{\"input_root\":\"{}\",\"refinement_root\":\"{}\",\"schema\":\"{PERPS_MARGIN_GLOBAL_STATEMENT_SCHEMA_V2}\"}}",
        accepted.statement_root().as_str(),
        accepted.refinement().refinement_root().expect("refinement root").as_str(),
    )
    .into_bytes();
    assert_eq!(prepared, expected_journal);

    let mut noncanonical_assets = frame.clone();
    let length_offset = PERPS_MARGIN_FRAME_MAGIC_V2.len();
    let asset_start = length_offset + 4;
    noncanonical_assets.insert(asset_start, b' ');
    let original_length = u32::from_le_bytes(
        noncanonical_assets[length_offset..asset_start]
            .try_into()
            .expect("asset length"),
    );
    noncanonical_assets[length_offset..asset_start]
        .copy_from_slice(&(original_length + 1).to_le_bytes());
    assert_eq!(
        prepare_perps_margin_global_from_frame_v2(&noncanonical_assets),
        Err(PerpsMarginGlobalFrameErrorV2::Assets)
    );

    let mut trailing = frame.clone();
    trailing.push(0);
    assert_eq!(
        prepare_perps_margin_global_from_frame_v2(&trailing),
        Err(PerpsMarginGlobalFrameErrorV2::FrameTrailingBytes)
    );

    let zero_command = command("perps_margin_deposit", "margin-a", 0, 1);
    let zero_occurrence = make_occurrence(&state, &zero_command, 1);
    let zero_frame = exact_zdpm2_frame(&assets, &margin, &state, &zero_command, &zero_occurrence);
    assert_eq!(
        prepare_perps_margin_global_from_frame_v2(&zero_frame),
        Err(PerpsMarginGlobalFrameErrorV2::Rejected(
            PerpsMarginGlobalRejectCodeV2::Margin(PerpsMarginRejectCodeV1::ZERO_AMOUNT)
        ))
    );
}
