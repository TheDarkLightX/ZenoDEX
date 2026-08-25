use zenodex_global_settlement_abi_v1::{
    transition_perps_margin_v1, EconomicEffectKindV1, LaneIdV1, PerpsMarginAccountStatusV1,
    PerpsMarginAccountV1, PerpsMarginCommandV1, PerpsMarginContextV1, PerpsMarginMarketStatusV1,
    PerpsMarginRejectCodeV1, PerpsMarginRejectedV1, PerpsMarginResultV1, PerpsMarginStateV1,
    RootV1, TerminalObligationStatusV1, ACCOUNT_CUSTODY_DOMAIN_V1, GLOBAL_SETTLEMENT_ABI_V1,
    MAX_PERPS_MARGIN_ACCOUNTS_V1, PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
    PERPS_MARGIN_CUSTODY_DOMAIN_V1, PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1, PERPS_MARGIN_MODULE_SCHEMA_V1,
    PERPS_MARGIN_PRIVATE_PORT_SCHEMA_V1, PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, ZERO_ROOT_V1,
};

fn root(value: u8) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "perps margin test root", false).unwrap()
}

fn context(subject: &str) -> PerpsMarginContextV1 {
    PerpsMarginContextV1 {
        chain_id: "zeno-test-chain".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        module_release_id: root(3),
        command_occurrence_id: root(4),
        subject_id: subject.to_owned(),
        grant_root: root(5),
        oracle_authority_root: RootV1::parse(
            ZERO_ROOT_V1,
            "perps margin test absent Oracle authority",
            true,
        )
        .unwrap(),
        oracle_occurrence_root: RootV1::parse(
            ZERO_ROOT_V1,
            "perps margin test absent Oracle occurrence",
            true,
        )
        .unwrap(),
        oracle_price_e8: 0,
    }
}

fn withdraw_context(subject: &str) -> PerpsMarginContextV1 {
    PerpsMarginContextV1 {
        oracle_authority_root: root(9),
        oracle_occurrence_root: root(10),
        oracle_price_e8: 100_000_000,
        ..context(subject)
    }
}

fn account(collateral_atoms: u128, position_base: i128) -> PerpsMarginAccountV1 {
    PerpsMarginAccountV1 {
        account_id: "perps-account-1".to_owned(),
        owner: "alice".to_owned(),
        position_base,
        entry_price_e8: if position_base == 0 { 0 } else { 100_000_000 },
        collateral_atoms,
        nonce: 1,
        status: PerpsMarginAccountStatusV1::OPEN,
    }
}

fn counterparty(collateral_atoms: u128, position_base: i128) -> PerpsMarginAccountV1 {
    PerpsMarginAccountV1 {
        account_id: "perps-account-2".to_owned(),
        owner: "bob".to_owned(),
        position_base,
        entry_price_e8: if position_base == 0 { 0 } else { 100_000_000 },
        collateral_atoms,
        nonce: 1,
        status: PerpsMarginAccountStatusV1::OPEN,
    }
}

fn state(accounts: Vec<PerpsMarginAccountV1>) -> PerpsMarginStateV1 {
    PerpsMarginStateV1 {
        schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: root(3),
        market_id: "perp-btc-usd".to_owned(),
        collateral_asset: "zUSD".to_owned(),
        index_price_e8: 100_000_000,
        maintenance_margin_bps: 500,
        depeg_buffer_bps: 100,
        max_position_abs: 1_000_000,
        market_status: PerpsMarginMarketStatusV1::ACTIVE,
        accounts,
    }
}

fn command(kind: &str, amount_atoms: u128, nonce: u64) -> PerpsMarginCommandV1 {
    PerpsMarginCommandV1 {
        command_kind: kind.to_owned(),
        account_id: "perps-account-1".to_owned(),
        market_id: "perp-btc-usd".to_owned(),
        owner: "alice".to_owned(),
        asset: "zUSD".to_owned(),
        amount_atoms,
        nonce,
    }
}

#[test]
fn deposit_creates_open_claim_and_exact_candidate_effects() {
    let pre = state(Vec::new());
    let result = transition_perps_margin_v1(
        &context("alice"),
        &pre,
        &command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 25, 1),
    )
    .unwrap();
    let PerpsMarginResultV1::Accepted(accepted) = result else {
        panic!("deposit rejected")
    };
    assert_eq!(accepted.post_state.accounts, vec![account(25, 0)]);
    assert_eq!(accepted.module_journal.lane_id, LaneIdV1::PERPS_MARKET);
    assert_eq!(
        accepted.module_journal.private_port_root,
        accepted.private_port.port_root().unwrap()
    );
    assert!(accepted.private_port.oracle_authority_root.is_zero());
    assert!(accepted.private_port.oracle_occurrence_root.is_zero());
    assert_eq!(accepted.private_port.oracle_price_e8, 0);
    assert_eq!(
        accepted.statement_root.as_str(),
        "0x49a6c59cb5503baddd9c02d8a9c90aa2fce93f678fbaaad2ca85598dda6b39ac"
    );
    assert_eq!(
        accepted.private_port.port_root().unwrap().as_str(),
        "0x83654360225cd66ce3791aac313d0fd38beb629e93138bbae1d27df99dbdee38"
    );
    assert_eq!(
        accepted.module_journal.terminal_obligations_root,
        accepted.terminal_obligations_root().unwrap()
    );
    assert_eq!(accepted.terminal_obligations.len(), 1);
    assert_eq!(
        accepted.terminal_obligations[0].status,
        TerminalObligationStatusV1::OPEN
    );
    assert!(accepted.effects.asset_conservation.is_empty());
    assert_eq!(accepted.effects.rows.len(), 3);
    assert_eq!(
        accepted.effects.rows[0].kind,
        EconomicEffectKindV1::ACCOUNT_MOVEMENT
    );
    assert_eq!(
        accepted.effects.rows[0].custody_domain,
        ACCOUNT_CUSTODY_DOMAIN_V1
    );
    assert_eq!(accepted.effects.rows[0].delta_atoms, -25);
    assert_eq!(accepted.effects.rows[1].kind, EconomicEffectKindV1::CUSTODY);
    assert_eq!(
        accepted.effects.rows[1].custody_domain,
        PERPS_MARGIN_CUSTODY_DOMAIN_V1
    );
    assert_eq!(accepted.effects.rows[1].delta_atoms, 25);
    assert_eq!(
        accepted.effects.rows[2].kind,
        EconomicEffectKindV1::LIABILITY
    );
}

#[test]
fn deposit_golden_roots_match_python_projection() {
    let pre = state(Vec::new());
    let command = command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 25, 1);
    let result = transition_perps_margin_v1(&context("alice"), &pre, &command).unwrap();
    let PerpsMarginResultV1::Accepted(accepted) = result else {
        panic!("deposit rejected")
    };
    assert_eq!(
        pre.state_root().unwrap().as_str(),
        "0xf09237a0cbec631b97db5686b7760be2f1bab3a90cfcdd17625ab6f2f3738721"
    );
    assert_eq!(
        command.command_body_hash().unwrap().as_str(),
        "0x83b30c591ab4f1f08ca3174fcc00aeac67a51d65e9117b50874144ba3f8da93c"
    );
    assert_eq!(
        accepted.post_state.state_root().unwrap().as_str(),
        "0x14563fa71c63897bf9f52e284f6c8c9d3fb8108809e9fa9e9b0ffa7c3fad669d"
    );
    assert_eq!(
        accepted.effects.effect_plan_root().unwrap().as_str(),
        "0xd47cdd1920427234a76e5f9ab1b20e03b671b4e812a2ad6a968da1cad775760c"
    );
    assert_eq!(
        accepted.terminal_obligations_root().unwrap().as_str(),
        "0x1c5f7c894f22685e12e58aed34d1b8c37483aba3eadcb3f5680aca1d3bd2c2ca"
    );
    assert_eq!(
        accepted.receipt_root().as_str(),
        "0xb28cd992a77c6c4eba7ae55f22b3df7f7933f3de3502f4074489faae059340d1"
    );
}

#[test]
fn withdrawal_boundary_accepts_exact_requirement_and_rejects_one_atom_below() {
    let pre = state(vec![
        account(100_000_000, 10),
        counterparty(100_000_000, -10),
    ]);
    let accepted = transition_perps_margin_v1(
        &withdraw_context("alice"),
        &pre,
        &command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 40_000_000, 2),
    )
    .unwrap();
    let PerpsMarginResultV1::Accepted(accepted) = accepted else {
        panic!("boundary withdrawal rejected")
    };
    assert_eq!(accepted.post_state.accounts[0].collateral_atoms, 60_000_000);

    let rejected = transition_perps_margin_v1(
        &withdraw_context("alice"),
        &pre,
        &command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 40_000_001, 2),
    )
    .unwrap();
    let PerpsMarginResultV1::Rejected(rejected) = rejected else {
        panic!("unsafe withdrawal accepted")
    };
    assert_eq!(rejected.code, PerpsMarginRejectCodeV1::MAINTENANCE_BREACH);
    assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    assert!(rejected.effects.is_empty());
}

#[test]
fn oracle_bound_withdrawal_golden_roots_match_python_projection() {
    let pre = state(vec![
        account(100_000_000, 10),
        counterparty(100_000_000, -10),
    ]);
    let command = command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 40_000_000, 2);
    let result = transition_perps_margin_v1(&withdraw_context("alice"), &pre, &command).unwrap();
    let PerpsMarginResultV1::Accepted(accepted) = result else {
        panic!("Oracle-bound withdrawal rejected")
    };
    assert_eq!(
        accepted.module_journal.private_port_root,
        accepted.private_port.port_root().unwrap()
    );
    assert_eq!(
        accepted.private_port.command_body_hash,
        command.command_body_hash().unwrap()
    );
    assert_eq!(accepted.private_port.oracle_authority_root, root(9));
    assert_eq!(accepted.private_port.oracle_occurrence_root, root(10));
    assert_eq!(accepted.private_port.oracle_price_e8, 100_000_000);
    assert_eq!(
        accepted.statement_root.as_str(),
        "0xd9a591464d06a0c06f3a7f8f8fd2a80a2707f15970a3c1bb55a52cb30c7d0620"
    );
    assert_eq!(
        accepted.private_port.port_root().unwrap().as_str(),
        "0xfaf98464d17415fdc1661f7465acd81d25d542d95605e5e9b0b17aea0a45cf08"
    );
    assert_eq!(
        pre.state_root().unwrap().as_str(),
        "0xb3cfde94ceefa7082e1a8916ff0a284e66bebf96419f7a73da5b206565163da6"
    );
    assert_eq!(
        command.command_body_hash().unwrap().as_str(),
        "0x2e34c888f447e69e9e59c382532498ee2ec9200a28c971e821989b707d729aed"
    );
    assert_eq!(
        accepted.post_state.state_root().unwrap().as_str(),
        "0x46266091abad6ffaca603ddc821bae5241af4a46a55ac16b22afda6314604780"
    );
    assert_eq!(
        accepted.effects.effect_plan_root().unwrap().as_str(),
        "0xf304ad8551b029c9f012dffa1e36069c4f792980880b60c147f0ec41db2338dc"
    );
    assert_eq!(
        accepted.terminal_obligations_root().unwrap().as_str(),
        "0xc3779fc3bfa32a1b1dd273e8fcf85ac4a9647e38805f2c21d1e216d01fd3d22d"
    );
    assert_eq!(
        accepted.receipt_root().as_str(),
        "0xa4d4f717f661f87c84baed43d545eed9a4865e3ab6f6429e38b39fd933e150b6"
    );
}

#[test]
fn withdrawal_requires_exact_nonzero_oracle_authority_binding() {
    let pre = state(vec![account(25_000_000, 1), counterparty(100_000_000, -1)]);
    let command = command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 1, 2);

    let missing = transition_perps_margin_v1(&context("alice"), &pre, &command).unwrap();
    let PerpsMarginResultV1::Rejected(missing) = missing else {
        panic!("withdrawal without Oracle authority accepted")
    };
    assert_eq!(
        missing.code,
        PerpsMarginRejectCodeV1::ORACLE_AUTHORITY_MISSING
    );
    assert_eq!(missing.pre_state_root, missing.post_state_root);
    assert!(missing.effects.is_empty());

    let wrong_price = PerpsMarginContextV1 {
        oracle_price_e8: 99_999_999,
        ..withdraw_context("alice")
    };
    let mismatched = transition_perps_margin_v1(&wrong_price, &pre, &command).unwrap();
    let PerpsMarginResultV1::Rejected(mismatched) = mismatched else {
        panic!("withdrawal with mismatched Oracle price accepted")
    };
    assert_eq!(
        mismatched.code,
        PerpsMarginRejectCodeV1::ORACLE_PRICE_MISMATCH
    );
    assert_eq!(mismatched.pre_state_root, mismatched.post_state_root);
    assert!(mismatched.effects.is_empty());
}

#[test]
fn price_independent_command_rejects_unexpected_oracle_binding() {
    let pre = state(Vec::new());
    let result = transition_perps_margin_v1(
        &withdraw_context("alice"),
        &pre,
        &command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 1, 1),
    )
    .unwrap();
    let PerpsMarginResultV1::Rejected(rejected) = result else {
        panic!("deposit accepted surplus Oracle authority")
    };
    assert_eq!(
        rejected.code,
        PerpsMarginRejectCodeV1::UNEXPECTED_ORACLE_AUTHORITY
    );
    assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    assert!(rejected.effects.is_empty());

    let flat = state(vec![account(1, 0)]);
    let result = transition_perps_margin_v1(
        &withdraw_context("alice"),
        &flat,
        &command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 1, 2),
    )
    .unwrap();
    let PerpsMarginResultV1::Rejected(rejected) = result else {
        panic!("flat withdrawal accepted surplus Oracle authority")
    };
    assert_eq!(
        rejected.code,
        PerpsMarginRejectCodeV1::UNEXPECTED_ORACLE_AUTHORITY
    );
    assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    assert!(rejected.effects.is_empty());
}

#[test]
fn partial_oracle_binding_is_invalid_input() {
    let malformed = PerpsMarginContextV1 {
        oracle_authority_root: root(9),
        ..context("alice")
    };
    let result = transition_perps_margin_v1(
        &malformed,
        &state(vec![account(25, 0)]),
        &command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 1, 2),
    );
    assert!(result.is_err());
}

#[test]
fn accepted_output_rejects_private_port_and_statement_substitution() {
    let result = transition_perps_margin_v1(
        &withdraw_context("alice"),
        &state(vec![account(25_000_000, 1), counterparty(100_000_000, -1)]),
        &command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 1, 2),
    )
    .unwrap();
    let PerpsMarginResultV1::Accepted(accepted) = result else {
        panic!("withdrawal rejected")
    };

    let mut port_substitution = (*accepted).clone();
    port_substitution.private_port.oracle_price_e8 = 99_999_999;
    assert!(port_substitution.validate().is_err());

    let mut statement_substitution = (*accepted).clone();
    statement_substitution.statement_root = root(99);
    assert!(statement_substitution.validate().is_err());
}

#[test]
fn closed_tombstone_cannot_reopen() {
    let mut zero = account(0, 0);
    zero.nonce = 2;
    let pre = state(vec![zero]);
    let closed = transition_perps_margin_v1(
        &context("alice"),
        &pre,
        &command(PERPS_MARGIN_CLOSE_COMMAND_KIND_V1, 0, 3),
    )
    .unwrap();
    let PerpsMarginResultV1::Accepted(closed) = closed else {
        panic!("close rejected")
    };
    assert_eq!(
        closed.post_state.accounts[0].status,
        PerpsMarginAccountStatusV1::CLOSED
    );
    assert_eq!(
        closed.terminal_obligations[0].status,
        TerminalObligationStatusV1::DRAINED
    );
    let retry = transition_perps_margin_v1(
        &context("alice"),
        &closed.post_state,
        &command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 1, 4),
    )
    .unwrap();
    let PerpsMarginResultV1::Rejected(retry) = retry else {
        panic!("closed account reopened")
    };
    assert_eq!(retry.code, PerpsMarginRejectCodeV1::ACCOUNT_CLOSED);
}

#[test]
fn drain_only_permits_withdraw_and_close_while_rejecting_deposit() {
    let mut pre = state(vec![account(10, 0)]);
    pre.market_status = PerpsMarginMarketStatusV1::DRAIN_ONLY;
    let deposit = transition_perps_margin_v1(
        &context("alice"),
        &pre,
        &command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 1, 2),
    )
    .unwrap();
    let PerpsMarginResultV1::Rejected(deposit) = deposit else {
        panic!("drain-only deposit accepted")
    };
    assert_eq!(deposit.code, PerpsMarginRejectCodeV1::MARKET_DRAIN_ONLY);

    let withdrawn = transition_perps_margin_v1(
        &context("alice"),
        &pre,
        &command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 10, 2),
    )
    .unwrap();
    let PerpsMarginResultV1::Accepted(withdrawn) = withdrawn else {
        panic!("drain-only withdrawal rejected")
    };
    let closed = transition_perps_margin_v1(
        &context("alice"),
        &withdrawn.post_state,
        &command(PERPS_MARGIN_CLOSE_COMMAND_KIND_V1, 0, 3),
    )
    .unwrap();
    let PerpsMarginResultV1::Accepted(closed) = closed else {
        panic!("drain-only close rejected")
    };
    assert_eq!(
        closed.terminal_obligations[0].status,
        TerminalObligationStatusV1::DRAINED
    );
}

#[test]
fn terminal_obligation_id_is_namespaced_by_release_market_and_account() {
    let first = state(vec![account(1, 0)]);
    let mut other_market = first.clone();
    other_market.market_id = "perp-eth-usd".to_owned();
    let mut other_release = first.clone();
    other_release.module_release_id = root(99);

    let first_id = first.terminal_obligations().unwrap()[0]
        .obligation_id
        .clone();
    let market_id = other_market.terminal_obligations().unwrap()[0]
        .obligation_id
        .clone();
    let release_id = other_release.terminal_obligations().unwrap()[0]
        .obligation_id
        .clone();
    assert_ne!(first_id, "perps-account-1");
    assert_ne!(first_id, market_id);
    assert_ne!(first_id, release_id);
    assert_ne!(market_id, release_id);
}

#[test]
fn hash_derived_terminal_obligations_are_canonically_sorted() {
    let obligations = state(vec![account(1, 1), counterparty(1, -1)])
        .terminal_obligations()
        .unwrap();
    assert!(obligations
        .windows(2)
        .all(|pair| pair[0].obligation_id < pair[1].obligation_id));
}

#[test]
fn peer_to_peer_market_requires_exact_zero_net_position() {
    assert!(state(vec![account(1, 1)]).validate().is_err());

    let balanced = state(vec![account(1, 1), counterparty(1, -1)]);
    assert!(balanced.validate().is_ok());
    assert_eq!(
        balanced
            .accounts
            .iter()
            .map(|account| account.position_base)
            .sum::<i128>(),
        0
    );
}

#[test]
fn account_count_uses_exact_maximum_boundary() {
    let accounts = (0..=MAX_PERPS_MARGIN_ACCOUNTS_V1)
        .map(|index| PerpsMarginAccountV1 {
            account_id: format!("account-{index:03}"),
            owner: format!("owner-{index:03}"),
            position_base: 0,
            entry_price_e8: 0,
            collateral_atoms: 0,
            nonce: 1,
            status: PerpsMarginAccountStatusV1::OPEN,
        })
        .collect::<Vec<_>>();

    let mut deposit = command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 1, 1);
    deposit.account_id = "perps-account-new".to_owned();
    let below_max = state(accounts[..MAX_PERPS_MARGIN_ACCOUNTS_V1 - 1].to_vec());
    let accepted = transition_perps_margin_v1(&context("alice"), &below_max, &deposit).unwrap();
    let PerpsMarginResultV1::Accepted(accepted) = accepted else {
        panic!("deposit at the account-count boundary rejected")
    };
    assert_eq!(
        accepted.post_state.accounts.len(),
        MAX_PERPS_MARGIN_ACCOUNTS_V1
    );

    let exact_max = state(accounts[..MAX_PERPS_MARGIN_ACCOUNTS_V1].to_vec());
    let rejected = transition_perps_margin_v1(&context("alice"), &exact_max, &deposit).unwrap();
    let PerpsMarginResultV1::Rejected(rejected) = rejected else {
        panic!("deposit above the account-count boundary accepted")
    };
    assert_eq!(rejected.code, PerpsMarginRejectCodeV1::ACCOUNT_LIMIT);
    assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    assert!(rejected.effects.is_empty());

    assert!(state(accounts).validate().is_err());
}

#[test]
fn decoded_rejection_requires_equal_roots_and_empty_effects() {
    let pre = state(Vec::new());
    let result = transition_perps_margin_v1(
        &context("mallory"),
        &pre,
        &command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 1, 1),
    )
    .unwrap();
    let PerpsMarginResultV1::Rejected(rejected) = result else {
        panic!("unauthorized command accepted")
    };
    assert!(rejected.validate().is_ok());

    let unequal = PerpsMarginRejectedV1 {
        post_state_root: root(99),
        ..(*rejected).clone()
    };
    assert!(unequal.validate().is_err());

    let accepted = transition_perps_margin_v1(
        &context("alice"),
        &pre,
        &command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 1, 1),
    )
    .unwrap();
    let PerpsMarginResultV1::Accepted(accepted) = accepted else {
        panic!("deposit rejected")
    };
    let nonempty = PerpsMarginRejectedV1 {
        effects: accepted.effects.clone(),
        ..(*rejected).clone()
    };
    assert!(nonempty.validate().is_err());
}

#[test]
fn effect_delta_overflow_rejects() {
    let pre = state(Vec::new());
    let result = transition_perps_margin_v1(
        &context("alice"),
        &pre,
        &command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 1_u128 << 127, 1),
    )
    .unwrap();
    let PerpsMarginResultV1::Rejected(rejected) = result else {
        panic!("unrepresentable effect delta accepted")
    };
    assert_eq!(
        rejected.code,
        PerpsMarginRejectCodeV1::EFFECT_DELTA_OVERFLOW
    );
}

#[test]
fn serde_rejects_unknown_fields_and_invalid_closed_shape() {
    let mut encoded = serde_json::to_value(state(Vec::new())).unwrap();
    encoded
        .as_object_mut()
        .unwrap()
        .insert("unexpected".to_owned(), serde_json::json!(true));
    assert!(serde_json::from_value::<PerpsMarginStateV1>(encoded).is_err());

    let invalid = PerpsMarginAccountV1 {
        status: PerpsMarginAccountStatusV1::CLOSED,
        ..account(1, 0)
    };
    let invalid_state = state(vec![invalid]);
    assert!(invalid_state.validate().is_err());
}

#[test]
fn constants_remain_bound_to_v1_contract() {
    assert_eq!(GLOBAL_SETTLEMENT_ABI_V1, "zenodex/global-settlement-abi/v1");
    assert_eq!(
        PERPS_MARGIN_MODULE_SCHEMA_V1,
        "zenodex/perps-margin-module/v1"
    );
    assert_eq!(
        PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1,
        "zenodex/perps-margin-module-input/v1"
    );
    assert_eq!(
        PERPS_MARGIN_PRIVATE_PORT_SCHEMA_V1,
        "zenodex/perps-margin-private-port/v1"
    );
}
