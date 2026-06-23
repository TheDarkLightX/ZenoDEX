#![no_main]
//! libFuzzer target: zusd::step must never panic for any command/arg, and every
//! accepted state must satisfy supply conservation (free + sp == debt).

use libfuzzer_sys::fuzz_target;
use zenodex_runtime_core::zusd::{step as zusd_step, ZusdCommand, ZusdState};

#[derive(arbitrary::Arbitrary, Debug)]
enum Cmd {
    AdvanceEpoch(Option<String>),
    BootstrapOracle(bool, Option<String>),
    OracleReport(bool, Option<String>),
    OracleCommit(bool),
    DepositCollateral(Option<String>),
    WithdrawCollateral(Option<String>),
    Mint(Option<String>),
    Repay(Option<String>),
    DepositSp(Option<String>),
    WithdrawSp(Option<String>),
    Redeem(Option<String>),
    Liquidate,
    Unknown,
}

fn to_cmd(c: Cmd) -> ZusdCommand {
    match c {
        Cmd::AdvanceEpoch(delta) => ZusdCommand::AdvanceEpoch { delta },
        Cmd::BootstrapOracle(auth_ok, price_e8) => ZusdCommand::BootstrapOracle { auth_ok, price_e8 },
        Cmd::OracleReport(auth_ok, price_e8) => ZusdCommand::OracleReport { auth_ok, price_e8 },
        Cmd::OracleCommit(auth_ok) => ZusdCommand::OracleCommit { auth_ok },
        Cmd::DepositCollateral(a) => ZusdCommand::DepositCollateral { amount_e8: a },
        Cmd::WithdrawCollateral(a) => ZusdCommand::WithdrawCollateral { amount_e8: a },
        Cmd::Mint(a) => ZusdCommand::MintZusd { amount_e8: a },
        Cmd::Repay(a) => ZusdCommand::RepayZusd { amount_e8: a },
        Cmd::DepositSp(a) => ZusdCommand::DepositSp { amount_e8: a },
        Cmd::WithdrawSp(a) => ZusdCommand::WithdrawSp { amount_e8: a },
        Cmd::Redeem(a) => ZusdCommand::RedeemZusd { amount_e8: a },
        Cmd::Liquidate => ZusdCommand::Liquidate,
        Cmd::Unknown => ZusdCommand::Unknown,
    }
}

fuzz_target!(|cmds: Vec<Cmd>| {
    let mut state = ZusdState::default();
    for c in cmds.into_iter().take(64) {
        if let Ok(acc) = zusd_step(&state, &to_cmd(c)) {
            assert_eq!(acc.state.free_debt_e8 + acc.state.sp_debt_e8, acc.state.debt_e8);
            let _ = acc.state.state_root();
            state = acc.state;
        }
    }
});
