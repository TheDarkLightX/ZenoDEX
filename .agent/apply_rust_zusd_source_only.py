#!/usr/bin/env python3
"""Apply the audited zUSD authority relation to the tracked Rust source.

This second-stage publisher exists because the first workflow validated the
modified Rust worktree but its pushed commit omitted the Rust and inventory
files. Every replacement is exact and the publication workflow verifies both
paths are staged before committing.
"""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUST_ZUSD = ROOT / "rust-runtime/crates/zenodex-runtime-core/src/zusd.rs"
INVENTORY = ROOT / "docs/runtime/RUST_VALUE_MOVEMENT_INVENTORY_V1.json"


def replace_once(text: str, old: str, new: str, *, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one exact preimage, found {count}")
    return text.replace(old, new, 1)


def update_rust() -> None:
    text = RUST_ZUSD.read_text(encoding="utf-8")

    old_invariants = '''/// Mirrors `zusd.check_invariants`; returns the list of failed codes.
pub fn check_invariants(state: &ZusdState) -> Vec<&'static str> {
    let mut failed = Vec::new();
    if state.oracle_last_update_epoch > state.now_epoch {
        failed.push("inv_oracle_update_not_future");
    }
    if state.base_rate_last_epoch > state.now_epoch {
        failed.push("inv_base_rate_not_future");
    }
    if state.oracle_seen && (state.price_e8 == 0 || state.price_pending_e8 == 0) {
        failed.push("inv_oracle_seen_positive_prices");
    }
    if state.oracle_seen && state.price_pending_e8 > state.price_e8 {
        failed.push("inv_pending_le_active");
    }
    if !state.oracle_seen
        && (state.price_e8 != 0
            || state.price_pending_e8 != 0
            || state.oracle_last_update_epoch != 0)
    {
        failed.push("inv_oracle_unseen_zeroed");
    }
    if state.free_debt_e8 + state.sp_debt_e8 != state.debt_e8 {
        failed.push("inv_supply_conservation");
    }
    if !debt_floor_ok(state.debt_e8, state.min_debt_open_e8) {
        failed.push("inv_debt_floor");
    }
    let sys_coll = state.collateral_e8 + state.sp_coll_e8 + state.protocol_collateral_e8;
    let price_for_solvency = if state.price_e8 > 0 {
        state.price_e8
    } else {
        E8
    };
    if !solvent_at_price(sys_coll, state.debt_e8, price_for_solvency) {
        failed.push("inv_system_no_bad_debt");
    }
    failed
}
'''
    new_invariants = '''/// Hard accounting and representation invariants.
pub fn check_invariants(state: &ZusdState) -> Vec<&'static str> {
    let mut failed = Vec::new();
    if state.oracle_last_update_epoch > state.now_epoch {
        failed.push("inv_oracle_update_not_future");
    }
    if state.base_rate_last_epoch > state.now_epoch {
        failed.push("inv_base_rate_not_future");
    }
    if state.oracle_seen && (state.price_e8 == 0 || state.price_pending_e8 == 0) {
        failed.push("inv_oracle_seen_positive_prices");
    }
    if state.oracle_seen && state.price_pending_e8 > state.price_e8 {
        failed.push("inv_pending_le_active");
    }
    if !state.oracle_seen
        && (state.price_e8 != 0
            || state.price_pending_e8 != 0
            || state.oracle_last_update_epoch != 0)
    {
        failed.push("inv_oracle_unseen_zeroed");
    }
    if state.free_debt_e8 + state.sp_debt_e8 != state.debt_e8 {
        failed.push("inv_supply_conservation");
    }
    if state.debt_e8 > state.max_debt_supply_e8 {
        failed.push("inv_total_debt_cap");
    }
    if !debt_floor_ok(state.debt_e8, state.min_debt_open_e8) {
        failed.push("inv_debt_floor");
    }
    failed
}

/// Finalized-price health facts. Distress remains representable state.
pub fn check_health_conditions(state: &ZusdState) -> Vec<&'static str> {
    let mut failed = Vec::new();
    if !state.oracle_seen || state.price_e8 == 0 {
        return failed;
    }
    if state.debt_e8 > 0
        && !mcr_ok(
            state.collateral_e8,
            state.debt_e8,
            state.price_e8,
            state.mcr_bps,
        )
    {
        failed.push("health_vault_below_mcr");
    }
    let system_collateral = state
        .collateral_e8
        .saturating_add(state.sp_coll_e8)
        .saturating_add(state.protocol_collateral_e8);
    if !solvent_at_price(system_collateral, state.debt_e8, state.price_e8) {
        failed.push("health_system_bad_debt");
    }
    failed
}
'''
    text = replace_once(
        text,
        old_invariants,
        new_invariants,
        label="Rust hard invariants and health split",
    )

    old_shape_tail = '''    if state.base_rate_bps > BPS_SCALE
        || state.base_rate_decay_per_epoch_bps > BPS_SCALE
        || state.base_rate_borrow_bump_bps > BPS_SCALE
        || state.base_rate_redeem_bump_bps > BPS_SCALE
        || state.borrow_fee_floor_bps > state.borrow_fee_max_bps
        || state.borrow_fee_max_bps > BPS_SCALE
        || state.redemption_fee_floor_bps > state.redemption_fee_max_bps
        || state.redemption_fee_max_bps > BPS_SCALE
        || state.liquidation_gas_comp_bps > BPS_SCALE
    {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    Ok(())
}
'''
    new_shape_tail = '''    if state.base_rate_bps > BPS_SCALE
        || state.base_rate_decay_per_epoch_bps > BPS_SCALE
        || state.base_rate_borrow_bump_bps > BPS_SCALE
        || state.base_rate_redeem_bump_bps > BPS_SCALE
        || state.borrow_fee_floor_bps > state.borrow_fee_max_bps
        || state.borrow_fee_max_bps > BPS_SCALE
        || state.redemption_fee_floor_bps > state.redemption_fee_max_bps
        || state.redemption_fee_max_bps > BPS_SCALE
        || state.liquidation_gas_comp_bps > BPS_SCALE
    {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    if !check_invariants(state).is_empty() {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    Ok(())
}
'''
    text = replace_once(
        text,
        old_shape_tail,
        new_shape_tail,
        label="Rust pre-state hard invariant admission",
    )

    old_commit = '''        ZusdCommand::OracleCommit { auth_ok } => {
            if !state.oracle_seen {
                return Err("oracle_not_bootstrapped");
            }
            if !auth_ok {
                return Err("commit_requires_auth");
            }
            if !mcr_ok(
                state.collateral_e8,
                state.debt_e8,
                state.price_pending_e8,
                state.mcr_bps,
            ) {
                return Err("commit_below_mcr");
            }
            let ns = ZusdState {
                price_e8: state.price_pending_e8,
                oracle_last_update_epoch: state.now_epoch,
                ..state.clone()
            };
            finish("oracle_commit", ns)
        }
'''
    new_commit = '''        ZusdCommand::OracleCommit { auth_ok } => {
            if !state.oracle_seen {
                return Err("oracle_not_bootstrapped");
            }
            if !auth_ok {
                return Err("commit_requires_auth");
            }
            if !is_oracle_fresh(
                state.now_epoch,
                state.oracle_last_update_epoch,
                state.max_oracle_staleness_epochs,
                state.oracle_seen,
            ) {
                return Err("commit_stale_oracle_context");
            }
            let ns = ZusdState {
                price_e8: state.price_pending_e8,
                oracle_last_update_epoch: state.now_epoch,
                ..state.clone()
            };
            finish("oracle_commit", ns)
        }
'''
    text = replace_once(text, old_commit, new_commit, label="Rust Oracle commit")

    text = replace_once(
        text,
        "            if bu(state.free_debt_e8) + &debt_delta_big > bu(state.max_debt_supply_e8) {\n",
        "            if new_debt_big > bu(state.max_debt_supply_e8) {\n",
        label="Rust total debt cap",
    )

    old_liquidate = '''        ZusdCommand::Liquidate => {
            if !state.oracle_seen || state.price_pending_e8 == 0 {
                return Err("liquidate_oracle_uninitialized");
            }
            if state.debt_e8 == 0 {
                return Err("liquidate_no_debt");
            }
            if mcr_ok(
                state.collateral_e8,
                state.debt_e8,
                state.price_pending_e8,
                state.mcr_bps,
            ) {
                return Err("liquidate_not_under_mcr");
            }
            if state.debt_e8 > state.sp_debt_e8 {
                return Err("liquidate_sp_cannot_absorb");
            }
'''
    new_liquidate = '''        ZusdCommand::Liquidate => {
            if !state.oracle_seen || state.price_e8 == 0 {
                return Err("liquidate_oracle_uninitialized");
            }
            if state.price_pending_e8 != state.price_e8 {
                return Err("liquidate_pending_mismatch");
            }
            if !is_oracle_fresh(
                state.now_epoch,
                state.oracle_last_update_epoch,
                state.max_oracle_staleness_epochs,
                state.oracle_seen,
            ) {
                return Err("liquidate_stale_oracle");
            }
            if state.debt_e8 == 0 {
                return Err("liquidate_no_debt");
            }
            if mcr_ok(
                state.collateral_e8,
                state.debt_e8,
                state.price_e8,
                state.mcr_bps,
            ) {
                return Err("liquidate_not_under_mcr");
            }
            if state.debt_e8 > state.sp_debt_e8 {
                return Err("liquidate_sp_cannot_absorb");
            }
'''
    text = replace_once(
        text,
        old_liquidate,
        new_liquidate,
        label="Rust finalized-price liquidation authority",
    )

    test_marker = '''    #[test]
    fn state_root_changes_on_mint() {
        let s = bootstrap(&ZusdState::default(), "100000000");
        let s = step(
            &s,
            &ZusdCommand::DepositCollateral {
                amount_e8: amt("100000000000"),
            },
        )
        .unwrap()
        .state;
        let before = s.state_root();
        let after = step(
            &s,
            &ZusdCommand::MintZusd {
                amount_e8: amt("20000000000"),
            },
        )
        .unwrap()
        .state;
        assert_ne!(before, after.state_root());
    }
}
'''
    new_tests = '''    #[test]
    fn state_root_changes_on_mint() {
        let s = bootstrap(&ZusdState::default(), "100000000");
        let s = step(
            &s,
            &ZusdCommand::DepositCollateral {
                amount_e8: amt("100000000000"),
            },
        )
        .unwrap()
        .state;
        let before = s.state_root();
        let after = step(
            &s,
            &ZusdCommand::MintZusd {
                amount_e8: amt("20000000000"),
            },
        )
        .unwrap()
        .state;
        assert_ne!(before, after.state_root());
    }

    fn cap_state() -> ZusdState {
        ZusdState {
            oracle_seen: true,
            price_e8: 100 * E8,
            price_pending_e8: 100 * E8,
            collateral_e8: 100 * E8,
            debt_e8: 1_400 * E8,
            free_debt_e8: 100 * E8,
            sp_debt_e8: 1_300 * E8,
            max_debt_e8: 2_000 * E8,
            max_debt_supply_e8: 1_500 * E8,
            ..Default::default()
        }
    }

    #[test]
    fn mint_counts_existing_stability_pool_debt_against_cap() {
        let state = cap_state();
        assert_eq!(
            step(
                &state,
                &ZusdCommand::MintZusd {
                    amount_e8: amt(&(200 * E8).to_string()),
                },
            ),
            Err("mint_exceeds_max_supply")
        );
        let accepted = step(
            &state,
            &ZusdCommand::MintZusd {
                amount_e8: amt(&(100 * E8).to_string()),
            },
        )
        .unwrap();
        assert_eq!(accepted.state.debt_e8, 1_500 * E8);
        assert_eq!(accepted.state.free_debt_e8, 200 * E8);
        assert_eq!(accepted.state.sp_debt_e8, 1_300 * E8);
    }

    fn pending_distress() -> ZusdState {
        let state = bootstrap(&ZusdState::default(), &(100 * E8).to_string());
        let state = step(
            &state,
            &ZusdCommand::DepositCollateral {
                amount_e8: amt(&(2 * E8).to_string()),
            },
        )
        .unwrap()
        .state;
        let state = step(
            &state,
            &ZusdCommand::MintZusd {
                amount_e8: amt(&(150 * E8).to_string()),
            },
        )
        .unwrap()
        .state;
        let state = step(
            &state,
            &ZusdCommand::DepositSp {
                amount_e8: amt(&(150 * E8).to_string()),
            },
        )
        .unwrap()
        .state;
        step(
            &state,
            &ZusdCommand::OracleReport {
                auth_ok: true,
                price_e8: amt(&(70 * E8).to_string()),
            },
        )
        .unwrap()
        .state
    }

    #[test]
    fn pending_price_cannot_liquidate_before_finalization() {
        assert_eq!(
            step(&pending_distress(), &ZusdCommand::Liquidate),
            Err("liquidate_pending_mismatch")
        );
    }

    #[test]
    fn adverse_price_finalizes_then_authorizes_liquidation() {
        let finalized = step(
            &pending_distress(),
            &ZusdCommand::OracleCommit { auth_ok: true },
        )
        .unwrap()
        .state;
        assert_eq!(finalized.price_e8, 70 * E8);
        assert!(check_invariants(&finalized).is_empty());
        let health = check_health_conditions(&finalized);
        assert!(health.contains(&"health_vault_below_mcr"));
        assert!(health.contains(&"health_system_bad_debt"));

        let liquidated = step(&finalized, &ZusdCommand::Liquidate).unwrap();
        assert_eq!(liquidated.state.debt_e8, 0);
        assert_eq!(liquidated.state.collateral_e8, 0);
    }

    #[test]
    fn stale_finalized_price_cannot_liquidate() {
        let finalized = step(
            &pending_distress(),
            &ZusdCommand::OracleCommit { auth_ok: true },
        )
        .unwrap()
        .state;
        let stale = step(
            &finalized,
            &ZusdCommand::AdvanceEpoch {
                delta: amt(&(finalized.max_oracle_staleness_epochs + 1).to_string()),
            },
        )
        .unwrap()
        .state;
        assert_eq!(
            step(&stale, &ZusdCommand::Liquidate),
            Err("liquidate_stale_oracle")
        );
    }
}
'''
    text = replace_once(
        text,
        test_marker,
        new_tests,
        label="Rust audit regression tests",
    )

    RUST_ZUSD.write_text(text, encoding="utf-8")


def update_inventory() -> None:
    doc = json.loads(INVENTORY.read_text(encoding="utf-8"))
    surface = next(
        item
        for item in doc["surfaces"]
        if item["surface_id"] == "zusd_single_vault"
    )
    surface["known_blockers"] = [
        "Rust effects remain Python-derived after state/root agreement.",
        "Full BigUint ratio arithmetic and the full transition remain partial CBC.",
        "The complete atomic state/effect/receipt/nonce/outbox commit is not yet proved.",
    ]
    surface["parity_repairs"] = [
        "ZDX-GLOBAL-007: total debt cap counts existing Stability Pool debt.",
        "ZDX-GLOBAL-008: only fresh finalized Oracle state authorizes liquidation.",
    ]
    INVENTORY.write_text(
        json.dumps(doc, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main() -> None:
    update_rust()
    update_inventory()
    print("applied tracked Rust zUSD audit parity source")


if __name__ == "__main__":
    main()
