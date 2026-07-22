#!/usr/bin/env python3
"""Keep the Rust single-vault debt-cap witness inside the valid parameter domain."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUST_ZUSD = ROOT / "rust-runtime/crates/zenodex-runtime-core/src/zusd.rs"
PARITY_TEST = ROOT / "tests/runtime/test_zusd_rust_audit_parity.py"


def replace_once(text: str, old: str, new: str, *, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one exact preimage, found {count}")
    return text.replace(old, new, 1)


def update_rust_tests() -> None:
    text = RUST_ZUSD.read_text(encoding="utf-8")
    old = '''    fn cap_state() -> ZusdState {
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
'''
    new = '''    fn cap_state() -> ZusdState {
        ZusdState {
            oracle_seen: true,
            price_e8: 100 * E8,
            price_pending_e8: 100 * E8,
            collateral_e8: 100 * E8,
            debt_e8: 1_400 * E8,
            free_debt_e8: 100 * E8,
            sp_debt_e8: 1_300 * E8,
            max_debt_e8: 1_500 * E8,
            max_debt_supply_e8: 1_500 * E8,
            ..Default::default()
        }
    }

    #[test]
    fn mint_accepts_exact_total_debt_cap() {
        let accepted = step(
            &cap_state(),
            &ZusdCommand::MintZusd {
                amount_e8: amt(&(100 * E8).to_string()),
            },
        )
        .unwrap();
        assert_eq!(accepted.state.debt_e8, 1_500 * E8);
        assert_eq!(accepted.state.free_debt_e8, 200 * E8);
        assert_eq!(accepted.state.sp_debt_e8, 1_300 * E8);
        assert!(check_invariants(&accepted.state).is_empty());
    }

    #[test]
    fn mint_above_shared_vault_and_supply_cap_rejects() {
        assert_eq!(
            step(
                &cap_state(),
                &ZusdCommand::MintZusd {
                    amount_e8: amt(&(101 * E8).to_string()),
                },
            ),
            Err("mint_exceeds_max_debt")
        );
    }

    #[test]
    fn forged_total_debt_above_cap_is_invalid_state() {
        let forged = ZusdState {
            oracle_seen: true,
            price_e8: 100 * E8,
            price_pending_e8: 100 * E8,
            collateral_e8: 100 * E8,
            debt_e8: 1_600 * E8,
            free_debt_e8: 300 * E8,
            sp_debt_e8: 1_300 * E8,
            max_debt_e8: 1_500 * E8,
            max_debt_supply_e8: 1_500 * E8,
            ..Default::default()
        };
        assert!(check_invariants(&forged).contains(&"inv_total_debt_cap"));
        assert_eq!(
            step(
                &forged,
                &ZusdCommand::DepositCollateral {
                    amount_e8: amt("1"),
                },
            ),
            Err(REJ_INVARIANT_VIOLATION)
        );
    }
'''
    RUST_ZUSD.write_text(
        replace_once(text, old, new, label="Rust valid debt-cap witnesses"),
        encoding="utf-8",
    )


def update_cross_language_tests() -> None:
    text = PARITY_TEST.read_text(encoding="utf-8")
    text = replace_once(
        text,
        "        max_debt_e8=2_000 * E8,\n",
        "        max_debt_e8=1_500 * E8,\n",
        label="Python parity cap parameters",
    )
    old = '''def test_rust_mint_counts_existing_stability_pool_debt(rust_env: Path) -> None:
    set_active_authority_policy(_policy())
    state = _cap_state()

    rejected = _step_both(state, _cmd("mint_zusd", amount_e8=200 * E8))

    assert rejected.ok is False
    assert rejected.state is None
    assert rejected.effects is None
    assert rejected.error == "mint exceeds max_debt_supply_e8"
    assert state.debt_e8 == 1_400 * E8
'''
    new = '''def test_rust_mint_above_shared_vault_and_supply_cap_rejects(
    rust_env: Path,
) -> None:
    set_active_authority_policy(_policy())
    state = _cap_state()

    # The promoted Rust surface is single-vault. Valid parameters require the
    # per-vault cap to be no greater than the global cap, so this rejection is
    # selected by the per-vault check before the equivalent total-debt check.
    rejected = _step_both(state, _cmd("mint_zusd", amount_e8=101 * E8))

    assert rejected.ok is False
    assert rejected.state is None
    assert rejected.effects is None
    assert rejected.error == "mint exceeds per-vault max_debt_e8"
    assert state.debt_e8 == 1_400 * E8
'''
    PARITY_TEST.write_text(
        replace_once(text, old, new, label="Python/Rust valid cap rejection"),
        encoding="utf-8",
    )


def main() -> None:
    update_rust_tests()
    update_cross_language_tests()
    print("normalized Rust single-vault debt-cap witnesses")


if __name__ == "__main__":
    main()
