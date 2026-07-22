#!/usr/bin/env python3
"""Update legacy zUSD tests to the finalized-Oracle authority lifecycle."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEST = ROOT / "tests/core/test_zusd.py"


def replace_once(text: str, old: str, new: str, *, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one exact preimage, found {count}")
    return text.replace(old, new, 1)


def main() -> None:
    text = TEST.read_text(encoding="utf-8")

    text = replace_once(
        text,
        '''def test_oracle_commit_requires_mcr_at_pending_price() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=150 * E8)
    s = _ok(s, "oracle_report", price_e8=50 * E8, auth_ok=True)

    r = step(s, ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}))
    assert not r.ok
    assert "below MCR" in (r.error or "")
''',
        '''def test_oracle_commit_finalizes_distressed_price() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=150 * E8)
    s = _ok(s, "oracle_report", price_e8=50 * E8, auth_ok=True)

    r = step(s, ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}))
    assert r.ok, r.error
    assert r.state is not None
    assert r.state.price_e8 == 50 * E8
    assert r.state.price_pending_e8 == 50 * E8
    assert check_invariants(r.state) == []
''',
        label="Oracle commit test",
    )

    text = replace_once(
        text,
        '''def test_liquidation_under_pending_price_moves_debt_to_sp() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=150 * E8)
    s = _ok(s, "deposit_sp", amount_e8=150 * E8)
    s = _ok(s, "oracle_report", price_e8=70 * E8, auth_ok=True)

    r = step(s, ZUSDCommand(tag="liquidate", args={}))
    assert r.ok, r.error
    assert r.state is not None
    ns = r.state
    assert ns.debt_e8 == 0
    assert ns.collateral_e8 == 0
    assert ns.sp_debt_e8 == 0
    assert ns.sp_coll_e8 == 2 * E8
    assert ns.liquidator_compensation_collateral_cum_e8 == 0
''',
        '''def test_liquidation_under_finalized_price_moves_debt_to_sp() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=150 * E8)
    s = _ok(s, "deposit_sp", amount_e8=150 * E8)
    s = _ok(s, "oracle_report", price_e8=70 * E8, auth_ok=True)

    pending = step(s, ZUSDCommand(tag="liquidate", args={}))
    assert not pending.ok
    assert pending.state is None
    assert pending.effects is None
    assert "pending mismatch" in (pending.error or "")

    s = _ok(s, "oracle_commit", auth_ok=True)
    r = step(s, ZUSDCommand(tag="liquidate", args={}))
    assert r.ok, r.error
    assert r.state is not None
    ns = r.state
    assert ns.debt_e8 == 0
    assert ns.collateral_e8 == 0
    assert ns.sp_debt_e8 == 0
    assert ns.sp_coll_e8 == 2 * E8
    assert ns.liquidator_compensation_collateral_cum_e8 == 0
''',
        label="finalized liquidation test",
    )

    text = replace_once(
        text,
        '    s = _ok(s, "oracle_report", price_e8=1 * E8, auth_ok=True)\n\n'
        '    r = step(s, ZUSDCommand(tag="liquidate", args={}))\n',
        '    s = _ok(s, "oracle_report", price_e8=1 * E8, auth_ok=True)\n'
        '    s = _ok(s, "oracle_commit", auth_ok=True)\n\n'
        '    r = step(s, ZUSDCommand(tag="liquidate", args={}))\n',
        label="107 percent liquidation finalization",
    )

    text = replace_once(
        text,
        '    s = _ok(s, "oracle_report", price_e8=50 * E8, auth_ok=True)\n\n'
        '    r = step(s, ZUSDCommand(tag="liquidate", args={}))\n',
        '    s = _ok(s, "oracle_report", price_e8=50 * E8, auth_ok=True)\n'
        '    s = _ok(s, "oracle_commit", auth_ok=True)\n\n'
        '    r = step(s, ZUSDCommand(tag="liquidate", args={}))\n',
        label="gas compensation liquidation finalization",
    )

    TEST.write_text(text, encoding="utf-8")
    print("updated zUSD core tests for finalized Oracle authority")


if __name__ == "__main__":
    main()
