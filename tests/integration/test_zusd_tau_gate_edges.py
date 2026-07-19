from __future__ import annotations

import stat
from pathlib import Path

import pytest

import src.integration.zusd_tau_gate as gate
from src.core.zusd import (
    E8,
    ZUSDCommand,
    init_state,
    step,
)
from src.integration.zusd_tau_gate import (
    ZUSDTauGateConfig,
    step_with_tau,
    validate_zusd_transition,
)


def _single_ok(state, tag: str, **args):
    res = step(state, ZUSDCommand(tag=tag, args=args))  # type: ignore[arg-type]
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def test_zusd_tau_gate_resolve_bin_and_gate_output_edges(monkeypatch, tmp_path: Path) -> None:
    exe = tmp_path / "tau"
    exe.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    exe.chmod(exe.stat().st_mode | stat.S_IXUSR)

    not_exe = tmp_path / "tau-noexec"
    not_exe.write_text("x", encoding="utf-8")

    ok, tau_bin, err = gate._resolve_tau_bin(
        ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False)
    )
    assert ok is True and tau_bin == str(exe) and err is None
    ok, tau_bin, err = gate._resolve_tau_bin(
        ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=True)
    )
    assert ok is True and tau_bin == str(exe) and err is None

    ok, _tau_bin, err = gate._resolve_tau_bin(
        ZUSDTauGateConfig(enabled=True, tau_bin="relative/tau", allow_path_lookup=False)
    )
    assert ok is False and "absolute path" in (err or "")

    ok, _tau_bin, err = gate._resolve_tau_bin(
        ZUSDTauGateConfig(enabled=True, tau_bin=str(not_exe), allow_path_lookup=False)
    )
    assert ok is False and "not an executable file" in (err or "")

    monkeypatch.setattr(gate, "find_tau_bin", lambda: str(exe))
    ok, tau_bin, err = gate._resolve_tau_bin(ZUSDTauGateConfig(enabled=True, allow_path_lookup=True))
    assert ok is True and tau_bin == str(exe) and err is None

    monkeypatch.setattr(gate, "find_tau_bin", lambda: None)
    ok, _tau_bin, err = gate._resolve_tau_bin(ZUSDTauGateConfig(enabled=True, allow_path_lookup=True))
    assert ok is False and "not found" in (err or "")

    ok, _tau_bin, err = gate._resolve_tau_bin(ZUSDTauGateConfig(enabled=True))
    assert ok is False and "not configured" in (err or "")

    assert gate._require_gate_ok({0: {"o4": 1}}, spec_ref=gate.ZUSD_MINT_GUARD_V1) == (True, None)
    missing_ok, missing_err = gate._require_gate_ok({0: {}}, spec_ref=gate.ZUSD_MINT_GUARD_V1)
    assert missing_ok is False and "Tau missing" in (missing_err or "")
    fail_ok, fail_err = gate._require_gate_ok({0: {"o4": 0}}, spec_ref=gate.ZUSD_MINT_GUARD_V1)
    assert fail_ok is False and "Tau gate failed" in (fail_err or "")

    assert gate._is_oracle_fresh(now_epoch=5, last_update_epoch=4, max_staleness_epochs=2, oracle_seen=True) is True
    assert gate._is_oracle_fresh(now_epoch=5, last_update_epoch=4, max_staleness_epochs=2, oracle_seen=False) is False
    assert gate._is_oracle_fresh(now_epoch=5, last_update_epoch=4, max_staleness_epochs=-1, oracle_seen=True) is False
    assert gate._mcr_ok(collateral_e8=0, debt_e8=0, price_e8=0, mcr_bps=11_000) is True
    assert gate._mcr_ok(collateral_e8=E8, debt_e8=100 * E8, price_e8=100 * E8, mcr_bps=11_000) is False
    with pytest.raises(ValueError, match="amount_e8 must be a positive int"):
        gate._require_pos_int_arg({"amount_e8": 0}, "amount_e8")

    assert gate._single_risky_ops_allowed(init_state()) is False
    assert (
        gate._single_risky_ops_allowed(
            _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
        )
        is True
    )
    assert (
        gate._single_risky_ops_allowed(
            _single_ok(
                _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True),
                "oracle_report",
                price_e8=90 * E8,
                auth_ok=True,
            )
        )
        is False
    )
    assert (
        gate._single_risky_ops_allowed(
            _single_ok(
                _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True),
                "advance_epoch",
                delta=101,
            )
        )
        is False
    )
    assert (
        gate._single_risky_ops_allowed(
            gate.ZUSDState(
                oracle_seen=True,
                oracle_last_update_epoch=0,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                collateral_e8=E8,
                debt_e8=100 * E8,
                free_debt_e8=100 * E8,
            )
        )
        is False
    )


def test_zusd_tau_gate_single_checks_cover_all_guard_builders() -> None:
    base = _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    funded = _single_ok(base, "deposit_collateral", amount_e8=3 * E8)
    minted = _single_ok(funded, "mint_zusd", amount_e8=140 * E8)
    repaid = _single_ok(minted, "repay_zusd", amount_e8=20 * E8)
    sp = _single_ok(repaid, "deposit_sp", amount_e8=10 * E8)
    sp_out = _single_ok(sp, "withdraw_sp", amount_e8=5 * E8)
    withdraw = _single_ok(sp_out, "withdraw_collateral", amount_e8=E8 // 2)
    redeem = _single_ok(withdraw, "redeem_zusd", amount_e8=10 * E8)

    pending = _single_ok(
        _single_ok(_single_ok(minted, "deposit_sp", amount_e8=140 * E8), "oracle_report", price_e8=40 * E8, auth_ok=True),
        "advance_epoch",
        delta=1,
    )
    liquidated = step(pending, ZUSDCommand(tag="liquidate", args={}))
    assert liquidated.ok and liquidated.state is not None

    checks = gate._single_checks(pre_state=base, cmd=ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}), post_state=base)
    assert checks[0][0].spec_id == gate.ZUSD_ORACLE_COMMIT_GUARD_V2.spec_id
    string_auth_checks = gate._single_checks(
        pre_state=base,
        cmd=ZUSDCommand(tag="oracle_commit", args={"auth_ok": "yes"}),
        post_state=base,
    )
    assert string_auth_checks[0][1]["i4"] == 0
    assert gate._single_checks(pre_state=funded, cmd=ZUSDCommand(tag="mint_zusd", args={"amount_e8": 120 * E8}), post_state=minted)[0][0].spec_id == gate.ZUSD_MINT_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=minted, cmd=ZUSDCommand(tag="repay_zusd", args={"amount_e8": 20 * E8}), post_state=repaid)[0][0].spec_id == gate.ZUSD_REPAY_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=withdraw, cmd=ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 10 * E8}), post_state=redeem)[0][0].spec_id == gate.ZUSD_REDEEM_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=sp_out, cmd=ZUSDCommand(tag="withdraw_collateral", args={"amount_e8": E8 // 2}), post_state=withdraw)[0][0].spec_id == gate.ZUSD_WITHDRAW_COLLATERAL_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=repaid, cmd=ZUSDCommand(tag="deposit_sp", args={"amount_e8": 10 * E8}), post_state=sp)[0][0].spec_id == gate.ZUSD_DEPOSIT_SP_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=sp, cmd=ZUSDCommand(tag="withdraw_sp", args={"amount_e8": 5 * E8}), post_state=sp_out)[0][0].spec_id == gate.ZUSD_WITHDRAW_SP_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=pending, cmd=ZUSDCommand(tag="liquidate", args={}), post_state=liquidated.state)[0][0].spec_id == gate.ZUSD_LIQUIDATION_GUARD_V2.spec_id
    single_unknown_checks = gate._single_checks(
        pre_state=minted,
        cmd=ZUSDCommand(tag="unknown", args={}),  # type: ignore[arg-type]
        post_state=minted,
    )
    assert [spec.spec_id for spec, _payload in single_unknown_checks] == [gate.ZUSD_SUPPLY_CONSERVATION_V2.spec_id]


def test_zusd_tau_gate_validate_and_step_fail_closed_edges(monkeypatch, tmp_path: Path) -> None:
    exe = tmp_path / "tau"
    exe.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    exe.chmod(exe.stat().st_mode | stat.S_IXUSR)

    pre = _single_ok(_single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True), "deposit_collateral", amount_e8=2 * E8)
    post = _single_ok(pre, "mint_zusd", amount_e8=100 * E8)
    cmd = ZUSDCommand(tag="mint_zusd", args={"amount_e8": 100 * E8})

    assert validate_zusd_transition(pre_state=pre, cmd=cmd, post_state=post, config=ZUSDTauGateConfig(enabled=False)) == (True, None)
    ok, err = validate_zusd_transition(
        pre_state=pre,
        cmd=cmd,
        post_state=post,
        config=ZUSDTauGateConfig(enabled=True, tau_bin="relative/tau", allow_path_lookup=False),
    )
    assert ok is False and "absolute path" in (err or "")

    monkeypatch.setattr(gate, "run_tau_spec_steps", lambda **kwargs: {0: {"o4": 0}})
    ok, err = validate_zusd_transition(
        pre_state=pre,
        cmd=cmd,
        post_state=post,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False),
    )
    assert ok is False and "Tau gate failed" in (err or "")

    def _boom(**kwargs):
        raise RuntimeError("tau exploded")

    monkeypatch.setattr(gate, "run_tau_spec_steps", _boom)
    ok, err = validate_zusd_transition(
        pre_state=pre,
        cmd=cmd,
        post_state=post,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False),
    )
    assert ok is False and "RuntimeError" in (err or "")

    monkeypatch.setattr(gate, "run_tau_spec_steps", lambda **kwargs: {0: {"o4": 1}})
    assert validate_zusd_transition(
        pre_state=pre,
        cmd=cmd,
        post_state=post,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False),
    ) == (True, None)

    rejected = step_with_tau(
        pre,
        cmd,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False),
    )
    assert rejected.ok is True

    monkeypatch.setattr(gate, "run_tau_spec_steps", lambda **kwargs: {0: {"o4": 0}})
    rejected = step_with_tau(
        pre,
        cmd,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False),
    )
    assert rejected.ok is False and "tau_gate_rejected" in (rejected.error or "")
