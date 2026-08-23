from __future__ import annotations

import stat
from dataclasses import replace
from pathlib import Path

import pytest

import src.integration.zusd_tau_gate as gate
from src.core.zusd import (
    E8,
    ZUSDCommand,
    ZUSDMultiCommand,
    ZUSDVault,
    init_multi_state,
    init_state,
    step,
    step_multi,
)
from src.integration.zusd_tau_gate import (
    ZUSDTauGateConfig,
    step_multi_with_tau,
    step_with_tau,
    validate_zusd_multi_transition,
    validate_zusd_transition,
)


def _single_ok(state, tag: str, **args):
    res = step(state, ZUSDCommand(tag=tag, args=args))
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _multi_ok(state, tag: str, **args):
    res = step_multi(state, ZUSDMultiCommand(tag=tag, args=args))
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
    assert gate._multi_risky_ops_allowed(init_multi_state()) is False
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
    assert (
        gate._multi_risky_ops_allowed(
            _multi_ok(init_multi_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
        )
        is True
    )
    assert (
        gate._multi_risky_ops_allowed(
            _multi_ok(
                _multi_ok(init_multi_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True),
                "oracle_report",
                price_e8=90 * E8,
                auth_ok=True,
            )
        )
        is False
    )
    assert (
        gate._multi_risky_ops_allowed(
            _multi_ok(
                _multi_ok(init_multi_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True),
                "advance_epoch",
                delta=101,
            )
        )
        is False
    )
    assert (
        gate._multi_risky_ops_allowed(
            gate.ZUSDMultiState(
                oracle_seen=True,
                oracle_last_update_epoch=0,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                vault_a=ZUSDVault(collateral_e8=E8, debt_e8=100 * E8),
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

    reported = _single_ok(
        _single_ok(minted, "deposit_sp", amount_e8=140 * E8),
        "oracle_report",
        price_e8=50 * E8,
        auth_ok=True,
    )
    committed = _single_ok(reported, "oracle_commit", auth_ok=True)
    liquidatable = _single_ok(
        committed,
        "advance_epoch",
        delta=1,
    )
    liquidated = step(liquidatable, ZUSDCommand(tag="liquidate", args={}))
    assert liquidated.ok and liquidated.state is not None

    checks = gate._single_checks(
        pre_state=reported,
        cmd=ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}),
        post_state=committed,
    )
    assert checks[0][0].spec_id == gate.ZUSD_ORACLE_COMMIT_GUARD_V3.spec_id
    assert checks[0][1] == {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1}
    string_auth_checks = gate._single_checks(
        pre_state=reported,
        cmd=ZUSDCommand(tag="oracle_commit", args={"auth_ok": "yes"}),
        post_state=committed,
    )
    assert string_auth_checks[0][1]["i4"] == 0
    assert gate._single_checks(pre_state=funded, cmd=ZUSDCommand(tag="mint_zusd", args={"amount_e8": 120 * E8}), post_state=minted)[0][0].spec_id == gate.ZUSD_MINT_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=minted, cmd=ZUSDCommand(tag="repay_zusd", args={"amount_e8": 20 * E8}), post_state=repaid)[0][0].spec_id == gate.ZUSD_REPAY_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=withdraw, cmd=ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 10 * E8}), post_state=redeem)[0][0].spec_id == gate.ZUSD_REDEEM_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=sp_out, cmd=ZUSDCommand(tag="withdraw_collateral", args={"amount_e8": E8 // 2}), post_state=withdraw)[0][0].spec_id == gate.ZUSD_WITHDRAW_COLLATERAL_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=repaid, cmd=ZUSDCommand(tag="deposit_sp", args={"amount_e8": 10 * E8}), post_state=sp)[0][0].spec_id == gate.ZUSD_DEPOSIT_SP_GUARD_V1.spec_id
    assert gate._single_checks(pre_state=sp, cmd=ZUSDCommand(tag="withdraw_sp", args={"amount_e8": 5 * E8}), post_state=sp_out)[0][0].spec_id == gate.ZUSD_WITHDRAW_SP_GUARD_V1.spec_id
    liquidation_check = gate._single_checks(
        pre_state=liquidatable,
        cmd=ZUSDCommand(tag="liquidate", args={}),
        post_state=liquidated.state,
    )[0]
    assert liquidation_check[0].spec_id == gate.ZUSD_LIQUIDATION_GUARD_V3.spec_id
    assert liquidation_check[1] == {f"i{i}": 1 for i in range(1, 10)}

    destination_mutant = replace(
        liquidated.state,
        sp_coll_e8=liquidated.state.sp_coll_e8 + 1,
    )
    destination_mutant_check = gate._single_checks(
        pre_state=liquidatable,
        cmd=ZUSDCommand(tag="liquidate", args={}),
        post_state=destination_mutant,
    )[0]
    assert destination_mutant_check[1]["i7"] == 0
    assert destination_mutant_check[1]["i9"] == 0

    pending_liquidation_check = gate._single_checks(
        pre_state=reported,
        cmd=ZUSDCommand(tag="liquidate", args={}),
        post_state=liquidated.state,
    )[0]
    assert pending_liquidation_check[1]["i2"] == 0
    single_unknown_checks = gate._single_checks(
        pre_state=minted,
        cmd=ZUSDCommand(tag="unknown", args={}),
        post_state=minted,
    )
    assert [spec.spec_id for spec, _payload in single_unknown_checks] == [gate.ZUSD_SUPPLY_CONSERVATION_V3.spec_id]


def test_zusd_tau_oracle_commit_v3_accepts_price_increase_and_binds_delta() -> None:
    active = _single_ok(
        init_state(),
        "bootstrap_oracle",
        price_e8=100 * E8,
        auth_ok=True,
    )
    reported = _single_ok(
        active,
        "oracle_report",
        price_e8=120 * E8,
        auth_ok=True,
    )
    committed = _single_ok(reported, "oracle_commit", auth_ok=True)

    accepted_check = gate._single_checks(
        pre_state=reported,
        cmd=ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}),
        post_state=committed,
    )[0]
    assert accepted_check[0] == gate.ZUSD_ORACLE_COMMIT_GUARD_V3
    assert accepted_check[1] == {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1}

    delta_mutant = replace(committed, collateral_e8=1)
    mutant_check = gate._single_checks(
        pre_state=reported,
        cmd=ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}),
        post_state=delta_mutant,
    )[0]
    assert mutant_check[1]["i5"] == 0


def test_zusd_tau_v3_executes_committed_liquidation_lifecycle() -> None:
    tau_bin = gate.find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")
    config = ZUSDTauGateConfig(
        enabled=True,
        tau_bin=tau_bin,
        allow_path_lookup=False,
        timeout_s=10.0,
    )
    state = _single_ok(
        init_state(),
        "bootstrap_oracle",
        price_e8=150 * E8,
        auth_ok=True,
    )
    state = _single_ok(state, "deposit_collateral", amount_e8=2 * E8)
    state = _single_ok(state, "mint_zusd", amount_e8=150 * E8)
    state = _single_ok(state, "deposit_sp", amount_e8=150 * E8)
    reported = _single_ok(
        state,
        "oracle_report",
        price_e8=80 * E8,
        auth_ok=True,
    )

    committed = step_with_tau(
        reported,
        ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}),
        config=config,
    )
    assert committed.ok is True, committed.error
    assert committed.state is not None

    liquidated = step_with_tau(
        committed.state,
        ZUSDCommand(tag="liquidate", args={}),
        config=config,
    )
    assert liquidated.ok is True, liquidated.error
    assert liquidated.state is not None
    assert liquidated.state.debt_e8 == 0
    assert liquidated.state.sp_coll_e8 == 2 * E8


def test_zusd_tau_gate_multi_helpers_and_checks_cover_all_paths() -> None:
    base = _multi_ok(init_multi_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    funded = _multi_ok(_multi_ok(base, "deposit_collateral", vault="a", amount_e8=4 * E8), "deposit_collateral", vault="b", amount_e8=4 * E8)
    minted_a = _multi_ok(funded, "mint_zusd", vault="a", amount_e8=140 * E8)
    minted = _multi_ok(minted_a, "mint_zusd", vault="b", amount_e8=120 * E8)
    repaid = _multi_ok(minted, "repay_zusd", vault="a", amount_e8=20 * E8)
    sp = _multi_ok(repaid, "deposit_sp", amount_e8=10 * E8)
    sp_out = _multi_ok(sp, "withdraw_sp", amount_e8=5 * E8)
    withdraw = _multi_ok(sp_out, "withdraw_collateral", vault="a", amount_e8=E8 // 2)
    redeem_explicit = _multi_ok(withdraw, "redeem_zusd", vault="a", amount_e8=10 * E8)
    redeem_auto = _multi_ok(minted, "redeem_zusd", amount_e8=10 * E8)

    reported = _multi_ok(
        _multi_ok(minted, "deposit_sp", amount_e8=150 * E8),
        "oracle_report",
        price_e8=35 * E8,
        auth_ok=True,
    )
    committed = _multi_ok(reported, "oracle_commit", auth_ok=True)
    liquidatable = _multi_ok(
        committed,
        "advance_epoch",
        delta=1,
    )
    liquidated = step_multi(
        liquidatable,
        ZUSDMultiCommand(tag="liquidate", args={"vault": "a"}),
    )
    assert liquidated.ok and liquidated.state is not None

    assert gate._multi_vault_for_cmd(minted, ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a"})) == (
        minted.vault_a.collateral_e8,
        minted.vault_a.debt_e8,
    )
    assert gate._multi_vault_for_cmd(minted, ZUSDMultiCommand(tag="mint_zusd", args={"vault": "b"})) == (
        minted.vault_b.collateral_e8,
        minted.vault_b.debt_e8,
    )
    with pytest.raises(ValueError, match="vault must be 'a' or 'b'"):
        gate._multi_vault_for_cmd(minted, ZUSDMultiCommand(tag="mint_zusd", args={"vault": "bad"}))

    assert gate._infer_multi_redeem_vault(minted, redeem_auto) in {"a", "b"}
    with pytest.raises(ValueError, match="unable to infer"):
        gate._infer_multi_redeem_vault(minted, minted)

    commit_check = gate._multi_checks(
        pre_state=reported,
        cmd=ZUSDMultiCommand(tag="oracle_commit", args={"auth_ok": True}),
        post_state=committed,
    )[0]
    assert commit_check[0].spec_id == gate.ZUSD_ORACLE_COMMIT_GUARD_V3.spec_id
    assert commit_check[1] == {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1}
    string_auth_checks = gate._multi_checks(
        pre_state=reported,
        cmd=ZUSDMultiCommand(tag="oracle_commit", args={"auth_ok": "yes"}),
        post_state=committed,
    )
    assert string_auth_checks[0][1]["i4"] == 0
    assert gate._multi_checks(pre_state=funded, cmd=ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a", "amount_e8": 120 * E8}), post_state=minted_a)[0][0].spec_id == gate.ZUSD_MINT_GUARD_V1.spec_id
    assert gate._multi_checks(pre_state=minted, cmd=ZUSDMultiCommand(tag="repay_zusd", args={"vault": "a", "amount_e8": 20 * E8}), post_state=repaid)[0][0].spec_id == gate.ZUSD_REPAY_GUARD_V1.spec_id
    assert gate._multi_checks(pre_state=withdraw, cmd=ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 10 * E8}), post_state=redeem_explicit)[0][0].spec_id == gate.ZUSD_REDEEM_GUARD_V1.spec_id
    assert gate._multi_checks(pre_state=minted, cmd=ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 10 * E8}), post_state=redeem_auto)[0][0].spec_id == gate.ZUSD_REDEEM_GUARD_V1.spec_id
    with pytest.raises(ValueError, match="vault must be 'a' or 'b'"):
        gate._multi_checks(pre_state=minted, cmd=ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "bad", "amount_e8": 1}), post_state=redeem_auto)
    assert gate._multi_checks(pre_state=sp_out, cmd=ZUSDMultiCommand(tag="withdraw_collateral", args={"vault": "a", "amount_e8": E8 // 2}), post_state=withdraw)[0][0].spec_id == gate.ZUSD_WITHDRAW_COLLATERAL_GUARD_V1.spec_id
    assert gate._multi_checks(pre_state=repaid, cmd=ZUSDMultiCommand(tag="deposit_sp", args={"amount_e8": 10 * E8}), post_state=sp)[0][0].spec_id == gate.ZUSD_DEPOSIT_SP_GUARD_V1.spec_id
    assert gate._multi_checks(pre_state=sp, cmd=ZUSDMultiCommand(tag="withdraw_sp", args={"amount_e8": 5 * E8}), post_state=sp_out)[0][0].spec_id == gate.ZUSD_WITHDRAW_SP_GUARD_V1.spec_id
    liquidation_check = gate._multi_checks(
        pre_state=liquidatable,
        cmd=ZUSDMultiCommand(tag="liquidate", args={"vault": "a"}),
        post_state=liquidated.state,
    )[0]
    assert liquidation_check[0].spec_id == gate.ZUSD_LIQUIDATION_GUARD_V3.spec_id
    assert liquidation_check[1] == {f"i{i}": 1 for i in range(1, 10)}
    unknown_checks = gate._multi_checks(
        pre_state=minted,
        cmd=ZUSDMultiCommand(tag="unknown", args={}),
        post_state=minted,
    )
    assert [spec.spec_id for spec, _payload in unknown_checks] == [gate.ZUSD_SUPPLY_CONSERVATION_V3.spec_id]

    with pytest.raises(ValueError, match="no redeemable vault"):
        gate._expected_multi_redeem_vault(
            gate.ZUSDMultiState(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                free_debt_e8=10 * E8,
                vault_a=ZUSDVault(collateral_e8=E8, debt_e8=5 * E8),
                vault_b=ZUSDVault(collateral_e8=E8, debt_e8=5 * E8),
            ),
            amount_e8=10 * E8,
        )

    expected_vault = gate._expected_multi_redeem_vault(minted, amount_e8=10 * E8)
    wrong_vault = "b" if expected_vault == "a" else "a"
    redeemed_vault_state = redeem_auto.vault_a if expected_vault == "a" else redeem_auto.vault_b
    if wrong_vault == "a":
        mismatched_post = gate.ZUSDMultiState(
            **{
                **minted.__dict__,
                "vault_a": redeemed_vault_state,
                "free_debt_e8": redeem_auto.free_debt_e8,
                "protocol_collateral_e8": redeem_auto.protocol_collateral_e8,
                "base_rate_bps": redeem_auto.base_rate_bps,
                "base_rate_last_epoch": redeem_auto.base_rate_last_epoch,
            }
        )
    else:
        mismatched_post = gate.ZUSDMultiState(
            **{
                **minted.__dict__,
                "vault_b": redeemed_vault_state,
                "free_debt_e8": redeem_auto.free_debt_e8,
                "protocol_collateral_e8": redeem_auto.protocol_collateral_e8,
                "base_rate_bps": redeem_auto.base_rate_bps,
                "base_rate_last_epoch": redeem_auto.base_rate_last_epoch,
            }
        )
    with pytest.raises(ValueError, match="auto redeem selected wrong vault"):
        gate._multi_checks(
            pre_state=minted,
            cmd=ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 10 * E8}),
            post_state=mismatched_post,
        )


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

    multi_pre = _multi_ok(
        _multi_ok(_multi_ok(init_multi_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True), "deposit_collateral", vault="a", amount_e8=2 * E8),
        "deposit_collateral",
        vault="b",
        amount_e8=2 * E8,
    )
    multi_post = _multi_ok(multi_pre, "mint_zusd", vault="a", amount_e8=100 * E8)
    multi_cmd = ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a", "amount_e8": 100 * E8})

    monkeypatch.setattr(gate, "run_tau_spec_steps", lambda **kwargs: {0: {"o4": 1}})
    assert validate_zusd_multi_transition(
        pre_state=multi_pre,
        cmd=multi_cmd,
        post_state=multi_post,
        config=ZUSDTauGateConfig(enabled=False),
    ) == (True, None)
    assert validate_zusd_multi_transition(
        pre_state=multi_pre,
        cmd=multi_cmd,
        post_state=multi_post,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False),
    ) == (True, None)

    ok, err = validate_zusd_multi_transition(
        pre_state=multi_pre,
        cmd=multi_cmd,
        post_state=multi_post,
        config=ZUSDTauGateConfig(enabled=True, tau_bin="relative/tau", allow_path_lookup=False),
    )
    assert ok is False and "absolute path" in (err or "")

    monkeypatch.setattr(gate, "run_tau_spec_steps", lambda **kwargs: {0: {"o4": 0}})
    rejected_multi = step_multi_with_tau(
        multi_pre,
        multi_cmd,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False),
    )
    assert rejected_multi.ok is False and "tau_gate_rejected" in (rejected_multi.error or "")

    monkeypatch.setattr(gate, "run_tau_spec_steps", _boom)
    ok, err = validate_zusd_multi_transition(
        pre_state=multi_pre,
        cmd=multi_cmd,
        post_state=multi_post,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False),
    )
    assert ok is False and "RuntimeError" in (err or "")

    passthrough_disabled = step_multi_with_tau(
        multi_pre,
        multi_cmd,
        config=ZUSDTauGateConfig(enabled=False),
    )
    assert passthrough_disabled.ok is True
    assert passthrough_disabled.state == multi_post

    failed_core = step_multi_with_tau(
        init_multi_state(),
        ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a", "amount_e8": 1}),
        config=ZUSDTauGateConfig(enabled=True, tau_bin=str(exe), allow_path_lookup=False),
    )
    assert failed_core.ok is False
    assert "tau_gate_rejected" not in (failed_core.error or "")
