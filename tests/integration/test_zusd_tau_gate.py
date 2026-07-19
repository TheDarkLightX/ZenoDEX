from __future__ import annotations

import sys

import src.integration.zusd_tau_gate as zusd_tau_gate
from src.core.zusd import (
    E8,
    ZUSDCommand,
    init_state,
    step,
)
from src.integration.zusd_tau_gate import ZUSDTauGateConfig, step_with_tau


def _ok_single(s, tag: str, **kwargs):
    r = step(s, ZUSDCommand(tag=tag, args=kwargs))
    assert r.ok, r.error
    assert r.state is not None
    return r.state


def _single_mint_pre_state():
    s = init_state()
    s = _ok_single(s, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    s = _ok_single(s, "deposit_collateral", amount_e8=2 * E8)
    return s


def test_step_with_tau_disabled_passthrough() -> None:
    s = _single_mint_pre_state()
    cmd = ZUSDCommand(tag="mint_zusd", args={"amount_e8": 100 * E8})

    base = step(s, cmd)
    gated = step_with_tau(s, cmd, config=ZUSDTauGateConfig(enabled=False))

    assert gated == base


def test_step_with_tau_accepts_when_tau_outputs_one(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    s = _single_mint_pre_state()
    cmd = ZUSDCommand(tag="mint_zusd", args={"amount_e8": 100 * E8})
    calls: list[str] = []

    def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
        calls.append(spec_path.name)
        assert len(steps) == 1
        return {0: {"o4": 1}}

    monkeypatch.setattr(zusd_tau_gate, "run_tau_spec_steps", _fake_tau)

    res = step_with_tau(
        s,
        cmd,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert res.ok, res.error
    assert calls == ["zusd_mint_guard_v1.tau", "zusd_supply_conservation_v2.tau"]


def test_step_with_tau_rejects_when_any_gate_fails(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    s = _single_mint_pre_state()
    cmd = ZUSDCommand(tag="mint_zusd", args={"amount_e8": 100 * E8})

    def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
        assert len(steps) == 1
        if spec_path.name == "zusd_mint_guard_v1.tau":
            return {0: {"o4": 0}}
        return {0: {"o4": 1}}

    monkeypatch.setattr(zusd_tau_gate, "run_tau_spec_steps", _fake_tau)

    res = step_with_tau(
        s,
        cmd,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert not res.ok
    assert res.error and "tau_gate_rejected" in res.error
    assert "zusd_mint_guard_v1" in res.error


def test_step_with_tau_fail_closed_on_runner_exception(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    s = _single_mint_pre_state()
    cmd = ZUSDCommand(tag="mint_zusd", args={"amount_e8": 100 * E8})

    def _boom(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise RuntimeError("tau crashed")

    monkeypatch.setattr(zusd_tau_gate, "run_tau_spec_steps", _boom)

    res = step_with_tau(
        s,
        cmd,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert not res.ok
    assert res.error and "RuntimeError" in res.error


def test_step_with_tau_redeem_runs_redeem_guard(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    s = init_state()
    s = _ok_single(s, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    s = _ok_single(s, "deposit_collateral", amount_e8=5 * E8)
    s = _ok_single(s, "mint_zusd", amount_e8=200 * E8)
    cmd = ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 50 * E8})
    calls: list[str] = []

    def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
        calls.append(spec_path.name)
        assert len(steps) == 1
        return {0: {"o4": 1}}

    monkeypatch.setattr(zusd_tau_gate, "run_tau_spec_steps", _fake_tau)

    res = step_with_tau(
        s,
        cmd,
        config=ZUSDTauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert res.ok, res.error
    assert calls == ["zusd_redeem_guard_v1.tau", "zusd_supply_conservation_v2.tau"]
