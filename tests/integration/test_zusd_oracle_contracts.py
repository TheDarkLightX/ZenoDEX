from __future__ import annotations

import pytest

from src.core.zusd import (
    E8,
    ZUSDCommand,
    ZUSDMultiCommand,
    init_multi_state,
    init_state,
    step,
    step_multi,
)
from src.integration.tau_witness import ZUSD_CROSS_MODULE_ORACLE_SYNC_GATE_V1
from src.integration.zusd_oracle_contracts import (
    ZUSDCrossModuleOracleSyncContract,
    ZUSDOraclePendingGateContract,
    build_zusd_cross_module_oracle_sync_contract,
    build_zusd_oracle_pending_gate_contract,
    replay_tau_step,
    verify_zusd_cross_module_oracle_sync_contract_payload,
    verify_zusd_oracle_pending_gate_contract_payload,
)


def _single_ok(state, tag: str, **args):
    res = step(state, ZUSDCommand(tag=tag, args=args))  # type: ignore[arg-type]
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _multi_ok(state, tag: str, **args):
    res = step_multi(state, ZUSDMultiCommand(tag=tag, args=args))  # type: ignore[arg-type]
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def test_zusd_oracle_pending_gate_contract_accepts_aligned_state() -> None:
    state = _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    contract = build_zusd_oracle_pending_gate_contract(state, risky_requested=True, tcr_ok=True)

    assert contract.pending_eq is True
    assert contract.price_pos is True
    assert contract.fresh is True
    assert contract.risky_ops_allowed is True
    assert contract.action_allowed is True

    ok, err = verify_zusd_oracle_pending_gate_contract_payload(contract.to_dict())
    assert ok, err


def test_zusd_oracle_pending_gate_contract_rejects_pending_mismatch() -> None:
    state = _single_ok(
        _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True),
        "oracle_report",
        price_e8=90 * E8,
        auth_ok=True,
    )
    contract = build_zusd_oracle_pending_gate_contract(state, risky_requested=True, tcr_ok=True)

    assert contract.pending_eq is False
    assert contract.risky_ops_allowed is False
    assert contract.action_allowed is False

    payload = contract.to_dict()
    payload["action_allowed"] = True
    ok, err = verify_zusd_oracle_pending_gate_contract_payload(payload)
    assert not ok
    assert err == "action_allowed mismatch"


def test_zusd_oracle_pending_gate_contract_supports_multi_state() -> None:
    state = _multi_ok(init_multi_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    contract = build_zusd_oracle_pending_gate_contract(state, risky_requested=False, tcr_ok=False)

    assert contract.state_mode == "multi"
    assert contract.action_allowed is True
    assert contract.blocked_by_recovery is True


def test_zusd_oracle_pending_gate_contract_rejects_string_boolean_flags() -> None:
    state = _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    payload = build_zusd_oracle_pending_gate_contract(state, risky_requested=True, tcr_ok=True).to_dict()

    payload["oracle_seen"] = "yes"

    with pytest.raises(ValueError, match="oracle_seen must be a bool"):
        ZUSDOraclePendingGateContract.from_dict(payload)

    ok, err = verify_zusd_oracle_pending_gate_contract_payload(payload)
    assert not ok
    assert err == "oracle_seen must be a bool"


def test_zusd_oracle_pending_gate_contract_rejects_missing_boolean_flags() -> None:
    state = _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    payload = build_zusd_oracle_pending_gate_contract(state, risky_requested=True, tcr_ok=True).to_dict()
    del payload["action_allowed"]

    with pytest.raises(ValueError, match="action_allowed must be a bool"):
        ZUSDOraclePendingGateContract.from_dict(payload)


def test_zusd_cross_module_oracle_sync_contract_accepts_aligned_snapshot() -> None:
    contract = build_zusd_cross_module_oracle_sync_contract(
        market_id="TAU-USD",
        zusd_price_e8=50_000_000,
        zusd_epoch=100,
        perp_price_e8=50_000_000,
        perp_oracle_epoch=95,
        max_divergence_bps=0,
        max_epoch_lag=10,
    )

    assert contract.sync_snapshot_available is True
    assert contract.divergence_bounded is True
    assert contract.epoch_lag_bounded is True
    assert contract.sync_gate_ok is True

    ok, err = verify_zusd_cross_module_oracle_sync_contract_payload(contract.to_dict())
    assert ok, err


def test_zusd_cross_module_oracle_sync_contract_rejects_tampering() -> None:
    contract = build_zusd_cross_module_oracle_sync_contract(
        market_id="TAU-USD",
        zusd_price_e8=100 * E8,
        zusd_epoch=100,
        perp_price_e8=50_000_000,
        perp_oracle_epoch=95,
        max_divergence_bps=100,
        max_epoch_lag=10,
    )
    payload = contract.to_dict()
    payload["divergence_bounded"] = True

    ok, err = verify_zusd_cross_module_oracle_sync_contract_payload(payload)
    assert not ok
    assert err == "contract payload mismatch"


def test_zusd_cross_module_oracle_sync_contract_rejects_string_boolean_flags() -> None:
    payload = build_zusd_cross_module_oracle_sync_contract(
        market_id="TAU-USD",
        zusd_price_e8=50_000_000,
        zusd_epoch=100,
        perp_price_e8=50_000_000,
        perp_oracle_epoch=95,
        max_divergence_bps=0,
        max_epoch_lag=10,
    ).to_dict()

    payload["sync_gate_ok"] = "yes"

    with pytest.raises(ValueError, match="sync_gate_ok must be a bool"):
        ZUSDCrossModuleOracleSyncContract.from_dict(payload)

    ok, err = verify_zusd_cross_module_oracle_sync_contract_payload(payload)
    assert not ok
    assert err == "sync_gate_ok must be a bool"


def test_zusd_cross_module_oracle_sync_contract_rejects_missing_boolean_flags() -> None:
    payload = build_zusd_cross_module_oracle_sync_contract(
        market_id="TAU-USD",
        zusd_price_e8=50_000_000,
        zusd_epoch=100,
        perp_price_e8=50_000_000,
        perp_oracle_epoch=95,
        max_divergence_bps=0,
        max_epoch_lag=10,
    ).to_dict()
    del payload["sync_snapshot_available"]

    with pytest.raises(ValueError, match="sync_snapshot_available must be a bool"):
        ZUSDCrossModuleOracleSyncContract.from_dict(payload)


def test_zusd_cross_module_oracle_sync_contract_tau_replay_when_available() -> None:
    contract = build_zusd_cross_module_oracle_sync_contract(
        market_id="TAU-USD",
        zusd_price_e8=50_000_000,
        zusd_epoch=100,
        perp_price_e8=50_000_000,
        perp_oracle_epoch=100,
        max_divergence_bps=0,
        max_epoch_lag=0,
    )
    ok, err = replay_tau_step(
        ZUSD_CROSS_MODULE_ORACLE_SYNC_GATE_V1,
        step=contract.tau_step,
    )
    if not ok and err == "tau not found":
        pytest.skip("tau not found")
    assert ok, err
