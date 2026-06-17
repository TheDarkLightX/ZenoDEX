from __future__ import annotations

import pytest

import src.integration.zusd_oracle_recovery_lifecycle as recovery_lifecycle
from src.core.zusd import E8, ZUSDCommand, init_state, step
from src.integration.zusd_oracle_contracts import (
    build_zusd_cross_module_oracle_sync_contract,
    build_zusd_oracle_pending_gate_contract,
)
from src.integration.zusd_oracle_recovery_lifecycle import (
    ZUSD_ORACLE_RECOVERY_LIFECYCLE_PACKET_SCHEMA,
    build_zusd_oracle_recovery_lifecycle_packet,
    verify_zusd_oracle_recovery_lifecycle_packet_payload,
)


def _ok(state, tag: str, **args):
    res = step(state, ZUSDCommand(tag=tag, args=args))  # type: ignore[arg-type]
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def test_zusd_oracle_recovery_lifecycle_packet_reenables_risky_ops_after_recovery() -> None:
    previous_state = _ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    previous_state = _ok(previous_state, "advance_epoch", delta=150)
    current_state = _ok(previous_state, "oracle_report", price_e8=100 * E8, auth_ok=True)
    current_state = _ok(current_state, "oracle_commit", auth_ok=True)

    previous_pending = build_zusd_oracle_pending_gate_contract(
        previous_state, risky_requested=True, tcr_ok=True
    )
    current_pending = build_zusd_oracle_pending_gate_contract(
        current_state, risky_requested=True, tcr_ok=True
    )
    current_sync = build_zusd_cross_module_oracle_sync_contract(
        market_id="TAU-USD",
        zusd_price_e8=current_state.price_e8,
        zusd_epoch=current_state.oracle_last_update_epoch,
        perp_price_e8=current_state.price_e8,
        perp_oracle_epoch=current_state.oracle_last_update_epoch,
        max_divergence_bps=0,
        max_epoch_lag=0,
    )

    packet = build_zusd_oracle_recovery_lifecycle_packet(
        previous_pending_gate_contract=previous_pending,
        current_pending_gate_contract=current_pending,
        current_sync_contract=current_sync,
    )

    assert packet.schema == ZUSD_ORACLE_RECOVERY_LIFECYCLE_PACKET_SCHEMA
    assert packet.nested_contracts_ok is True
    assert packet.risky_action_requested is True
    assert packet.previous_risky_action_blocked is True
    assert packet.healthy_now is True
    assert packet.current_risky_ops_allowed is True
    assert packet.risky_ops_reenabled is True
    assert packet.rejected_with_reason is False
    assert packet.rejection_reason is None
    assert packet.lifecycle_ok is True

    ok, err = verify_zusd_oracle_recovery_lifecycle_packet_payload(packet.to_dict())
    assert ok, err


def test_zusd_oracle_recovery_lifecycle_packet_rejects_when_sync_not_ok() -> None:
    previous_state = _ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    previous_state = _ok(previous_state, "advance_epoch", delta=150)
    current_state = _ok(previous_state, "oracle_report", price_e8=100 * E8, auth_ok=True)
    current_state = _ok(current_state, "oracle_commit", auth_ok=True)

    packet = build_zusd_oracle_recovery_lifecycle_packet(
        previous_pending_gate_contract=build_zusd_oracle_pending_gate_contract(
            previous_state, risky_requested=True, tcr_ok=True
        ),
        current_pending_gate_contract=build_zusd_oracle_pending_gate_contract(
            current_state, risky_requested=True, tcr_ok=True
        ),
        current_sync_contract=build_zusd_cross_module_oracle_sync_contract(
            market_id="TAU-USD",
            zusd_price_e8=current_state.price_e8,
            zusd_epoch=current_state.oracle_last_update_epoch,
            perp_price_e8=95 * E8,
            perp_oracle_epoch=current_state.oracle_last_update_epoch,
            max_divergence_bps=0,
            max_epoch_lag=0,
        ),
    )

    assert packet.nested_contracts_ok is True
    assert packet.previous_risky_action_blocked is True
    assert packet.current_oracle_env_ok is True
    assert packet.current_sync_gate_ok is False
    assert packet.healthy_now is False
    assert packet.risky_ops_reenabled is False
    assert packet.rejected_with_reason is True
    assert packet.rejection_reason == "current_cross_module_sync_not_ok"
    assert packet.lifecycle_ok is True


def test_zusd_oracle_recovery_lifecycle_packet_rejects_tampering() -> None:
    previous_state = _ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    previous_state = _ok(previous_state, "advance_epoch", delta=150)
    current_state = _ok(previous_state, "oracle_report", price_e8=100 * E8, auth_ok=True)
    current_state = _ok(current_state, "oracle_commit", auth_ok=True)
    packet = build_zusd_oracle_recovery_lifecycle_packet(
        previous_pending_gate_contract=build_zusd_oracle_pending_gate_contract(
            previous_state, risky_requested=True, tcr_ok=True
        ),
        current_pending_gate_contract=build_zusd_oracle_pending_gate_contract(
            current_state, risky_requested=True, tcr_ok=True
        ),
        current_sync_contract=build_zusd_cross_module_oracle_sync_contract(
            market_id="TAU-USD",
            zusd_price_e8=current_state.price_e8,
            zusd_epoch=current_state.oracle_last_update_epoch,
            perp_price_e8=current_state.price_e8,
            perp_oracle_epoch=current_state.oracle_last_update_epoch,
            max_divergence_bps=0,
            max_epoch_lag=0,
        ),
    )
    payload = packet.to_dict()
    payload["risky_ops_reenabled"] = False

    ok, err = verify_zusd_oracle_recovery_lifecycle_packet_payload(payload)
    assert not ok
    assert err == "rejected_with_reason mismatch"


def test_zusd_oracle_recovery_lifecycle_verifier_propagates_programmer_errors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = {"schema": ZUSD_ORACLE_RECOVERY_LIFECYCLE_PACKET_SCHEMA}

    def programmer_error(_payload: object) -> object:
        raise RuntimeError("unexpected oracle recovery parser bug")

    monkeypatch.setattr(
        recovery_lifecycle.ZUSDOracleRecoveryLifecyclePacket,
        "from_dict",
        programmer_error,
    )

    with pytest.raises(RuntimeError, match="unexpected oracle recovery parser bug"):
        verify_zusd_oracle_recovery_lifecycle_packet_payload(payload)
