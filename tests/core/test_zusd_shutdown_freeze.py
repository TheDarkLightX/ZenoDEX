from __future__ import annotations

import pytest

from src.core.zusd import (
    E8,
    ZUSDCommand,
    ZUSDState,
    ZUSDWithShutdownExtension,
    step,
    step_with_shutdown_extension,
)
from src.core.zusd_shutdown import (
    ZUSDShutdownExtensionState,
    ZUSDShutdownPhase,
    shutdown_triggered,
)

_SOURCE_ROOT = "ab" * 32


@pytest.mark.parametrize(
    ("collateral_e8", "price_e8", "debt_e8", "floor_bps", "expected"),
    (
        (100 * E8, 110 * E8 // 100, 100 * E8, 11_000, False),
        (100 * E8, 109 * E8 // 100, 100 * E8, 11_000, True),
        (0, E8, 0, 11_000, False),
        (1, 1, 1, 0, False),
    ),
)
def test_shutdown_trigger_uses_strict_integer_tcr_boundary(
    collateral_e8: int,
    price_e8: int,
    debt_e8: int,
    floor_bps: int,
    expected: bool,
) -> None:
    assert shutdown_triggered(
        collateral_e8=collateral_e8,
        debt_e8=debt_e8,
        price_e8=price_e8,
        shutdown_tcr_bps=floor_bps,
    ) is expected


def _reported_state(*, pending_price_e8: int) -> ZUSDWithShutdownExtension:
    return ZUSDWithShutdownExtension(
        baseline=ZUSDState(
            now_epoch=4,
            oracle_seen=True,
            oracle_last_update_epoch=3,
            oracle_pending_update_epoch=4,
            price_e8=2 * E8,
            price_pending_e8=pending_price_e8,
            collateral_e8=100 * E8,
            debt_e8=100 * E8,
            free_debt_e8=100 * E8,
        ),
        extension=ZUSDShutdownExtensionState(),
    )


def test_baseline_oracle_commit_below_mcr_activates_solvent_price() -> None:
    state = _reported_state(pending_price_e8=109 * E8 // 100).baseline
    result = step(
        state,
        ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}),
    )
    assert result.ok, result.error
    assert result.state is not None
    assert result.state.price_e8 == 109 * E8 // 100


def test_wrapper_commit_below_mcr_rejects_invariant_violating_candidate() -> None:
    state = _reported_state(pending_price_e8=90 * E8 // 100)
    result = step_with_shutdown_extension(
        state,
        ZUSDCommand(
            tag="oracle_commit",
            args={"auth_ok": True, "shutdown_source_state_root": _SOURCE_ROOT},
        ),
    )
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "invariant violation: inv_system_no_bad_debt"
    assert state.extension.phase is ZUSDShutdownPhase.OPEN
    assert state.baseline.price_e8 == 2 * E8


def test_quarantined_wrapper_can_replay_legacy_solvent_freeze_candidate() -> None:
    state = _reported_state(pending_price_e8=109 * E8 // 100)
    result = step_with_shutdown_extension(
        state,
        ZUSDCommand(
            tag="oracle_commit",
            args={"auth_ok": True, "shutdown_source_state_root": _SOURCE_ROOT},
        ),
    )

    assert result.ok, result.error
    assert result.state is not None
    frozen = result.state
    assert frozen.baseline.price_e8 == 109 * E8 // 100
    assert frozen.extension.phase is ZUSDShutdownPhase.FROZEN
    assert frozen.extension.epoch == 4
    assert frozen.extension.oracle_observed_epoch == 4
    assert frozen.extension.price_e8 == frozen.baseline.price_e8
    assert frozen.extension.collateral_e8 == 100 * E8
    assert frozen.extension.debt_e8 == 100 * E8
    assert frozen.extension.source_state_root == _SOURCE_ROOT
    assert result.effects == {
        "event": "shutdown_frozen",
        "price_e8": frozen.baseline.price_e8,
        "oracle_last_update_epoch": 4,
        "shutdown_source_state_root": _SOURCE_ROOT,
    }


def test_shutdown_trigger_without_source_root_rejects_as_atomic_noop() -> None:
    state = _reported_state(pending_price_e8=109 * E8 // 100)
    result = step_with_shutdown_extension(
        state,
        ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}),
    )
    assert result.ok is False
    assert result.state is None
    assert result.error == (
        "shutdown_source_state_root must be 64 lowercase hex characters"
    )
    assert state.extension.phase is ZUSDShutdownPhase.OPEN


def _frozen_state() -> ZUSDWithShutdownExtension:
    baseline = ZUSDState(
        now_epoch=4,
        oracle_seen=True,
        oracle_last_update_epoch=4,
        oracle_pending_update_epoch=4,
        price_e8=109 * E8 // 100,
        price_pending_e8=109 * E8 // 100,
        collateral_e8=100 * E8,
        debt_e8=100 * E8,
        free_debt_e8=100 * E8,
    )
    return ZUSDWithShutdownExtension(
        baseline=baseline,
        extension=ZUSDShutdownExtensionState(
            phase=ZUSDShutdownPhase.FROZEN,
            epoch=4,
            oracle_observed_epoch=4,
            price_e8=baseline.price_e8,
            collateral_e8=baseline.collateral_e8,
            debt_e8=baseline.debt_e8,
            source_state_root=_SOURCE_ROOT,
        ),
    )


@pytest.mark.parametrize(
    ("tag", "args"),
    (
        ("bootstrap_oracle", {"auth_ok": True, "price_e8": E8}),
        ("oracle_report", {"auth_ok": True, "price_e8": E8}),
        ("oracle_commit", {"auth_ok": True}),
        ("deposit_collateral", {"amount_e8": E8}),
        ("withdraw_collateral", {"amount_e8": E8}),
        ("mint_zusd", {"amount_e8": E8}),
        ("repay_zusd", {"amount_e8": E8}),
        ("deposit_sp", {"amount_e8": E8}),
        ("withdraw_sp", {"amount_e8": E8}),
        ("redeem_zusd", {"amount_e8": E8}),
        ("liquidate", {}),
    ),
)
def test_frozen_wrapper_rejects_every_value_or_oracle_transition(
    tag: str,
    args: dict[str, object],
) -> None:
    result = step_with_shutdown_extension(
        _frozen_state(),
        ZUSDCommand(tag=tag, args=args),
    )
    assert result.ok is False
    assert result.state is None
    assert result.error == f"shutdown phase FROZEN blocks {tag}"


def test_frozen_wrapper_allows_epoch_advance_without_changing_snapshot() -> None:
    frozen = _frozen_state()
    result = step_with_shutdown_extension(
        frozen,
        ZUSDCommand(tag="advance_epoch", args={"delta": 1}),
    )
    assert result.ok, result.error
    assert result.state is not None
    assert result.state.baseline.now_epoch == 5
    assert result.state.extension == frozen.extension


def test_wrapper_rejects_inconsistent_frozen_snapshot_by_construction() -> None:
    baseline = _frozen_state().baseline
    with pytest.raises(ValueError, match="shutdown debt must equal active debt"):
        ZUSDWithShutdownExtension(
            baseline=baseline,
            extension=ZUSDShutdownExtensionState(
                phase=ZUSDShutdownPhase.FROZEN,
                epoch=4,
                oracle_observed_epoch=4,
                price_e8=baseline.price_e8,
                collateral_e8=baseline.collateral_e8,
                debt_e8=baseline.debt_e8 - 1,
                source_state_root=_SOURCE_ROOT,
            ),
        )


@pytest.mark.parametrize(
    ("field_name", "value", "message"),
    (
        ("epoch", True, "shutdown_extension.epoch must be an int"),
        ("price_e8", False, "shutdown_extension.price_e8 must be an int"),
        (
            "source_state_root",
            0,
            "shutdown_extension.source_state_root must be a str",
        ),
    ),
)
def test_shutdown_extension_decoder_rejects_ambiguous_scalar_types(
    field_name: str,
    value: object,
    message: str,
) -> None:
    payload = ZUSDShutdownExtensionState().to_obj()
    payload[field_name] = value
    with pytest.raises(TypeError, match=message):
        ZUSDShutdownExtensionState.from_obj(payload)
