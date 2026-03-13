from __future__ import annotations

from dataclasses import asdict

from generated.perp_python import perp_epoch_isolated_v2_ref as ref

from src.core.perp_epoch import (
    perp_epoch_isolated_v2_native_apply,
    perp_epoch_isolated_v2_native_initial_state,
    perp_epoch_isolated_v3_native_initial_state,
)


def test_perp_epoch_isolated_v2_native_initial_state_matches_v2_ref_shape() -> None:
    native = dict(perp_epoch_isolated_v2_native_initial_state())
    reference = dict(asdict(ref.init_state()))
    assert "epoch_phase" not in native
    assert native == reference


def test_perp_epoch_isolated_v2_native_deposit_insurance_matches_v2_ref_shape() -> None:
    native_state = dict(perp_epoch_isolated_v2_native_initial_state())
    params = {"amount": 1_000_000_000_000}

    native = perp_epoch_isolated_v2_native_apply(state=native_state, action="deposit_insurance", params=params)
    reference = ref.step(ref.init_state(), ref.Command(tag="deposit_insurance", args=params))

    assert native.ok is True
    assert reference.ok is True
    assert native.state is not None
    assert "epoch_phase" not in native.state
    assert native.state == dict(asdict(reference.state))


def test_perp_epoch_isolated_v3_native_initial_state_keeps_epoch_phase() -> None:
    native = dict(perp_epoch_isolated_v3_native_initial_state())
    assert native["epoch_phase"] == "Open"
