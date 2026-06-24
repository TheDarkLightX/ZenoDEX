from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.perp_epoch import _verify_adapter_ir_hash, perp_epoch_isolated_default_apply
from src.core.perp_v2.math import remaining_position_signed
from src.core.perp_v2.state import initial_state, state_to_dict
from src.core.perp_v2.types import EpochPhase


def _liquidatable_state_dict() -> dict[str, bool | int | str]:
    return state_to_dict(
        replace(
            initial_state(),
            now_epoch=2,
            epoch_phase=EpochPhase.OPEN,
            oracle_seen=True,
            oracle_last_update_epoch=2,
            index_price_e8=100_000_000,
            collateral_quote=5_000,
            position_base=100_000,
            entry_price_e8=100_000_000,
            fee_pool_quote=100,
            fee_income=100,
            initial_insurance=500,
            insurance_balance=600,
            min_notional_for_bounty=0,
        )
    )


def test_default_adapter_supports_partial_liquidate() -> None:
    state = _liquidatable_state_dict()

    res = perp_epoch_isolated_default_apply(
        state=state,
        action="partial_liquidate",
        params={"fraction_bps": 2_500, "auth_ok": True},
    )

    assert res.ok is True, f"code={res.code} err={res.error}"
    assert res.state is not None
    assert res.effects is not None
    assert res.effects["event"] == "PartialLiquidationApplied"
    assert res.state["position_base"] == remaining_position_signed(100_000, 2_500)
    assert res.state["liquidated_this_step"] is True


def test_adapter_ir_hash_check_accepts_matching_or_absent_hash() -> None:
    _verify_adapter_ir_hash(expected_hash="hash:abc", model_hash="hash:abc")
    _verify_adapter_ir_hash(expected_hash="", model_hash="hash:abc")
    _verify_adapter_ir_hash(expected_hash=None, model_hash="hash:abc")


def test_adapter_ir_hash_check_rejects_mismatch() -> None:
    with pytest.raises(RuntimeError, match="perp kernel IR hash mismatch"):
        _verify_adapter_ir_hash(expected_hash="hash:old", model_hash="hash:new")


def test_default_adapter_partial_liquidate_defaults_fraction_to_auto() -> None:
    state = _liquidatable_state_dict()

    res = perp_epoch_isolated_default_apply(
        state=state,
        action="partial_liquidate",
        params={"auth_ok": True},
    )

    assert res.ok is True, f"code={res.code} err={res.error}"
    assert res.state is not None
    assert res.effects is not None
    assert res.effects["event"] == "PartialLiquidationApplied"
    assert int(res.state["position_base"]) < 100_000
    assert res.state["liquidated_this_step"] is True


def test_default_adapter_partial_liquidate_requires_auth() -> None:
    state = _liquidatable_state_dict()

    res = perp_epoch_isolated_default_apply(
        state=state,
        action="partial_liquidate",
        params={"fraction_bps": 2_500},
    )

    assert res.ok is False
    assert res.code == "GuardFalse"
    assert res.error == "guard"
