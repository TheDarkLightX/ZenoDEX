from __future__ import annotations

import pytest

from src.core.perp_liquidation_eligibility_gate import (
    evaluate_perp_liquidation_eligibility_gate,
    perp_liquidation_eligibility_gate_error,
)
from src.core.perp_v2.types import EpochPhase


def _base_kwargs() -> dict[str, object]:
    return {
        "now_epoch": 10,
        "epoch_phase": EpochPhase.OPEN,
        "auth_ok": True,
        "position_base": 100_000,
        "index_price_e8": 100_000_000,
        "oracle_last_update_epoch": 9,
        "max_oracle_staleness_epochs": 2,
        "oracle_seen": True,
        "collateral_quote": 5_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
    }


def test_perp_liquidation_eligibility_gate_accepts_liquidatable_account() -> None:
    outcome = evaluate_perp_liquidation_eligibility_gate(**_base_kwargs())

    assert outcome.phase_open_ok is True
    assert outcome.oracle_fresh is True
    assert outcome.liquidatable is True
    assert outcome.partial_liquidation_allowed is True
    assert outcome.effective_maint_bps == 600
    assert outcome.maint_req_quote == 6_000
    assert perp_liquidation_eligibility_gate_error(outcome) is None


def test_perp_liquidation_eligibility_gate_rejects_stale_oracle() -> None:
    kwargs = _base_kwargs()
    kwargs["now_epoch"] = 20
    kwargs["max_oracle_staleness_epochs"] = 2
    outcome = evaluate_perp_liquidation_eligibility_gate(**kwargs)

    assert outcome.oracle_fresh is False
    assert outcome.partial_liquidation_allowed is False
    assert perp_liquidation_eligibility_gate_error(outcome) == "partial_liquidate requires fresh oracle"


def test_perp_liquidation_eligibility_gate_rejects_wrong_phase() -> None:
    kwargs = _base_kwargs()
    kwargs["epoch_phase"] = EpochPhase.PRICE_PUBLISHED
    outcome = evaluate_perp_liquidation_eligibility_gate(**kwargs)

    assert outcome.phase_open_ok is False
    assert outcome.partial_liquidation_allowed is False
    assert perp_liquidation_eligibility_gate_error(outcome) == "partial_liquidate only allowed during open phase"


def test_perp_liquidation_eligibility_gate_rejects_safe_account() -> None:
    kwargs = _base_kwargs()
    kwargs["collateral_quote"] = 7_500
    outcome = evaluate_perp_liquidation_eligibility_gate(**kwargs)

    assert outcome.liquidatable is False
    assert outcome.partial_liquidation_allowed is False
    assert perp_liquidation_eligibility_gate_error(outcome) == "partial_liquidate requires liquidatable account"


def test_perp_liquidation_eligibility_gate_rejects_noncanonical_flags() -> None:
    kwargs = _base_kwargs()
    kwargs["auth_ok"] = 2

    with pytest.raises(ValueError, match="auth_ok must be 0 or 1"):
        evaluate_perp_liquidation_eligibility_gate(**kwargs)
