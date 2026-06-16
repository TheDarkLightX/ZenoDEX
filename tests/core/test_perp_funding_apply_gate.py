from __future__ import annotations

import pytest

from src.core.perp_funding_apply_gate import (
    evaluate_perp_funding_apply_gate,
    perp_funding_apply_gate_error,
)
from src.core.perp_v2.types import EpochPhase


def _base_kwargs() -> dict[str, object]:
    return {
        "now_epoch": 10,
        "epoch_phase": EpochPhase.OPEN,
        "auth_ok": True,
        "index_price_e8": 100_000_000,
        "oracle_last_update_epoch": 9,
        "max_oracle_staleness_epochs": 2,
        "oracle_seen": True,
        "funding_last_applied_epoch": 9,
        "funding_cap_bps": 100,
        "new_rate_bps": 50,
        "position_base": 1_000,
        "collateral_quote": 100_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "funding_paid_cumulative": 0,
    }


def test_perp_funding_apply_gate_accepts_happy_path() -> None:
    outcome = evaluate_perp_funding_apply_gate(**_base_kwargs())

    assert outcome.phase_allows_funding is True
    assert outcome.oracle_fresh is True
    assert outcome.rate_within_cap is True
    assert outcome.funding_payment_quote == 5
    assert outcome.collateral_after_quote == 99_995
    assert outcome.maint_req_quote == 60
    assert outcome.cumulative_after_quote == 5
    assert outcome.funding_apply_allowed is True
    assert perp_funding_apply_gate_error(outcome) is None


def test_perp_funding_apply_gate_rejects_stale_oracle() -> None:
    kwargs = _base_kwargs()
    kwargs["now_epoch"] = 20
    kwargs["max_oracle_staleness_epochs"] = 2
    outcome = evaluate_perp_funding_apply_gate(**kwargs)

    assert outcome.oracle_fresh is False
    assert outcome.funding_apply_allowed is False
    assert perp_funding_apply_gate_error(outcome) == "apply_funding requires fresh oracle"


def test_perp_funding_apply_gate_rejects_double_apply() -> None:
    kwargs = _base_kwargs()
    kwargs["funding_last_applied_epoch"] = 10
    outcome = evaluate_perp_funding_apply_gate(**kwargs)

    assert outcome.funding_not_applied_this_epoch is False
    assert outcome.funding_apply_allowed is False
    assert perp_funding_apply_gate_error(outcome) == "apply_funding already applied this epoch"


def test_perp_funding_apply_gate_rejects_rate_outside_cap() -> None:
    kwargs = _base_kwargs()
    kwargs["new_rate_bps"] = 101
    outcome = evaluate_perp_funding_apply_gate(**kwargs)

    assert outcome.rate_within_cap is False
    assert outcome.funding_apply_allowed is False
    assert perp_funding_apply_gate_error(outcome) == "apply_funding requires new_rate_bps within funding_cap_bps"


def test_perp_funding_apply_gate_rejects_maintenance_violation() -> None:
    kwargs = _base_kwargs()
    kwargs["collateral_quote"] = 6
    kwargs["position_base"] = 100
    kwargs["new_rate_bps"] = 100
    outcome = evaluate_perp_funding_apply_gate(**kwargs)

    assert outcome.collateral_after_quote == 5
    assert outcome.maint_req_quote == 6
    assert outcome.maint_margin_ok is False
    assert outcome.funding_apply_allowed is False
    assert perp_funding_apply_gate_error(outcome) == "apply_funding would violate maintenance margin"


@pytest.mark.parametrize(
    ("overrides", "expected_error"),
    [
        ({"epoch_phase": EpochPhase.SETTLED}, "apply_funding only allowed during open or price-published phase"),
        ({"auth_ok": False}, "apply_funding requires auth"),
        ({"index_price_e8": 0}, "apply_funding requires positive index_price_e8"),
        ({"oracle_seen": False}, "apply_funding requires oracle_seen"),
        ({"max_oracle_staleness_epochs": 0}, "apply_funding requires valid max_oracle_staleness_epochs"),
        ({"position_base": 0}, "apply_funding requires non-zero position"),
        ({"collateral_quote": -1, "position_base": 0}, "apply_funding requires non-zero position"),
        ({"funding_paid_cumulative": 10**30}, "apply_funding would violate cumulative funding bounds"),
    ],
)
def test_perp_funding_apply_gate_error_precedence(overrides: dict[str, object], expected_error: str) -> None:
    kwargs = _base_kwargs()
    kwargs.update(overrides)

    outcome = evaluate_perp_funding_apply_gate(**kwargs)

    assert outcome.funding_apply_allowed is False
    assert perp_funding_apply_gate_error(outcome) == expected_error


def test_perp_funding_apply_gate_rejects_noncanonical_flag() -> None:
    kwargs = _base_kwargs()
    kwargs["auth_ok"] = 2

    with pytest.raises(ValueError, match="auth_ok must be 0 or 1"):
        evaluate_perp_funding_apply_gate(**kwargs)
