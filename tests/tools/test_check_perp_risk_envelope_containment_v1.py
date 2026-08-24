from __future__ import annotations

from copy import deepcopy
from typing import Any

import pytest

from tools.check_perp_risk_envelope_containment_v1 import (
    BV32_MAX,
    _boundary_witness,
    _evaluate_risk_envelope,
    check_perp_risk_envelope_containment_v1,
)


def test_containment_pack_closes_every_named_boundary_obligation() -> None:
    # Arrange
    expected_scenarios = {
        "all_exact_boundaries_accept",
        "mark_oracle_gap_plus_one_rejects",
        "mark_drift_plus_one_rejects",
        "oracle_drift_plus_one_rejects",
        "open_interest_plus_one_rejects",
        "funding_plus_one_rejects",
        "liquidation_penalty_plus_one_rejects",
        "insurance_one_below_floor_rejects",
        "margin_one_below_maintenance_rejects",
        "missing_proof_rejects",
        "missing_binding_rejects",
        "stale_oracle_with_proof_rejects",
        "active_breaker_with_proof_rejects",
    }

    # Act
    report = check_perp_risk_envelope_containment_v1()

    # Assert
    assert report["ok"] is True
    assert report["production_authority"] == "NONE"
    assert report["scenario_count"] == len(expected_scenarios)
    assert {row["scenario_id"] for row in report["scenarios"]} == expected_scenarios
    assert all(row["observed"] is row["expected"] for row in report["scenarios"])


@pytest.mark.parametrize(
    ("replacement", "output"),
    [
        ({"mark_price_e8": 1_000_100, "prev_mark_price_e8": 1_000_100}, "mark_oracle_gap_ok"),
        ({"mark_price_e8": 999_900, "prev_mark_price_e8": 999_900}, "mark_oracle_gap_ok"),
        ({"prev_mark_price_e8": 999_900}, "mark_drift_ok"),
        ({"prev_mark_price_e8": 1_000_100}, "mark_drift_ok"),
        ({"prev_oracle_price_e8": 999_900}, "oracle_drift_ok"),
        ({"prev_oracle_price_e8": 1_000_100}, "oracle_drift_ok"),
        ({"open_interest": 100}, "oi_cap_ok"),
        ({"funding_abs_bps": 10}, "funding_cap_ok"),
        ({"liq_penalty_bps": 50}, "liq_penalty_cap_ok"),
        ({"insurance_balance": 1_000}, "insurance_floor_ok"),
        ({"margin_ratio_bps": 500}, "margin_guard_ok"),
    ],
)
def test_exact_numeric_boundaries_accept(replacement: dict[str, int], output: str) -> None:
    # Arrange
    witness = {**_boundary_witness(), **replacement}

    # Act
    result = _evaluate_risk_envelope(**witness)

    # Assert
    assert result[output] is True
    assert result["risk_envelope_ok"] is True


@pytest.mark.parametrize(
    ("replacement", "output"),
    [
        ({"mark_price_e8": 1_000_101, "prev_mark_price_e8": 1_000_101}, "mark_oracle_gap_ok"),
        ({"mark_price_e8": 999_899, "prev_mark_price_e8": 999_899}, "mark_oracle_gap_ok"),
        ({"prev_mark_price_e8": 999_899}, "mark_drift_ok"),
        ({"prev_mark_price_e8": 1_000_101}, "mark_drift_ok"),
        ({"prev_oracle_price_e8": 999_899}, "oracle_drift_ok"),
        ({"prev_oracle_price_e8": 1_000_101}, "oracle_drift_ok"),
        ({"open_interest": 101}, "oi_cap_ok"),
        ({"funding_abs_bps": 11}, "funding_cap_ok"),
        ({"liq_penalty_bps": 51}, "liq_penalty_cap_ok"),
        ({"insurance_balance": 999}, "insurance_floor_ok"),
        ({"margin_ratio_bps": 499}, "margin_guard_ok"),
    ],
)
def test_one_atom_past_numeric_boundaries_reject(replacement: dict[str, int], output: str) -> None:
    # Arrange
    witness = {**_boundary_witness(), **replacement}

    # Act
    result = _evaluate_risk_envelope(**witness)

    # Assert
    assert result[output] is False
    assert result["risk_envelope_ok"] is False


def test_closed_position_does_not_require_a_margin_ratio() -> None:
    # Arrange
    witness = {**_boundary_witness(), "has_open_positions": False, "margin_ratio_bps": 0}

    # Act
    result = _evaluate_risk_envelope(**witness)

    # Assert
    assert result["margin_guard_ok"] is True
    assert result["risk_envelope_ok"] is True


@pytest.mark.parametrize("numeric_value", [0, BV32_MAX])
def test_tau_numeric_domain_endpoints_are_representable(numeric_value: int) -> None:
    # Arrange
    witness = {
        **_boundary_witness(),
        **{
            field: numeric_value
            for field in (
                "mark_price_e8",
                "oracle_price_e8",
                "prev_mark_price_e8",
                "prev_oracle_price_e8",
                "open_interest",
                "max_open_interest",
                "funding_abs_bps",
                "funding_cap_bps",
                "liq_penalty_bps",
                "liq_penalty_cap_bps",
                "insurance_balance",
                "insurance_floor",
                "margin_ratio_bps",
                "maint_margin_bps",
            )
        },
    }

    # Act
    result = _evaluate_risk_envelope(**witness)

    # Assert
    assert result["risk_envelope_ok"] is True


@pytest.mark.parametrize("flag", ["stale_oracle_flag", "breaker_active_flag"])
def test_proof_cannot_override_stale_or_breaker_state(flag: str) -> None:
    # Arrange
    witness = {**_boundary_witness(), flag: True, "proof_ok": True}

    # Act
    result = _evaluate_risk_envelope(**witness)

    # Assert
    assert result["risk_envelope_ok"] is False


@pytest.mark.parametrize("field", ["proof_ok", "binding_ok"])
def test_missing_authority_input_rejects_without_changing_witness(field: str) -> None:
    # Arrange
    witness = {**_boundary_witness(), field: False}
    before = deepcopy(witness)

    # Act
    result = _evaluate_risk_envelope(**witness)

    # Assert
    assert result["risk_envelope_ok"] is False
    assert witness == before


@pytest.mark.parametrize(
    ("field", "invalid"),
    [
        ("mark_price_e8", -1),
        ("mark_price_e8", BV32_MAX + 1),
        ("mark_price_e8", True),
        ("mark_price_e8", 1.0),
        ("proof_ok", 1),
        ("proof_ok", "true"),
    ],
)
def test_noncanonical_tau_inputs_fail_closed(field: str, invalid: Any) -> None:
    # Arrange
    witness = {**_boundary_witness(), field: invalid}

    # Act / Assert
    with pytest.raises(ValueError, match=field):
        _evaluate_risk_envelope(**witness)
