from __future__ import annotations

import pytest

from tools.check_tau_experiment_promotion_candidates import (
    DEFAULT_TRACE_REPORT,
    validate_tau_experiment_promotion_candidates,
)


def test_tau_experiment_promotion_candidates_static_gate() -> None:
    result = validate_tau_experiment_promotion_candidates()

    assert result.errors == []
    assert set(result.checked_candidates) == {
        "settlement_admission_envelope_v1",
        "settlement_admission_envelope_temporal_v1",
    }
    assert result.trace_report_checked is False


def test_tau_experiment_promotion_candidates_trace_report_gate() -> None:
    if not DEFAULT_TRACE_REPORT.exists():
        pytest.skip("Tau optimization trace report has not been generated")

    result = validate_tau_experiment_promotion_candidates(require_trace_report=True)

    assert result.errors == []
    assert set(result.checked_trace_cases) == {
        "settlement_admission_envelope_pass",
        "settlement_admission_envelope_fail_two_actions",
        "settlement_admission_envelope_fail_replay",
        "settlement_admission_envelope_fail_quote_and_risk",
        "settlement_admission_temporal_pass",
        "settlement_admission_temporal_fail_chain_height",
        "settlement_admission_temporal_fail_oracle_diversity",
        "settlement_admission_temporal_fail_pause",
        "settlement_admission_temporal_fail_two_actions",
    }
    assert result.trace_report_checked is True
