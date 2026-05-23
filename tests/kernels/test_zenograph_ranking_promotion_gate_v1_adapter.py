from __future__ import annotations

from src.kernels.python.zenograph_ranking_promotion_gate_v1_adapter import (
    check_zenograph_ranking_promotion_gate,
)


def test_zenograph_ranking_promotion_gate_passes_only_on_clean_signed_release() -> None:
    result = check_zenograph_ranking_promotion_gate(
        signed_input_only=True,
        ranking_only_mode=True,
        minimum_case_count_met=True,
        required_family_coverage_met=True,
        submit_vs_block_zero=True,
        block_vs_allow_zero=True,
        operator_release_enabled=True,
    )

    assert result.ok is True
    assert result.ranking_influence_allowed is True
    assert result.block_reason is None


def test_zenograph_ranking_promotion_gate_fails_closed_on_submit_block_disagreement() -> None:
    result = check_zenograph_ranking_promotion_gate(
        signed_input_only=True,
        ranking_only_mode=True,
        minimum_case_count_met=True,
        required_family_coverage_met=True,
        submit_vs_block_zero=False,
        block_vs_allow_zero=True,
        operator_release_enabled=True,
    )

    assert result.ok is False
    assert result.ranking_influence_allowed is False
    assert result.block_reason == "submit_vs_block_disagreement"


def test_zenograph_ranking_promotion_gate_prioritizes_unsigned_inputs() -> None:
    result = check_zenograph_ranking_promotion_gate(
        signed_input_only=False,
        ranking_only_mode=True,
        minimum_case_count_met=True,
        required_family_coverage_met=True,
        submit_vs_block_zero=True,
        block_vs_allow_zero=True,
        operator_release_enabled=True,
    )

    assert result.ok is False
    assert result.block_reason == "unsigned_inputs"


def test_zenograph_ranking_promotion_gate_fails_closed_on_missing_replay_coverage() -> None:
    result = check_zenograph_ranking_promotion_gate(
        signed_input_only=True,
        ranking_only_mode=True,
        minimum_case_count_met=False,
        required_family_coverage_met=True,
        submit_vs_block_zero=True,
        block_vs_allow_zero=True,
        operator_release_enabled=True,
    )

    assert result.ok is False
    assert result.block_reason == "insufficient_case_count"
    assert "minimum_case_count_met" in result.unmet_criteria
