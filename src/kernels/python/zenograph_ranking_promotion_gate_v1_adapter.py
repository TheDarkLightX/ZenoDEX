from __future__ import annotations

from dataclasses import dataclass


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


@dataclass(frozen=True)
class ZenoGraphRankingPromotionGateResult:
    ranking_influence_allowed: bool
    signed_input_only: bool
    ranking_only_mode: bool
    minimum_case_count_met: bool
    required_family_coverage_met: bool
    submit_vs_block_zero: bool
    block_vs_allow_zero: bool
    operator_release_enabled: bool
    block_reason: str | None

    @property
    def ok(self) -> bool:
        return bool(self.ranking_influence_allowed)

    @property
    def error(self) -> str | None:
        return self.block_reason

    @property
    def unmet_criteria(self) -> tuple[str, ...]:
        criteria: list[str] = []
        if not self.signed_input_only:
            criteria.append("signed_input_only")
        if not self.ranking_only_mode:
            criteria.append("ranking_only_mode")
        if not self.minimum_case_count_met:
            criteria.append("minimum_case_count_met")
        if not self.required_family_coverage_met:
            criteria.append("required_family_coverage_met")
        if not self.submit_vs_block_zero:
            criteria.append("submit_vs_block_zero")
        if not self.block_vs_allow_zero:
            criteria.append("block_vs_allow_zero")
        if not self.operator_release_enabled:
            criteria.append("operator_release_enabled")
        return tuple(criteria)

    def to_dict(self) -> dict[str, object]:
        return {
            "ok": bool(self.ok),
            "ranking_influence_allowed": bool(self.ranking_influence_allowed),
            "signed_input_only": bool(self.signed_input_only),
            "ranking_only_mode": bool(self.ranking_only_mode),
            "minimum_case_count_met": bool(self.minimum_case_count_met),
            "required_family_coverage_met": bool(self.required_family_coverage_met),
            "submit_vs_block_zero": bool(self.submit_vs_block_zero),
            "block_vs_allow_zero": bool(self.block_vs_allow_zero),
            "operator_release_enabled": bool(self.operator_release_enabled),
            "block_reason": self.block_reason,
            "error": self.error,
            "unmet_criteria": list(self.unmet_criteria),
        }


def check_zenograph_ranking_promotion_gate(
    *,
    signed_input_only: bool,
    ranking_only_mode: bool,
    minimum_case_count_met: bool,
    required_family_coverage_met: bool,
    submit_vs_block_zero: bool,
    block_vs_allow_zero: bool,
    operator_release_enabled: bool,
) -> ZenoGraphRankingPromotionGateResult:
    signed_input_only = _require_bool("signed_input_only", signed_input_only)
    ranking_only_mode = _require_bool("ranking_only_mode", ranking_only_mode)
    minimum_case_count_met = _require_bool(
        "minimum_case_count_met", minimum_case_count_met
    )
    required_family_coverage_met = _require_bool(
        "required_family_coverage_met", required_family_coverage_met
    )
    submit_vs_block_zero = _require_bool("submit_vs_block_zero", submit_vs_block_zero)
    block_vs_allow_zero = _require_bool("block_vs_allow_zero", block_vs_allow_zero)
    operator_release_enabled = _require_bool(
        "operator_release_enabled", operator_release_enabled
    )

    if not signed_input_only:
        block_reason = "unsigned_inputs"
    elif not ranking_only_mode:
        block_reason = "not_ranking_only"
    elif not minimum_case_count_met:
        block_reason = "insufficient_case_count"
    elif not required_family_coverage_met:
        block_reason = "required_family_coverage_missing"
    elif not submit_vs_block_zero:
        block_reason = "submit_vs_block_disagreement"
    elif not block_vs_allow_zero:
        block_reason = "block_vs_allow_disagreement"
    elif not operator_release_enabled:
        block_reason = "operator_release_disabled"
    else:
        block_reason = None

    return ZenoGraphRankingPromotionGateResult(
        ranking_influence_allowed=block_reason is None,
        signed_input_only=signed_input_only,
        ranking_only_mode=ranking_only_mode,
        minimum_case_count_met=minimum_case_count_met,
        required_family_coverage_met=required_family_coverage_met,
        submit_vs_block_zero=submit_vs_block_zero,
        block_vs_allow_zero=block_vs_allow_zero,
        operator_release_enabled=operator_release_enabled,
        block_reason=block_reason,
    )
