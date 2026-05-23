from __future__ import annotations

from typing import Mapping


def render_zenograph_ranking_review_markdown(
    baseline_report: Mapping[str, object],
    gate_report: Mapping[str, object],
) -> str:
    if not isinstance(baseline_report, Mapping):
        raise TypeError("baseline_report must be a mapping")
    if not isinstance(gate_report, Mapping):
        raise TypeError("gate_report must be a mapping")

    baseline_schema = baseline_report.get("schema")
    gate_schema = gate_report.get("schema")
    if baseline_schema != "zenodex/zenograph-autotrader-shadow-compare-baseline/v1":
        raise ValueError("unsupported baseline report schema")
    if gate_schema != "zenodex/zenograph-autotrader-ranking-promotion-gate-report/v1":
        raise ValueError("unsupported gate report schema")

    gate = _require_mapping(gate_report.get("gate"), name="gate")
    contract = _require_mapping(gate_report.get("promotion_contract"), name="promotion_contract")
    family_summary = _require_mapping(
        baseline_report.get("family_summary"), name="family_summary"
    )

    case_count = _require_int(baseline_report.get("case_count"), name="case_count")
    disagreement_rate = _require_number(
        baseline_report.get("disagreement_rate"), name="disagreement_rate"
    )
    submit_vs_block_rate = _require_number(
        baseline_report.get("controller_submit_vs_zenograph_block_rate"),
        name="controller_submit_vs_zenograph_block_rate",
    )
    block_vs_allow_rate = _require_number(
        baseline_report.get("controller_block_vs_zenograph_allow_rate"),
        name="controller_block_vs_zenograph_allow_rate",
    )
    ranking_allowed = _require_bool(
        gate.get("ranking_influence_allowed"), name="gate.ranking_influence_allowed"
    )
    block_reason = gate.get("block_reason")
    if block_reason is not None and not isinstance(block_reason, str):
        raise TypeError("gate.block_reason must be a string or null")
    unmet_criteria = _require_str_list(gate.get("unmet_criteria"), name="gate.unmet_criteria")
    required_case_count = _require_int(
        contract.get("required_case_count"), name="promotion_contract.required_case_count"
    )
    required_families = _require_str_list(
        contract.get("required_families"), name="promotion_contract.required_families"
    )

    lines = [
        "# ZenoGraph Ranking Review Bundle",
        "",
        "> Advanced experimental automation and AI review surface. At your own risk.",
        "",
        "## Baseline",
        "",
        f"- Case count: `{case_count}`",
        f"- Disagreement rate: `{disagreement_rate}`",
        f"- Submit-vs-block rate: `{submit_vs_block_rate}`",
        f"- Block-vs-allow rate: `{block_vs_allow_rate}`",
        "",
        "## Family Coverage",
        "",
    ]
    for family in sorted(family_summary):
        item = _require_mapping(family_summary[family], name=f"family_summary.{family}")
        family_case_count = _require_int(item.get("case_count"), name=f"{family}.case_count")
        family_disagreement_rate = _require_number(
            item.get("disagreement_rate"), name=f"{family}.disagreement_rate"
        )
        lines.append(
            f"- `{family}`: cases=`{family_case_count}`, disagreement_rate=`{family_disagreement_rate}`"
        )

    lines.extend(
        [
            "",
            "## Gate",
            "",
            f"- Ranking influence allowed: `{str(ranking_allowed).lower()}`",
            f"- Block reason: `{block_reason or 'none'}`",
        ]
    )
    if unmet_criteria:
        lines.append("- Unmet criteria:")
        lines.extend(f"  - `{item}`" for item in unmet_criteria)

    lines.extend(
        [
            "",
            "## Promotion Contract",
            "",
            f"- Required case count: `{required_case_count}`",
            "- Required families:",
        ]
    )
    lines.extend(f"  - `{item}`" for item in required_families)
    lines.extend(
        [
            "",
            "## Safety",
            "",
            "- This bundle does not change controller execution.",
            "- This bundle is for signed replay review only.",
            "- Ranking influence must remain blocked until the gate passes.",
        ]
    )

    return "\n".join(lines) + "\n"


def _require_mapping(value: object, *, name: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return value


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an int")
    return value


def _require_number(value: object, *, name: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise TypeError(f"{name} must be numeric")
    return float(value)


def _require_str_list(value: object, *, name: str) -> list[str]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    out: list[str] = []
    for item in value:
        if not isinstance(item, str):
            raise TypeError(f"{name} entries must be strings")
        out.append(item)
    return out
