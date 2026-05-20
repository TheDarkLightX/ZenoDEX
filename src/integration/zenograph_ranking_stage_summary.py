from __future__ import annotations

from typing import Mapping


def render_zenograph_ranking_stage_markdown(report: Mapping[str, object]) -> str:
    if not isinstance(report, Mapping):
        raise TypeError("report must be a mapping")

    schema = report.get("schema")
    if schema != "zenodex/zenograph-autotrader-ranking-stage-report/v1":
        raise ValueError("unsupported ranking stage report schema")

    risk = _require_mapping(report.get("risk_disclosure"), name="risk_disclosure")
    stage = _require_mapping(report.get("ranking_stage"), name="ranking_stage")
    advisory = _require_mapping(report.get("zenograph_advisory"), name="zenograph_advisory")

    current_template = _require_str(stage.get("current_template_id"), name="current_template_id")
    effective_template = _require_str(
        stage.get("effective_ranking_template_id"),
        name="effective_ranking_template_id",
    )
    stage_tag = _require_str(stage.get("stage_tag"), name="stage_tag")
    selected_template = stage.get("zenograph_selected_template_id")
    if selected_template is not None and not isinstance(selected_template, str):
        raise TypeError("zenograph_selected_template_id must be a string or null")
    block_reason = stage.get("block_reason")
    if block_reason is not None and not isinstance(block_reason, str):
        raise TypeError("block_reason must be a string or null")
    unmet_criteria = _require_str_list(stage.get("unmet_criteria"), name="unmet_criteria")

    tactic_eval = _require_mapping(advisory.get("tactic_evaluation"), name="tactic_evaluation")
    admissible = _require_bool(tactic_eval.get("admissible"), name="tactic_evaluation.admissible")
    blocked_reasons = _require_str_list(
        tactic_eval.get("blocked_reasons"), name="tactic_evaluation.blocked_reasons"
    )

    guidance = _require_str_list(risk.get("guidance"), name="risk_disclosure.guidance")
    summary = _require_str(risk.get("summary"), name="risk_disclosure.summary")

    lines = [
        "# ZenoGraph Ranking Stage",
        "",
        "> Advanced experimental automation and AI surface. At your own risk.",
        "",
        summary,
        "",
        "## Stage",
        "",
        f"- Stage tag: `{stage_tag}`",
        f"- Current template: `{current_template}`",
        f"- Effective ranking template: `{effective_template}`",
        f"- ZenoGraph selected template: `{selected_template or 'none'}`",
        f"- Tactic admissible: `{str(admissible).lower()}`",
    ]

    if block_reason is not None:
        lines.append(f"- Gate block reason: `{block_reason}`")
    if unmet_criteria:
        lines.append("- Unmet criteria:")
        lines.extend(f"  - `{item}`" for item in unmet_criteria)
    if blocked_reasons:
        lines.append("- Advisory blocked reasons:")
        lines.extend(f"  - `{item}`" for item in blocked_reasons)

    lines.extend(
        [
            "",
            "## Safety",
            "",
            "- This surface does not change controller execution.",
            "- This surface does not submit transactions.",
            "- Any future ranking use remains gated separately from execution.",
        ]
    )

    if guidance:
        lines.extend(["", "## Guidance", ""])
        lines.extend(f"- {item}" for item in guidance)

    return "\n".join(lines) + "\n"


def _require_mapping(value: object, *, name: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return value


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return value


def _require_str_list(value: object, *, name: str) -> list[str]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    out: list[str] = []
    for item in value:
        if not isinstance(item, str):
            raise TypeError(f"{name} entries must be strings")
        out.append(item)
    return out
