#!/usr/bin/env python3
"""Run named repo-local chaos campaigns."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.chaos.regret_scheduler import build_campaign_state, write_json_artifact
from tools.chaos.run_chaos_experiments import (
    EXPERIMENTS,
    EXPERIMENTS_DIR,
    OUTPUT_DIR,
    _get_git_commit,
)


CAMPAIGNS_DIR = ROOT / "tools" / "chaos" / "campaigns"


class ChaosCampaignError(ValueError):
    pass


@dataclass(frozen=True)
class CampaignDefinition:
    campaign_id: str
    description: str
    target_areas: tuple[str, ...]
    required_experiments: tuple[str, ...]
    optional_experiments: tuple[str, ...]
    required_prerequisites: tuple[str, ...]
    optional_prerequisites: tuple[str, ...]
    max_recommended_blast_radius: float


@dataclass(frozen=True)
class CampaignPlan:
    campaign: CampaignDefinition
    experiments_to_run: tuple[str, ...]
    skipped_experiments: tuple[str, ...]
    unavailable_prerequisites: tuple[str, ...]


def _toxiproxy_available() -> bool:
    import socket

    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.settimeout(1.0)
            s.connect(("127.0.0.1", 8474))
            return True
    except Exception:
        return False


def _available_prerequisites() -> set[str]:
    available: set[str] = set()
    if _toxiproxy_available():
        available.add("toxiproxy")
    return available


def _read_campaign_file(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ChaosCampaignError(f"campaign file not found: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ChaosCampaignError(f"invalid campaign JSON {path}: {exc}") from exc
    if not isinstance(data, dict):
        raise ChaosCampaignError(f"{path}: expected top-level object")
    return data


def _read_string_tuple(value: object, *, path: Path, field_name: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise ChaosCampaignError(f"{path}: {field_name} must be a list")
    items: list[str] = []
    for idx, item in enumerate(value):
        if not isinstance(item, str) or not item.strip():
            raise ChaosCampaignError(f"{path}: {field_name}[{idx}] must be a non-empty string")
        items.append(item.strip())
    return tuple(items)


def load_campaign_definition(campaign_id: str, *, campaigns_dir: Path = CAMPAIGNS_DIR) -> CampaignDefinition:
    path = campaigns_dir / f"{campaign_id}.json"
    doc = _read_campaign_file(path)
    schema = doc.get("schema")
    if schema != "chaos/campaign/v1":
        raise ChaosCampaignError(f"{path}: unsupported schema {schema!r}")
    desc = doc.get("description")
    if not isinstance(desc, str) or not desc.strip():
        raise ChaosCampaignError(f"{path}: description must be a non-empty string")
    target_areas = _read_string_tuple(doc.get("target_areas"), path=path, field_name="target_areas")
    required_experiments = _read_string_tuple(doc.get("required_experiments"), path=path, field_name="required_experiments")
    optional_experiments = _read_string_tuple(doc.get("optional_experiments", []), path=path, field_name="optional_experiments")
    required_prerequisites = _read_string_tuple(
        doc.get("required_prerequisites", []),
        path=path,
        field_name="required_prerequisites",
    )
    optional_prerequisites = _read_string_tuple(
        doc.get("optional_prerequisites", []),
        path=path,
        field_name="optional_prerequisites",
    )
    max_recommended_blast_radius = float(doc.get("max_recommended_blast_radius", 1.0))

    unknown = (set(required_experiments) | set(optional_experiments)) - set(EXPERIMENTS)
    if unknown:
        raise ChaosCampaignError(f"{path}: unknown experiments: {', '.join(sorted(unknown))}")

    return CampaignDefinition(
        campaign_id=campaign_id,
        description=desc.strip(),
        target_areas=target_areas,
        required_experiments=required_experiments,
        optional_experiments=optional_experiments,
        required_prerequisites=required_prerequisites,
        optional_prerequisites=optional_prerequisites,
        max_recommended_blast_radius=max_recommended_blast_radius,
    )


def build_campaign_plan(campaign: CampaignDefinition, *, available_prerequisites: set[str] | None = None) -> CampaignPlan:
    available = set(available_prerequisites or _available_prerequisites())
    missing_required = tuple(sorted(set(campaign.required_prerequisites) - available))
    if missing_required:
        raise ChaosCampaignError(
            f"campaign {campaign.campaign_id} missing required prerequisites: {', '.join(missing_required)}"
        )

    optional_missing = set(campaign.optional_prerequisites) - available
    can_run_optional = not optional_missing
    experiments_to_run = list(campaign.required_experiments)
    skipped_experiments: list[str] = []
    if can_run_optional:
        experiments_to_run.extend(campaign.optional_experiments)
    else:
        skipped_experiments.extend(campaign.optional_experiments)

    return CampaignPlan(
        campaign=campaign,
        experiments_to_run=tuple(experiments_to_run),
        skipped_experiments=tuple(skipped_experiments),
        unavailable_prerequisites=tuple(sorted(optional_missing)),
    )


def _refresh_artifacts(
    *,
    output_dir: Path,
    context_key: str,
    max_blast_radius: float | None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    campaign_state, regret_snapshot = build_campaign_state(
        runs_root=output_dir,
        experiments_dir=EXPERIMENTS_DIR,
        context_key=context_key,
        max_blast_radius=max_blast_radius,
    )
    write_json_artifact(output_dir / "campaign_state.json", campaign_state)
    write_json_artifact(output_dir / "regret_snapshot.json", regret_snapshot)
    return campaign_state, regret_snapshot


def _list_campaigns(*, campaigns_dir: Path = CAMPAIGNS_DIR) -> list[str]:
    return sorted(path.stem for path in campaigns_dir.glob("*.json"))


def main() -> int:
    parser = argparse.ArgumentParser(description="Run a named chaos campaign")
    parser.add_argument("--campaign", type=str, default="shell_boundaries_v1", help="Campaign id to run")
    parser.add_argument("--list", action="store_true", help="List available campaigns")
    parser.add_argument("--output", type=Path, default=OUTPUT_DIR / "campaigns", help="Output root")
    parser.add_argument("--context-key", type=str, default="", help="Campaign context key (default: git:<commit>)")
    parser.add_argument(
        "--max-blast-radius",
        type=float,
        default=None,
        help="Optional selection filter when refreshing campaign/regret artifacts",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON summary")
    args = parser.parse_args()

    if args.list:
        for name in _list_campaigns():
            print(name)
        return 0

    try:
        definition = load_campaign_definition(args.campaign)
        plan = build_campaign_plan(definition)
    except ChaosCampaignError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    context_key = args.context_key.strip() or f"git:{_get_git_commit()}"
    campaign_output_dir = args.output / definition.campaign_id
    campaign_output_dir.mkdir(parents=True, exist_ok=True)

    results: list[dict[str, Any]] = []
    for experiment_name in plan.experiments_to_run:
        experiment_output = campaign_output_dir / experiment_name
        experiment_output.mkdir(parents=True, exist_ok=True)
        result = EXPERIMENTS[experiment_name](
            experiment_output,
            verbose=False,
            context_key=context_key,
        )
        results.append(
            {
                "name": result.name,
                "outcome": result.outcome,
                "duration_s": result.duration_s,
                "artifact_dir": result.artifact_dir,
                "error": result.error,
            }
        )

    campaign_state, regret_snapshot = _refresh_artifacts(
        output_dir=campaign_output_dir,
        context_key=context_key,
        max_blast_radius=args.max_blast_radius,
    )

    summary = {
        "schema": "chaos/campaign_run_summary/v1",
        "campaign_id": definition.campaign_id,
        "description": definition.description,
        "target_areas": list(definition.target_areas),
        "required_experiments": list(definition.required_experiments),
        "optional_experiments": list(definition.optional_experiments),
        "executed_experiments": list(plan.experiments_to_run),
        "skipped_experiments": list(plan.skipped_experiments),
        "unavailable_prerequisites": list(plan.unavailable_prerequisites),
        "context_key": context_key,
        "output_dir": str(campaign_output_dir),
        "selected_experiment": campaign_state.get("selected_experiment"),
        "results": results,
    }
    write_json_artifact(campaign_output_dir / "summary.json", summary)

    if args.json:
        print(
            json.dumps(
                {
                    "summary": summary,
                    "campaign_state": campaign_state,
                    "regret_snapshot": regret_snapshot,
                },
                indent=2,
                sort_keys=True,
            )
        )
    else:
        print(f"campaign={definition.campaign_id}")
        print(f"executed={','.join(plan.experiments_to_run)}")
        if plan.skipped_experiments:
            print(f"skipped={','.join(plan.skipped_experiments)}")
        print(f"selected_next={campaign_state.get('selected_experiment')}")

    failed = sum(1 for item in results if item["outcome"] in {"falsified", "error"})
    return 1 if failed > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
