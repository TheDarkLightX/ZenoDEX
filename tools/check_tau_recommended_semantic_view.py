#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
import sys
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.generate_tau_semantic_view import _render_markdown, build_semantic_view


DEFAULT_VIEW_JSON = REPO_ROOT / "formal" / "tau" / "recommended_semantic_view.json"
DEFAULT_VIEW_MD = REPO_ROOT / "formal" / "tau" / "recommended_semantic_view.md"
DEFAULT_EXECUTION_CENSUS = REPO_ROOT / "formal" / "tau" / "recommended_execution_census_best.json"
SCHEMA = "zenodex/tau/semantic-view/v1"


@dataclass(frozen=True)
class TauRecommendedSemanticViewResult:
    errors: list[str]
    spec_count: int
    extractable_count: int
    temporal_count: int


def _load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise TypeError(f"{path}: expected a JSON object")
    return raw


def _recommended_spec_ids(*, repo_root: Path = REPO_ROOT) -> list[str]:
    spec_root = repo_root / "src" / "tau_specs" / "recommended"
    return [path.stem for path in sorted(spec_root.glob("*.tau"))]


def validate_tau_recommended_semantic_view(
    *,
    view_json_path: Path = DEFAULT_VIEW_JSON,
    view_md_path: Path = DEFAULT_VIEW_MD,
    execution_census_path: Path = DEFAULT_EXECUTION_CENSUS,
    repo_root: Path = REPO_ROOT,
) -> TauRecommendedSemanticViewResult:
    errors: list[str] = []
    if not view_json_path.exists():
        errors.append(f"missing semantic view JSON: {view_json_path}")
        return TauRecommendedSemanticViewResult(errors=errors, spec_count=0, extractable_count=0, temporal_count=0)
    if not view_md_path.exists():
        errors.append(f"missing semantic view Markdown: {view_md_path}")
        return TauRecommendedSemanticViewResult(errors=errors, spec_count=0, extractable_count=0, temporal_count=0)

    raw = _load_json(view_json_path)
    if raw.get("schema") != SCHEMA:
        errors.append(f"{view_json_path}: unexpected schema {raw.get('schema')!r}")

    expected_ids = _recommended_spec_ids(repo_root=repo_root)
    packets = raw.get("packets")
    if not isinstance(packets, list):
        errors.append(f"{view_json_path}: packets must be a list")
        return TauRecommendedSemanticViewResult(errors=errors, spec_count=0, extractable_count=0, temporal_count=0)

    spec_count = len(packets)
    if raw.get("spec_count") != len(expected_ids):
        errors.append(
            f"{view_json_path}: expected spec_count {len(expected_ids)}, found {raw.get('spec_count')!r}"
        )
    if spec_count != len(expected_ids):
        errors.append(f"{view_json_path}: expected {len(expected_ids)} packets, found {spec_count}")

    seen_ids: set[str] = set()
    extractable_count = 0
    temporal_count = 0
    for packet in packets:
        if not isinstance(packet, dict):
            errors.append(f"{view_json_path}: packet entries must be objects")
            continue
        spec_id = str(packet.get("spec_id", "")).strip()
        if not spec_id:
            errors.append(f"{view_json_path}: packet missing spec_id")
            continue
        if spec_id in seen_ids:
            errors.append(f"{view_json_path}: duplicate packet for {spec_id}")
            continue
        seen_ids.add(spec_id)

        if not str(packet.get("profile", "")).strip():
            errors.append(f"{view_json_path}: packet {spec_id} missing profile")
        if not str(packet.get("rule", "")).strip():
            errors.append(f"{view_json_path}: packet {spec_id} missing rule")

        control_surface = packet.get("control_surface", {})
        if not isinstance(control_surface, dict):
            errors.append(f"{view_json_path}: packet {spec_id} control_surface must be an object")
        else:
            always_count = int(control_surface.get("always_count", 0))
            if always_count <= 0:
                errors.append(f"{view_json_path}: packet {spec_id} has no always clauses")

        output_streams = packet.get("output_streams", {})
        if not isinstance(output_streams, dict):
            errors.append(f"{view_json_path}: packet {spec_id} output_streams must be an object")
            output_count = 0
        else:
            output_count = len(output_streams)
            if output_count <= 0:
                errors.append(f"{view_json_path}: packet {spec_id} has no outputs")

        equation_surface = packet.get("equation_surface", {})
        if not isinstance(equation_surface, dict):
            errors.append(f"{view_json_path}: packet {spec_id} equation_surface must be an object")
        else:
            extractable = bool(equation_surface.get("extractable", False))
            equation_count = int(equation_surface.get("equation_count", 0))
            rows = equation_surface.get("rows", [])
            if not isinstance(rows, list):
                errors.append(f"{view_json_path}: packet {spec_id} equation_surface rows must be a list")
                rows = []
            covered_outputs = sorted(
                {
                    str(row.get("name", "")).strip()
                    for row in rows
                    if isinstance(row, dict) and str(row.get("name", "")).strip()
                }
            )
            if extractable:
                extractable_count += 1
            else:
                errors.append(f"{view_json_path}: packet {spec_id} equation surface is not extractable")
            if equation_count != len(rows):
                errors.append(
                    f"{view_json_path}: packet {spec_id} equation_count {equation_count} != row_count {len(rows)}"
                )
            if covered_outputs != sorted(output_streams):
                errors.append(
                    f"{view_json_path}: packet {spec_id} covered outputs {covered_outputs!r} "
                    f"!= declared outputs {sorted(output_streams)!r}"
                )

        if bool(packet.get("temporal", False)):
            temporal_count += 1

    expected_set = set(expected_ids)
    missing_ids = sorted(expected_set - seen_ids)
    unexpected_ids = sorted(seen_ids - expected_set)
    if missing_ids:
        errors.append(
            f"{view_json_path}: missing recommended spec packets: {', '.join(missing_ids[:8])}"
        )
    if unexpected_ids:
        errors.append(
            f"{view_json_path}: unexpected packets outside recommended set: {', '.join(unexpected_ids[:8])}"
        )

    expected_view = build_semantic_view(
        spec_ids=expected_ids,
        execution_census_path=execution_census_path,
    )
    if raw != expected_view:
        errors.append(
            f"{view_json_path}: artifact is stale; regenerate with "
            f"`python3 tools/generate_tau_semantic_view.py --all-recommended "
            f"--out-json {view_json_path.relative_to(repo_root)} --out-md {view_md_path.relative_to(repo_root)}`"
        )

    md_text = view_md_path.read_text(encoding="utf-8")
    expected_md = _render_markdown(expected_view)
    if md_text != expected_md:
        errors.append(
            f"{view_md_path}: artifact is stale; regenerate with "
            f"`python3 tools/generate_tau_semantic_view.py --all-recommended "
            f"--out-json {view_json_path.relative_to(repo_root)} --out-md {view_md_path.relative_to(repo_root)}`"
        )

    return TauRecommendedSemanticViewResult(
        errors=errors,
        spec_count=len(expected_ids),
        extractable_count=extractable_count,
        temporal_count=temporal_count,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate the repo-wide recommended Tau semantic view artifact.")
    parser.add_argument("--view-json", default=str(DEFAULT_VIEW_JSON))
    parser.add_argument("--view-md", default=str(DEFAULT_VIEW_MD))
    parser.add_argument("--execution-census", default=str(DEFAULT_EXECUTION_CENSUS))
    args = parser.parse_args()

    result = validate_tau_recommended_semantic_view(
        view_json_path=Path(args.view_json),
        view_md_path=Path(args.view_md),
        execution_census_path=Path(args.execution_census),
    )
    if result.errors:
        for error in result.errors:
            print(f"ERROR: {error}")
        return 1

    print(f"recommended semantic view specs: {result.spec_count}")
    print(f"equation-surface extractable: {result.extractable_count}")
    print(f"temporal specs: {result.temporal_count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
