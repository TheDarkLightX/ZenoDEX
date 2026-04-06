#!/usr/bin/env python3
"""Render a checked markdown matrix for the conservative RC1 verified surface."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

import yaml


REPO_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = REPO_ROOT / "tools" / "rc1_scope_manifest.json"
CLAIMS_REGISTRY_PATH = REPO_ROOT / "docs" / "claims_registry.yaml"
OUTPUT_PATH = REPO_ROOT / "docs" / "RC1_VERIFIED_SURFACE_MATRIX.md"

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

try:
    from tools.permissionless_assurance import _status_payload as assurance_status_payload
except ModuleNotFoundError:  # pragma: no cover - script execution path
    from permissionless_assurance import _status_payload as assurance_status_payload


class RenderError(RuntimeError):
    pass


def _load_manifest(path: Path = MANIFEST_PATH) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RenderError(f"missing RC1 scope manifest: {path.relative_to(REPO_ROOT)}") from exc
    except json.JSONDecodeError as exc:
        raise RenderError(f"invalid RC1 scope manifest JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise RenderError("RC1 scope manifest must be an object")
    if data.get("schema") != "zenodex/rc1-scope-manifest/v1":
        raise RenderError("RC1 scope manifest has unexpected schema")
    return data


def _load_claim_statuses(path: Path = CLAIMS_REGISTRY_PATH) -> dict[str, str]:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RenderError(f"missing claims registry: {path.relative_to(REPO_ROOT)}") from exc
    except yaml.YAMLError as exc:
        raise RenderError(f"invalid claims registry YAML: {exc}") from exc
    if not isinstance(data, dict) or not isinstance(data.get("claims"), list):
        raise RenderError("claims registry is malformed")
    out: dict[str, str] = {}
    for claim in data["claims"]:
        if not isinstance(claim, dict):
            continue
        claim_id = claim.get("id")
        status = claim.get("status")
        if isinstance(claim_id, str) and isinstance(status, str):
            out[claim_id] = status
    return out


def _string_list(obj: object, *, field: str) -> list[str]:
    if obj is None:
        return []
    if not isinstance(obj, list) or not all(isinstance(item, str) for item in obj):
        raise RenderError(f"{field} must be a list of strings")
    return [str(item) for item in obj]


def _command_list(obj: object, *, field: str) -> list[list[str]]:
    if obj is None:
        return []
    if not isinstance(obj, list):
        raise RenderError(f"{field} must be a list")
    out: list[list[str]] = []
    for item in obj:
        if not isinstance(item, list) or not item or not all(isinstance(part, str) for part in item):
            raise RenderError(f"{field} entries must be non-empty string lists")
        out.append([str(part) for part in item])
    return out


def _surface_list(obj: object, *, field: str) -> list[dict[str, Any]]:
    if not isinstance(obj, list) or not all(isinstance(item, dict) for item in obj):
        raise RenderError(f"{field} must be a list of objects")
    return [dict(item) for item in obj]


def _lane_index(assurance_payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    lanes = assurance_payload.get("lanes")
    if not isinstance(lanes, list):
        raise RenderError("assurance payload is missing lane inventory")
    out: dict[str, dict[str, Any]] = {}
    for raw in lanes:
        if not isinstance(raw, dict):
            continue
        name = raw.get("name")
        if isinstance(name, str):
            out[name] = dict(raw)
    return out


def _format_commands(commands: Sequence[Sequence[str]]) -> str:
    if not commands:
        return "_none_"
    return "<br>".join(f"`{' '.join(command)}`" for command in commands)


def _format_lanes(lane_names: Sequence[str], lane_index: Mapping[str, Mapping[str, Any]]) -> str:
    if not lane_names:
        return "_none_"
    rendered: list[str] = []
    for name in lane_names:
        lane = lane_index.get(name)
        if lane is None:
            rendered.append(f"`{name}`")
            continue
        rendered.append(f"`{name}` ({'READY' if lane.get('ready') else 'MISSING'})")
    return "<br>".join(rendered)


def _primary_command(commands: Sequence[Sequence[str]]) -> str:
    if not commands:
        return "_none_"
    return f"`{' '.join(commands[0])}`"


def _routes_for_surface(surface: Mapping[str, Any], manifest: Mapping[str, Any]) -> list[str]:
    if not surface.get("routes_from_manifest"):
        return _string_list(surface.get("routes"), field="surface.routes")
    boundary = manifest.get("supported_http_boundary")
    if not isinstance(boundary, dict):
        raise RenderError("supported_http_boundary must be an object")
    return _string_list(boundary.get("routes"), field="supported_http_boundary.routes")


def _render_surface_details(
    *,
    surface: Mapping[str, Any],
    manifest: Mapping[str, Any],
    lane_index: Mapping[str, Mapping[str, Any]],
) -> list[str]:
    label = str(surface.get("label", "unnamed surface"))
    authority = str(surface.get("authority", "unknown"))
    claim_class = str(surface.get("claim_class", "unspecified"))
    docs = _string_list(surface.get("docs"), field="surface.docs")
    paths = _string_list(surface.get("paths"), field="surface.paths")
    lanes = _string_list(surface.get("lanes"), field="surface.lanes")
    commands = _command_list(surface.get("commands"), field="surface.commands")
    notes = _string_list(surface.get("notes"), field="surface.notes")
    routes = _routes_for_surface(surface, manifest)

    lines = [f"### {label}", "", f"- Authority: `{authority}`", f"- Claim class: {claim_class}"]
    if docs:
        lines.append("- Docs:")
        lines.extend(f"  - `{path}`" for path in docs)
    if paths:
        lines.append("- Runtime and artifact paths:")
        lines.extend(f"  - `{path}`" for path in paths)
    if routes:
        lines.append("- Supported HTTP routes:")
        lines.extend(f"  - `{route}`" for route in routes)
    if lanes:
        lines.append("- Backing lanes:")
        for name in lanes:
            lane = lane_index.get(name)
            if lane is None:
                lines.append(f"  - `{name}`")
                continue
            lines.append(f"  - `{name}`: {'READY' if lane.get('ready') else 'MISSING'}")
            description = lane.get("description")
            if isinstance(description, str):
                lines.append(f"    {description}")
    if commands:
        lines.append("- Primary commands:")
        lines.extend(f"  - `{' '.join(command)}`" for command in commands)
    if notes:
        lines.append("- Notes:")
        lines.extend(f"  - {note}" for note in notes)
    lines.append("")
    return lines


def _render_excluded_surfaces(excluded: Sequence[Mapping[str, Any]], claim_statuses: Mapping[str, str]) -> list[str]:
    lines = ["## Explicitly Excluded Surfaces", "", "| Surface | Reason | Paths / claims |", "| --- | --- | --- |"]
    for item in excluded:
        label = str(item.get("label", "unnamed excluded surface"))
        reason = str(item.get("reason", "unspecified"))
        paths = _string_list(item.get("paths"), field="excluded_surface.paths")
        claim_ids = _string_list(item.get("claim_ids"), field="excluded_surface.claim_ids")
        rendered_items = [f"`{path}`" for path in paths]
        rendered_items.extend(f"`{claim_id}` ({claim_statuses.get(claim_id, 'missing')})" for claim_id in claim_ids)
        detail = "<br>".join(rendered_items) if rendered_items else "_none_"
        lines.append(f"| {label} | {reason} | {detail} |")
    lines.append("")
    return lines


def render_matrix_text(
    *,
    root: Path = REPO_ROOT,
    manifest: dict[str, Any] | None = None,
    claim_statuses: dict[str, str] | None = None,
    assurance_payload: dict[str, Any] | None = None,
) -> str:
    manifest_data = manifest if manifest is not None else _load_manifest(root / "tools" / "rc1_scope_manifest.json")
    claim_data = claim_statuses if claim_statuses is not None else _load_claim_statuses(root / "docs" / "claims_registry.yaml")
    assurance_data = assurance_payload if assurance_payload is not None else assurance_status_payload()

    surfaces = _surface_list(manifest_data.get("verified_surfaces"), field="verified_surfaces")
    excluded = _surface_list(manifest_data.get("excluded_surface_matrix"), field="excluded_surface_matrix")
    lane_index = _lane_index(assurance_data)
    excluded_claim_ids = _string_list(
        manifest_data.get("excluded_claims_expected_disputed"),
        field="excluded_claims_expected_disputed",
    )

    lines = [
        "---",
        "title: RC1_VERIFIED_SURFACE_MATRIX",
        "type: note",
        "permalink: autonomous-tau-dex-review/docs/rc1-verified-surface-matrix",
        "---",
        "",
        "# RC1 Verified Surface Matrix",
        "",
        "<!-- Generated from tools/rc1_scope_manifest.json, docs/claims_registry.yaml, and tools/permissionless_assurance.py lane inventory. -->",
        "",
        "This matrix defines the exact conservative RC1 claim boundary for ZenoDEX.",
        "",
        "```text",
        "RC1ClaimOK := CleanTree ∧ ScopeFrozen ∧ ReplayGreen ∧ ExclusionsHonest",
        "```",
        "",
        "Standard reading: RC1 is honest only when the tree is clean, the supported surface is explicit, the replay lanes are green, and excluded or disputed surfaces stay excluded.",
        "",
        "Practical consequence: this matrix is configuration-specific. It is not a claim about every file in the repo.",
        "",
        "## Included Surfaces",
        "",
        "| Surface | Authority | Backing lanes | Primary check |",
        "| --- | --- | --- | --- |",
    ]

    for surface in surfaces:
        label = str(surface.get("label", "unnamed surface"))
        authority = str(surface.get("authority", "unknown"))
        lanes = _string_list(surface.get("lanes"), field="surface.lanes")
        commands = _command_list(surface.get("commands"), field="surface.commands")
        lines.append(
            f"| {label} | `{authority}` | {_format_lanes(lanes, lane_index)} | {_primary_command(commands)} |"
        )
    lines.extend(["", "## Surface Details", ""])

    for surface in surfaces:
        lines.extend(_render_surface_details(surface=surface, manifest=manifest_data, lane_index=lane_index))

    lines.extend(
        [
            "## Excluded Claims That Must Stay Out Of RC1",
            "",
            "| Claim | Registry status |",
            "| --- | --- |",
        ]
    )
    for claim_id in excluded_claim_ids:
        lines.append(f"| `{claim_id}` | `{claim_data.get(claim_id, 'missing')}` |")
    lines.append("")

    lines.extend(_render_excluded_surfaces(excluded, claim_data))
    lines.extend(
        [
            "## Release Hooks",
            "",
            "- `python3 tools/rc1_readiness.py`",
            "- `python3 tools/rc1_readiness.py --check`",
            "- `python3 tools/render_rc1_verified_surface_matrix.py --check`",
            "",
            "These checks are intentionally narrower than the full repo. They exist to keep the RC1 claim specific and auditable.",
            "",
        ]
    )
    return "\n".join(lines)


def matrix_status(
    *,
    root: Path = REPO_ROOT,
    manifest: dict[str, Any] | None = None,
    claim_statuses: dict[str, str] | None = None,
    assurance_payload: dict[str, Any] | None = None,
) -> dict[str, Any]:
    try:
        expected = render_matrix_text(
            root=root,
            manifest=manifest,
            claim_statuses=claim_statuses,
            assurance_payload=assurance_payload,
        ) + "\n"
    except RenderError as exc:
        return {
            "ok": False,
            "path": str((root / "docs" / "RC1_VERIFIED_SURFACE_MATRIX.md").relative_to(root)),
            "error": str(exc),
        }
    output_path = root / "docs" / "RC1_VERIFIED_SURFACE_MATRIX.md"
    current = output_path.read_text(encoding="utf-8") if output_path.exists() else ""
    return {
        "ok": current == expected,
        "path": str(output_path.relative_to(root)),
        "error": None,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Render a checked matrix of the conservative RC1 surface.")
    parser.add_argument("--check", action="store_true", help="fail if the generated matrix is stale")
    args = parser.parse_args(argv)

    try:
        rendered = render_matrix_text() + "\n"
    except RenderError as exc:
        print(f"error: {exc}")
        return 1

    if args.check:
        if not OUTPUT_PATH.is_file():
            print(f"error: missing generated file {OUTPUT_PATH.relative_to(REPO_ROOT)}")
            return 1
        current = OUTPUT_PATH.read_text(encoding="utf-8")
        if current != rendered:
            print(
                "error: generated RC1 verified surface matrix is stale; "
                "run `python3 tools/render_rc1_verified_surface_matrix.py`"
            )
            return 1
        return 0

    OUTPUT_PATH.write_text(rendered, encoding="utf-8")
    print(f"wrote {OUTPUT_PATH.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
