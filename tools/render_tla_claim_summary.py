#!/usr/bin/env python3
"""Render a checked markdown summary of supported TLA claims."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

import yaml


REPO_ROOT = Path(__file__).resolve().parents[1]
CLAIMS_REGISTRY_PATH = REPO_ROOT / "docs" / "claims_registry.yaml"
OUTPUT_PATH = REPO_ROOT / "docs" / "TLA_CLAIM_SUMMARY.md"

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.run_tla_models import _discover_models


class RenderError(RuntimeError):
    pass


LAYER_ORDER = {
    "safety": 0,
    "liveness": 1,
}


def _load_supported_tla_claims() -> list[dict[str, Any]]:
    try:
        data = yaml.safe_load(CLAIMS_REGISTRY_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RenderError(f"missing claims registry: {CLAIMS_REGISTRY_PATH.relative_to(REPO_ROOT)}") from exc
    except yaml.YAMLError as exc:
        raise RenderError(f"claims registry YAML is invalid: {exc}") from exc
    if not isinstance(data, dict) or not isinstance(data.get("claims"), list):
        raise RenderError("claims registry is malformed")
    claims = [
        claim
        for claim in data["claims"]
        if isinstance(claim, dict)
        and claim.get("status") == "supported"
        and claim.get("evidence", {}).get("kind") == "tla"
    ]
    if not claims:
        raise RenderError("expected at least one supported TLA claim")
    return claims


def _cfg_metadata(cfg_path: Path) -> tuple[list[str], list[str]]:
    invariants: list[str] = []
    properties: list[str] = []
    for raw_line in cfg_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if line.startswith("INVARIANT "):
            invariants.append(line.removeprefix("INVARIANT ").strip())
        elif line.startswith("PROPERTY "):
            properties.append(line.removeprefix("PROPERTY ").strip())
    return invariants, properties


def _claim_index_by_cfg(claims: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    index: dict[str, dict[str, Any]] = {}
    for claim in claims:
        files = claim.get("evidence", {}).get("files", [])
        cfgs = [path for path in files if isinstance(path, str) and path.endswith(".cfg")]
        if len(cfgs) != 1:
            raise RenderError(f"{claim.get('id')}: expected exactly one .cfg file")
        stem = Path(cfgs[0]).stem
        if stem in index:
            raise RenderError(f"duplicate supported TLA claim for model {stem}")
        index[stem] = claim
    return index


def _render(claims: list[dict[str, Any]]) -> str:
    discovered = _discover_models(REPO_ROOT / "formal" / "tla")
    index = _claim_index_by_cfg(claims)
    discovered_stems = {name for name, _cfg, _tla in discovered}
    claimed_stems = set(index)

    extra = sorted(discovered_stems - claimed_stems)
    missing = sorted(claimed_stems - discovered_stems)
    if extra:
        raise RenderError(f"discovered TLA models without supported claim entries: {', '.join(extra)}")
    if missing:
        raise RenderError(f"supported TLA claims missing discovered models: {', '.join(missing)}")

    lines = [
        "# TLA Claim Summary",
        "",
        "<!-- Generated from docs/claims_registry.yaml and formal/tla/*.cfg. -->",
        "",
        f"- Supported TLA claims: `{len(claims)}`",
        f"- Discovered TLC models: `{len(discovered)}`",
        "- Batch checker: `python3 tools/run_tla_models.py --json`",
        "- Inventory guard: `pytest -q tests/formal/test_tla_claim_inventory.py tests/test_claims_registry.py`",
        "",
    ]

    ordered = sorted(
        discovered,
        key=lambda item: (
            LAYER_ORDER.get(str(index[item[0]].get("layer", "unknown")), 99),
            str(index[item[0]].get("layer", "unknown")),
            item[0],
        ),
    )

    current_layer: str | None = None
    for name, cfg, tla in ordered:
        claim = index[name]
        layer = str(claim.get("layer", "unknown"))
        if layer != current_layer:
            lines.extend([f"## {layer.title()}", ""])
            current_layer = layer
        invariants, properties = _cfg_metadata(cfg)
        lines.extend(
            [
                f"### `{name}`",
                "",
                f"- Claim: `{claim['id']}`",
                f"- Module: `{tla.relative_to(REPO_ROOT)}`",
                f"- Config: `{cfg.relative_to(REPO_ROOT)}`",
                f"- Invariants: {', '.join(f'`{item}`' for item in invariants) if invariants else '_none_'}",
                f"- Properties: {', '.join(f'`{item}`' for item in properties) if properties else '_none_'}",
                f"- Statement: {str(claim['statement']).strip()}",
                "",
            ]
        )
    lines.extend(
        [
            "## Notes",
            "",
            "- These are bounded TLC model checks, not unbounded proofs.",
            "- Fairness assumptions and model bounds are part of each claim statement and must not be widened implicitly.",
            "- The generated summary is only as strong as the corresponding `.tla`, `.cfg`, and release-checked claim entry.",
            "",
        ]
    )
    return "\n".join(lines)


def render_summary_text() -> str:
    return _render(_load_supported_tla_claims()) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Render a checked summary of supported TLA claims.")
    parser.add_argument("--check", action="store_true", help="fail if the generated summary is stale")
    args = parser.parse_args(argv)

    try:
        rendered = render_summary_text()
    except RenderError as exc:
        print(f"error: {exc}")
        return 1

    if args.check:
        if not OUTPUT_PATH.is_file():
            print(f"error: missing generated file {OUTPUT_PATH.relative_to(REPO_ROOT)}")
            return 1
        current = OUTPUT_PATH.read_text(encoding="utf-8")
        if current != rendered:
            print("error: generated TLA claim summary is stale; run `python3 tools/render_tla_claim_summary.py`")
            return 1
        return 0

    OUTPUT_PATH.write_text(rendered, encoding="utf-8")
    print(f"wrote {OUTPUT_PATH.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
