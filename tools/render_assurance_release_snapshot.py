#!/usr/bin/env python3
"""Render public assurance snapshot docs from the canonical snapshot source."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import date
from pathlib import Path
from typing import Any

import yaml


REPO_ROOT = Path(__file__).resolve().parents[1]
SNAPSHOT_JSON_PATH = REPO_ROOT / "docs" / "assurance_release_snapshot.json"
CLAIMS_REGISTRY_PATH = REPO_ROOT / "docs" / "claims_registry.yaml"
README_PATH = REPO_ROOT / "README.md"
PUBLIC_REPLAY_PATH = REPO_ROOT / "docs" / "PUBLIC_ASSURANCE_REPLAY.md"
SNAPSHOT_MD_PATH = REPO_ROOT / "docs" / "ASSURANCE_RELEASE_SNAPSHOT.md"

README_MARKER = "ASSURANCE_RELEASE_SNAPSHOT"
PUBLIC_REPLAY_MARKER = "PUBLIC_ASSURANCE_RELEASE_SNAPSHOT"


class RenderError(RuntimeError):
    pass


def _load_snapshot() -> dict[str, Any]:
    try:
        data = json.loads(SNAPSHOT_JSON_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RenderError(f"missing snapshot source: {SNAPSHOT_JSON_PATH.relative_to(REPO_ROOT)}") from exc
    except json.JSONDecodeError as exc:
        raise RenderError(f"snapshot JSON is invalid: {exc}") from exc
    if data.get("schema") != "zenodex/assurance-release-snapshot/v1":
        raise RenderError(f"unsupported snapshot schema: {data.get('schema')!r}")
    if not isinstance(data.get("snapshot_label"), str) or not data["snapshot_label"].strip():
        raise RenderError("snapshot_label must be a non-empty string")
    if not isinstance(data.get("as_of_date"), str) or not data["as_of_date"].strip():
        raise RenderError("as_of_date must be a non-empty ISO date string")
    try:
        date.fromisoformat(data["as_of_date"])
    except ValueError as exc:
        raise RenderError(f"invalid as_of_date {data['as_of_date']!r}; expected YYYY-MM-DD") from exc
    metrics = data.get("metrics")
    if not isinstance(metrics, list) or not metrics:
        raise RenderError("metrics must be a non-empty list")
    seen_labels: set[str] = set()
    for idx, metric in enumerate(metrics):
        if not isinstance(metric, dict):
            raise RenderError(f"metrics[{idx}] must be an object")
        label = metric.get("label")
        value = metric.get("value")
        if not isinstance(label, str) or not label.strip():
            raise RenderError(f"metrics[{idx}].label must be a non-empty string")
        if label in seen_labels:
            raise RenderError(f"duplicate metric label: {label}")
        seen_labels.add(label)
        if not isinstance(value, str) or not value.strip():
            raise RenderError(f"metrics[{idx}].value must be a non-empty string")
        branch = metric.get("branch_coverage")
        if branch is not None and (not isinstance(branch, str) or not branch.strip()):
            raise RenderError(f"metrics[{idx}].branch_coverage must be a non-empty string when present")
    derivatives = data.get("derivatives")
    if not isinstance(derivatives, dict):
        raise RenderError("derivatives must be an object")
    published_story = derivatives.get("published_story")
    if not isinstance(published_story, list) or len(published_story) != 2:
        raise RenderError("derivatives.published_story must contain exactly two entries")
    for idx, item in enumerate(published_story):
        if not isinstance(item, dict):
            raise RenderError(f"derivatives.published_story[{idx}] must be an object")
        for key in ("kernel", "role"):
            if not isinstance(item.get(key), str) or not item[key].strip():
                raise RenderError(f"derivatives.published_story[{idx}].{key} must be a non-empty string")
    reference_only = derivatives.get("reference_only")
    if not isinstance(reference_only, list) or len(reference_only) != 1 or not isinstance(reference_only[0], str):
        raise RenderError("derivatives.reference_only must contain exactly one kernel name")
    disputed = derivatives.get("disputed_authorization_claims")
    if not isinstance(disputed, list) or not disputed:
        raise RenderError("derivatives.disputed_authorization_claims must be a non-empty list")
    for idx, item in enumerate(disputed):
        if not isinstance(item, dict):
            raise RenderError(f"derivatives.disputed_authorization_claims[{idx}] must be an object")
        for key in ("claim_id", "display_name"):
            if not isinstance(item.get(key), str) or not item[key].strip():
                raise RenderError(
                    f"derivatives.disputed_authorization_claims[{idx}].{key} must be a non-empty string"
                )
    return data


def _load_registry_index() -> dict[str, dict[str, Any]]:
    try:
        data = yaml.safe_load(CLAIMS_REGISTRY_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RenderError(f"missing claims registry: {CLAIMS_REGISTRY_PATH.relative_to(REPO_ROOT)}") from exc
    except yaml.YAMLError as exc:
        raise RenderError(f"claims registry YAML is invalid: {exc}") from exc
    if not isinstance(data, dict) or not isinstance(data.get("claims"), list):
        raise RenderError("claims registry is malformed")
    out: dict[str, dict[str, Any]] = {}
    for claim in data["claims"]:
        if isinstance(claim, dict) and isinstance(claim.get("id"), str):
            out[claim["id"]] = claim
    return out


def _render_metrics(snapshot: dict[str, Any]) -> str:
    lines: list[str] = []
    for metric in snapshot["metrics"]:
        label = metric["label"]
        value = metric["value"]
        branch = metric.get("branch_coverage")
        if branch:
            lines.append(f"- {label}: `{value}`, `{branch}` branch coverage")
        else:
            lines.append(f"- {label}: `{value}`")
    return "\n".join(lines)


def _render_story(snapshot: dict[str, Any]) -> tuple[str, str]:
    story = snapshot["derivatives"]["published_story"]
    first, second = story
    published = (
        "- The published v1.1 funding-rate formal claim is now the decomposed one:\n"
        f"  `{first['kernel']}` for {first['role']} plus\n"
        f"  `{second['kernel']}` for {second['role']}."
    )
    reference_kernel = snapshot["derivatives"]["reference_only"][0]
    reference = (
        f"- The monolithic `{reference_kernel}` kernel remains useful as a parity/reference artifact, "
        "but it is not part of the published formal release claim."
    )
    return published, reference


def _disputed_entries(snapshot: dict[str, Any], registry_index: dict[str, dict[str, Any]]) -> list[dict[str, str]]:
    disputed: list[dict[str, str]] = []
    for entry in snapshot["derivatives"]["disputed_authorization_claims"]:
        claim = registry_index.get(entry["claim_id"])
        if claim is None:
            raise RenderError(f"missing claim in registry: {entry['claim_id']}")
        if claim.get("status") != "disputed":
            raise RenderError(f"claim is no longer disputed: {entry['claim_id']}")
        disputed.append({"display_name": entry["display_name"], "claim_id": entry["claim_id"]})
    return disputed


def _disputed_sentence(disputed: list[dict[str, str]]) -> str:
    names = [f"`{entry['display_name']}`" for entry in disputed]
    names_text = f"{names[0]} and {names[1]}" if len(names) == 2 else ", ".join(names)
    return (
        f"- {names_text} remain `disputed` in the claims registry for settlement authorization semantics "
        "and should not be treated as authorization-complete public settlement guarantees."
    )


def _glossary_lines() -> str:
    return "\n".join(
        [
            "Release vocabulary:",
            "- `release-backed`: included in the current published formal/public assurance claim",
            "- `public replay`: reproducible from a clean checkout plus the documented external toolchains via the shipped replay/checker surface",
            "- `authorization-complete`: safe to treat as a public settlement-authorizing guarantee without extra trusted environment inputs",
            "- `disputed`: intentionally excluded from stronger public authorization claims until the witness/auth lane is trust-complete",
        ]
    )


def _replace_marked_block(text: str, marker: str, content: str) -> str:
    begin = f"<!-- BEGIN GENERATED:{marker} -->"
    end = f"<!-- END GENERATED:{marker} -->"
    if begin not in text or end not in text:
        raise RenderError(f"missing generated markers for {marker}")
    start = text.index(begin) + len(begin)
    finish = text.index(end)
    return text[:start] + "\n" + content + "\n" + text[finish:]


def _render_readme(snapshot: dict[str, Any], disputed: list[dict[str, str]]) -> str:
    published, reference = _render_story(snapshot)
    return "\n".join(
        [
            f"The pinned release replay for the release tree dated `{snapshot['as_of_date']}` was green:",
            "",
            _render_metrics(snapshot),
            "",
            f"This is historical release evidence for the pinned release tree. It is not a live statement about the current checkout.",
            "For live status on the current checkout, run `python3 tools/permissionless_assurance.py status`.",
            "",
            "Important derivatives note:",
            "",
            published[:-1] + ", both in the release-backed assurance lane.",
            reference,
            _disputed_sentence(disputed),
            "- `python3 tools/permissionless_assurance.py replay zusd` is a public replay lane for zUSD monetary and transport surfaces; it does not upgrade disputed derivatives settlement kernels into release-backed guarantees.",
            "- The bounded TLC/TLA+ claim surface is summarized in [docs/TLA_CLAIM_SUMMARY.md](docs/TLA_CLAIM_SUMMARY.md) and release-checked via `python3 tools/render_tla_claim_summary.py --check`.",
            "",
            _glossary_lines(),
            "",
            "More detail:",
            "- [docs/ASSURANCE_RELEASE_SNAPSHOT.md](docs/ASSURANCE_RELEASE_SNAPSHOT.md)",
            "- [docs/PUBLIC_ASSURANCE_REPLAY.md](docs/PUBLIC_ASSURANCE_REPLAY.md)",
            "- [docs/TLA_CLAIM_SUMMARY.md](docs/TLA_CLAIM_SUMMARY.md)",
            "- [docs/ASSURANCE_GLOSSARY.md](docs/ASSURANCE_GLOSSARY.md)",
            "- [docs/claims_registry.yaml](docs/claims_registry.yaml)",
        ]
    )


def _render_public_replay(snapshot: dict[str, Any], disputed: list[dict[str, str]]) -> str:
    published, reference = _render_story(snapshot)
    return "\n".join(
        [
            f"{snapshot['snapshot_label']} (as of {snapshot['as_of_date']}):",
            "",
            _render_metrics(snapshot),
            "",
            "This is historical release evidence for the pinned release tree, not a live status board for the current checkout.",
            "For live checkout status, use `python3 tools/permissionless_assurance.py status`.",
            "",
            "Current derivatives note:",
            "",
            published,
            reference,
            _disputed_sentence(disputed),
            "- `replay zusd` is a public replay lane for the zUSD monetary core, Tau gating, Tau transfer transport, wallet CLI, and `protocol_token_v1` formal lane. It does not promote disputed derivatives settlement kernels into authorization-complete public guarantees.",
            "- The bounded TLC/TLA+ claim surface is summarized in [docs/TLA_CLAIM_SUMMARY.md](TLA_CLAIM_SUMMARY.md) and release-checked via `python3 tools/render_tla_claim_summary.py --check`.",
            "",
            "Release vocabulary is defined in [docs/ASSURANCE_GLOSSARY.md](ASSURANCE_GLOSSARY.md).",
        ]
    )


def _render_snapshot_doc(snapshot: dict[str, Any], disputed: list[dict[str, str]]) -> str:
    published, reference = _render_story(snapshot)
    claim_ids = ", ".join(f"`{entry['claim_id']}`" for entry in disputed)
    return "\n".join(
        [
            "## Assurance Release Snapshot",
            "",
            "<!-- Generated from docs/assurance_release_snapshot.json and docs/claims_registry.yaml. -->",
            "",
            f"{snapshot['snapshot_label']} (as of {snapshot['as_of_date']}):",
            "",
            _render_metrics(snapshot),
            "",
            "This is historical release evidence for the pinned release tree. It is not a live status board for the current checkout.",
            "For live checkout status, use `python3 tools/permissionless_assurance.py status`.",
            "",
            "### Derivatives Formal Note",
            "",
            published,
            reference,
            _disputed_sentence(disputed),
            f"- The disputed authorization status above is sourced from {claim_ids} in the claims registry.",
            "",
            "### Vocabulary",
            "",
            "- `release-backed` means included in the current published formal/public assurance claim.",
            "- `public replay` means reproducible from a clean checkout plus the documented external toolchains via the shipped replay/checker surface.",
            "- `authorization-complete` means safe to treat as a public settlement-authorizing guarantee without extra trusted environment inputs.",
            "- `disputed` means intentionally excluded from stronger public authorization claims until the witness/auth lane is trust-complete.",
            "",
            "### Replay",
            "",
            "Use the repo-local replay lanes:",
            "",
            "```bash",
            "bash tools/run_derivatives_evidence.sh",
            "bash tools/run_release_gate.sh",
            "```",
            "",
            "### Temporal Surface",
            "",
            "- The bounded TLC/TLA+ claim surface is summarized in [docs/TLA_CLAIM_SUMMARY.md](TLA_CLAIM_SUMMARY.md).",
            "- The release gate fail-closes on `python3 tools/render_tla_claim_summary.py --check` and `python3 tools/run_tla_models.py --json`.",
            "",
        ]
    )


def render_targets() -> dict[Path, str]:
    snapshot = _load_snapshot()
    registry_index = _load_registry_index()
    disputed = _disputed_entries(snapshot, registry_index)
    readme = _replace_marked_block(
        README_PATH.read_text(encoding="utf-8"),
        README_MARKER,
        _render_readme(snapshot, disputed),
    )
    public_replay = _replace_marked_block(
        PUBLIC_REPLAY_PATH.read_text(encoding="utf-8"),
        PUBLIC_REPLAY_MARKER,
        _render_public_replay(snapshot, disputed),
    )
    snapshot_doc = _render_snapshot_doc(snapshot, disputed)
    return {
        README_PATH: readme,
        PUBLIC_REPLAY_PATH: public_replay,
        SNAPSHOT_MD_PATH: snapshot_doc,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Render the public assurance snapshot docs")
    parser.add_argument("--check", action="store_true", help="Fail if generated files are stale")
    parser.add_argument("--write", action="store_true", help="Write generated files")
    args = parser.parse_args(argv)

    if args.check == args.write:
        parser.error("pick exactly one of --check or --write")

    try:
        rendered = render_targets()
    except RenderError as exc:
        print(f"render error: {exc}", file=sys.stderr)
        return 1
    stale: list[Path] = []
    for path, expected in rendered.items():
        current = path.read_text(encoding="utf-8") if path.exists() else ""
        if current != expected:
            stale.append(path)
            if args.write:
                path.write_text(expected, encoding="utf-8")

    if args.check and stale:
        for path in stale:
            print(f"stale: {path.relative_to(REPO_ROOT)}")
        return 1

    if args.write:
        for path in rendered:
            print(path.relative_to(REPO_ROOT))
    else:
        print("ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
