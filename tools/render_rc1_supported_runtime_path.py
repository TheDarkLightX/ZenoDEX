#!/usr/bin/env python3
"""Render a checked markdown summary of the conservative RC1 runtime/signing path."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = REPO_ROOT / "tools" / "rc1_scope_manifest.json"
OUTPUT_PATH = REPO_ROOT / "docs" / "RC1_SUPPORTED_RUNTIME_PATH.md"


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


def _release_labels(manifest: dict[str, Any]) -> tuple[str, str]:
    historical = manifest.get("historical_release_label", "RC1")
    active = manifest.get("active_candidate_label", "RC2")
    if not isinstance(historical, str) or not historical.strip():
        raise RenderError("historical_release_label must be a non-empty string")
    if not isinstance(active, str) or not active.strip():
        raise RenderError("active_candidate_label must be a non-empty string")
    return historical, active


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


def _load_runtime_path(manifest: dict[str, Any]) -> dict[str, Any]:
    data = manifest.get("supported_runtime_path")
    if not isinstance(data, dict):
        raise RenderError("supported_runtime_path must be an object")
    return data


def _routes(read_only_http: dict[str, Any], manifest: dict[str, Any]) -> list[str]:
    if bool(read_only_http.get("routes_from_manifest")):
        boundary = manifest.get("supported_http_boundary")
        if not isinstance(boundary, dict):
            raise RenderError("supported_http_boundary must be an object")
        return _string_list(boundary.get("routes"), field="supported_http_boundary.routes")
    return _string_list(read_only_http.get("routes"), field="supported_runtime_path.read_only_http_boundary.routes")


def render_runtime_path_text(*, root: Path = REPO_ROOT, manifest: dict[str, Any] | None = None) -> str:
    manifest_data = manifest if manifest is not None else _load_manifest(root / "tools" / "rc1_scope_manifest.json")
    historical_label, active_label = _release_labels(manifest_data)
    runtime = _load_runtime_path(manifest_data)

    read_only_http = runtime.get("read_only_http_boundary")
    spot_submission = runtime.get("spot_submission_path")
    zusd_wallet = runtime.get("zusd_wallet_transport")
    if not isinstance(read_only_http, dict) or not isinstance(spot_submission, dict) or not isinstance(zusd_wallet, dict):
        raise RenderError("supported_runtime_path entries are malformed")

    http_routes = _routes(read_only_http, manifest_data)
    http_notes = _string_list(read_only_http.get("notes"), field="read_only_http_boundary.notes")
    spot_tests = _string_list(spot_submission.get("tests"), field="spot_submission_path.tests")
    spot_notes = _string_list(spot_submission.get("notes"), field="spot_submission_path.notes")
    spot_commands = _command_list(spot_submission.get("commands"), field="spot_submission_path.commands")
    zusd_tests = _string_list(zusd_wallet.get("tests"), field="zusd_wallet_transport.tests")
    zusd_notes = _string_list(zusd_wallet.get("notes"), field="zusd_wallet_transport.notes")
    zusd_commands = _command_list(zusd_wallet.get("commands"), field="zusd_wallet_transport.commands")

    lines = [
        "---",
        f"title: {active_label}_SUPPORTED_RUNTIME_PATH",
        "type: note",
        "permalink: autonomous-tau-dex-review/docs/rc1-supported-runtime-path",
        "---",
        "",
        f"# {active_label} Candidate Supported Runtime And Signing Path",
        "",
        "<!-- Generated from tools/rc1_scope_manifest.json. -->",
        "",
        f"Historical release baseline: `{historical_label}` already shipped. This file keeps the `RC1_*` path for compatibility, but the live candidate label is `{active_label}`.",
        "",
        "```text",
        "RuntimePathOK := ReadOnlyHTTPBounded ∧ SpotAdmissionPinned ∧ WalletTransportPinned",
        "```",
        "",
        f"Plain reading: the conservative {active_label} runtime claim is only about a narrow HTTP subset, one pinned spot admission/signing path, and the narrow zUSD wallet transport path.",
        "",
        f"Practical consequence: this document does not promote the entire integration shell into {active_label} authority.",
        "",
        "## 1. Read-only HTTP subset",
        "",
        f"- Entrypoint: `{read_only_http.get('file', '')}`",
        "- Supported routes:",
    ]
    lines.extend(f"  - `{route}`" for route in http_routes)
    if http_notes:
        lines.append("- Notes:")
        lines.extend(f"  - {note}" for note in http_notes)

    lines.extend(
        [
            "",
            "## 2. Spot intent admission and signing path",
            "",
            f"- Entrypoint: `{spot_submission.get('entrypoint', '')}`",
            f"- Signing contract: `{spot_submission.get('signing_doc', '')}`",
            f"- Auth-message builder: `{spot_submission.get('auth_message_path', '')}`",
            f"- Nonce and sequence state: `{spot_submission.get('nonce_state_path', '')}`",
            "",
            "```text",
            "IntentAccepted -> CanonicalSigningPayloadVerified ∧ NonceBatchAccepted ∧ PreconditionsHold",
            "```",
            "",
            "Plain reading: spot admission accepts an intent batch only after canonical signing payload verification, nonce-batch validation, and ordinary precondition checks succeed.",
            "",
            f"Practical consequence: {active_label} should describe one exact signing and nonce path, not a mix of alternative ingress behaviors.",
            "",
            "- Replay command:",
        ]
    )
    lines.extend(f"  - `{' '.join(command)}`" for command in spot_commands)
    lines.append("- Coverage tests:")
    lines.extend(f"  - `{path}`" for path in spot_tests)
    if spot_notes:
        lines.append("- Notes:")
        lines.extend(f"  - {note}" for note in spot_notes)

    lines.extend(
        [
            "",
            "## 3. zUSD Tau wallet transport",
            "",
            f"- Doc: `{zusd_wallet.get('doc', '')}`",
            f"- CLI: `{zusd_wallet.get('cli', '')}`",
            "- Replay command:",
        ]
    )
    lines.extend(f"  - `{' '.join(command)}`" for command in zusd_commands)
    lines.append("- Coverage tests:")
    lines.extend(f"  - `{path}`" for path in zusd_tests)
    if zusd_notes:
        lines.append("- Notes:")
        lines.extend(f"  - {note}" for note in zusd_notes)

    lines.extend(
        [
            "",
            "## Release Hooks",
            "",
            "- `python3 tools/check_tau_supported_runtime_subset.py`",
            "- `python3 tools/check_production_boundary.py`",
            "- `python3 tools/render_rc1_supported_runtime_path.py --check`",
            "- `python3 tools/rc1_readiness.py --check`",
            "- `python3 tools/rc1_candidate.py --plan`",
            "",
        ]
    )
    return "\n".join(lines)


def runtime_path_status(*, root: Path = REPO_ROOT, manifest: dict[str, Any] | None = None) -> dict[str, Any]:
    try:
        expected = render_runtime_path_text(root=root, manifest=manifest) + "\n"
    except RenderError as exc:
        return {
            "ok": False,
            "path": str((root / "docs" / "RC1_SUPPORTED_RUNTIME_PATH.md").relative_to(root)),
            "error": str(exc),
        }
    output_path = root / "docs" / "RC1_SUPPORTED_RUNTIME_PATH.md"
    current = output_path.read_text(encoding="utf-8") if output_path.exists() else ""
    return {
        "ok": current == expected,
        "path": str(output_path.relative_to(root)),
        "error": None,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Render a checked summary of the conservative RC1 runtime/signing path.")
    parser.add_argument("--check", action="store_true", help="fail if the generated summary is stale")
    args = parser.parse_args(argv)

    try:
        rendered = render_runtime_path_text() + "\n"
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
                "error: generated RC1 supported runtime path is stale; "
                "run `python3 tools/render_rc1_supported_runtime_path.py`"
            )
            return 1
        return 0

    OUTPUT_PATH.write_text(rendered, encoding="utf-8")
    print(f"wrote {OUTPUT_PATH.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
