#!/usr/bin/env python3
"""Static release-publication workflow guard."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_WORKFLOW = ROOT / ".github" / "workflows" / "release-publish.yml"
REPORT_SCHEMA = "zenodex.release_publication_workflow_check.v0"


REQUIRED_TOKENS = (
    "push:",
    "tags:",
    '"v*"',
    "workflow_dispatch:",
    "actions/upload-artifact@v4",
    "actions/download-artifact@v4",
    "softprops/action-gh-release@v2",
    "docker/login-action@v3",
    "docker/build-push-action@v6",
    "tools/build_operator_release_bundle.py build",
    "tools/build_zenodex_oracle_release.py",
    "build-native-launchers:",
    "cargo build --release -p zenodex-launcher",
    "zenodex-native-launcher-",
    "linux-x86_64",
    "macos-x86_64",
    "windows-x86_64",
    "tools/build_release_sboms.py",
    "npm pack",
    "npm version --no-git-tag-version --allow-same-version",
    "npm publish --access public --provenance --ignore-scripts *.tgz",
    "NPM_TOKEN",
    "SHA256SUMS",
    "zenodex-release-manifest.json",
    "ghcr.io/",
    "Dockerfile.production-hashlocked",
    "Dockerfile.operator-tools",
)


def _top_level_permissions_are_read_only(text: str) -> bool:
    lines = text.splitlines()
    for idx, raw_line in enumerate(lines):
        if raw_line.startswith((" ", "\t")) or raw_line.strip() != "permissions:":
            continue
        block: list[str] = []
        for child in lines[idx + 1 :]:
            if not child.strip() or child.lstrip().startswith("#"):
                continue
            if not child.startswith((" ", "\t")):
                break
            block.append(child.strip())
        return "contents: read" in block and all(
            not item.endswith(": write") for item in block
        )
    return False


def _job_block(text: str, job_name: str) -> str:
    lines = text.splitlines(keepends=True)
    header = f"  {job_name}:\n"
    for index, line in enumerate(lines):
        if line != header:
            continue
        block: list[str] = []
        for child in lines[index + 1 :]:
            if child.strip() and not child.startswith((" ", "\t")):
                break
            block.append(child)
        return "".join(block)
    return ""


def _job_has_permissions(job: str, required: set[str]) -> bool:
    return required <= {line.strip() for line in job.splitlines()}


def _step_block(job: str, step_name: str) -> str:
    lines = job.splitlines(keepends=True)
    header = f"      - name: {step_name}\n"
    for index, line in enumerate(lines):
        if line != header:
            continue
        block: list[str] = []
        for child in lines[index + 1 :]:
            if child.startswith("      - name:"):
                break
            block.append(child)
        return "".join(block)
    return ""


def _npm_token_is_publish_scoped(npm_job: str) -> bool:
    prepare_step = _step_block(npm_job, "Prepare package")
    publish_step = _step_block(npm_job, "Publish package to npm")
    if not prepare_step or not publish_step:
        return False
    if "NODE_AUTH_TOKEN" in prepare_step:
        return False
    required_prepare_commands = ("npm ci", "npm test", "npm pack --ignore-scripts")
    required_publish_tokens = (
        "NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}",
        "npm publish --access public --provenance --ignore-scripts *.tgz",
    )
    return all(
        command in prepare_step for command in required_prepare_commands
    ) and all(token in publish_step for token in required_publish_tokens)


def _workflow_dispatch_input_default(text: str, input_name: str) -> str | None:
    match = re.search(
        rf"^      {re.escape(input_name)}:\n(?P<body>(?:        .*\n?)*)", text, re.M
    )
    if match is None:
        return None
    for raw_line in match.group("body").splitlines():
        stripped = raw_line.strip()
        if stripped.startswith("default:"):
            return stripped.split(":", 1)[1].strip()
    return None


def check_release_publication_workflow(path: Path = DEFAULT_WORKFLOW) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    errors: list[str] = []
    if not path.is_file():
        return {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "errors": [f"missing release publication workflow: {path}"],
            "checks": [],
        }

    text = path.read_text(encoding="utf-8")

    for token in REQUIRED_TOKENS:
        ok = token in text
        checks.append({"id": f"contains:{token}", "ok": ok})
        if not ok:
            errors.append(f"release publication workflow must contain {token}")

    top_permissions_ok = _top_level_permissions_are_read_only(text)
    checks.append({"id": "top_level_permissions_read_only", "ok": top_permissions_ok})
    if not top_permissions_ok:
        errors.append(
            "release publication workflow must keep top-level permissions at contents: read"
        )

    github_release_job = _job_block(text, "publish-github-release")
    containers_job = _job_block(text, "publish-containers")
    npm_job = _job_block(text, "publish-npm")
    job_checks = {
        "publish_github_release_contents_write": (
            github_release_job,
            {"permissions:", "contents: write"},
        ),
        "publish_containers_packages_write": (
            containers_job,
            {"permissions:", "contents: read", "packages: write", "id-token: write"},
        ),
        "publish_npm_manual_id_token": (
            npm_job,
            {"permissions:", "contents: read", "id-token: write"},
        ),
    }
    for check_id, (job, required) in job_checks.items():
        ok = bool(job) and _job_has_permissions(job, required)
        checks.append({"id": check_id, "ok": ok})
        if not ok:
            errors.append(
                f"release publication workflow job permission check failed: {check_id}"
            )

    npm_manual_only = (
        "if: ${{ github.event_name == 'workflow_dispatch' && inputs.publish_npm }}"
        in npm_job
    )
    checks.append({"id": "npm_publish_manual_only", "ok": npm_manual_only})
    if not npm_manual_only:
        errors.append("npm publish must remain manual opt-in")

    npm_token_scoped = _npm_token_is_publish_scoped(npm_job)
    checks.append({"id": "npm_token_publish_scoped", "ok": npm_token_scoped})
    if not npm_token_scoped:
        errors.append("NPM_TOKEN must only be exposed to the minimal npm publish step")

    containers_tag_or_manual = (
        "if: ${{ github.event_name == 'push' || inputs.publish_containers }}"
        in containers_job
    )
    checks.append(
        {"id": "container_publish_tag_or_manual", "ok": containers_tag_or_manual}
    )
    if not containers_tag_or_manual:
        errors.append("container publish must run on tag pushes or manual opt-in")

    manual_defaults = {
        "publish_github_release": "false",
        "publish_containers": "false",
        "publish_npm": "false",
    }
    for input_name, expected in manual_defaults.items():
        actual = _workflow_dispatch_input_default(text, input_name)
        ok = actual == expected
        checks.append(
            {"id": f"manual_default:{input_name}", "ok": ok, "actual": actual}
        )
        if not ok:
            errors.append(
                f"manual workflow_dispatch input {input_name} must default to {expected}"
            )

    forbidden = ("secrets.PRIVATE_KEY", "secrets.PRIVKEY", "secrets.PASSWORD")
    for token in forbidden:
        ok = token not in text
        checks.append({"id": f"forbid:{token}", "ok": ok})
        if not ok:
            errors.append(f"release publication workflow must not reference {token}")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "checks": checks,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workflow", type=Path, default=DEFAULT_WORKFLOW)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)
    report = check_release_publication_workflow(args.workflow)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
