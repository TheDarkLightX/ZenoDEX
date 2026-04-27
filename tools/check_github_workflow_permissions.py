from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence


DEFAULT_WORKFLOW_DIR = Path(".github/workflows")


@dataclass(frozen=True)
class WorkflowPermissionFinding:
    path: str
    reason: str


def _strip_inline_comment(value: str) -> str:
    return value.split("#", 1)[0].strip()


def _top_level_permissions_block(lines: Sequence[str]) -> tuple[int, str, list[str]] | None:
    for idx, raw_line in enumerate(lines):
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if raw_line.startswith((" ", "\t")):
            continue
        if not stripped.startswith("permissions:"):
            continue

        scalar = _strip_inline_comment(stripped[len("permissions:") :])
        block: list[str] = []
        for child in lines[idx + 1 :]:
            child_stripped = child.strip()
            if not child_stripped or child_stripped.startswith("#"):
                continue
            if not child.startswith((" ", "\t")):
                break
            block.append(child)
        return idx + 1, scalar, block
    return None


def _mapping_from_block(block: Iterable[str]) -> dict[str, str]:
    parsed: dict[str, str] = {}
    for raw_line in block:
        stripped = raw_line.strip()
        if ":" not in stripped:
            continue
        key, value = stripped.split(":", 1)
        parsed[key.strip()] = _strip_inline_comment(value)
    return parsed


def workflow_permission_findings(path: Path) -> list[WorkflowPermissionFinding]:
    text = path.read_text(encoding="utf-8")
    block = _top_level_permissions_block(text.splitlines())
    rel_path = str(path)
    if block is None:
        return [
            WorkflowPermissionFinding(
                path=rel_path,
                reason="missing top-level permissions block",
            )
        ]

    line_no, scalar, child_block = block
    if scalar:
        return [
            WorkflowPermissionFinding(
                path=rel_path,
                reason=f"top-level permissions must be a mapping with contents: read (line {line_no})",
            )
        ]

    permissions = _mapping_from_block(child_block)
    findings: list[WorkflowPermissionFinding] = []
    if permissions.get("contents") != "read":
        findings.append(
            WorkflowPermissionFinding(
                path=rel_path,
                reason="top-level permissions must include contents: read",
            )
        )
    for permission, value in sorted(permissions.items()):
        if value == "write" or value == "write-all":
            findings.append(
                WorkflowPermissionFinding(
                    path=rel_path,
                    reason=f"top-level permissions grants write scope: {permission}: {value}",
                )
            )
    return findings


def workflow_paths(workflow_dir: Path) -> list[Path]:
    if workflow_dir.is_file():
        return [workflow_dir]
    paths = [
        path
        for path in workflow_dir.iterdir()
        if path.is_file() and path.suffix in {".yml", ".yaml"}
    ]
    return sorted(paths)


def check_workflows(workflow_dir: Path = DEFAULT_WORKFLOW_DIR) -> list[WorkflowPermissionFinding]:
    findings: list[WorkflowPermissionFinding] = []
    for path in workflow_paths(workflow_dir):
        findings.extend(workflow_permission_findings(path))
    return findings


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Fail when GitHub Actions workflows omit least-privilege token permissions."
    )
    parser.add_argument(
        "--workflow-dir",
        type=Path,
        default=DEFAULT_WORKFLOW_DIR,
        help="Workflow directory or single workflow file to inspect.",
    )
    args = parser.parse_args(argv)

    findings = check_workflows(args.workflow_dir)
    print(
        json.dumps(
            {
                "ok": not findings,
                "finding_count": len(findings),
                "findings": [asdict(finding) for finding in findings],
            },
            indent=2,
            sort_keys=True,
        )
    )
    if findings:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
