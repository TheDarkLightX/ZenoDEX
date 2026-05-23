from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence


DEFAULT_WORKFLOW_DIR = Path(".github/workflows")
ALLOWED_JOB_WRITE_PERMISSIONS = {
    "release-integrity.yml": {
        "release-integrity": {"attestations", "id-token"},
    },
    "release-publish.yml": {
        "publish-github-release": {"contents"},
        "publish-containers": {"id-token", "packages"},
        "publish-npm": {"id-token"},
    },
}


@dataclass(frozen=True)
class WorkflowPermissionFinding:
    path: str
    reason: str


@dataclass(frozen=True)
class _PermissionBlock:
    line_index: int
    line_no: int
    indent: int
    scalar: str
    block: list[str]


def _strip_inline_comment(value: str) -> str:
    return value.split("#", 1)[0].strip()


def _indent(raw_line: str) -> int:
    return len(raw_line) - len(raw_line.lstrip(" \t"))


def _permissions_blocks(lines: Sequence[str]) -> list[_PermissionBlock]:
    blocks: list[_PermissionBlock] = []
    for idx, raw_line in enumerate(lines):
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if not stripped.startswith("permissions:"):
            continue

        scalar = _strip_inline_comment(stripped[len("permissions:") :])
        indent = _indent(raw_line)
        block: list[str] = []
        for child in lines[idx + 1 :]:
            child_stripped = child.strip()
            if not child_stripped or child_stripped.startswith("#"):
                continue
            if _indent(child) <= indent:
                break
            block.append(child)
        blocks.append(_PermissionBlock(idx, idx + 1, indent, scalar, block))
    return blocks


def _top_level_permissions_block(lines: Sequence[str]) -> _PermissionBlock | None:
    for block in _permissions_blocks(lines):
        if block.indent == 0:
            return block
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


def _enclosing_job_id(lines: Sequence[str], block: _PermissionBlock) -> str | None:
    for raw_line in reversed(lines[: block.line_index]):
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if _indent(raw_line) != 2 or not stripped.endswith(":"):
            continue
        key = stripped[:-1].strip()
        if key and key != "jobs":
            return key
    return None


def workflow_permission_findings(path: Path) -> list[WorkflowPermissionFinding]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    block = _top_level_permissions_block(lines)
    rel_path = str(path)
    if block is None:
        return [
            WorkflowPermissionFinding(
                path=rel_path,
                reason="missing top-level permissions block",
            )
        ]

    findings: list[WorkflowPermissionFinding] = []
    if block.scalar:
        return [
            WorkflowPermissionFinding(
                path=rel_path,
                reason=f"top-level permissions must be a mapping with contents: read (line {block.line_no})",
            )
        ]

    permissions = _mapping_from_block(block.block)
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
    allowed_job_writes = ALLOWED_JOB_WRITE_PERMISSIONS.get(path.name, {})
    for nested in _permissions_blocks(lines):
        if nested.indent == 0:
            continue
        job_id = _enclosing_job_id(lines, nested)
        allowed_permissions = allowed_job_writes.get(job_id or "", set())
        if nested.scalar:
            if nested.scalar in {"write-all"} or nested.scalar.endswith("write"):
                findings.append(
                    WorkflowPermissionFinding(
                        path=rel_path,
                        reason=(
                            f"nested permissions grants scalar write scope "
                            f"at line {nested.line_no} in job {job_id or '<unknown>'}: {nested.scalar}"
                        ),
                    )
                )
            continue
        nested_permissions = _mapping_from_block(nested.block)
        for permission, value in sorted(nested_permissions.items()):
            if value == "write" or value == "write-all":
                if permission not in allowed_permissions:
                    findings.append(
                        WorkflowPermissionFinding(
                            path=rel_path,
                            reason=(
                                f"nested permissions grants unapproved write scope "
                                f"at line {nested.line_no} in job {job_id or '<unknown>'}: "
                                f"{permission}: {value}"
                            ),
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
