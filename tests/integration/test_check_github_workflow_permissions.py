from __future__ import annotations

import textwrap
from pathlib import Path

from tools.check_github_workflow_permissions import (
    check_workflows,
    main,
    workflow_permission_findings,
)


def _write_workflow(path: Path, body: str) -> Path:
    path.write_text(textwrap.dedent(body).strip() + "\n", encoding="utf-8")
    return path


def test_accepts_contents_read_mapping(tmp_path: Path) -> None:
    workflow = _write_workflow(
        tmp_path / "ok.yml",
        """
        name: ok
        on: pull_request
        permissions:
          contents: read
        jobs:
          test:
            runs-on: ubuntu-latest
            steps:
              - run: true
        """,
    )
    assert workflow_permission_findings(workflow) == []


def test_rejects_missing_permissions(tmp_path: Path) -> None:
    workflow = _write_workflow(
        tmp_path / "missing.yml",
        """
        name: missing
        on: pull_request
        jobs:
          test:
            runs-on: ubuntu-latest
            steps:
              - run: true
        """,
    )
    findings = workflow_permission_findings(workflow)
    assert len(findings) == 1
    assert "missing top-level permissions" in findings[0].reason


def test_rejects_scalar_permissions(tmp_path: Path) -> None:
    workflow = _write_workflow(
        tmp_path / "scalar.yml",
        """
        name: scalar
        on: pull_request
        permissions: read-all
        jobs:
          test:
            runs-on: ubuntu-latest
            steps:
              - run: true
        """,
    )
    findings = workflow_permission_findings(workflow)
    assert len(findings) == 1
    assert "must be a mapping" in findings[0].reason


def test_rejects_write_scope(tmp_path: Path) -> None:
    workflow = _write_workflow(
        tmp_path / "write.yml",
        """
        name: write
        on: pull_request
        permissions:
          contents: read
          pull-requests: write
        jobs:
          test:
            runs-on: ubuntu-latest
            steps:
              - run: true
        """,
    )
    findings = workflow_permission_findings(workflow)
    assert len(findings) == 1
    assert "write scope" in findings[0].reason


def test_cli_accepts_current_workflows(capsys) -> None:  # type: ignore[no-untyped-def]
    assert main([]) == 0
    captured = capsys.readouterr()
    assert '"ok": true' in captured.out


def test_directory_check_rejects_one_bad_workflow(tmp_path: Path) -> None:
    _write_workflow(
        tmp_path / "ok.yml",
        """
        name: ok
        on: pull_request
        permissions:
          contents: read
        jobs:
          test:
            runs-on: ubuntu-latest
            steps:
              - run: true
        """,
    )
    _write_workflow(
        tmp_path / "bad.yaml",
        """
        name: bad
        on: pull_request
        jobs:
          test:
            runs-on: ubuntu-latest
            steps:
              - run: true
        """,
    )
    findings = check_workflows(tmp_path)
    assert len(findings) == 1
    assert findings[0].path.endswith("bad.yaml")
