from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest

from tools import operator_surface_registry_v2 as registry
from tools.check_operator_surface_registry_v2 import check_operator_surface_registry_v2

ROOT = Path(__file__).resolve().parents[1]


def _git(root: Path, *arguments: str) -> str:
    result = subprocess.run(
        ("git", "-C", str(root), *arguments),
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(
        root,
        "-c",
        "user.name=O004 V2 Test",
        "-c",
        "user.email=o004-v2@example.invalid",
        "commit",
        "-m",
        message,
    )
    return _git(root, "rev-parse", "HEAD")


def _subject_repo(tmp_path: Path) -> Path:
    """Build a small exact Git subject from the bounded V2 source denominator."""

    repo = tmp_path / "subject"
    repo.mkdir()
    _git(repo, "init", "-q")
    for relative_path in registry.SOURCE_PATHS_V2:
        source = ROOT / relative_path
        target = repo / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    _commit(repo, "stage-a operator registry source")
    return repo


def _stage_b_repo(tmp_path: Path) -> tuple[Path, bytes, str]:
    repo = _subject_repo(tmp_path)
    stage_a = _git(repo, "rev-parse", "HEAD")
    payload = registry.build_registry_bytes_v2(repo)
    artifact = repo / registry.ARTIFACT_RELATIVE_PATH_V2
    artifact.parent.mkdir(parents=True, exist_ok=True)
    artifact.write_bytes(payload)
    _commit(repo, "stage-b operator registry artifact")
    return repo, payload, stage_a


def _finding_code(report: dict[str, object]) -> str:
    findings = report["findings"]
    assert type(findings) is list and findings
    finding = findings[0]
    assert type(finding) is dict
    code = finding["code"]
    assert type(code) is str
    return code


def test_stage_a_projection_has_closed_registry_schema(tmp_path: Path) -> None:
    repo = _subject_repo(tmp_path)

    artifact = registry.build_registry_artifact_v2(repo)

    assert artifact["schema"] == registry.SCHEMA_V2
    assert artifact["status"] == "COMPLETE_SOURCE_BOUND_OPERATOR_REFERENCE_REGISTRY"
    assert artifact["closed_gap"] == "operator_documentation_drift"
    assert artifact["authority"] == registry.NO_AUTHORITY_V2
    assert artifact["runtime_test_execution"] == "OUTSIDE_DETERMINISTIC_ARTIFACT"
    assert artifact["vm_gates_closed"] == []
    route_rows = artifact["route_registry"]
    assert type(route_rows) is list
    assert [row["route_id"] for row in route_rows] == list(registry.ROUTE_IDS_V2)
    assert [row["classification"] for row in route_rows] == [
        "MOUNTED_LOCAL_PROFILE",
        "MOUNTED_LOCAL_PROFILE",
        "MOUNTED_LOCAL_PROFILE",
        "QUARANTINED",
        "QUARANTINED",
        "QUARANTINED",
        "QUARANTINED",
    ]
    presentations = artifact["presentation_registry"]
    assert type(presentations) is list
    assert {row["presentation_id"] for row in presentations} == {
        "swap",
        "pools",
        "stats",
        "perps",
        "strategy",
        "zusd",
        "oracle",
        "confidential",
        "governance",
        "proofs",
    }
    keys = next(row for row in presentations if row["presentation_id"] == "governance")
    assert keys["label"] == "Keys"
    assert keys["status"] == "RETAINED_PRESENTATION"
    assert keys["route_ids"] == []
    proofs = next(row for row in presentations if row["presentation_id"] == "proofs")
    assert proofs["visibility"] == "HIDDEN_ROUTE"


def test_stage_b_checker_requires_a_direct_artifact_only_child(tmp_path: Path) -> None:
    repo, payload, stage_a = _stage_b_repo(tmp_path)

    report = check_operator_surface_registry_v2(repo)

    assert report["ok"] is True
    assert report["implementation_subject"] == stage_a
    assert report["artifact_sha256"] == registry.sha256_hex_v2(payload)
    assert report["authority"] == registry.NO_AUTHORITY_V2
    assert report["runtime_test_execution"] == "OUTSIDE_DETERMINISTIC_ARTIFACT"
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True

    (repo / "notes.txt").write_text("harmless descendant\n", encoding="utf-8")
    _commit(repo, "harmless post-artifact descendant")
    report = check_operator_surface_registry_v2(repo)
    assert report["ok"] is True
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True

    config = repo / "tools/dex-ui/public/zenodex-config.json"
    config.write_text(config.read_text(encoding="utf-8") + "\n", encoding="utf-8")
    _commit(repo, "critical source drift after artifact")
    report = check_operator_surface_registry_v2(repo)
    assert report["ok"] is False
    assert _finding_code(report) == "CURRENT_SOURCE_DRIFT"
    assert report["historical_valid"] is True
    assert report["current_applicable"] is False


def test_checker_rejects_missing_artifact_at_stage_a(tmp_path: Path) -> None:
    repo = _subject_repo(tmp_path)

    report = check_operator_surface_registry_v2(repo)

    assert report["ok"] is False
    assert _finding_code(report) == "ARTIFACT_UNAVAILABLE"
    assert report["authority"] == registry.NO_AUTHORITY_V2


def test_checker_rejects_noncanonical_artifact_and_terminal_source_drift(tmp_path: Path) -> None:
    repo, payload, _stage_a = _stage_b_repo(tmp_path)
    artifact = repo / registry.ARTIFACT_RELATIVE_PATH_V2
    artifact.write_text(json.dumps(json.loads(payload), indent=2), encoding="utf-8")

    report = check_operator_surface_registry_v2(repo)
    assert report["ok"] is False
    assert _finding_code(report) == "NONCANONICAL_ARTIFACT"

    artifact.write_bytes(payload)
    config = repo / "tools/dex-ui/public/zenodex-config.json"
    config.write_text(config.read_text(encoding="utf-8") + "\n", encoding="utf-8")
    report = check_operator_surface_registry_v2(repo)
    assert report["ok"] is False
    assert _finding_code(report) == "WORKTREE_SOURCE_DRIFT"


def test_strict_ui_config_rejects_duplicate_keys_and_bool_aliases() -> None:
    duplicate = (
        b'{"perpsWalletUiEnabled":false,"perpsWalletUiEnabled":true,'
        b'"zusdTauWalletUiEnabled":false,"zusdMonetaryWalletUiEnabled":false}'
    )
    with pytest.raises(registry.OperatorSurfaceRegistryRejectV2) as captured:
        registry.project_ui_config_v2(duplicate)
    assert captured.value.code == "JSON_DUPLICATE_KEY"

    alias = (
        b'{"perpsWalletUiEnabled":0,"zusdTauWalletUiEnabled":false,'
        b'"zusdMonetaryWalletUiEnabled":false}'
    )
    with pytest.raises(registry.OperatorSurfaceRegistryRejectV2) as captured:
        registry.project_ui_config_v2(alias)
    assert captured.value.code == "UI_CONFIG_ROUTE_FLAGS"


def test_all_evidence_references_bind_one_top_level_python_test(tmp_path: Path) -> None:
    path = tmp_path / "test_evidence.py"
    path.write_text(
        "def test_once():\n    pass\n\nclass Nested:\n    def test_once(self):\n        pass\n",
        encoding="utf-8",
    )
    registry.validate_evidence_reference_v2(
        {"path": "test_evidence.py", "node_id": "test_once", "evidence_kind": "positive"},
        {"test_evidence.py": path.read_bytes()},
    )
    with pytest.raises(registry.OperatorSurfaceRegistryRejectV2) as captured:
        registry.validate_evidence_reference_v2(
            {"path": "test_evidence.py", "node_id": "missing", "evidence_kind": "positive"},
            {"test_evidence.py": path.read_bytes()},
        )
    assert captured.value.code == "EVIDENCE_AST_NODE"
