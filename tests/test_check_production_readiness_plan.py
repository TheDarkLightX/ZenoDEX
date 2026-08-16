from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

from tools import check_production_readiness_plan as readiness_check

REPO_ROOT = Path(__file__).resolve().parents[1]


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write(tmp_path: Path, name: str, value: dict[str, Any]) -> Path:
    path = tmp_path / name
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def _check(
    *,
    task_graph_path: Path = readiness_check.DEFAULT_TASK_GRAPH,
    coverage_path: Path = readiness_check.DEFAULT_COVERAGE,
    donor_path: Path = readiness_check.DEFAULT_DONORS,
    plan_path: Path = readiness_check.DEFAULT_PLAN,
    readme_path: Path = readiness_check.DEFAULT_README,
) -> dict[str, Any]:
    return readiness_check.check_bundle(
        readiness_check.BundlePaths(
            repo_root=REPO_ROOT,
            plan=plan_path,
            task_graph=task_graph_path,
            coverage=coverage_path,
            donors=donor_path,
            readme=readme_path,
        )
    )


def test_g0_bundle_passes_with_zero_readiness_claims() -> None:
    report = _check()

    assert report["status"] == "PASS"
    assert report["errors"] == []
    assert report["production_ready"] is False
    assert report["counts"]["task_count"] == 9
    assert report["counts"]["complete_task_count"] == 1
    assert report["counts"]["m6_requirements_complete"] == 0
    assert report["counts"]["commands_complete"] == 0
    assert report["counts"]["donor_import_count"] == 0


def test_dependency_cycle_fails_closed(tmp_path: Path) -> None:
    graph = _load(readiness_check.DEFAULT_TASK_GRAPH)
    graph["tasks"][1]["dependencies"] = ["G5"]
    path = _write(tmp_path, "cyclic-task-graph.json", graph)

    report = _check(task_graph_path=path)

    assert report["status"] == "FAIL"
    assert any("cyclic" in error for error in report["errors"])


def test_missing_command_fails_closed(tmp_path: Path) -> None:
    ledger = _load(readiness_check.DEFAULT_COVERAGE)
    ledger["commands"].pop()
    path = _write(tmp_path, "missing-command.json", ledger)

    report = _check(coverage_path=path)

    assert report["status"] == "FAIL"
    assert any("command ids differ" in error for error in report["errors"])


def test_g0_cannot_promote_one_m6_row(tmp_path: Path) -> None:
    ledger = _load(readiness_check.DEFAULT_COVERAGE)
    row = ledger["m6_requirements"][0]
    row.update(
        {
            "formal_status": "PROVED",
            "implementation_status": "IMPLEMENTED",
            "mount_status": "MOUNTED",
            "test_status": "TESTED",
            "promotion_complete": True,
        }
    )
    ledger["promotion_counts"]["m6_requirements_complete"] = 1
    path = _write(tmp_path, "promoted-row.json", ledger)

    report = _check(coverage_path=path)

    assert report["status"] == "FAIL"
    assert any("G0 must remain 0/13" in error for error in report["errors"])


def test_unreviewed_donor_import_fails_closed(tmp_path: Path) -> None:
    inventory = _load(readiness_check.DEFAULT_DONORS)
    candidate = next(
        row
        for row in inventory["candidates"]
        if row["review_status"] == "UNREVIEWED"
    )
    candidate["imported_into_g0"] = True
    inventory["counts"]["imports"] = 1
    path = _write(tmp_path, "unreviewed-import.json", inventory)

    report = _check(donor_path=path)

    assert report["status"] == "FAIL"
    assert any("lacks obligation-sized review" in error for error in report["errors"])


def test_missing_readme_link_fails_closed(tmp_path: Path) -> None:
    readme = readiness_check.DEFAULT_README.read_text(encoding="utf-8")
    readme = readme.replace("docs/PRODUCTION_READINESS_PLAN.md", "docs/REMOVED.md")
    path = tmp_path / "README.md"
    path.write_text(readme, encoding="utf-8")

    report = _check(readme_path=path)

    assert report["status"] == "FAIL"
    assert any("plan link is missing" in error for error in report["errors"])


def test_base_binding_mutation_fails_closed(tmp_path: Path) -> None:
    graph = copy.deepcopy(_load(readiness_check.DEFAULT_TASK_GRAPH))
    graph["base_commit"] = "0" * 40
    path = _write(tmp_path, "wrong-base.json", graph)

    report = _check(task_graph_path=path)

    assert report["status"] == "FAIL"
    assert any("base binding mismatch" in error for error in report["errors"])
