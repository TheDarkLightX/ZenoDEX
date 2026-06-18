from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import pytest

import tools.check_batch_auction_ifql_vmo_manifest as checker


def _valid_report(intent_source: Path) -> dict[str, Any]:
    return {
        "ok": True,
        "schema": "esso-intent-report/v1",
        "intent_hash": "intent123",
        "intent_source": str(intent_source),
        "issues": [],
        "stats": {
            "nodes": 9,
            "leaf_nodes": 4,
            "leaf_nodes_mapped": 4,
        },
        "coverage": {
            "required": {
                "ok": True,
            },
        },
    }


def _valid_entry(report_path: Path, intent_source: Path) -> dict[str, Any]:
    return {
        "report_path": str(report_path),
        "intent_hash": "intent123",
        "intent_source": str(intent_source),
        "nodes": 9,
        "leaf_nodes": 4,
        "leaf_nodes_mapped": 4,
        "required_ok": True,
    }


def _write_report(tmp_path: Path, report: dict[str, Any]) -> Path:
    path = tmp_path / "intent_lint.json"
    path.write_text(json.dumps(report, sort_keys=True), encoding="utf-8")
    return path


def test_batch_auction_intent_lint_accepts_strictly_typed_stats(tmp_path: Path) -> None:
    intent_source = tmp_path / "intent.yaml"
    report_path = _write_report(tmp_path, _valid_report(intent_source))

    checker._check_intent_lint(_valid_entry(report_path, intent_source))


@pytest.mark.parametrize(
    ("field", "value", "match"),
    [
        ("nodes", "9", "stats.nodes: expected int"),
        ("leaf_nodes", True, "stats.leaf_nodes: expected int"),
        ("leaf_nodes_mapped", "4", "stats.leaf_nodes_mapped: expected int"),
    ],
)
def test_batch_auction_intent_lint_rejects_coerced_report_stats(
    tmp_path: Path,
    field: str,
    value: object,
    match: str,
) -> None:
    intent_source = tmp_path / "intent.yaml"
    report = _valid_report(intent_source)
    stats = report["stats"]
    assert isinstance(stats, dict)
    stats[field] = value
    report_path = _write_report(tmp_path, report)

    with pytest.raises(checker.ManifestError, match=match):
        checker._check_intent_lint(_valid_entry(report_path, intent_source))


def test_batch_auction_intent_lint_rejects_coerced_expected_stats(tmp_path: Path) -> None:
    intent_source = tmp_path / "intent.yaml"
    report_path = _write_report(tmp_path, _valid_report(intent_source))
    entry = copy.deepcopy(_valid_entry(report_path, intent_source))
    entry["nodes"] = "9"

    with pytest.raises(checker.ManifestError, match="expected nodes: expected int"):
        checker._check_intent_lint(entry)
