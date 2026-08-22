from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from tools.check_m6_value_sinks_v1 import (
    check_m6_value_sinks_v1,
    compare_value_sink_inventory_v1,
    load_value_sink_manifest_v1,
    main,
    scan_python_value_sinks_v1,
)

ROOT = Path(__file__).resolve().parents[1]


def test_current_python_value_sinks_are_exhaustively_classified_for_v1() -> None:
    report = check_m6_value_sinks_v1(ROOT)

    assert report["ok"] is True
    assert report["findings"] == []
    assert report["classified_identity_count"] == 13
    assert report["observed_occurrence_count"] == 15
    assert report["release_ready"] is False
    assert report["production_authority"] is False
    assert len(report["release_gaps"]) == 12


def test_arbitrary_function_name_cannot_hide_literal_sql_value_mutation(tmp_path: Path) -> None:
    source = tmp_path / "src" / "rogue.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "def persist_balance_patch(connection):\n"
        "    connection.execute('UPDATE balances SET atoms = 0')\n",
        encoding="utf-8",
    )

    observations = scan_python_value_sinks_v1(tmp_path)

    assert [(item.symbol, item.sink_kind) for item in observations] == [
        ("persist_balance_patch", "SQL_DML")
    ]


def test_arbitrary_sql_mutation_propagates_to_fail_closed_inventory_finding(
    tmp_path: Path,
) -> None:
    source = tmp_path / "src" / "rogue.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "def persist_balance_patch(connection):\n"
        "    connection.execute('UPDATE balances SET atoms = 0')\n",
        encoding="utf-8",
    )

    observations = scan_python_value_sinks_v1(tmp_path)
    findings = compare_value_sink_inventory_v1((), observations)

    assert [finding.rule_id for finding in findings] == [
        "unclassified_value_sink"
    ]
    assert findings[0].evidence == "persist_balance_patch:SQL_DML:1"


def test_import_aliased_atomic_replace_remains_visible(tmp_path: Path) -> None:
    source = tmp_path / "src" / "store.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "from os import replace as install\n"
        "def innocuous_name(source, target):\n"
        "    install(source, target)\n",
        encoding="utf-8",
    )

    observations = scan_python_value_sinks_v1(tmp_path)

    assert [(item.symbol, item.sink_kind) for item in observations] == [
        ("innocuous_name", "OS_REPLACE")
    ]


def test_read_only_sql_does_not_create_a_false_value_sink(tmp_path: Path) -> None:
    source = tmp_path / "src" / "reader.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "def read_balance(connection):\n"
        "    return connection.execute('SELECT atoms FROM balances')\n",
        encoding="utf-8",
    )

    observations = scan_python_value_sinks_v1(tmp_path)

    assert observations == ()


def test_direct_state_publication_is_detected_independent_of_method_name(tmp_path: Path) -> None:
    source = tmp_path / "src" / "integration" / "publisher.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "class Publisher:\n"
        "    def innocuous_name(self, candidate):\n"
        "        self._state = candidate\n",
        encoding="utf-8",
    )

    observations = scan_python_value_sinks_v1(tmp_path)

    assert [(item.symbol, item.sink_kind) for item in observations] == [
        ("Publisher.innocuous_name", "STATE_ATTRIBUTE_ASSIGN")
    ]


def test_manifest_occurrence_drift_fails_closed(tmp_path: Path) -> None:
    del tmp_path
    specs = load_value_sink_manifest_v1()
    observations = scan_python_value_sinks_v1(ROOT)
    mutated_specs = (replace(specs[0], occurrence_count=2), *specs[1:])

    findings = compare_value_sink_inventory_v1(mutated_specs, observations)

    assert [finding.rule_id for finding in findings] == [
        "value_sink_occurrence_mismatch"
    ]
    assert findings[0].path == specs[0].path


def test_manifest_rejects_duplicate_json_keys(tmp_path: Path) -> None:
    path = tmp_path / "manifest.json"
    path.write_text(
        '{"schema":"zenodex/m6-value-sink-inventory/v1","schema":"duplicate"}',
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="duplicate JSON key: schema"):
        load_value_sink_manifest_v1(path)


def test_release_ready_mode_fails_for_research_only_sink_bindings(
    capsys: pytest.CaptureFixture[str],
) -> None:
    exit_code = main(["--root", str(ROOT), "--json", "--require-release-ready"])
    report = json.loads(capsys.readouterr().out)

    assert exit_code == 1
    assert report["ok"] is True
    assert report["release_ready"] is False
    assert report["production_authority"] is False
