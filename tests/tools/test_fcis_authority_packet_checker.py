from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE_PACKET = REPO_ROOT / "docs/specs/fcis_authority_snapshot_v1"


def _copy_packet(tmp_path: Path) -> Path:
    packet = tmp_path / "fcis_authority_snapshot_v1"
    shutil.copytree(SOURCE_PACKET, packet)
    return packet


def _load_ledger(packet: Path) -> dict[str, Any]:
    return json.loads((packet / "requirements.json").read_text(encoding="utf-8"))


def _write_ledger(packet: Path, ledger: dict[str, Any]) -> None:
    (packet / "requirements.json").write_text(
        json.dumps(ledger, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _run_checker(packet: Path) -> tuple[int, dict[str, Any]]:
    completed = subprocess.run(
        [sys.executable, "-B", str(packet / "check_packet.py")],
        cwd=packet,
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.stderr == ""
    return completed.returncode, json.loads(completed.stdout)


def _file_inventory(packet: Path) -> tuple[str, ...]:
    return tuple(
        sorted(
            path.relative_to(packet).as_posix()
            for path in packet.rglob("*")
            if path.is_file() or path.is_symlink()
        )
    )


def test_packet_checker_accepts_clean_packet(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)

    returncode, report = _run_checker(packet)

    assert returncode == 0
    assert report["ok"] is True
    assert report["errors"] == []
    assert report["declared_test_id_count"] == 103
    assert report["referenced_test_id_count"] == 84
    assert report["bound_test_id_count"] == 103


def test_packet_checker_rejects_unbound_mandatory_test(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    ledger = _load_ledger(packet)
    del ledger["test_bindings"]["FCIS-T-COMB-004"]
    _write_ledger(packet, ledger)

    returncode, report = _run_checker(packet)

    assert returncode == 1
    assert report["ok"] is False
    assert report["errors"] == ["TEST_ID_UNBOUND:FCIS-T-COMB-004"]


def test_packet_checker_rejects_unknown_requirement_binding(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    ledger = _load_ledger(packet)
    ledger["test_bindings"]["FCIS-T-COMB-004"] = ["FCIS-477-999"]
    _write_ledger(packet, ledger)

    returncode, report = _run_checker(packet)

    assert returncode == 1
    assert report["ok"] is False
    assert report["errors"] == [
        "TEST_BINDING_REQUIREMENT_UNKNOWN:FCIS-T-COMB-004:FCIS-477-999",
        "TEST_ID_UNBOUND:FCIS-T-COMB-004",
    ]


def test_packet_checker_rejects_nested_undeclared_file(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    rogue = packet / "nested/rogue.md"
    rogue.parent.mkdir()
    rogue.write_text("undeclared\n", encoding="utf-8")

    returncode, report = _run_checker(packet)

    assert returncode == 1
    assert report["ok"] is False
    assert report["errors"] == ["UNDECLARED_PACKET_FILE:nested/rogue.md"]


def test_packet_checker_rejects_generated_python_cache(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    cache_file = packet / "__pycache__/check_packet.cpython-999.pyc"
    cache_file.parent.mkdir(exist_ok=True)
    cache_file.write_bytes(b"generated cache")

    returncode, report = _run_checker(packet)

    assert returncode == 1
    assert report["ok"] is False
    assert report["errors"] == ["UNDECLARED_PACKET_FILE:__pycache__/check_packet.cpython-999.pyc"]


def test_packet_checker_repeat_clean_run_preserves_inventory(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    inventory_before = _file_inventory(packet)

    first_returncode, first_report = _run_checker(packet)
    inventory_after_first = _file_inventory(packet)
    second_returncode, second_report = _run_checker(packet)
    inventory_after_second = _file_inventory(packet)

    assert first_returncode == second_returncode == 0
    assert first_report == second_report
    assert first_report["ok"] is True
    assert first_report["errors"] == []
    assert inventory_after_first == inventory_before
    assert inventory_after_second == inventory_before


def test_packet_checker_rejects_unknown_root_key(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    ledger = _load_ledger(packet)
    ledger["undeclared_policy"] = True
    _write_ledger(packet, ledger)

    returncode, report = _run_checker(packet)

    assert returncode == 1
    assert report["ok"] is False
    assert report["errors"] == ["LEDGER_ROOT_KEYS:undeclared_policy"]


def test_packet_checker_rejects_duplicate_json_member(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    ledger_path = packet / "requirements.json"
    original = ledger_path.read_text(encoding="utf-8")
    ledger_path.write_text(
        original.replace(
            '"schema": "zenodex/fcis-authority-snapshot-requirements/v1",',
            '"schema": "zenodex/fcis-authority-snapshot-requirements/v1",\n'
            '  "schema": "zenodex/fcis-authority-snapshot-requirements/v1",',
            1,
        ),
        encoding="utf-8",
    )

    returncode, report = _run_checker(packet)

    assert returncode == 1
    assert report["ok"] is False
    assert report["errors"] == ["LEDGER_INVALID:DuplicateJsonMember"]


def test_packet_checker_rejects_unknown_pattern_binding(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    ledger = _load_ledger(packet)
    ledger["audit_pattern_bindings"]["cases"]["STATE-ALIAS-001"] = ["FCIS-PAT-UNKNOWN-V1"]
    _write_ledger(packet, ledger)

    returncode, report = _run_checker(packet)

    assert returncode == 1
    assert report["ok"] is False
    assert "PATTERN_BINDING_UNKNOWN:cases:STATE-ALIAS-001:FCIS-PAT-UNKNOWN-V1" in report["errors"]


def test_packet_checker_rejects_design_pattern_document_drift(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    design_path = packet / "DESIGN_PATTERN_AUDIT.md"
    text = design_path.read_text(encoding="utf-8")
    design_path.write_text(
        text.replace(
            "## Pattern FCIS-PAT-CLOSED-ADMISSION-V1",
            "## Removed closed admission pattern",
            1,
        ),
        encoding="utf-8",
    )

    returncode, report = _run_checker(packet)

    assert returncode == 1
    assert report["ok"] is False
    assert "PATTERN_DOC_MISSING:FCIS-PAT-CLOSED-ADMISSION-V1" in report["errors"]


def test_packet_checker_rejects_stale_mutable_core_architecture(tmp_path: Path) -> None:
    packet = _copy_packet(tmp_path)
    contract_path = packet / "COMBINATOR_CONTRACT.md"
    text = contract_path.read_text(encoding="utf-8")
    contract_path.write_text(
        text.replace(
            "## 8. Pure persistent transition",
            "## 8. Scratch conversion",
            1,
        ),
        encoding="utf-8",
    )

    returncode, report = _run_checker(packet)

    assert returncode == 1
    assert report["ok"] is False
    assert report["errors"] == [
        "ARCHITECTURE_CLAUSE_MISSING:COMBINATOR_CONTRACT.md:## 8. Pure persistent transition",
        "STALE_MUTABLE_CORE_CLAUSE:COMBINATOR_CONTRACT.md:## 8. Scratch conversion",
    ]
