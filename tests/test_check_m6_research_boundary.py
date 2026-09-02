from __future__ import annotations

from pathlib import Path

from tools.check_m6_research_boundary import check_m6_research_boundary, scan_m6_research_file

ROOT = Path(__file__).resolve().parents[1]


def test_current_m6_research_boundary_is_unmounted_and_clean() -> None:
    report = check_m6_research_boundary(ROOT)

    assert report["ok"] is True
    assert report["m6_production_mounted"] is False
    assert report["production_authority"] is False
    assert report["findings"] == []
    assert report["checked_file_count"] > 0


def test_research_boundary_rejects_a_new_production_import(tmp_path: Path) -> None:
    source = tmp_path / "src" / "unsafe_writer.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "from src.integration.m6_durable_store_v1 import M6DurableLedgerStoreV1\n",
        encoding="utf-8",
    )

    findings = scan_m6_research_file(source, root=tmp_path)

    assert [finding.rule_id for finding in findings] == ["research_module_import"]


def test_research_boundary_rejects_package_and_relative_m6_aliases(tmp_path: Path) -> None:
    package_source = tmp_path / "src" / "unsafe_package_import.py"
    package_source.parent.mkdir(parents=True, exist_ok=True)
    package_source.write_text(
        "from src.integration import m6_migration_admission_v1 as migration\n",
        encoding="utf-8",
    )
    relative_source = tmp_path / "src" / "integration" / "unsafe_relative_import.py"
    relative_source.parent.mkdir(parents=True, exist_ok=True)
    relative_source.write_text(
        "from . import m6_migration_admission_v1 as migration\n",
        encoding="utf-8",
    )

    package_findings = scan_m6_research_file(package_source, root=tmp_path)
    relative_findings = scan_m6_research_file(relative_source, root=tmp_path)

    assert [finding.rule_id for finding in package_findings] == ["research_module_import"]
    assert [finding.rule_id for finding in relative_findings] == ["research_module_import"]


def test_research_boundary_rejects_new_m6_symbol_reexport(tmp_path: Path) -> None:
    source = tmp_path / "src" / "unsafe_symbol_reexport.py"
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(
        "from src.integration import M6MigrationVerifiedAdmissionV1\n",
        encoding="utf-8",
    )

    findings = scan_m6_research_file(source, root=tmp_path)

    assert [finding.rule_id for finding in findings] == ["research_symbol_reexport"]
