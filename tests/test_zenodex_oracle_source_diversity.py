from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_source_diversity import (  # noqa: E402
    sample_source_diversity,
    source_set_content_hash,
)


def _refresh_source_set_id(receipt: dict) -> None:
    receipt["source_set_id"] = source_set_content_hash(receipt)


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "source-diversity.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_source_diversity.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_source_diversity_accepts_sample_receipt(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_source_diversity())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["source_count"] == 3
    assert result["distinct_operator_count"] == 3
    assert result["distinct_venue_count"] == 3
    assert result["distinct_data_family_count"] == 3
    assert result["distinct_transport_count"] == 3
    assert result["distinct_jurisdiction_count"] == 3
    assert result["max_operator_concentration"] == 1
    assert result["max_venue_concentration"] == 1
    assert result["max_data_family_concentration"] == 1
    assert result["max_transport_concentration"] == 1
    assert result["max_jurisdiction_concentration"] == 1
    assert result["errors"] == []


def test_source_diversity_rejects_forged_source_set_id(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    forged_id = receipt["source_set_id"]
    receipt["min_sources"] = 2
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert f"source_set_content_hash_mismatch:{forged_id}" in result["errors"]


def test_source_diversity_rejects_duplicate_source_id(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"][1]["source_id"] = receipt["sources"][0]["source_id"]
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert any(error.startswith("duplicate_source_id:") for error in result["errors"])


def test_source_diversity_rejects_too_few_sources(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"] = receipt["sources"][:2]
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "not_enough_sources" in result["errors"]
    assert "not_enough_distinct_operators" in result["errors"]
    assert "not_enough_distinct_venues" in result["errors"]


def test_source_diversity_rejects_operator_concentration(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"][1]["operator_id"] = receipt["sources"][0]["operator_id"]
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "not_enough_distinct_operators" in result["errors"]
    assert "operator_concentration_exceeds_policy" in result["errors"]


def test_source_diversity_rejects_venue_concentration(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"][1]["venue_id"] = receipt["sources"][0]["venue_id"]
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "not_enough_distinct_venues" in result["errors"]
    assert "venue_concentration_exceeds_policy" in result["errors"]


def test_source_diversity_rejects_data_family_concentration(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"][1]["data_family_id"] = receipt["sources"][0]["data_family_id"]
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "not_enough_distinct_data_families" in result["errors"]
    assert "data_family_concentration_exceeds_policy" in result["errors"]


def test_source_diversity_rejects_transport_concentration(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"][1]["transport_id"] = receipt["sources"][0]["transport_id"]
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "not_enough_distinct_transports" in result["errors"]
    assert "transport_concentration_exceeds_policy" in result["errors"]


def test_source_diversity_rejects_jurisdiction_concentration(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"][1]["jurisdiction_id"] = receipt["sources"][0]["jurisdiction_id"]
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "not_enough_distinct_jurisdictions" in result["errors"]
    assert "jurisdiction_concentration_exceeds_policy" in result["errors"]


def test_source_diversity_rejects_unknown_top_level_field(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["debug_override"] = True
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "unknown_source_diversity_field:debug_override" in result["errors"]


def test_source_diversity_rejects_unknown_source_field(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"][0]["weight_override"] = 99
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "unknown_source_0_field:weight_override" in result["errors"]


def test_source_diversity_rejects_bad_source_token(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"][0]["operator_id"] = "Operator Alpha"
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "operator_id_must_be_token" in result["errors"]


def test_source_diversity_rejects_boolean_threshold(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["min_sources"] = True
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "min_sources_must_be_int_between_1_and_64" in result["errors"]


def test_source_diversity_rejects_sources_not_list(tmp_path: Path) -> None:
    receipt = sample_source_diversity()
    receipt["sources"] = {"source_id": "source.fake"}
    _refresh_source_set_id(receipt)
    code, result = _run_verify(tmp_path, receipt)
    assert code == 2
    assert "sources_must_be_list" in result["errors"]


def test_source_diversity_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-source-diversity.json"
    path.write_text('{"padding":"' + ("x" * 500_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_source_diversity.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(
        error.startswith("source_diversity_load_failed:source_diversity_file_too_large:")
        for error in result["errors"]
    )


def test_source_diversity_sample_cli_emits_verifiable_receipt(tmp_path: Path) -> None:
    path = tmp_path / "source-diversity.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_source_diversity.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_source_diversity.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["distinct_jurisdiction_count"] == 3
