from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_adapter import profile_content_hash  # noqa: E402
from zenodex_oracle_consumer_profiles import sample_catalog, sample_hash  # noqa: E402


def _refresh_profile_id(catalog: dict, index: int) -> None:
    profile = catalog["profiles"][index]
    profile["profile_id"] = profile_content_hash(profile)


def _run_verify(tmp_path: Path, catalog: dict) -> tuple[int, dict]:
    catalog_path = tmp_path / "consumer-profiles.json"
    catalog_path.write_text(json.dumps(catalog, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_consumer_profiles.py", "verify", str(catalog_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_consumer_profile_catalog_accepts_sample(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_catalog())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["profile_count"] == 6
    assert result["required_profile_count"] == 6
    assert "zenodex.perps:settle_epoch" in result["profile_keys"]
    assert "zenodex.zusd:mint" in result["profile_keys"]
    assert "zenodex.routing:guarded_quote" in result["profile_keys"]
    assert result["errors"] == []


def test_consumer_profile_catalog_rejects_missing_required_profile(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"] = catalog["profiles"][1:]
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert any(error.startswith("missing_required_profile:") for error in result["errors"])
    assert any(error.startswith("profile_count_mismatch:") for error in result["errors"])


def test_consumer_profile_catalog_rejects_duplicate_profile_key(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"][1] = dict(catalog["profiles"][0])
    catalog["profiles"][1]["profile_id"] = profile_content_hash(catalog["profiles"][1])
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert any(error.startswith("duplicate_profile_key:") for error in result["errors"])


def test_consumer_profile_catalog_rejects_duplicate_profile_id(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"][1]["profile_id"] = catalog["profiles"][0]["profile_id"]
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert any(error.startswith("duplicate_profile_id:") for error in result["errors"])


def test_consumer_profile_catalog_rejects_profile_hash_forgery(tmp_path: Path) -> None:
    catalog = sample_catalog()
    forged_id = catalog["profiles"][0]["profile_id"]
    catalog["profiles"][0]["max_freshness_window_epochs"] += 1
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert f"profile_content_hash_mismatch:{forged_id}" in result["errors"]


def test_consumer_profile_catalog_rejects_unsupported_profile_key(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"][0]["consumer_module"] = "zenodex.unknown"
    _refresh_profile_id(catalog, 0)
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert "unsupported_profile_key:zenodex.unknown:liquidate_account" in result["errors"]


def test_consumer_profile_catalog_rejects_wrong_query(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"][0]["query_id"] = sample_hash("other-query")
    _refresh_profile_id(catalog, 0)
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert any(error.startswith("profile_query_id_mismatch:") for error in result["errors"])


def test_consumer_profile_catalog_rejects_weak_evidence_floor(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"][0]["required_evidence_floor"] = "O2"
    _refresh_profile_id(catalog, 0)
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert "required_evidence_floor_below_critical_minimum" in result["errors"]
    assert any(error.startswith("profile_evidence_floor_below_required:") for error in result["errors"])


def test_consumer_profile_catalog_rejects_loose_freshness(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"][0]["max_freshness_window_epochs"] += 1
    _refresh_profile_id(catalog, 0)
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert any(error.startswith("profile_freshness_window_exceeds_required:") for error in result["errors"])


def test_consumer_profile_catalog_rejects_noncritical_profile(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"][0]["critical"] = False
    _refresh_profile_id(catalog, 0)
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert "profile_must_be_critical:0" in result["errors"]


def test_consumer_profile_catalog_rejects_hidden_profile_field(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"][0]["admin_override"] = True
    _refresh_profile_id(catalog, 0)
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert "unknown_profile_0_field:admin_override" in result["errors"]


def test_consumer_profile_catalog_rejects_wrong_schema(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["schema"] = "zenodex.oracle.consumer_profile_catalog.v0"
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert "catalog_schema_mismatch" in result["errors"]


def test_consumer_profile_catalog_rejects_boolean_freshness(tmp_path: Path) -> None:
    catalog = sample_catalog()
    catalog["profiles"][0]["max_freshness_window_epochs"] = True
    _refresh_profile_id(catalog, 0)
    code, result = _run_verify(tmp_path, catalog)
    assert code == 2
    assert "max_freshness_window_epochs_must_be_int_ge_0" in result["errors"]


def test_consumer_profile_catalog_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-consumer-profiles.json"
    path.write_text('{"padding":"' + ("x" * 500_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_consumer_profiles.py", "verify", str(path)],
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
        error.startswith("consumer_profile_catalog_load_failed:consumer_profile_catalog_file_too_large:")
        for error in result["errors"]
    )


def test_consumer_profile_catalog_sample_cli_emits_verifiable_catalog(tmp_path: Path) -> None:
    path = tmp_path / "sample-consumer-profiles.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_consumer_profiles.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_consumer_profiles.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
