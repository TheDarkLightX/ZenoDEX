from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_feed_registry_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_feed_registry_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 26
    assert receipt["rejected_case_count"] == 26
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "registry_hash_forgery_survives" in names
    assert "feed_hash_forgery_survives" in names
    assert "query_hash_forgery_survives" in names
    assert "aggregate_policy_hash_forgery_survives" in names
    assert "source_diversity_hash_forgery_survives" in names
    assert "duplicate_feed_id_survives" in names
    assert "duplicate_query_id_survives" in names
    assert "base_quote_same_survives" in names
    assert "weak_min_reporters_survives" in names
    assert "weak_min_sources_survives" in names
    assert "zero_freshness_survives" in names
    assert "excessive_deviation_survives" in names
    assert "weak_evidence_floor_survives" in names
    assert "unsupported_aggregate_policy_survives" in names
    assert "unsupported_report_schema_survives" in names
    assert "source_query_mismatch_survives" in names
    assert "source_operator_correlation_survives" in names
    assert "future_created_feed_survives" in names
    assert "inactive_feed_survives" in names
    assert "hidden_registry_field_survives" in names
    assert "hidden_feed_field_survives" in names
    assert "hidden_query_field_survives" in names
    assert "hidden_policy_field_survives" in names
    assert "wrong_registry_schema_survives" in names
    assert "feeds_as_object_survives" in names
    assert "boolean_current_epoch_survives" in names


def test_zenodex_oracle_feed_registry_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-feed-registry-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_feed_registry_chaos.py",
            "--output",
            str(output),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == ""
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["schema"] == "zenodex.oracle.feed_registry_chaos_replay.v1"
    assert receipt["ok"] is True
