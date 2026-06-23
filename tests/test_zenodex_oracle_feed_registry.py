from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_feed_registry import content_hash, sample_feed_registry  # noqa: E402
from zenodex_oracle_source_diversity import source_set_content_hash  # noqa: E402


def _refresh_query(feed: dict) -> None:
    feed["query_spec"]["query_id"] = content_hash(feed["query_spec"], omit_key="query_id")


def _refresh_source(feed: dict) -> None:
    feed["source_diversity"]["source_set_id"] = source_set_content_hash(feed["source_diversity"])


def _refresh_policy(feed: dict) -> None:
    feed["aggregate_policy"]["policy_id"] = content_hash(feed["aggregate_policy"], omit_key="policy_id")


def _refresh_feed(feed: dict) -> None:
    feed["feed_id"] = content_hash(feed, omit_key="feed_id")


def _refresh_registry(registry: dict) -> None:
    registry["registry_id"] = content_hash(registry, omit_key="registry_id")


def _refresh_all(registry: dict) -> None:
    for feed in registry["feeds"]:
        _refresh_query(feed)
        feed["source_diversity"]["query_id"] = feed["query_spec"]["query_id"]
        _refresh_source(feed)
        _refresh_policy(feed)
        _refresh_feed(feed)
    _refresh_registry(registry)


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "feed-registry.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_feed_registry.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_feed_registry_accepts_sample_registry(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_feed_registry())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["feed_count"] == 1
    assert result["active_feed_count"] == 1
    assert len(result["feed_ids"]) == 1
    assert len(result["query_ids"]) == 1
    assert result["errors"] == []


def test_feed_registry_accepts_two_distinct_feeds_with_same_policy_shape(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    second_feed = copy.deepcopy(registry["feeds"][0])
    second_feed["query_spec"]["base_asset"] = "wbtc"
    second_feed["query_spec"]["quote_asset"] = "usdc"
    registry["feeds"].append(second_feed)
    _refresh_all(registry)

    code, result = _run_verify(tmp_path, registry)
    assert code == 0
    assert result["status"] == "accepted"
    assert result["feed_count"] == 2
    assert len(set(result["query_ids"])) == 2


def test_feed_registry_rejects_registry_hash_forgery(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    registry_id = registry["registry_id"]
    registry["current_epoch"] = 11
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert f"registry_content_hash_mismatch:{registry_id}" in result["errors"]


def test_feed_registry_rejects_feed_hash_forgery(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    feed_id = registry["feeds"][0]["feed_id"]
    registry["feeds"][0]["created_epoch"] = 9
    _refresh_registry(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert f"feed_content_hash_mismatch:{feed_id}" in result["errors"]


def test_feed_registry_rejects_query_hash_forgery(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    query_id = registry["feeds"][0]["query_spec"]["query_id"]
    registry["feeds"][0]["query_spec"]["base_asset"] = "wbtc"
    _refresh_feed(registry["feeds"][0])
    _refresh_registry(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert f"query_spec_content_hash_mismatch:{query_id}" in result["errors"]


def test_feed_registry_rejects_aggregate_policy_hash_forgery(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    policy_id = registry["feeds"][0]["aggregate_policy"]["policy_id"]
    registry["feeds"][0]["aggregate_policy"]["min_reporters"] = 4
    _refresh_feed(registry["feeds"][0])
    _refresh_registry(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert f"aggregate_policy_content_hash_mismatch:{policy_id}" in result["errors"]


def test_feed_registry_rejects_source_diversity_query_mismatch(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    feed = registry["feeds"][0]
    feed["source_diversity"]["query_id"] = "sha256:" + ("2" * 64)
    _refresh_source(feed)
    _refresh_feed(feed)
    _refresh_registry(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert "source_diversity_query_mismatch" in result["errors"]


def test_feed_registry_rejects_source_diversity_policy_failure(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    feed = registry["feeds"][0]
    feed["source_diversity"]["sources"][1]["operator_id"] = feed["source_diversity"]["sources"][0]["operator_id"]
    _refresh_source(feed)
    _refresh_feed(feed)
    _refresh_registry(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert "source_diversity_rejected" in result["errors"]
    assert "source_diversity:not_enough_distinct_operators" in result["errors"]




def test_feed_registry_rejects_weak_source_diversity_policy_even_when_self_consistent(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    feed = registry["feeds"][0]
    for source in feed["source_diversity"]["sources"]:
        source["operator_id"] = "operator.shared"
        source["venue_id"] = "venue.shared"
        source["data_family_id"] = "data_family.shared"
        source["transport_id"] = "transport.shared"
        source["jurisdiction_id"] = "jurisdiction.shared"

    weak_policy = {
        "min_operators": 1,
        "min_venues": 1,
        "min_data_families": 1,
        "min_transports": 1,
        "min_jurisdictions": 1,
        "max_same_operator": 3,
        "max_same_venue": 3,
        "max_same_data_family": 3,
        "max_same_transport": 3,
        "max_same_jurisdiction": 3,
    }
    feed["source_diversity"].update(weak_policy)

    _refresh_all(registry)
    code, result = _run_verify(tmp_path, registry)

    assert code == 2
    assert "source_diversity_below_feed_min_distinct_operators" in result["errors"]
    assert "source_diversity_above_feed_max_same_operator" in result["errors"]
def test_feed_registry_rejects_duplicate_feed_id(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    registry["feeds"].append(copy.deepcopy(registry["feeds"][0]))
    _refresh_registry(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert any(error.startswith("duplicate_feed_id:") for error in result["errors"])


def test_feed_registry_rejects_duplicate_query_id(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    duplicate = copy.deepcopy(registry["feeds"][0])
    duplicate["created_epoch"] = 9
    _refresh_feed(duplicate)
    registry["feeds"].append(duplicate)
    _refresh_registry(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert any(error.startswith("duplicate_query_id:") for error in result["errors"])


def test_feed_registry_rejects_base_quote_same(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    registry["feeds"][0]["query_spec"]["quote_asset"] = "agrs"
    _refresh_all(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert "base_quote_assets_must_differ" in result["errors"]


def test_feed_registry_rejects_weak_aggregate_policy(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    registry["feeds"][0]["aggregate_policy"]["evidence_floor"] = "O2"
    registry["feeds"][0]["aggregate_policy"]["min_reporters"] = 2
    registry["feeds"][0]["aggregate_policy"]["freshness_window_epochs"] = 0
    registry["feeds"][0]["aggregate_policy"]["max_deviation_bps"] = 10_001
    _refresh_all(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert "evidence_floor_below_critical_minimum" in result["errors"]
    assert "min_reporters_must_be_int_between_3_and_64" in result["errors"]
    assert "freshness_window_epochs_must_be_int_between_1_and_1000000000000" in result["errors"]
    assert "max_deviation_bps_must_be_int_between_0_and_10000" in result["errors"]


def test_feed_registry_rejects_unsupported_schemas(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    registry["feeds"][0]["aggregate_policy"]["aggregation_schema"] = "zenodex.oracle.mean.v1"
    registry["feeds"][0]["aggregate_policy"]["report_schema"] = "zenodex.oracle.raw_report.v1"
    _refresh_all(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert "aggregation_schema_must_be_admitted_median3" in result["errors"]
    assert "report_schema_must_be_signed_report_v1" in result["errors"]


def test_feed_registry_rejects_future_or_inactive_feed(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    registry["feeds"][0]["created_epoch"] = 11
    registry["feeds"][0]["status"] = "paused"
    _refresh_all(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert "feed_created_epoch_in_future" in result["errors"]
    assert "feed_status_must_be_active" in result["errors"]


def test_feed_registry_rejects_hidden_fields(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    registry["governance_override"] = True
    registry["feeds"][0]["admin_override"] = True
    registry["feeds"][0]["query_spec"]["semantic_alias"] = "trusted"
    registry["feeds"][0]["aggregate_policy"]["skip_disputes"] = True
    _refresh_all(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert "unknown_feed_registry_field:governance_override" in result["errors"]
    assert "unknown_feed_field:admin_override" in result["errors"]
    assert "unknown_query_spec_field:semantic_alias" in result["errors"]
    assert "unknown_aggregate_policy_field:skip_disputes" in result["errors"]


def test_feed_registry_rejects_malformed_registry_shape(tmp_path: Path) -> None:
    registry = sample_feed_registry()
    registry["schema"] = "zenodex.oracle.feed_registry.v0"
    registry["current_epoch"] = True
    registry["feeds"] = {"feed_id": "feed.fake"}
    _refresh_registry(registry)
    code, result = _run_verify(tmp_path, registry)
    assert code == 2
    assert "feed_registry_schema_mismatch" in result["errors"]
    assert "current_epoch_must_be_int_between_0_and_1000000000000" in result["errors"]
    assert "feeds_must_be_list" in result["errors"]


def test_feed_registry_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-feed-registry.json"
    path.write_text('{"padding":"' + ("x" * 1_000_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_feed_registry.py", "verify", str(path)],
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
        error.startswith("feed_registry_load_failed:feed_registry_file_too_large:")
        for error in result["errors"]
    )


def test_feed_registry_sample_cli_emits_verifiable_registry(tmp_path: Path) -> None:
    path = tmp_path / "feed-registry.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_feed_registry.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_feed_registry.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["feed_count"] == 1
