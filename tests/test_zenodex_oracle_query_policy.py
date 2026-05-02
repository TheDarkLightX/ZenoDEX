from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_query_policy import content_hash, sample_hash, sample_policy_trace  # noqa: E402


def _refresh_policy_id(trace: dict, event_index: int) -> None:
    policy = trace["events"][event_index]["policy"]
    policy["policy_id"] = content_hash(policy, omit_key="policy_id")


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "query-policy.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_query_policy.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_query_policy_accepts_sample_trace(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_policy_trace())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["active_policy_version"] == 2
    assert result["published_policy_count"] == 2
    assert result["bound_consumer_count"] == 1
    assert result["errors"] == []


def test_query_policy_rejects_staleness_downgrade(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["max_staleness_epochs"] = 5
    _refresh_policy_id(trace, 2)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "policy_staleness_downgrade" in result["errors"]


def test_query_policy_rejects_deviation_downgrade(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["max_deviation_bps"] = 250
    _refresh_policy_id(trace, 2)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "policy_deviation_downgrade" in result["errors"]


def test_query_policy_rejects_evidence_floor_downgrade(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["evidence_floor"] = "O2"
    _refresh_policy_id(trace, 2)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "evidence_floor_below_critical_minimum" in result["errors"]
    assert "policy_evidence_floor_downgrade" in result["errors"]


def test_query_policy_rejects_source_quorum_downgrade(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["min_distinct_sources"] = 2
    _refresh_policy_id(trace, 2)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "policy_source_quorum_downgrade" in result["errors"]


def test_query_policy_rejects_reporter_quorum_downgrade(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["min_distinct_reporters"] = 2
    _refresh_policy_id(trace, 2)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "policy_reporter_quorum_downgrade" in result["errors"]


def test_query_policy_rejects_schema_drift(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["aggregation_schema"] = "zenodex.oracle.mean3_aggregate.v1"
    _refresh_policy_id(trace, 2)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "policy_aggregation_schema_change" in result["errors"]


def test_query_policy_rejects_policy_content_hash_mismatch(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    forged_policy_id = trace["events"][0]["policy"]["policy_id"]
    trace["events"][0]["policy"]["max_staleness_epochs"] = 7
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert f"policy_content_hash_mismatch:{forged_policy_id}" in result["errors"]


def test_query_policy_rejects_policy_query_mismatch(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][0]["policy"]["query_id"] = sample_hash("other-query")
    _refresh_policy_id(trace, 0)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "policy_query_id_mismatch" in result["errors"]


def test_query_policy_rejects_wrong_supersedes(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["supersedes_policy_id"] = sample_hash("wrong-policy")
    _refresh_policy_id(trace, 2)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "policy_supersedes_must_equal_active_policy" in result["errors"]


def test_query_policy_rejects_version_skip(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["version"] = 3
    _refresh_policy_id(trace, 2)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "policy_version_must_increment_by_1" in result["errors"]


def test_query_policy_rejects_unknown_policy_binding(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][1]["policy_id"] = sample_hash("missing-policy")
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "consumer_binds_unknown_policy" in result["errors"]


def test_query_policy_rejects_nonlatest_policy_binding(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    publish_v2 = trace["events"][2]
    bind_v1 = trace["events"][1]
    publish_v2["epoch"] = 2
    bind_v1["epoch"] = 3
    bind_v1["action_epoch"] = 3
    trace["events"] = [trace["events"][0], publish_v2, bind_v1]
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "consumer_binds_nonlatest_policy" in result["errors"]


def test_query_policy_rejects_noncritical_binding(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][1]["critical"] = False
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "consumer_binding_must_be_critical" in result["errors"]


def test_query_policy_rejects_action_before_binding(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][1]["action_epoch"] = 1
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "consumer_action_before_policy_binding" in result["errors"]


def test_query_policy_rejects_hidden_policy_field(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][0]["policy"]["admin_override"] = True
    _refresh_policy_id(trace, 0)
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "unknown_policy_field:admin_override" in result["errors"]


def test_query_policy_rejects_hidden_event_field(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][1]["admin_override"] = True
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "unknown_event_bind_consumer_field:admin_override" in result["errors"]


def test_query_policy_rejects_epoch_regression(tmp_path: Path) -> None:
    trace = sample_policy_trace()
    trace["events"][2]["epoch"] = 0
    code, result = _run_verify(tmp_path, trace)
    assert code == 2
    assert "event_epoch_regression:2" in result["errors"]


def test_query_policy_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-query-policy.json"
    path.write_text('{"padding":"' + ("x" * 250_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_query_policy.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("query_policy_load_failed:query_policy_file_too_large:") for error in result["errors"])


def test_query_policy_sample_cli_emits_verifiable_trace(tmp_path: Path) -> None:
    path = tmp_path / "sample-query-policy.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_query_policy.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_query_policy.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["active_policy_version"] == 2
