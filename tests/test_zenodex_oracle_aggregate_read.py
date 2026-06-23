from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle import receipt_content_hash  # noqa: E402
from zenodex_oracle_aggregate_read import (  # noqa: E402
    bridge_content_hash,
    sample_aggregate_read_bridge,
    sample_hash,
)
from zenodex_oracle_admitted_median3 import aggregate_content_hash  # noqa: E402


def _read(bridge: dict) -> dict:
    return bridge["receipt_bundle"]["receipts"][0]


def _action(bridge: dict) -> dict:
    return bridge["receipt_bundle"]["receipts"][1]


def _refresh_read_action_ids(bridge: dict) -> None:
    read = _read(bridge)
    action = _action(bridge)
    read["id"] = receipt_content_hash(read)
    action["read_receipt_id"] = read["id"]
    action["depends_on"] = [read["id"]]
    action["id"] = receipt_content_hash(action)
    bridge["receipt_bundle"]["terminal"]["read_receipt_id"] = read["id"]
    bridge["receipt_bundle"]["terminal"]["consumer_action_receipt_id"] = action["id"]


def _refresh_bridge_id(bridge: dict) -> None:
    bridge["bridge_id"] = bridge_content_hash(bridge)


def _refresh_aggregate_id(bridge: dict) -> None:
    bridge["aggregate"]["aggregate_id"] = aggregate_content_hash(bridge["aggregate"])


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "aggregate-read.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_aggregate_read.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_aggregate_read_accepts_sample(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_aggregate_read_bridge())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["value_e8"] == 100_000_000
    assert result["confidence_e8"] == 1_000_000
    assert result["deviation_bps"] == 100
    assert result["evidence_class"] == "O3"
    assert result["errors"] == []


def test_aggregate_read_rejects_bridge_hash_forgery(tmp_path: Path) -> None:
    bridge = sample_aggregate_read_bridge()
    forged = sample_hash("forged-aggregate-read")
    bridge["bridge_id"] = forged
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert f"bridge_content_hash_mismatch:{forged}" in result["errors"]


def test_aggregate_read_rejects_rejected_aggregate(tmp_path: Path) -> None:
    bridge = sample_aggregate_read_bridge()
    bridge["aggregate"]["aggregate"]["value_e8"] += 1
    _refresh_aggregate_id(bridge)
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "admitted_aggregate_not_accepted" in result["errors"]
    assert "aggregate:aggregate_value_not_median" in result["errors"]


def test_aggregate_read_rejects_rejected_bundle(tmp_path: Path) -> None:
    bridge = sample_aggregate_read_bridge()
    _read(bridge)["fresh"] = False
    _refresh_read_action_ids(bridge)
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "receipt_bundle_not_accepted" in result["errors"]
    assert "bundle:read_fresh_required" in result["errors"]


def test_aggregate_read_rejects_query_mismatch(tmp_path: Path) -> None:
    bridge = sample_aggregate_read_bridge()
    wrong = sample_hash("wrong-query")
    _read(bridge)["query_id"] = wrong
    _action(bridge)["query_id"] = wrong
    _refresh_read_action_ids(bridge)
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "bundle_query_id_mismatch" in result["errors"]


def test_aggregate_read_rejects_value_hash_mismatch(tmp_path: Path) -> None:
    bridge = sample_aggregate_read_bridge()
    wrong = sample_hash("wrong-value")
    _read(bridge)["value_hash"] = wrong
    _action(bridge)["value_hash"] = wrong
    _refresh_read_action_ids(bridge)
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "bundle_value_hash_mismatch" in result["errors"]


def test_aggregate_read_rejects_observed_epoch_mismatch(tmp_path: Path) -> None:
    bridge = sample_aggregate_read_bridge()
    _read(bridge)["observed_epoch"] += 1
    _refresh_read_action_ids(bridge)
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "bundle_observed_epoch_mismatch" in result["errors"]


def test_aggregate_read_rejects_expiry_mismatch(tmp_path: Path) -> None:
    bridge = sample_aggregate_read_bridge()
    _read(bridge)["expires_at_epoch"] += 1
    _refresh_read_action_ids(bridge)
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "bundle_expiry_mismatch" in result["errors"]


def test_aggregate_read_rejects_bundle_evidence_class_mismatch(tmp_path: Path) -> None:
    bridge = sample_aggregate_read_bridge()
    _read(bridge)["evidence_class"] = "O4"
    _refresh_read_action_ids(bridge)
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "bundle_evidence_class_mismatch" in result["errors"]


def test_aggregate_read_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-aggregate-read.json"
    path.write_text('{"padding":"' + ("x" * 3_000_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_aggregate_read.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("aggregate_read_load_failed:aggregate_read_file_too_large:") for error in result["errors"])


def test_aggregate_read_sample_cli_emits_verifiable_bridge(tmp_path: Path) -> None:
    path = tmp_path / "aggregate-read.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_aggregate_read.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_aggregate_read.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
