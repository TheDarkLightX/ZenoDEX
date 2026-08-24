from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_adapter import profile_content_hash  # noqa: E402
from zenodex_oracle_aggregate_adapter import (  # noqa: E402
    aggregate_adapter_content_hash,
    sample_aggregate_adapter_bridge,
    sample_hash,
)
from zenodex_oracle_aggregate_read import (  # noqa: E402
    bridge_content_hash as aggregate_read_content_hash,
)


def _refresh_bridge_id(bridge: dict) -> None:
    bridge["bridge_id"] = aggregate_adapter_content_hash(bridge)


def _refresh_aggregate_read_id(bridge: dict) -> None:
    aggregate_read = bridge["aggregate_read"]
    aggregate_read["bridge_id"] = aggregate_read_content_hash(aggregate_read)


def _refresh_profile_id(bridge: dict) -> None:
    bridge["profile"]["profile_id"] = profile_content_hash(bridge["profile"])


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "aggregate-adapter.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_aggregate_adapter.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_aggregate_adapter_accepts_sample(tmp_path: Path) -> None:
    bridge = sample_aggregate_adapter_bridge()

    code, result = _run_verify(tmp_path, bridge)

    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["consumer_module"] == "zenodex.oracle.sample"
    assert result["action_kind"] == "sample_aggregate_read"
    assert result["value_e8"] == bridge["aggregate_read"]["aggregate"]["aggregate"]["value_e8"]
    assert result["action_epoch"] == bridge["action"]["action_epoch"]
    assert result["errors"] == []


def test_aggregate_adapter_rejects_bridge_hash_forgery(tmp_path: Path) -> None:
    bridge = sample_aggregate_adapter_bridge()
    forged = sample_hash("forged-aggregate-adapter")
    bridge["bridge_id"] = forged
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert f"aggregate_adapter_content_hash_mismatch:{forged}" in result["errors"]


def test_aggregate_adapter_rejects_bad_aggregate_read(tmp_path: Path) -> None:
    bridge = sample_aggregate_adapter_bridge()
    bridge["aggregate_read"]["receipt_bundle"]["receipts"][0]["fresh"] = False
    _refresh_aggregate_read_id(bridge)
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "aggregate_read_not_accepted" in result["errors"]
    assert "aggregate_read:receipt_bundle_not_accepted" in result["errors"]


def test_aggregate_adapter_rejects_action_query_mismatch(tmp_path: Path) -> None:
    bridge = sample_aggregate_adapter_bridge()
    bridge["action"]["query_id"] = sample_hash("wrong-action-query")
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "adapter_not_accepted" in result["errors"]
    assert "adapter:adapter_query_id_mismatch" in result["errors"]


def test_aggregate_adapter_rejects_action_value_mismatch(tmp_path: Path) -> None:
    bridge = sample_aggregate_adapter_bridge()
    bridge["action"]["value_hash"] = sample_hash("wrong-action-value")
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "adapter_not_accepted" in result["errors"]
    assert "adapter:adapter_value_hash_mismatch" in result["errors"]


def test_aggregate_adapter_rejects_profile_weakened_hash_forgery(tmp_path: Path) -> None:
    bridge = sample_aggregate_adapter_bridge()
    bridge["profile"]["max_freshness_window_epochs"] += 1
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert any(error.startswith("adapter:profile_content_hash_mismatch:") for error in result["errors"])


def test_aggregate_adapter_rejects_profile_mismatch(tmp_path: Path) -> None:
    bridge = sample_aggregate_adapter_bridge()
    bridge["profile"]["consumer_module"] = "zenodex.oracle.other"
    _refresh_profile_id(bridge)
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "adapter:profile_consumer_module_mismatch" in result["errors"]


def test_aggregate_adapter_rejects_missing_action(tmp_path: Path) -> None:
    bridge = sample_aggregate_adapter_bridge()
    bridge["action"] = None
    _refresh_bridge_id(bridge)
    code, result = _run_verify(tmp_path, bridge)
    assert code == 2
    assert "action_must_be_object" in result["errors"]


def test_aggregate_adapter_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-aggregate-adapter.json"
    path.write_text('{"padding":"' + ("x" * 3_500_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_aggregate_adapter.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("aggregate_adapter_load_failed:aggregate_adapter_file_too_large:") for error in result["errors"])


def test_aggregate_adapter_sample_cli_emits_verifiable_bridge(tmp_path: Path) -> None:
    path = tmp_path / "aggregate-adapter.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_aggregate_adapter.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_aggregate_adapter.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
