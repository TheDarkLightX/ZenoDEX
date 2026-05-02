from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle import sample_hash  # noqa: E402
from zenodex_oracle_adapter import sample_action_and_bundle  # noqa: E402


def _run_verify(tmp_path: Path, action: dict, bundle: dict) -> tuple[int, dict]:
    action_path = tmp_path / "action.json"
    bundle_path = tmp_path / "bundle.json"
    action_path.write_text(json.dumps(action, indent=2, sort_keys=True), encoding="utf-8")
    bundle_path.write_text(json.dumps(bundle, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_adapter.py",
            "verify",
            "--action",
            str(action_path),
            "--bundle",
            str(bundle_path),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_oracle_adapter_accepts_matching_action_and_bundle(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["consumer_module"] == action["consumer_module"]
    assert result["action_kind"] == action["action_kind"]
    assert result["action_id"] == action["action_id"]
    assert result["query_id"] == action["query_id"]
    assert result["value_hash"] == action["value_hash"]
    assert result["evidence_class"] == "O3"
    assert result["required_evidence_floor"] == "O3"
    assert result["errors"] == []


def test_oracle_adapter_rejects_unaccepted_bundle(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    bundle["receipts"][0]["fresh"] = False
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "oracle_bundle_not_accepted" in result["errors"]
    assert any(error.startswith("bundle:") for error in result["errors"])


def test_oracle_adapter_rejects_consumer_module_mismatch(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["consumer_module"] = "zenodex.perps"
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_consumer_module_mismatch" in result["errors"]


def test_oracle_adapter_rejects_action_kind_mismatch(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["action_kind"] = "liquidate_account"
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_action_kind_mismatch" in result["errors"]


def test_oracle_adapter_rejects_action_id_mismatch(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["action_id"] = sample_hash("other-action")
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_action_id_mismatch" in result["errors"]


def test_oracle_adapter_rejects_action_epoch_mismatch(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["action_epoch"] += 1
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_action_epoch_mismatch" in result["errors"]


def test_oracle_adapter_rejects_query_mismatch(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["query_id"] = sample_hash("other-query")
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_query_id_mismatch" in result["errors"]


def test_oracle_adapter_rejects_value_mismatch(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["value_hash"] = sample_hash("other-value")
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_value_hash_mismatch" in result["errors"]


def test_oracle_adapter_rejects_read_receipt_mismatch(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["read_receipt_id"] = sample_hash("other-read")
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_read_receipt_id_mismatch" in result["errors"]


def test_oracle_adapter_rejects_consumer_action_receipt_mismatch(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["consumer_action_receipt_id"] = sample_hash("other-consumer-action")
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_consumer_action_receipt_id_mismatch" in result["errors"]


def test_oracle_adapter_rejects_evidence_below_action_floor(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["required_evidence_floor"] = "O4"
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_evidence_below_required_floor" in result["errors"]


def test_oracle_adapter_rejects_looser_bundle_freshness_window(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["max_freshness_window_epochs"] = 3
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "adapter_freshness_window_exceeds_action_limit" in result["errors"]


def test_oracle_adapter_rejects_noncritical_action_descriptor(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["critical"] = False
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "action_must_be_critical" in result["errors"]


def test_oracle_adapter_rejects_weak_required_evidence_floor(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["required_evidence_floor"] = "O2"
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "required_evidence_floor_below_critical_minimum" in result["errors"]


def test_oracle_adapter_rejects_hidden_action_field(tmp_path: Path) -> None:
    action, bundle = sample_action_and_bundle()
    action["admin_override"] = True
    code, result = _run_verify(tmp_path, action, bundle)
    assert code == 2
    assert "unknown_action_field:admin_override" in result["errors"]


def test_oracle_adapter_verify_inconclusive_on_oversized_action(tmp_path: Path) -> None:
    action_path = tmp_path / "oversized-action.json"
    bundle_path = tmp_path / "bundle.json"
    _, bundle = sample_action_and_bundle()
    action_path.write_text('{"padding":"' + ("x" * 250_001) + '"}', encoding="utf-8")
    bundle_path.write_text(json.dumps(bundle, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_adapter.py",
            "verify",
            "--action",
            str(action_path),
            "--bundle",
            str(bundle_path),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("adapter_load_failed:action_file_too_large:") for error in result["errors"])


def test_oracle_adapter_sample_cli_emits_verifiable_action_and_bundle(tmp_path: Path) -> None:
    action_path = tmp_path / "sample-action.json"
    bundle_path = tmp_path / "sample-bundle.json"
    sample = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_adapter.py",
            "sample",
            "--action-output",
            str(action_path),
            "--bundle-output",
            str(bundle_path),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_adapter.py",
            "verify",
            "--action",
            str(action_path),
            "--bundle",
            str(bundle_path),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
