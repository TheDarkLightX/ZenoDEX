from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def _h(tag: str) -> str:
    return "sha256:" + tag.encode("utf-8").hex().ljust(64, "0")[:64]


def _bundle(
    *,
    evidence_class: str = "O3",
    fresh: bool = True,
    dispute_clear: bool = True,
    uncertainty_accepted: bool = True,
    action_query_id: str | None = None,
    action_value_hash: str | None = None,
    emergency_bypass: bool = False,
    include_dependency: bool = True,
) -> dict:
    query_id = _h("query")
    value_hash = _h("value")
    read_id = _h("read")
    action_id = _h("action")
    return {
        "schema": "zenodex.oracle.receipt_bundle.v1",
        "terminal": {
            "read_receipt_id": read_id,
            "consumer_action_receipt_id": action_id,
        },
        "receipts": [
            {
                "id": read_id,
                "type": "accepted_read_receipt",
                "status": "accepted",
                "query_id": query_id,
                "value_hash": value_hash,
                "evidence_class": evidence_class,
                "fresh": fresh,
                "dispute_clear": dispute_clear,
                "uncertainty_accepted": uncertainty_accepted,
                "depends_on": [],
            },
            {
                "id": action_id,
                "type": "consumer_action_receipt",
                "status": "accepted",
                "query_id": action_query_id or query_id,
                "value_hash": action_value_hash or value_hash,
                "read_receipt_id": read_id,
                "critical": True,
                "emergency_oracle_bypass": emergency_bypass,
                "depends_on": [read_id] if include_dependency else [],
            },
        ],
    }


def _run_verify(tmp_path: Path, bundle: dict) -> tuple[int, dict]:
    bundle_path = tmp_path / "bundle.json"
    bundle_path.write_text(json.dumps(bundle, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle.py", "verify", str(bundle_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_zenodex_oracle_verify_accepts_minimal_o3_bundle(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _bundle())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["evidence_class"] == "O3"
    assert result["errors"] == []
    assert "does_not_claim_true_market_price" in result["not_claimed"]


def test_zenodex_oracle_verify_rejects_weak_critical_evidence(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _bundle(evidence_class="O2"))
    assert code == 2
    assert result["ok"] is False
    assert "critical_read_requires_o3_or_higher" in result["errors"]


def test_zenodex_oracle_verify_rejects_open_dispute(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _bundle(dispute_clear=False))
    assert code == 2
    assert "read_dispute_clear_required" in result["errors"]


def test_zenodex_oracle_verify_rejects_consumer_action_value_borrowing(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _bundle(action_value_hash=_h("other-value")))
    assert code == 2
    assert "consumer_action_value_hash_mismatch" in result["errors"]


def test_zenodex_oracle_verify_rejects_emergency_bypass(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _bundle(emergency_bypass=True))
    assert code == 2
    assert "emergency_oracle_bypass_rejected" in result["errors"]


def test_zenodex_oracle_verify_rejects_action_without_read_dependency(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _bundle(include_dependency=False))
    assert code == 2
    assert "consumer_action_must_depend_on_read_receipt" in result["errors"]


def test_zenodex_oracle_verify_rejects_unreachable_receipt(tmp_path: Path) -> None:
    bundle = _bundle()
    bundle["receipts"].append(
        {
            "id": _h("stray"),
            "type": "accepted_read_receipt",
            "status": "accepted",
            "query_id": _h("stray-query"),
            "value_hash": _h("stray-value"),
            "evidence_class": "O3",
            "fresh": True,
            "dispute_clear": True,
            "uncertainty_accepted": True,
            "depends_on": [],
        }
    )
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert any(error.startswith("unreachable_receipt:") for error in result["errors"])


def test_zenodex_oracle_sample_bundle_cli_emits_verifiable_bundle(tmp_path: Path) -> None:
    bundle_path = tmp_path / "sample-bundle.json"
    sample_proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle.py", "sample-bundle", "--output", str(bundle_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample_proc.returncode == 0, sample_proc.stderr
    assert sample_proc.stdout == ""

    verify_proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle.py", "verify", str(bundle_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify_proc.returncode == 0, verify_proc.stderr
    result = json.loads(verify_proc.stdout)
    assert result["status"] == "accepted"
    assert result["evidence_class"] == "O3"
