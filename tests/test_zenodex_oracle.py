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
    observed_epoch: int = 100,
    expires_at_epoch: int = 104,
    consumer_module: str = "zenodex.oracle.sample",
    action_kind: str = "sample_critical_read",
    action_epoch: int = 102,
    freshness_window_epochs: int = 4,
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
                "observed_epoch": observed_epoch,
                "expires_at_epoch": expires_at_epoch,
                "dispute_clear": dispute_clear,
                "uncertainty_accepted": uncertainty_accepted,
                "depends_on": [],
            },
            {
                "id": action_id,
                "type": "consumer_action_receipt",
                "status": "accepted",
                "consumer_module": consumer_module,
                "action_kind": action_kind,
                "action_id": _h("downstream-action"),
                "action_epoch": action_epoch,
                "freshness_window_epochs": freshness_window_epochs,
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


def test_zenodex_oracle_verify_rejects_expired_read_for_action(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _bundle(action_epoch=105))
    assert code == 2
    assert "consumer_action_after_read_expiry" in result["errors"]
    assert "consumer_action_exceeds_freshness_window" in result["errors"]


def test_zenodex_oracle_verify_rejects_action_before_observation(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _bundle(action_epoch=99))
    assert code == 2
    assert "consumer_action_before_read_observation" in result["errors"]


def test_zenodex_oracle_verify_rejects_missing_consumer_identity(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _bundle(consumer_module=""))
    assert code == 2
    assert "consumer_module_must_be_token" in result["errors"]


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


def test_zenodex_oracle_verify_rejects_unsupported_receipt_type(tmp_path: Path) -> None:
    bundle = _bundle()
    support_id = _h("support")
    bundle["receipts"].insert(
        0,
        {
            "id": support_id,
            "type": "unsupported_source_receipt",
            "status": "accepted",
            "depends_on": [],
        },
    )
    bundle["receipts"][2]["depends_on"].append(support_id)
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert f"unsupported_receipt_type:{support_id}" in result["errors"]


def test_zenodex_oracle_verify_rejects_dependency_order_violation(tmp_path: Path) -> None:
    bundle = _bundle()
    bundle["receipts"] = [bundle["receipts"][1], bundle["receipts"][0]]
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert any(error.startswith("dependency_order_violation:") for error in result["errors"])


def test_zenodex_oracle_verify_rejects_dependency_self_reference(tmp_path: Path) -> None:
    bundle = _bundle()
    bundle["receipts"][0]["depends_on"] = [bundle["receipts"][0]["id"]]
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert any(error.startswith("dependency_self_reference:") for error in result["errors"])


def test_zenodex_oracle_verify_rejects_read_dependencies(tmp_path: Path) -> None:
    bundle = _bundle()
    bundle["receipts"][0]["depends_on"] = [bundle["receipts"][1]["id"]]
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert "read_receipt_must_have_no_dependencies" in result["errors"]


def test_zenodex_oracle_verify_rejects_extra_action_dependency(tmp_path: Path) -> None:
    bundle = _bundle()
    extra_id = _h("extra-read")
    bundle["receipts"].insert(
        1,
        {
            "id": extra_id,
            "type": "accepted_read_receipt",
            "status": "accepted",
            "query_id": _h("query"),
            "value_hash": _h("value"),
            "evidence_class": "O3",
            "fresh": True,
            "dispute_clear": True,
            "uncertainty_accepted": True,
            "depends_on": [],
        },
    )
    bundle["receipts"][2]["depends_on"] = [bundle["receipts"][0]["id"], extra_id]
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert "consumer_action_dependency_must_equal_read_receipt" in result["errors"]


def test_zenodex_oracle_verify_rejects_duplicate_action_dependency(tmp_path: Path) -> None:
    bundle = _bundle()
    read_id = bundle["receipts"][0]["id"]
    bundle["receipts"][1]["depends_on"] = [read_id, read_id]
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert any(error.startswith("duplicate_dependency:") for error in result["errors"])
    assert "consumer_action_dependency_must_equal_read_receipt" in result["errors"]


def test_zenodex_oracle_verify_rejects_terminal_id_aliasing(tmp_path: Path) -> None:
    bundle = _bundle()
    bundle["terminal"]["consumer_action_receipt_id"] = bundle["terminal"]["read_receipt_id"]
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert "terminal_receipts_must_be_distinct" in result["errors"]


def test_zenodex_oracle_verify_rejects_unknown_top_level_field(tmp_path: Path) -> None:
    bundle = _bundle()
    bundle["debug_override"] = True
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert "unknown_bundle_field:debug_override" in result["errors"]


def test_zenodex_oracle_verify_rejects_unknown_terminal_field(tmp_path: Path) -> None:
    bundle = _bundle()
    bundle["terminal"]["action_kind"] = "perp_settle"
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert "unknown_terminal_field:action_kind" in result["errors"]


def test_zenodex_oracle_verify_rejects_unknown_read_field(tmp_path: Path) -> None:
    bundle = _bundle()
    bundle["receipts"][0]["source_debug_json"] = {"unchecked": True}
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert "unknown_read_receipt_field:source_debug_json" in result["errors"]


def test_zenodex_oracle_verify_rejects_unknown_action_field(tmp_path: Path) -> None:
    bundle = _bundle()
    bundle["receipts"][1]["skip_oracle_guard"] = False
    code, result = _run_verify(tmp_path, bundle)
    assert code == 2
    assert "unknown_consumer_action_receipt_field:skip_oracle_guard" in result["errors"]


def test_zenodex_oracle_verify_inconclusive_on_oversized_bundle(tmp_path: Path) -> None:
    bundle_path = tmp_path / "oversized-bundle.json"
    bundle_path.write_text('{"padding":"' + ("x" * 1_000_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle.py", "verify", str(bundle_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("bundle_load_failed:bundle_file_too_large:") for error in result["errors"])


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
