from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zeno_oracle_disaster_class_corpus import build_corpus


ROOT = Path(__file__).resolve().parents[1]


def test_named_disaster_class_corpus_closes_requested_classes(tmp_path: Path) -> None:
    receipt = build_corpus(store_root=tmp_path / "stores")

    assert receipt["schema"] == "zenodex.oracle.disaster_class_corpus.v1"
    assert receipt["status"] == "accepted"
    assert receipt["named_disaster_class_count"] == 9
    assert receipt["closed_class_count"] == 9
    assert receipt["failed_class_count"] == 0

    cases = {case["class_id"]: case for case in receipt["cases"]}
    assert set(cases) == {
        "source_cartel",
        "dispute_griefing",
        "settlement_execution_total_drift",
        "registry_drift",
        "verifier_spoofing",
        "o5_independence_spoofing",
        "proof_timeout_treated_as_success",
        "terminal_replay_integrity",
        "cross_module_split_brain",
    }

    assert "operator_concentration_exceeds_policy" in cases["source_cartel"]["observed"]["errors"]
    assert "dispute_bond_required" in cases["dispute_griefing"]["observed"]["errors"]
    assert (
        "receipt:settlement_execution_report_reward_paid_e8_mismatch"
        in cases["settlement_execution_total_drift"]["observed"]["errors"]
    )
    assert any(
        error.startswith("registry_content_hash_mismatch:")
        for error in cases["registry_drift"]["observed"]["errors"]
    )
    assert "verifier_not_registered" in cases["verifier_spoofing"]["observed"]["errors"]
    assert "o5_independence_witness_required" in cases["o5_independence_spoofing"]["observed"]["errors"]
    assert cases["o5_independence_spoofing"]["observed"]["receipt_status"] == "accepted"
    assert cases["o5_independence_spoofing"]["observed"]["proof_status"] == "accepted"
    assert (
        "external_verifier_failed:proof verification timed out"
        in cases["proof_timeout_treated_as_success"]["observed"]["errors"]
    )
    assert cases["proof_timeout_treated_as_success"]["observed"]["proof_ok"] is False
    assert cases["terminal_replay_integrity"]["observed"]["closed_required_replay_states"] == cases[
        "terminal_replay_integrity"
    ]["observed"]["required_replay_states"]
    assert "recovery_divergence_split_brain_rejects" in cases["cross_module_split_brain"]["observed"]["scenario_ids"]


def test_named_disaster_class_corpus_cli_writes_receipt(tmp_path: Path) -> None:
    output = tmp_path / "disaster-class-corpus.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zeno_oracle_disaster_class_corpus.py",
            "--store-root",
            str(tmp_path / "stores"),
            "--output",
            str(output),
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "closed_class_count = 9" in proc.stdout
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["status"] == "accepted"
