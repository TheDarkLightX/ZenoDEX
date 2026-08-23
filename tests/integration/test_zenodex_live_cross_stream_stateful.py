from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_live_cross_stream_stateful_replay_accepts_all_scenarios() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_live_cross_stream_stateful.py", "--format", "json"],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.live_cross_stream_stateful_replay.v1"
    assert receipt["ok"] is True
    assert receipt["scenario_count"] == 9
    assert receipt["accepted_scenario_count"] == receipt["scenario_count"]
    assert receipt["fuzz_campaign"]["ok"] is True
    assert receipt["fuzz_campaign"]["seed_count"] == 4
    assert receipt["fuzz_campaign"]["steps_per_seed"] == 32
    assert receipt["fuzz_campaign"]["accepted_total"] > 0
    assert receipt["fuzz_campaign"]["rejected_total"] > 0
    assert set(receipt["disaster_states"]) == {
        "balance_drift_after_cross_stream_success",
        "duplicate_side_effect_after_replay",
        "cross_stream_partial_mutation",
        "expired_deadline_materializes",
        "perps_overdeposit_materializes",
        "stale_or_missing_oracle_evidence_settles",
        "duplicate_confidential_admission_after_replay",
        "duplicate_confidential_runtime_after_replay",
        "autotrader_ambiguous_send_replayed_or_silently_released",
    }


def test_live_cross_stream_stateful_replay_writes_receipt(tmp_path: Path) -> None:
    output = tmp_path / "live-cross-stream-stateful.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_live_cross_stream_stateful.py",
            "--format",
            "json",
            "--output",
            str(output),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["ok"] is True
    by_id = {scenario["id"]: scenario for scenario in receipt["scenarios"]}
    assert by_id["cross_stream_valid_zusd_bad_perps_is_atomic"]["evidence"]["rejection"] == "unknown market_id"
    assert "nonce invalid" in by_id["duplicate_zusd_mint_replay_rejected_without_side_effect"]["evidence"]["rejection"]
    assert (
        by_id["confidential_live_admission_replay_rejected_without_double_consume"]["evidence"]["replay_rejection"]
        == "request_replay"
    )
    assert (
        by_id["confidential_live_admission_replay_rejected_without_double_consume"]["evidence"][
            "policy_mismatch_rejection"
        ]
        == "policy_digest_mismatch"
    )
    assert (
        by_id["confidential_runtime_execute_replay_rejected_without_double_consume"]["evidence"]["bad_runtime_error"]
        == "execution_id must be a safe token"
    )
    assert (
        by_id["confidential_runtime_execute_replay_rejected_without_double_consume"]["evidence"][
            "retry_after_bad_runtime"
        ]
        == "accepted"
    )
    assert (
        by_id["confidential_runtime_execute_replay_rejected_without_double_consume"]["evidence"][
            "replay_rejection"
        ]
        == "request_replay"
    )
    assert (
        by_id["autotrader_ambiguous_send_quarantined_without_retry"]["evidence"]["first_failure"]
        == "sendtx_failed"
    )
    assert (
        by_id["autotrader_ambiguous_send_quarantined_without_retry"]["evidence"]["state_after_ambiguous_send"]
        == "PENDING"
    )
    assert (
        by_id["autotrader_ambiguous_send_quarantined_without_retry"]["evidence"]["replay_rejection"]
        == "execution_replay"
    )
    assert (
        by_id["autotrader_ambiguous_send_quarantined_without_retry"]["evidence"]["send_attempt_count"]
        == 1
    )
    assert (
        by_id["autotrader_ambiguous_send_quarantined_without_retry"]["evidence"]["accepted_send_count"]
        == 0
    )
    assert receipt["fuzz_campaign"]["errors"] == []
    assert set(receipt["fuzz_campaign"]["disaster_states"]) == {
        "long_horizon_balance_drift",
        "long_horizon_cross_stream_partial_mutation",
        "long_horizon_nonce_replay_materializes",
    }
