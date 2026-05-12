from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_zeno_oracle_disaster_frontier import (
    _build_live_inputs,
    check_frontier,
    frontier_content_hash,
    sample_frontier,
)


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tools" / "zeno_oracle_disaster_obligation_certificate_manifest.json"


def _refresh_id(frontier: dict[str, object]) -> None:
    frontier["frontier_id"] = frontier_content_hash(frontier)


def _fake_receipts(frontier: dict[str, object]) -> tuple[dict[str, object], dict[str, object]]:
    families = frontier["families"]
    assert isinstance(families, list)
    devnet_cases = []
    corpus_cases = []
    for family in families:
        assert isinstance(family, dict)
        if family.get("devnet_disaster_state"):
            devnet_cases.append({"disaster_state": family["devnet_disaster_state"], "ok": True})
        if family.get("corpus_class_id"):
            corpus_cases.append({"class_id": family["corpus_class_id"], "ok": True})
    return {"cases": corpus_cases}, {"cases": devnet_cases}


def test_disaster_frontier_accepts_sample_against_live_public_evidence() -> None:
    manifest, corpus_receipt, harness_receipt = _build_live_inputs(MANIFEST)

    result = check_frontier(
        sample_frontier(),
        manifest=manifest,
        corpus_receipt=corpus_receipt,
        harness_receipt=harness_receipt,
    )

    assert result["schema"] == "zenodex.oracle.production_disaster_frontier_check.v1"
    assert result["status"] == "accepted"
    assert result["frontier_family_count"] == 29
    assert result["closed_family_count"] == 24
    assert result["blocked_or_backlog_count"] == 5
    assert result["new_obligation_family_count"] == 0
    assert result["error_count"] == 0
    blockers = {item["family_id"] for item in result["closure_blockers"]}
    assert "cross_domain_finality_reorg_feeds_oracle_read" in blockers
    assert "does_not_claim_exhaustive_production_disaster_search" in result["not_claimed"]
    frontier = sample_frontier()
    settlement_drift_family = next(
        family for family in frontier["families"] if family["family_id"] == "settlement_execution_total_drift"
    )
    assert settlement_drift_family["corpus_class_id"] == "settlement_execution_total_drift"
    assert "python3 tools/zeno_oracle_disaster_class_corpus.py --format text" in settlement_drift_family["replay_commands"]
    snapshot_family = next(
        family for family in frontier["families"] if family["family_id"] == "oracle_settlement_without_usable_snapshot"
    )
    assert "python3 tools/check_zeno_oracle_perps_snapshot_gate.py --format text" in snapshot_family["replay_commands"]
    assert "perps_snapshot_theorem_is_restricted_to_usability_obligations" in snapshot_family["blockers"]
    finality_family = next(
        family for family in frontier["families"] if family["family_id"] == "cross_domain_finality_reorg_feeds_oracle_read"
    )
    assert "python3 tools/check_zeno_oracle_cross_domain_finality_gate.py --format text" in finality_family["replay_commands"]
    assert "cross_domain_finality_gate_is_local_receipt_replay_not_live" in finality_family["blockers"]
    reporter_soak_family = next(
        family for family in frontier["families"] if family["family_id"] == "public_reporter_cartel_after_soak_window"
    )
    assert "python3 tools/check_zeno_oracle_reporter_soak_gate.py --format text" in reporter_soak_family["replay_commands"]
    assert "reporter_soak_gate_is_local_observation_replay_not_public_soak" in reporter_soak_family["blockers"]
    governance_family = next(
        family for family in frontier["families"] if family["family_id"] == "onchain_governance_timelock_bypass"
    )
    assert "python3 tools/check_zeno_oracle_production_network_config.py --format text" in governance_family["replay_commands"]
    assert "feed_governance_execution_gate_is_local_receipt_replay_not_live" in governance_family["blockers"]
    live_escrow_family = next(
        family for family in frontier["families"] if family["family_id"] == "live_escrow_shortfall_blocks_reporter_payout"
    )
    assert "python3 tools/check_zeno_oracle_live_economics_policy.py --format text" in live_escrow_family["replay_commands"]
    assert "settlement_execution_receipt_not_verified_onchain" in live_escrow_family["blockers"]


def test_disaster_frontier_rejects_closed_family_without_devnet_evidence() -> None:
    frontier = sample_frontier()
    families = frontier["families"]
    assert isinstance(families, list)
    first = families[0]
    assert isinstance(first, dict)
    first["devnet_disaster_state"] = "missing_state"
    _refresh_id(frontier)
    corpus_receipt, harness_receipt = _fake_receipts(frontier)
    harness_receipt["cases"] = []

    result = check_frontier(
        frontier,
        manifest=json.loads(MANIFEST.read_text(encoding="utf-8")),
        corpus_receipt=corpus_receipt,
        harness_receipt=harness_receipt,
    )

    assert result["status"] == "rejected"
    assert "missing_devnet_disaster_state:accepted_read_without_accepted_aggregate:missing_state" in result["errors"]


def test_disaster_frontier_rejects_closed_family_with_unblocked_new_obligation() -> None:
    frontier = sample_frontier()
    families = frontier["families"]
    assert isinstance(families, list)
    first = families[0]
    assert isinstance(first, dict)
    obligations = first["manifest_obligations"]
    assert isinstance(obligations, list)
    obligations.append("bridge_attestation")
    _refresh_id(frontier)
    corpus_receipt, harness_receipt = _fake_receipts(frontier)

    result = check_frontier(
        frontier,
        manifest=json.loads(MANIFEST.read_text(encoding="utf-8")),
        corpus_receipt=corpus_receipt,
        harness_receipt=harness_receipt,
    )

    assert result["status"] == "rejected"
    assert (
        "new_obligation_without_blocker:accepted_read_without_accepted_aggregate:bridge_attestation"
        in result["errors"]
    )


def test_disaster_frontier_cli_sample_and_require_closed(tmp_path: Path) -> None:
    sample = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_disaster_frontier.py",
            "--sample-frontier",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0
    frontier_path = tmp_path / "disaster-frontier.json"
    frontier_path.write_text(sample.stdout, encoding="utf-8")

    accepted = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_disaster_frontier.py",
            "--frontier",
            str(frontier_path),
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert accepted.returncode == 0, accepted.stdout + accepted.stderr
    assert "status = accepted" in accepted.stdout
    assert "blocked_or_backlog_count = 5" in accepted.stdout

    require_closed = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_disaster_frontier.py",
            "--frontier",
            str(frontier_path),
            "--require-closed",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert require_closed.returncode == 1
    receipt = json.loads(require_closed.stdout)
    assert receipt["status"] == "rejected"
    assert "frontier_blockers_present" in receipt["errors"]
