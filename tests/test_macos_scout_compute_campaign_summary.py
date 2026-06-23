from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")


def _write_run(campaign_root: Path, name: str, *, reasons: list[str]) -> None:
    run_dir = campaign_root / name
    run_dir.mkdir()
    (run_dir / "summary.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/macos_derivatives_scout_summary/v1",
                "seed": 20260508,
                "candidates": 16,
                "paths": 4,
                "steps": 8,
                "counterexample_count": len(reasons),
                "zero_disaster_legal_shape_count": 2,
            }
        ),
        encoding="utf-8",
    )
    (run_dir / "regression_gate.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/macos-scout-regression-gate/v1",
                "ok": True,
                "status": "accepted",
            }
        ),
        encoding="utf-8",
    )
    (run_dir / "witness_space_receipt.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/macos-scout-witness-space-receipt/v1",
                "gate": "OPEN_FOR_BOUNDED_RESEARCH",
                "ok": True,
                "stable_receipt_hash": f"sha256:{name}",
            }
        ),
        encoding="utf-8",
    )
    _write_jsonl(
        run_dir / "counterexamples.jsonl",
        [
            {
                "id": index + 1,
                "path": 1,
                "step": index + 1,
                "reason": reason,
            }
            for index, reason in enumerate(reasons)
        ],
    )


def test_summarize_compute_campaign_counts_runs_and_reasons(tmp_path: Path) -> None:
    _write_run(tmp_path, "run_a", reasons=["liquidity_floor_breach_under_oracle_gap"])
    _write_run(
        tmp_path,
        "run_b",
        reasons=["liquidity_floor_breach_under_oracle_gap", "payout_cap_exceeded_initial_budget"],
    )
    (tmp_path / "witness_space_receipt.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/macos-scout-witness-space-receipt/v1",
                "gate": "OPEN_FOR_BOUNDED_RESEARCH",
                "ok": True,
                "reachable_witness_count": 0,
                "stable_receipt_hash": "sha256:campaign",
            }
        ),
        encoding="utf-8",
    )

    result = subprocess.run(
        [sys.executable, "tools/macos_scout/summarize_compute_campaign.py", str(tmp_path)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads((tmp_path / "campaign_summary.json").read_text(encoding="utf-8"))
    assert payload["schema"] == "zenodex/macos-scout-compute-campaign/v1"
    assert payload["run_count"] == 2
    assert payload["accepted_gate_count"] == 2
    assert payload["accepted_witness_count"] == 2
    assert payload["campaign_witness_status"] == "accepted"
    assert payload["campaign_witness_receipt_hash"] == "sha256:campaign"
    assert payload["campaign_reachable_witness_count"] == 0
    assert payload["total_candidates"] == 32
    assert payload["total_counterexamples"] == 3
    assert payload["runs"][0]["witness_receipt_hash"] == "sha256:run_a"
    assert payload["aggregate_reason_counts"] == {
        "liquidity_floor_breach_under_oracle_gap": 2,
        "payout_cap_exceeded_initial_budget": 1,
    }
    review = (tmp_path / "campaign_review.md").read_text(encoding="utf-8")
    assert "MacOS Compute Campaign Review" in review
    assert "Campaign witness receipt: accepted" in review
    assert "Promote no candidate unless it survives at least two seeds" in review
