from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_aot_imagination_campaign import build_receipt, generate_candidates


ROOT = Path(__file__).resolve().parents[1]


def test_aot_campaign_generates_exactly_1000_tau_native_candidates() -> None:
    candidates = generate_candidates()

    assert len(candidates) == 1000
    assert {candidate["bounded_model"]["tau_native"] for candidate in candidates} == {True}
    assert {candidate["bounded_model"]["uses_evm_assumptions"] for candidate in candidates} == {False}
    assert all("gas_war" in candidate["bounded_model"]["excluded_assumptions"] for candidate in candidates)


def test_aot_campaign_receipt_is_stable_and_ranked() -> None:
    receipt = build_receipt(top_n=20)

    assert receipt["schema"] == "zenodex.aot_imagination_campaign.v1"
    assert receipt["status"] == "accepted"
    assert receipt["candidate_count"] == 1000
    assert receipt["rejected_evmism_count"] == 0
    assert receipt["dimension_counts"] == {
        "surfaces": 10,
        "axes": 10,
        "adversaries": 5,
        "timings": 2,
    }
    assert len(receipt["top_candidates"]) == 20
    scores = [candidate["scores"]["score"] for candidate in receipt["top_candidates"]]
    assert scores == sorted(scores, reverse=True)
    assert len(receipt["top_promotion_targets"]) == 5
    assert receipt["top_promotion_targets"][0]["atom_id"] == receipt["top_candidates"][0]["atom_id"]
    target_atoms = {
        candidate["atom_id"]: candidate
        for candidate in receipt["top_candidates"]
        + [candidate for candidate in generate_candidates() if candidate["atom_id"] in {row["atom_id"] for row in receipt["top_promotion_targets"]}]
    }
    target_surfaces = {target_atoms[row["atom_id"]]["surface"] for row in receipt["top_promotion_targets"]}
    target_axes = {target_atoms[row["atom_id"]]["axis"] for row in receipt["top_promotion_targets"]}
    assert len(target_surfaces) == 5
    assert len(target_axes) == 5
    assert "does_not_claim_global_tau_lang_solver_complexity_bound" in receipt["not_claimed"]


def test_aot_campaign_cli_writes_json_and_text(tmp_path: Path) -> None:
    output_path = tmp_path / "campaign.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_aot_imagination_campaign.py",
            "--output",
            str(output_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    receipt = json.loads(output_path.read_text(encoding="utf-8"))
    assert receipt["candidate_count"] == 1000

    text = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_aot_imagination_campaign.py",
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert text.returncode == 0, text.stdout + text.stderr
    assert "candidate_count = 1000" in text.stdout
    assert "rejected_evmism_count = 0" in text.stdout
