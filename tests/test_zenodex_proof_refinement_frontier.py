from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_proof_refinement_frontier import (
    build_receipt,
    generate_candidates,
)


ROOT = Path(__file__).resolve().parents[1]


def test_proof_frontier_materializes_1000_zendex_atoms() -> None:
    candidates = generate_candidates()

    assert len(candidates) == 1000
    assert len({candidate["candidate_id"] for candidate in candidates}) == 1000
    assert len({candidate["atom_id"] for candidate in candidates}) == 1000
    assert {candidate["atom_type"] for candidate in candidates} == {"hypothesis"}
    assert {candidate["thought_iteration_index"] for candidate in candidates} == set(range(1, 1001))
    assert all(candidate["dependencies"] for candidate in candidates)
    assert all(candidate["dependencies"][0] == "ZDX-PRF-P0" for candidate in candidates)
    assert all(candidate["is_verified"] is False for candidate in candidates)
    assert all(0.25 <= candidate["confidence"] <= 0.82 for candidate in candidates)
    assert {candidate["status"] for candidate in candidates} == {"hypothesis"}
    assert {candidate["binding_mode"] for candidate in candidates} == {"model_anchor", "runtime_bound"}
    assert all(candidate["first_falsifier"] for candidate in candidates)
    assert all(candidate["evidence_command"] for candidate in candidates)
    assert all(candidate["artifact_paths"] for candidate in candidates)


def test_proof_frontier_dimensions_are_stable() -> None:
    receipt = build_receipt(top_n=25, promotion_n=10)

    assert receipt["schema"] == "zenodex.proof_refinement_frontier.v1"
    assert receipt["status"] == "accepted"
    assert receipt["aot_contract"]["root_atom"]["atom_id"] == "ZDX-PRF-P0"
    assert receipt["aot_contract"]["candidate_atom_type"] == "hypothesis"
    assert receipt["atom_iteration_count"] == 1000
    assert receipt["candidate_count"] == 1000
    assert receipt["dimension_counts"] == {
        "lanes": 10,
        "gap_classes": 10,
        "methods": 5,
        "binding_modes": 2,
    }
    assert set(receipt["lane_counts"].values()) == {100}
    assert set(receipt["gap_counts"].values()) == {100}
    assert set(receipt["method_counts"].values()) == {200}
    assert set(receipt["binding_counts"].values()) == {500}


def test_proof_frontier_ranking_and_diverse_promotion_queue() -> None:
    receipt = build_receipt(top_n=25, promotion_n=10)

    priorities = [candidate["scores"]["priority"] for candidate in receipt["top_candidates"]]
    assert priorities == sorted(priorities, reverse=True)
    assert len(receipt["top_promotion_targets"]) == 10

    lanes = {target["lane"] for target in receipt["top_promotion_targets"]}
    gaps = {target["gap_class"] for target in receipt["top_promotion_targets"]}
    assert len(lanes) == 10
    assert len(gaps) == 10
    assert {
        "settlement_certificate_verifier",
        "routing_exact_out_completeness",
        "perps_margin_funding_liquidation",
        "batch_upba_settlement",
        "cpmm_kernel_integer_math",
    }.issubset(lanes)
    assert "runtime_binding" in gaps
    assert "candidate_generator_completeness" in gaps
    assert "integer_rounding_bridge" in gaps


def test_proof_frontier_non_claims_prevent_overpromotion() -> None:
    receipt = build_receipt(top_n=10, promotion_n=5)

    assert "does_not_claim_1000_items_are_1000_verified_theorems" in receipt["not_claimed"]
    assert "does_not_claim_exhaustive_zenodex_safety" in receipt["not_claimed"]
    assert "does_not_claim_upba_is_deployed" in receipt["not_claimed"]
    assert all(
        "does_not_claim_1000_items_are_1000_verified_theorems" in candidate["non_claims"]
        for candidate in receipt["top_candidates"]
    )


def test_proof_frontier_can_emit_all_1000_ranked_candidates() -> None:
    receipt = build_receipt(top_n=10, promotion_n=5, include_candidates=True)

    assert "all_candidates" in receipt
    assert len(receipt["all_candidates"]) == 1000
    priorities = [candidate["scores"]["priority"] for candidate in receipt["all_candidates"]]
    assert priorities == sorted(priorities, reverse=True)


def test_proof_frontier_cli_outputs_json_text_and_markdown(tmp_path: Path) -> None:
    output_path = tmp_path / "frontier.json"
    json_proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_proof_refinement_frontier.py",
            "--output",
            str(output_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert json_proc.returncode == 0, json_proc.stdout + json_proc.stderr
    receipt = json.loads(output_path.read_text(encoding="utf-8"))
    assert receipt["atom_iteration_count"] == 1000

    full_output_path = tmp_path / "frontier-full.json"
    full_proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_proof_refinement_frontier.py",
            "--include-candidates",
            "--output",
            str(full_output_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert full_proc.returncode == 0, full_proc.stdout + full_proc.stderr
    full_receipt = json.loads(full_output_path.read_text(encoding="utf-8"))
    assert len(full_receipt["all_candidates"]) == 1000

    text_proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_proof_refinement_frontier.py",
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert text_proc.returncode == 0, text_proc.stdout + text_proc.stderr
    assert "atom_iteration_count = 1000" in text_proc.stdout
    assert "candidate_count = 1000" in text_proc.stdout

    markdown_proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_proof_refinement_frontier.py",
            "--format",
            "markdown",
            "--promotion-n",
            "3",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert markdown_proc.returncode == 0, markdown_proc.stdout + markdown_proc.stderr
    assert "# ZenoDEX Proof Refinement Frontier" in markdown_proc.stdout
