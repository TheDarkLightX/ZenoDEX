from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from tools.shapeforge_target_shape_eval import evaluate_target_shapes


ROOT = Path(__file__).resolve().parents[2]
TARGET_SHAPES = ROOT / "docs" / "zenodex" / "shapeforge_promoted" / "zenodex_target_shapes.seed.json"
EVAL_TOOL = ROOT / "tools" / "shapeforge_target_shape_eval.py"


def test_shape_pp_eval_has_expected_supported_and_blocked_profile() -> None:
    report = evaluate_target_shapes(TARGET_SHAPES)
    assert report["schema"] == "shapeforge/target-shape-eval-report/v1"
    result = next(result for result in report["results"] if result["target_shape_id"] == "shape_pp_candidate_v1")
    assert result["target_shape_id"] == "shape_pp_candidate_v1"
    assert result["support_count"] == 10
    assert result["gap_count"] == 0
    assert result["blocked_count"] == 0

    clauses = {clause["clause_id"]: clause for clause in result["clauses"]}
    assert clauses["cbc_validity"]["supported"] is True
    assert clauses["unique_canonical_winner_everywhere"]["supported"] is True
    assert clauses["proof_carrying_optimizer_certificates"]["blocked"] is False
    assert clauses["oracle_divergence_safety"]["supported"] is True
    assert clauses["oracle_divergence_safety"]["blocked"] is False
    assert clauses["cross_layer_replay_parity"]["supported"] is True
    assert clauses["cross_layer_replay_parity"]["blocked"] is False


def test_focused_target_profiles_surface_expected_ratios() -> None:
    report = evaluate_target_shapes(TARGET_SHAPES)
    results = {result["target_shape_id"]: result for result in report["results"]}
    assert results["dex_kernel_candidate_v1"]["support_count"] == 6
    assert results["dex_kernel_candidate_v1"]["blocked_count"] == 0
    assert results["runtime_boundary_candidate_v1"]["support_count"] == 5
    assert results["runtime_boundary_candidate_v1"]["blocked_count"] == 0


def test_shape_target_eval_cli_text_surface() -> None:
    result = subprocess.run(
        [sys.executable, str(EVAL_TOOL), str(TARGET_SHAPES)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    stdout = result.stdout
    assert "shape_pp_candidate_v1: support=10/10 gaps=0 blocked=0 ratio=1.00" in stdout
    assert "OK oracle_divergence_safety" in stdout
    assert "OK cross_layer_replay_parity" in stdout
    assert "OK proof_carrying_optimizer_certificates" in stdout
