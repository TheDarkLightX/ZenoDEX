from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_ab_child_frontier_generated_image_producer_n8_sample_20260629 import (
    EXPECTED_CHILD_STATE_COUNT,
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    EXPECTED_PREDECESSOR_TRANSITION_COUNT,
    EXPECTED_SAMPLED_CHILD_MASK_COUNT,
    EXPECTED_STAGE_ORDER,
    REPORT_JSON,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


def test_ab_child_frontier_generated_image_producer_n8_fast_report() -> None:
    report = build_report(replay_stages=False)
    manifest = report["manifest"]

    assert report["ok"] is True
    assert report["stage_replay"]["enabled"] is False
    assert tuple(manifest["producer_stage_order"]) == EXPECTED_STAGE_ORDER
    assert len(manifest["stage_manifests"]) == len(EXPECTED_STAGE_ORDER)
    assert report["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert report["negative_control_accept_count"] == 0
    assert report["verification"]["ok"] is True
    assert manifest["source_seed"] == "2026062908"


def test_ab_child_frontier_generated_image_producer_n8_stage_outputs() -> None:
    report = build_report(replay_stages=False)
    stages = {stage["stage_id"]: stage for stage in report["manifest"]["stage_manifests"]}

    assert stages["generation"]["outputs"]["frontier_rows_digest"] == (
        "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919"
    )
    assert stages["generation"]["outputs"]["sampled_child_mask_count"] == (
        EXPECTED_SAMPLED_CHILD_MASK_COUNT
    )
    assert stages["generation"]["outputs"]["sampled_child_state_count"] == (
        EXPECTED_CHILD_STATE_COUNT
    )
    assert stages["canonical_merkle"]["outputs"]["membership_rows_digest"] == (
        "bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2"
    )
    assert stages["witness_compression"]["outputs"]["witness_rows_digest"] == (
        "4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd"
    )
    assert stages["witness_compression"]["outputs"]["witness_transition_checks_saved"] == 180
    assert stages["bidirectional_transition"]["outputs"]["transition_rows_digest"] == (
        "0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09"
    )
    assert stages["bidirectional_transition"]["outputs"]["transition_row_count"] == (
        EXPECTED_PREDECESSOR_TRANSITION_COUNT
    )
    assert stages["bidirectional_transition"]["outputs"]["unique_generated_child_count"] == (
        EXPECTED_CHILD_STATE_COUNT
    )


def test_ab_child_frontier_generated_image_producer_n8_cross_links_and_controls() -> None:
    report = build_report(replay_stages=False)

    assert all(report["manifest"]["cross_stage_links"].values())
    controls = {control["mutation_id"]: control for control in report["negative_controls"]}
    assert set(controls) == {
        "manifest_hash_mismatch",
        "producer_stage_order_mismatch",
        "stage_manifest_missing",
        "source_seed_mismatch",
        "generation_script_hash_mismatch",
        "generation_report_hash_mismatch",
        "generation_output_digest_mismatch",
        "canonical_merkle_output_digest_mismatch",
        "witness_output_digest_mismatch",
        "bidirectional_transition_output_digest_mismatch",
        "authority_effect_present",
    }
    for control in controls.values():
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]


def test_ab_child_frontier_generated_image_producer_n8_non_claims() -> None:
    report = build_report(replay_stages=False)
    nonclaims = "\n".join(report["non_claims"])

    assert "bounded to the deterministic sampled n=8 zero-min" in nonclaims
    assert "does not prove exhaustive n=8 coverage" in nonclaims
    assert "does not prove Python-to-Lean refinement" in nonclaims
    assert "does not prove child-frontier generation in Lean" in nonclaims
    assert "does not cover nonzero min_amount_out behavior" in nonclaims
    assert "does not authorize settlement" in nonclaims


def test_ab_child_frontier_generated_image_producer_n8_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_generated_image_producer_n8_sample_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=240,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["stage_replay"]["enabled"] is True
    assert report["stage_replay"]["ok"] is True
    assert report["stage_replay"]["stage_count"] == len(EXPECTED_STAGE_ORDER)
    assert report["negative_control_accept_count"] == 0
