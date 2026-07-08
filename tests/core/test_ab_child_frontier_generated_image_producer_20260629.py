from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_ab_child_frontier_generated_image_producer_20260629 import (
    EXPECTED_CHILD_MASK_COUNT,
    EXPECTED_CHILD_STATE_COUNT,
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    EXPECTED_STAGE_ORDER,
    REPORT_JSON,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


def test_ab_child_frontier_generated_image_producer_fast_report() -> None:
    report = build_report(replay_stages=False)
    manifest = report["manifest"]

    assert report["ok"] is True
    assert report["stage_replay"]["enabled"] is False
    assert tuple(manifest["producer_stage_order"]) == EXPECTED_STAGE_ORDER
    assert len(manifest["stage_manifests"]) == len(EXPECTED_STAGE_ORDER)
    assert report["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert report["negative_control_accept_count"] == 0
    assert report["verification"]["ok"] is True


def test_ab_child_frontier_generated_image_producer_stage_outputs() -> None:
    report = build_report(replay_stages=False)
    stages = {stage["stage_id"]: stage for stage in report["manifest"]["stage_manifests"]}

    assert stages["generation"]["outputs"]["frontier_rows_digest"] == (
        "b0536297bdec3e49204d98e4a52b4b43ea1467f7a32c2e184cf0bec07955fba4"
    )
    assert stages["generation"]["outputs"]["child_mask_count"] == EXPECTED_CHILD_MASK_COUNT
    assert stages["generation"]["outputs"]["child_state_count"] == EXPECTED_CHILD_STATE_COUNT
    assert stages["canonical_merkle"]["outputs"]["membership_rows_digest"] == (
        "84cdbf4ebc62d758655f2ad253e541d072a7158f4c75bd939be521d613c84559"
    )
    assert stages["witness_compression"]["outputs"]["witness_rows_digest"] == (
        "d689dd569b28abf3cb2636def322fa9d8185c2eb1fe4843bd83d07bce69138c3"
    )
    assert stages["witness_merkle_cross_binding"]["outputs"]["bound_rows_digest"] == (
        "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551"
    )
    assert stages["corpus_root"]["outputs"]["corpus_root"] == (
        "8f4a1a08cf51215cdc9fd382dd2538cc199db35b87597aa9c468358925dfd3b0"
    )


def test_ab_child_frontier_generated_image_producer_cross_links_and_controls() -> None:
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
        "corpus_root_output_digest_mismatch",
        "authority_effect_present",
    }
    for control in controls.values():
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]


def test_ab_child_frontier_generated_image_producer_non_claims() -> None:
    report = build_report(replay_stages=False)
    nonclaims = "\n".join(report["non_claims"])

    assert "bounded to the committed n=7 zero-min child-frontier corpus" in nonclaims
    assert "does not prove Python-to-Lean refinement" in nonclaims
    assert "does not prove child-frontier generation in Lean" in nonclaims
    assert "does not cover nonzero min_amount_out behavior" in nonclaims
    assert "does not authorize settlement" in nonclaims


def test_ab_child_frontier_generated_image_producer_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_child_frontier_generated_image_producer_20260629.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["stage_replay"]["enabled"] is True
    assert report["stage_replay"]["ok"] is True
    assert report["negative_control_accept_count"] == 0
