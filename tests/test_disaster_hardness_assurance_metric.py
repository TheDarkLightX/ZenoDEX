from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_disaster_hardness_assurance_metric import build_metric

ROOT = Path(__file__).resolve().parents[1]


def test_disaster_hardness_assurance_metric_tracks_current_public_receipts() -> None:
    metric = build_metric()

    assert metric["schema"] == "zenodex/disaster-hardness-assurance-metric/v1"
    assert metric["ok"] is True
    assert metric["score"] == 80.8
    assert round(metric["score"]) == 81
    assert metric["level"] == "L3_STRONG_BOUNDED_DISASTER_HARDENING"
    assert metric["hardness_subscore"] == 100.0
    assert metric["assurance_subscore"] == 72.6

    stats = metric["statistics"]
    assert stats["core_closed_axis_count"] == 29
    assert stats["core_inventory_axis_count"] == 125
    assert stats["core_open_inventory_axis_count"] == 96
    assert stats["oracle_devnet_unreachable_count"] == 17
    assert stats["macos_post_materialized_witness_count"] == 65
    assert stats["macos_pre_reachable_witness_count"] == 43
    assert stats["macos_post_reachable_witness_count"] == 0
    assert stats["proof_schema_mapped_closed_axis_count"] == 29
    assert stats["macos_scout_screened_candidate_count"] == 1_700_256


def test_disaster_hardness_assurance_metric_cli_and_readme_summary_agree() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_disaster_hardness_assurance_metric.py",
            "--format",
            "json",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    metric = json.loads(proc.stdout)
    assert metric["score"] == 80.8
    assert metric["level"] == "L3_STRONG_BOUNDED_DISASTER_HARDENING"

    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    metric_doc = (ROOT / "docs" / "DISASTER_HARDNESS_ASSURANCE_METRIC.md").read_text(
        encoding="utf-8"
    )
    assert "DHAI = 81 / 100" in readme
    assert "level = L3_STRONG_BOUNDED_DISASTER_HARDENING" in readme
    assert "docs/DISASTER_HARDNESS_ASSURANCE_METRIC.md" in readme
    assert "raw_score = 80.8 / 100" in metric_doc
    assert "rounded_readme_score = 81 / 100" in metric_doc
