from __future__ import annotations

import json
import subprocess
from pathlib import Path

from src.integration.tau_runner import ROOT


def test_generate_tau_semantic_view_single_spec(tmp_path: Path) -> None:
    out_json = tmp_path / "semantic.json"
    out_md = tmp_path / "semantic.md"
    proc = subprocess.run(
        [
            "python3",
            "tools/generate_tau_semantic_view.py",
            "--execution-census",
            "formal/tau/recommended_execution_census_best.json",
            "--spec-id",
            "sandwich_detection_v1",
            "--out-json",
            str(out_json),
            "--out-md",
            str(out_md),
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "spec count: 1" in proc.stdout
    raw = json.loads(out_json.read_text(encoding="utf-8"))
    assert raw["schema"] == "zenodex/tau/semantic-view/v1"
    assert raw["spec_count"] == 1
    assert raw["packets"][0]["spec_id"] == "sandwich_detection_v1"
    assert out_md.exists()


def test_generate_tau_semantic_view_all_recommended(tmp_path: Path) -> None:
    out_json = tmp_path / "recommended-semantic.json"
    out_md = tmp_path / "recommended-semantic.md"
    proc = subprocess.run(
        [
            "python3",
            "tools/generate_tau_semantic_view.py",
            "--execution-census",
            "formal/tau/recommended_execution_census_best.json",
            "--all-recommended",
            "--out-json",
            str(out_json),
            "--out-md",
            str(out_md),
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    expected_count = len(list((ROOT / "src" / "tau_specs" / "recommended").glob("*.tau")))
    assert f"spec count: {expected_count}" in proc.stdout
    raw = json.loads(out_json.read_text(encoding="utf-8"))
    assert raw["schema"] == "zenodex/tau/semantic-view/v1"
    assert raw["spec_count"] == expected_count
    assert len(raw["packets"]) == expected_count
    assert all(packet["equation_surface"]["extractable"] for packet in raw["packets"])
    assert out_md.exists()


def test_generate_tau_semantic_view_history_shaped_spec(tmp_path: Path) -> None:
    out_json = tmp_path / "history-shaped-semantic.json"
    out_md = tmp_path / "history-shaped-semantic.md"
    subprocess.run(
        [
            "python3",
            "tools/generate_tau_semantic_view.py",
            "--execution-census",
            "formal/tau/recommended_execution_census_best.json",
            "--spec-id",
            "settlement_v4_buyback_floor_rebate_lock",
            "--out-json",
            str(out_json),
            "--out-md",
            str(out_md),
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    raw = json.loads(out_json.read_text(encoding="utf-8"))
    packet = raw["packets"][0]
    assert packet["spec_id"] == "settlement_v4_buyback_floor_rebate_lock"
    assert packet["temporal"] is True
    assert packet["equation_surface"]["extractable"] is True
    assert packet["equation_surface"]["equation_count"] > len(packet["output_streams"])
