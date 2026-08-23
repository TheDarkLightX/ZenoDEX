from __future__ import annotations

import json
from pathlib import Path

from src.integration.production_promotion_evidence import attach_production_app_root_jmt_hash_v2
from tools import build_app_root_jmt_evidence as builder
from tools.check_production_promotion_evidence_manifest import main as check_manifest

NOW = 1747878000
MANIFEST_SCHEMA = "zenodex/production-promotion-evidence-manifest/v1"


def test_builder_output_clears_app_root_jmt_lane(capsys, tmp_path: Path) -> None:
    evidence_path = tmp_path / "app-root-jmt.json"
    assert builder.main(["--out", str(evidence_path), "--now", str(NOW)]) == 0
    build_out = json.loads(capsys.readouterr().out)
    assert build_out["ok"] is True

    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {},
                "bundle": {"app_root_jmt": evidence},
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    assert check_manifest([str(manifest_path), "--lane", "app_root_jmt", "--now", str(NOW)]) == 0
    check_out = json.loads(capsys.readouterr().out)
    assert check_out["promotion_ready"] is True
    assert check_out["lanes"]["app_root_jmt"]["production_ready"] is True


def test_builder_output_has_teeth_against_root_drift(capsys, tmp_path: Path) -> None:
    evidence_path = tmp_path / "app-root-jmt.json"
    assert builder.main(["--out", str(evidence_path), "--now", str(NOW)]) == 0
    capsys.readouterr()

    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    evidence["live_root_checks"][0]["observed_root"] = "ff" * 32
    evidence.pop("evidence_hash")
    evidence = attach_production_app_root_jmt_hash_v2(evidence)
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {},
                "bundle": {"app_root_jmt": evidence},
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    assert check_manifest([str(manifest_path), "--lane", "app_root_jmt", "--now", str(NOW)]) == 1
    check_out = json.loads(capsys.readouterr().out)
    assert check_out["promotion_ready"] is False
    assert any("observed_root" in gap for gap in check_out["gaps"])
