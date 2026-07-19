from __future__ import annotations

import re
from pathlib import Path

from tools.check_dex_live_product_goal import (
    AnchorCheck,
    ForbiddenCheck,
    audit_live_product_goal,
    check_anchor,
    check_forbidden,
)

ROOT = Path(__file__).resolve().parents[1]


def test_current_live_product_goal_evidence_is_present() -> None:
    report = audit_live_product_goal(root=ROOT)

    assert report["schema"] == "zenodex/dex_live_product_goal_audit/v1"
    assert report["ok"] is True
    assert report["goal_complete"] is False
    assert report["status"] == "production_live_only_surface_present_with_open_promotion_limits"
    assert {area["id"] for area in report["areas"]} == {
        "mounted_live_surfaces",
        "live_data_authority",
        "signer_and_write_boundary",
        "artifact_exclusion",
    }
    assert {limit["id"] for limit in report["residual_limits"]} == {
        "production_chain_configuration",
        "zusd_external_signed_envelopes",
        "production_oracle_authority",
        "production_proof_artifacts",
    }


def test_anchor_check_rejects_missing_required_text(tmp_path: Path) -> None:
    rel_path = "README.md"
    (tmp_path / rel_path).write_text("ZenoDEX shell", encoding="utf-8")
    check = AnchorCheck(
        area_id="mounted_live_surfaces",
        check_id="sample",
        path=rel_path,
        anchors=("live-only surface",),
        description="sample",
    )

    result = check_anchor(check, root=tmp_path)

    assert result["ok"] is False
    assert result["missing"] == ["live-only surface"]


def test_anchor_check_rejects_missing_file(tmp_path: Path) -> None:
    check = AnchorCheck(
        area_id="mounted_live_surfaces",
        check_id="sample",
        path="missing.md",
        anchors=("anything",),
        description="sample",
    )

    result = check_anchor(check, root=tmp_path)

    assert result["ok"] is False
    assert result["error"] == "missing_file"


def test_forbidden_check_rejects_browser_key_capability(tmp_path: Path) -> None:
    rel_path = "tools/dex-ui/public/zenodex-config.json"
    target = tmp_path / rel_path
    target.parent.mkdir(parents=True)
    target.write_text('{"allowBrowserKeyGeneration": true}', encoding="utf-8")
    check = ForbiddenCheck(
        area_id="artifact_exclusion",
        check_id="browser_key_capability",
        path=rel_path,
        pattern=re.compile(r'"allowBrowserKeyGeneration"'),
        description="sample",
    )

    result = check_forbidden(check, root=tmp_path)

    assert result["ok"] is False
    assert result["matches"]
