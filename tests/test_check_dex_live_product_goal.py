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
    assert report["status"] == "local_testnet_evidence_present_with_open_production_limits"
    assert {area["id"] for area in report["areas"]} == {
        "mounted_ui_direction",
        "zeno_oracle_live",
        "transaction_surfaces_beyond_spot",
        "assurance_depth",
    }
    assert {limit["id"] for limit in report["residual_limits"]} == {
        "production_oracle_authority",
        "hardware_wallet_ux",
        "zk_wrapping",
        "production_autotrader",
        "confidential_runtime",
    }


def test_anchor_check_rejects_missing_required_text(tmp_path: Path) -> None:
    rel_path = "README.md"
    (tmp_path / rel_path).write_text("ZenoDEX shell", encoding="utf-8")
    check = AnchorCheck(
        area_id="mounted_ui_direction",
        check_id="sample",
        path=rel_path,
        anchors=("AutoTrader local/testnet panel",),
        description="sample",
    )

    result = check_anchor(check, root=tmp_path)

    assert result["ok"] is False
    assert result["missing"] == ["AutoTrader local/testnet panel"]


def test_anchor_check_rejects_missing_file(tmp_path: Path) -> None:
    check = AnchorCheck(
        area_id="mounted_ui_direction",
        check_id="sample",
        path="missing.md",
        anchors=("anything",),
        description="sample",
    )

    result = check_anchor(check, root=tmp_path)

    assert result["ok"] is False
    assert result["error"] == "missing_file"


def test_forbidden_check_rejects_stale_strategy_readme_claim(tmp_path: Path) -> None:
    rel_path = "tools/dex-ui/README.md"
    target = tmp_path / rel_path
    target.parent.mkdir(parents=True)
    target.write_text(
        "Strategy remains a planning workbench and reference surface. It does not submit live strategies.",
        encoding="utf-8",
    )
    check = ForbiddenCheck(
        area_id="mounted_ui_direction",
        check_id="stale_strategy",
        path=rel_path,
        pattern=re.compile(r"Strategy remains.*does\s+not\s+submit\s+live\s+strategies"),
        description="sample",
    )

    result = check_forbidden(check, root=tmp_path)

    assert result["ok"] is False
    assert result["matches"]
