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
    assert report["status"] == "source_inventory_present_with_quarantined_retired_tau_routes"
    assert report["source_anchor_inventory_only"] is True
    assert report["test_execution_verified"] is False
    assert report["production_authority"] == "NONE"
    assert report["vm_gates_closed"] == []
    assert report["quarantined_route_authority"] == "NONE"
    assert report["quarantined_routes"] == [
        "PERPS_WALLET_API_ENABLED",
        "ZUSD_TAU_WALLET_API_ENABLED",
        "ZUSD_MONETARY_WALLET_API_ENABLED",
    ]
    assert {area["id"] for area in report["areas"]} == {
        "mounted_ui_direction",
        "zeno_oracle_live",
        "transaction_surfaces_beyond_spot",
        "assurance_depth",
        "current_route_quarantine",
    }
    assert {limit["id"] for limit in report["residual_limits"]} == {
        "production_oracle_authority",
        "hardware_wallet_ux",
        "zk_wrapping",
        "production_autotrader",
        "confidential_runtime",
        "current_tau_route_rebind",
    }
    autotrader_checks = [
        check
        for area in report["areas"]
        for check in area["checks"]
        if "autotrader" in check["id"]
    ]
    assert autotrader_checks
    assert all("mounted" not in check["id"] for check in autotrader_checks)
    assert all(
        " mounted " not in f" {check['description'].lower()} "
        for check in autotrader_checks
    )
    anchor_checks = [
        check
        for area in report["areas"]
        for check in area["checks"]
        if check["kind"] == "source_anchors"
    ]
    assert anchor_checks
    assert all(check["execution_verified"] is False for check in anchor_checks)
    assert all("tests prove" not in check["description"].lower() for check in anchor_checks)
    assert all("executable tests" not in check["description"].lower() for check in anchor_checks)
    quarantine_check_ids = {
        check["id"]
        for area in report["areas"]
        if area["id"] == "current_route_quarantine"
        for check in area["checks"]
    }
    assert {
        "retired_value_route_browser_controls_are_quarantined",
        "runtime_config_disables_retired_value_route_ui",
        "runtime_value_route_presentation_is_exact_and_immutable",
        "perps_ui_gate_resists_write_override",
        "ui_contract_checks_current_quarantine_flags",
    } <= quarantine_check_ids


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


def test_donor_evidence_check_rejects_missing_retained_browser_scenario(tmp_path: Path) -> None:
    rel_path = "tests/integration/test_retired_route.py"
    target = tmp_path / rel_path
    target.parent.mkdir(parents=True)
    target.write_text(
        "def test_retired_route_browser_smoke():\n    pass\n",
        encoding="utf-8",
    )
    check = AnchorCheck(
        area_id="current_route_quarantine",
        check_id="retired_donor_scenario",
        path=rel_path,
        anchors=("test_expected_retained_browser_scenario",),
        description="sample",
    )

    result = check_anchor(check, root=tmp_path)

    assert result["ok"] is False
    assert result["missing"] == ["test_expected_retained_browser_scenario"]


def test_donor_evidence_check_rejects_file_level_skip_marker(tmp_path: Path) -> None:
    rel_path = "tests/integration/test_retired_route.py"
    target = tmp_path / rel_path
    target.parent.mkdir(parents=True)
    target.write_text(
        "pytestmark = pytest.mark.skip(reason='route retired')\n",
        encoding="utf-8",
    )
    check = ForbiddenCheck(
        area_id="current_route_quarantine",
        check_id="retained_donor_not_suppressed",
        path=rel_path,
        pattern=re.compile(
            r"RETAINED_QUARANTINED_DONOR_TESTS_V1|pytestmark\s*=\s*pytest\.mark\.skip"
        ),
        description="sample",
    )

    result = check_forbidden(check, root=tmp_path)

    assert result["ok"] is False
    assert result["matches"]


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
