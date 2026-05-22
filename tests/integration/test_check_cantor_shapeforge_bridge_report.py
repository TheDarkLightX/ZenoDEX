from __future__ import annotations

import json
from pathlib import Path

from src.integration.cantor_shapeforge_bridge_report import build_cantor_shapeforge_bridge_report
from tools.check_cantor_shapeforge_bridge_report import main


def test_check_cantor_shapeforge_bridge_report_cli_accepts_current_report(tmp_path: Path) -> None:
    report_path = tmp_path / "bridge.json"
    report_path.write_text(
        json.dumps(build_cantor_shapeforge_bridge_report().to_dict(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    assert main([str(report_path), "--require-current"]) == 0


def test_check_cantor_shapeforge_bridge_report_cli_rejects_tampered_report(tmp_path: Path) -> None:
    report_path = tmp_path / "bridge.json"
    payload = build_cantor_shapeforge_bridge_report().to_dict()
    payload["mapped_surface_count"] = 999
    report_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    assert main([str(report_path)]) == 1
