from __future__ import annotations

from tools.check_production_key_material_absence import run_check


def test_production_key_material_absence_check_accepts_tracked_repo() -> None:
    result = run_check()

    assert result["ok"] is True
    assert result["checked_file_count"] > 0
    assert result["issues"] == []
