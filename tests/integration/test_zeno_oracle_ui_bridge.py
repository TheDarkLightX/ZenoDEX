"""Oracle production UI is a read-only view of live service evidence."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def test_oracle_dashboard_is_live_read_only_and_has_no_write_harness() -> None:
    surface = (UI / "src" / "components" / "ZenoOracleDashboard.jsx").read_text(encoding="utf-8")
    query_write_hook = "zenodex" + "UiSmoke"
    assert "apiGetZenoOracleDashboard" in surface
    assert "This surface never synthesizes or submits reports" in surface
    assert query_write_hook not in surface
    assert "apiSubmit" not in surface
