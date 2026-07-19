"""Production UI exclusion contract for the fixture-backed AutoTrader surface."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def test_autotrader_fixture_surface_is_not_part_of_the_production_ui() -> None:
    app = (UI / "src" / "App.jsx").read_text(encoding="utf-8")
    assert "StrategyWorkbench" not in app
    assert not (UI / "src" / "components" / "StrategyWorkbench.jsx").exists()
    assert not (UI / "src" / "lib" / "strategyData.js").exists()
