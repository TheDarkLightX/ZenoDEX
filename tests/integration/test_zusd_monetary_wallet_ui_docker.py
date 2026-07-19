"""Container-facing zUSD monetary UI uses the same prepare-only source."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def test_container_ui_cannot_restore_monetary_browser_signing() -> None:
    surface = (UI / "src" / "components" / "ZUSDMonetarySurface.jsx").read_text(encoding="utf-8")
    config = (UI / "public" / "zenodex-config.json").read_text(encoding="utf-8")
    assert "apiSubmitZusdMonetary" not in surface
    assert "allowBrowserKeyGeneration" not in config
