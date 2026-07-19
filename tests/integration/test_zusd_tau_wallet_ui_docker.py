"""Container-facing zUSD wallet UI cannot enable browser signing."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def test_container_ui_keeps_zusd_wallet_prepare_only() -> None:
    surface = (UI / "src" / "components" / "ZUSDTauWalletSurface.jsx").read_text(encoding="utf-8")
    config = (UI / "public" / "zenodex-config.json").read_text(encoding="utf-8")
    assert "apiSubmitZusdWallet" not in surface
    assert "allowBrowserKeyGeneration" not in config
