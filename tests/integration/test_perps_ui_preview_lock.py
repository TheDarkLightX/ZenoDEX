"""Perpetuals production UI must remain live-data and external-signer only."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def test_perps_provider_has_no_preview_or_bundled_market_authority() -> None:
    provider = (UI / "src" / "lib" / "PerpProvider.jsx").read_text(encoding="utf-8")
    assert "const statusResp = await apiGetPerpsWalletStatus" in provider
    assert "Trader writes require a production signer bridge" in provider
    assert "perpMockData" not in provider
    assert "DemoMode" not in provider
