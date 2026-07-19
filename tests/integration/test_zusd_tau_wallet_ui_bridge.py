"""zUSD token wallet UI exposes unsigned preparation, never raw-key submit."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def test_zusd_wallet_surface_is_prepare_only_and_keyless() -> None:
    surface = (UI / "src" / "components" / "ZUSDTauWalletSurface.jsx").read_text(encoding="utf-8")
    raw_key_field = "signer_" + "privkey"
    assert "apiPrepareZusdWallet" in surface
    assert "Prepare unsigned request" in surface
    assert "apiSubmitZusdWallet" not in surface
    assert raw_key_field not in surface
