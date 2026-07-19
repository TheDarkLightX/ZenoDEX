"""Perpetuals wallet production-boundary checks without browser write hooks."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def test_perps_wallet_accepts_no_raw_key_or_query_trigger() -> None:
    surface = (UI / "src" / "components" / "perps" / "PerpLiveWalletSurface.jsx").read_text(encoding="utf-8")
    query_write_hook = "zenodex" + "UiSmoke"
    raw_key_field = "signer_" + "privkey"
    assert "apiInspectPerpsOracleBridge" in surface
    assert query_write_hook not in surface
    assert raw_key_field not in surface
