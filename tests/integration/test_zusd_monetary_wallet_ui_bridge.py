"""zUSD monetary UI remains prepare-only until external envelope signing exists."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def test_zusd_monetary_surface_is_prepare_only_and_keyless() -> None:
    surface = (UI / "src" / "components" / "ZUSDMonetarySurface.jsx").read_text(encoding="utf-8")
    raw_key_field = "signer_" + "privkey"
    assert "apiPrepareZusdMonetary" in surface
    assert "Production profile is prepare-only" in surface
    assert "apiSubmitZusdMonetary" not in surface
    assert raw_key_field not in surface
