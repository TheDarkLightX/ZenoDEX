"""Production UI exclusion contract for fixture-backed confidential flows."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def test_confidential_fixture_surface_is_not_part_of_the_production_ui() -> None:
    app = (UI / "src" / "App.jsx").read_text(encoding="utf-8")
    assert "ConfidentialWorkbench" not in app
    assert not (UI / "src" / "components" / "ConfidentialWorkbench.jsx").exists()
    assert not (UI / "src" / "lib" / "confidentialData.js").exists()
