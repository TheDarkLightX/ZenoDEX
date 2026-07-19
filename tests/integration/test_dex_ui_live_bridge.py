"""Static production-boundary checks replacing query-driven browser writes."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UI = ROOT / "tools" / "dex-ui"


def _read(relative: str) -> str:
    return (UI / relative).read_text(encoding="utf-8")


def test_production_swap_and_pool_surfaces_are_live_and_query_inert() -> None:
    app = _read("src/App.jsx")
    swap = _read("src/components/SwapInterface.jsx")
    pools = _read("src/components/PoolDashboard.jsx")
    query_write_hook = "zenodex" + "UiSmoke"

    assert "SwapInterface" in app
    assert "PoolDashboard" in app
    assert "availableTokens={tokens}" in swap
    assert "pool_feed_unavailable" in pools
    assert query_write_hook not in swap
    assert query_write_hook not in pools
    assert "apiMintTestnetFaucet" not in pools


def test_production_build_includes_a_forbidden_functionality_scan() -> None:
    package = _read("package.json")
    scan = _read("scripts/check-production-bundle.mjs")
    assert "check-production-bundle.mjs" in package
    assert "browser or raw-key signer" in scan
    assert "synthetic asset placeholder" in scan
