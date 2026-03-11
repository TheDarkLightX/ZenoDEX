from __future__ import annotations

import random

import pytest

from src.core.epoch_oracle_commitment import (
    EpochOracleCommitment,
    ModuleOracleView,
    OracleRegistry,
    create_module_views,
    estimate_cross_module_arbitrage_bps,
)


def test_registry_commit_is_monotonic_and_unique() -> None:
    registry = OracleRegistry()
    registry.commit(EpochOracleCommitment(epoch=1, price_e8=100_000_000, timestamp=1, source_hash="h1"))
    registry.commit(EpochOracleCommitment(epoch=2, price_e8=101_000_000, timestamp=2, source_hash="h2"))
    assert registry.latest_epoch == 2
    assert registry.commitment_count == 2

    with pytest.raises(ValueError):
        registry.commit(EpochOracleCommitment(epoch=2, price_e8=99_000_000, timestamp=3, source_hash="dup"))

    with pytest.raises(ValueError):
        registry.commit(EpochOracleCommitment(epoch=0, price_e8=99_000_000, timestamp=3, source_hash="back"))


def test_create_module_views_share_same_price_and_hash() -> None:
    registry = OracleRegistry()
    registry.commit(EpochOracleCommitment(epoch=7, price_e8=123_000_000, timestamp=10, source_hash="src"))
    modules = ["amm", "perps", "zusd", "funding"]
    views = create_module_views(registry, 7, modules)
    assert set(views.keys()) == set(modules)
    assert len({view.price_e8 for view in views.values()}) == 1
    assert len({view.source_hash for view in views.values()}) == 1


def test_create_module_views_missing_epoch_raises() -> None:
    registry = OracleRegistry()
    registry.commit(EpochOracleCommitment(epoch=1, price_e8=100, timestamp=1, source_hash="h"))
    with pytest.raises(KeyError):
        create_module_views(registry, 2, ["amm"])


def test_commitment_and_view_are_frozen() -> None:
    commitment = EpochOracleCommitment(epoch=1, price_e8=100, timestamp=1, source_hash="h")
    with pytest.raises(AttributeError):
        commitment.price_e8 = 200  # type: ignore[misc]

    view = ModuleOracleView(module_name="amm", epoch=1, price_e8=100, source_hash="h")
    with pytest.raises(AttributeError):
        view.price_e8 = 200  # type: ignore[misc]


def test_cross_module_arbitrage_bps_zero_when_prices_match() -> None:
    assert estimate_cross_module_arbitrage_bps(100_000_000, 100_000_000, 1_000_000) == 0


def test_cross_module_arbitrage_bps_positive_when_prices_diverge() -> None:
    arbitrage_bps = estimate_cross_module_arbitrage_bps(100_000_000, 101_000_000, 1_000_000)
    assert arbitrage_bps > 0
    assert 99 <= arbitrage_bps <= 101


def test_cross_module_arbitrage_monotone_in_gap() -> None:
    rng = random.Random(42)
    for _ in range(100):
        base = rng.randint(10_000_000, 1_000_000_000)
        arbitrage_series = []
        for gap_pct in (1, 2, 5, 10):
            other = base * (100 + gap_pct) // 100
            arbitrage_series.append(estimate_cross_module_arbitrage_bps(base, other, 1_000_000))
        assert arbitrage_series == sorted(arbitrage_series)


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"epoch": -1, "price_e8": 100, "timestamp": 1, "source_hash": "h"}, "epoch must be non-negative"),
        ({"epoch": 1, "price_e8": 0, "timestamp": 1, "source_hash": "h"}, "price_e8 must be positive"),
        ({"epoch": 1, "price_e8": 100, "timestamp": -1, "source_hash": "h"}, "timestamp must be non-negative"),
        ({"epoch": 1, "price_e8": 100, "timestamp": 1, "source_hash": ""}, "source_hash must be non-empty"),
    ],
)
def test_epoch_oracle_commitment_rejects_invalid_fields(kwargs: dict[str, object], message: str) -> None:
    with pytest.raises(ValueError, match=message):
        EpochOracleCommitment(**kwargs)


def test_registry_get_and_get_price_cover_missing_and_present_epochs() -> None:
    registry = OracleRegistry()
    commitment = EpochOracleCommitment(epoch=3, price_e8=123, timestamp=7, source_hash="src")
    registry.commit(commitment)

    assert registry.get(3) == commitment
    assert registry.get(99) is None
    assert registry.get_price_e8(3) == 123
    with pytest.raises(KeyError, match="No oracle commitment for epoch 99"):
        registry.get_price_e8(99)


def test_cross_module_arbitrage_rejects_bad_prices_and_zeroes_non_positive_trade_size() -> None:
    with pytest.raises(ValueError, match="Prices must be positive"):
        estimate_cross_module_arbitrage_bps(0, 100, 1)

    assert estimate_cross_module_arbitrage_bps(100, 101, 0) == 0
