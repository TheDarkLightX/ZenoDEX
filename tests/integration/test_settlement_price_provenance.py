from __future__ import annotations

from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    asset_prices_from_spot_price_packet,
    build_settlement_spot_price_packet,
    verify_settlement_spot_price_packet_payload,
)
from src.integration.zusd_oracle_contracts import build_zusd_cross_module_oracle_sync_contract


def test_settlement_spot_price_packet_round_trips_without_sync() -> None:
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset="A", price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset="B", price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
        cross_module_sync_required=False,
    )

    assert packet.unique_assets is True
    assert packet.all_positive is True
    assert packet.all_fresh is True
    assert packet.provenance_ok is True
    assert asset_prices_from_spot_price_packet(packet) == {"A": 100, "B": 120}

    ok, err = verify_settlement_spot_price_packet_payload(packet.to_dict())
    assert ok is True
    assert err is None


def test_settlement_spot_price_packet_rejects_stale_price() -> None:
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset="A", price=100, observed_epoch=80, age_epochs=20, source_id="local:a"),
            SettlementSpotPriceEntry(asset="B", price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
        cross_module_sync_required=False,
    )

    assert packet.all_fresh is False
    assert packet.provenance_ok is False

    ok, err = verify_settlement_spot_price_packet_payload(packet.to_dict())
    assert ok is True
    assert err is None


def test_settlement_spot_price_packet_binds_verified_sync_contract() -> None:
    sync_contract = build_zusd_cross_module_oracle_sync_contract(
        market_id="TAU-USD",
        zusd_price_e8=50_000_000,
        zusd_epoch=100,
        perp_price_e8=50_000_000,
        perp_oracle_epoch=99,
        max_divergence_bps=0,
        max_epoch_lag=2,
    )
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset="A", price=100, observed_epoch=99, age_epochs=1, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset="B", price=120, observed_epoch=99, age_epochs=1, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
        cross_module_sync_required=True,
        cross_module_sync_contract=sync_contract.to_dict(),
    )

    assert packet.cross_module_sync_ok is True
    assert packet.provenance_ok is True

    ok, err = verify_settlement_spot_price_packet_payload(packet.to_dict())
    assert ok is True
    assert err is None


def test_settlement_spot_price_packet_rejects_tampering() -> None:
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset="A", price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset="B", price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
        cross_module_sync_required=False,
    ).to_dict()
    packet["provenance_ok"] = False

    ok, err = verify_settlement_spot_price_packet_payload(packet)
    assert ok is False
    assert err == "settlement spot price packet mismatch"
