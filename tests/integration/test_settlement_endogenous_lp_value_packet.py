from __future__ import annotations

import pytest

import src.integration.settlement_endogenous_lp_value_packet as endogenous_packet
from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import LPDelta
from src.integration.settlement_endogenous_lp_value_packet import (
    SETTLEMENT_ENDOGENOUS_LP_VALUE_PACKET_SCHEMA,
    SettlementEndogenousLPValuePacket,
    build_settlement_endogenous_lp_value_packet_from_price_attestation,
    build_settlement_endogenous_lp_value_packet_from_price_packet,
    verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation,
    verify_settlement_endogenous_lp_value_packet_payload_from_price_packet,
)
from src.integration.settlement_price_attestation import build_settlement_spot_price_attestation
from src.integration.settlement_price_provenance import SettlementSpotPriceEntry, build_settlement_spot_price_packet
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _swap_context():
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(3300),
        sender_pubkey=pk,
        deadline=9_999_999_999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    return pk, asset0, asset1, pool_id, pool, settlement


def _price_packet_for(asset0: str, asset1: str):
    return build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )


def test_endogenous_lp_value_packet_round_trips_from_price_packet() -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )

    packet = build_settlement_endogenous_lp_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
        pool_snapshots=(pool,),
    )
    assert packet.schema == SETTLEMENT_ENDOGENOUS_LP_VALUE_PACKET_SCHEMA
    assert packet.price_input_kind == "packet"
    assert packet.packet_ok is True
    assert packet.lp_value_contract.lp_unit_values[0].pool_id == pool_id
    expected_unit_value = ((pool.reserve0 * 100) + (pool.reserve1 * 120)) // pool.lp_supply
    assert packet.lp_value_contract.lp_unit_values[0].unit_value == expected_unit_value

    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        pool_snapshots_payload=list(packet.pool_snapshots),
        packet_payload=packet.to_dict(),
    )
    assert ok is True
    assert err is None


def test_endogenous_lp_value_packet_round_trips_from_attestation() -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=2, delta_sub=0))
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    attestation = build_settlement_spot_price_attestation(packet=price_packet, signer_privkey=7)

    packet = build_settlement_endogenous_lp_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        pool_snapshots=(pool,),
        allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    )
    assert packet.price_input_kind == "attestation"
    assert packet.price_attestation is not None
    assert packet.packet_ok is True

    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation(
        settlement=settlement,
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        pool_snapshots_payload=list(packet.pool_snapshots),
        packet_payload=packet.to_dict(),
        allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    )
    assert ok is True
    assert err is None


def test_endogenous_lp_value_packet_rejects_tampering() -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=1, delta_sub=0))
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    packet = build_settlement_endogenous_lp_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
        pool_snapshots=(pool,),
    )
    bad = dict(packet.to_dict())
    bad["packet_ok"] = False

    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        pool_snapshots_payload=list(packet.pool_snapshots),
        packet_payload=bad,
    )
    assert ok is False
    assert err == "settlement endogenous lp value packet mismatch"


def test_endogenous_lp_value_packet_from_dict_round_trips() -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=1, delta_sub=0))
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    packet = build_settlement_endogenous_lp_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
        pool_snapshots=(pool,),
    )
    rebuilt = SettlementEndogenousLPValuePacket.from_dict(packet.to_dict())
    assert rebuilt == packet


def test_verify_endogenous_lp_value_packet_rejects_expected_price_packet_parse_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _reject_from_dict(*args: object, **kwargs: object) -> object:
        raise ValueError("endogenous price packet payload invalid")

    monkeypatch.setattr(endogenous_packet.SettlementSpotPricePacket, "from_dict", _reject_from_dict)

    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        pool_snapshots_payload=[_pool_payload(pool)],
        packet_payload={},
    )

    assert ok is False
    assert err == "endogenous price packet payload invalid"


def test_verify_endogenous_lp_value_packet_surfaces_unexpected_price_packet_parse_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _boom_from_dict(*args: object, **kwargs: object) -> object:
        raise RuntimeError("endogenous price packet parser internal fault")

    monkeypatch.setattr(endogenous_packet.SettlementSpotPricePacket, "from_dict", _boom_from_dict)

    with pytest.raises(RuntimeError, match="endogenous price packet parser internal fault"):
        verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            pool_snapshots_payload=[_pool_payload(pool)],
            packet_payload={},
        )


def test_verify_endogenous_lp_value_packet_rejects_expected_pool_snapshot_parse_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _reject_pool(*args: object, **kwargs: object) -> object:
        raise ValueError("pool snapshot payload invalid")

    monkeypatch.setattr(endogenous_packet, "_pool_from_dict", _reject_pool)

    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        pool_snapshots_payload=[_pool_payload(pool)],
        packet_payload={},
    )

    assert ok is False
    assert err == "pool snapshot payload invalid"


def test_verify_endogenous_lp_value_packet_surfaces_unexpected_pool_snapshot_parse_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _boom_pool(*args: object, **kwargs: object) -> object:
        raise RuntimeError("pool snapshot parser internal fault")

    monkeypatch.setattr(endogenous_packet, "_pool_from_dict", _boom_pool)

    with pytest.raises(RuntimeError, match="pool snapshot parser internal fault"):
        verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            pool_snapshots_payload=[_pool_payload(pool)],
            packet_payload={},
        )


def test_verify_endogenous_lp_value_packet_rejects_expected_builder_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _reject_build(*args: object, **kwargs: object) -> object:
        raise ValueError("endogenous value packet input invalid")

    monkeypatch.setattr(
        endogenous_packet,
        "build_settlement_endogenous_lp_value_packet_from_price_packet",
        _reject_build,
    )

    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        pool_snapshots_payload=[_pool_payload(pool)],
        packet_payload={},
    )

    assert ok is False
    assert err == "endogenous value packet input invalid"


def test_verify_endogenous_lp_value_packet_surfaces_unexpected_builder_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _boom_build(*args: object, **kwargs: object) -> object:
        raise RuntimeError("endogenous value packet builder internal fault")

    monkeypatch.setattr(
        endogenous_packet,
        "build_settlement_endogenous_lp_value_packet_from_price_packet",
        _boom_build,
    )

    with pytest.raises(RuntimeError, match="endogenous value packet builder internal fault"):
        verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            pool_snapshots_payload=[_pool_payload(pool)],
            packet_payload={},
        )


def test_verify_endogenous_lp_value_packet_rejects_expected_packet_payload_parse_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=1, delta_sub=0))
    price_packet = _price_packet_for(asset0, asset1)

    def _reject_packet(*args: object, **kwargs: object) -> object:
        raise ValueError("endogenous packet payload invalid")

    monkeypatch.setattr(endogenous_packet.SettlementEndogenousLPValuePacket, "from_dict", _reject_packet)

    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        pool_snapshots_payload=[_pool_payload(pool)],
        packet_payload={},
    )

    assert ok is False
    assert err == "endogenous packet payload invalid"


def test_verify_endogenous_lp_value_packet_surfaces_unexpected_packet_payload_parse_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=1, delta_sub=0))
    price_packet = _price_packet_for(asset0, asset1)

    def _boom_packet(*args: object, **kwargs: object) -> object:
        raise RuntimeError("endogenous packet payload parser internal fault")

    monkeypatch.setattr(endogenous_packet.SettlementEndogenousLPValuePacket, "from_dict", _boom_packet)

    with pytest.raises(RuntimeError, match="endogenous packet payload parser internal fault"):
        verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            pool_snapshots_payload=[_pool_payload(pool)],
            packet_payload={},
        )


def test_verify_attestation_endogenous_lp_value_packet_surfaces_unexpected_builder_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=2, delta_sub=0))
    price_packet = _price_packet_for(asset0, asset1)
    attestation = build_settlement_spot_price_attestation(packet=price_packet, signer_privkey=7)

    def _boom_build(*args: object, **kwargs: object) -> object:
        raise RuntimeError("attestation endogenous packet builder internal fault")

    monkeypatch.setattr(
        endogenous_packet,
        "build_settlement_endogenous_lp_value_packet_from_price_attestation",
        _boom_build,
    )

    with pytest.raises(RuntimeError, match="attestation endogenous packet builder internal fault"):
        verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation(
            settlement=settlement,
            price_attestation_payload=attestation.to_dict(),
            consumer_now_epoch=103,
            max_attestation_age_epochs=5,
            pool_snapshots_payload=[_pool_payload(pool)],
            packet_payload={},
            allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
        )


def _pool_payload(pool) -> dict[str, object]:
    return {
        "pool_id": pool.pool_id,
        "asset0": pool.asset0,
        "asset1": pool.asset1,
        "reserve0": pool.reserve0,
        "reserve1": pool.reserve1,
        "fee_bps": pool.fee_bps,
        "lp_supply": pool.lp_supply,
        "status": pool.status.name,
        "created_at": pool.created_at,
        "curve_tag": pool.curve_tag,
        "curve_params": pool.curve_params,
    }
