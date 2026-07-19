from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import LPDelta
from src.integration import settlement_endogenous_lp_value_packet as endogenous_packet_mod
from src.integration.settlement_endogenous_lp_value_packet import (
    SETTLEMENT_ENDOGENOUS_LP_VALUE_PACKET_SCHEMA,
    SettlementEndogenousLPValuePacket,
    build_settlement_endogenous_lp_value_packet_from_price_attestation,
    build_settlement_endogenous_lp_value_packet_from_price_packet,
    verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation,
    verify_settlement_endogenous_lp_value_packet_payload_from_price_packet,
)
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    SettlementSpotPricePacket,
    build_settlement_spot_price_packet,
)
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState
from tests.support.settlement_price_attestation_signer import (
    build_settlement_spot_price_attestation,
)


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


def _price_packet(asset0: str, asset1: str) -> SettlementSpotPricePacket:
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
    settlement = replace(
        settlement,
        lp_deltas=(*settlement.lp_deltas, LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0)),
    )
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
    settlement = replace(
        settlement,
        lp_deltas=(*settlement.lp_deltas, LPDelta(pubkey=pk, pool_id=pool_id, delta_add=2, delta_sub=0)),
    )
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
    settlement = replace(
        settlement,
        lp_deltas=(*settlement.lp_deltas, LPDelta(pubkey=pk, pool_id=pool_id, delta_add=1, delta_sub=0)),
    )
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
    settlement = replace(
        settlement,
        lp_deltas=(*settlement.lp_deltas, LPDelta(pubkey=pk, pool_id=pool_id, delta_add=1, delta_sub=0)),
    )
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


def test_endogenous_lp_value_packet_from_dict_rejects_string_boolean_flags() -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _swap_context()
    settlement = replace(
        settlement,
        lp_deltas=(*settlement.lp_deltas, LPDelta(pubkey=pk, pool_id=pool_id, delta_add=1, delta_sub=0)),
    )
    price_packet = _price_packet(asset0, asset1)
    packet = build_settlement_endogenous_lp_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
        pool_snapshots=(pool,),
    )
    payload = packet.to_dict()
    payload["packet_ok"] = "yes"

    with pytest.raises(TypeError, match="^packet_ok must be a bool$"):
        SettlementEndogenousLPValuePacket.from_dict(payload)


def test_endogenous_lp_value_packet_rejects_bool_pool_snapshot_numeric_fields() -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _swap_context()
    pool_with_unit_reserve = PoolState(
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=1,
        reserve1=pool.reserve1,
        fee_bps=pool.fee_bps,
        lp_supply=pool.lp_supply,
        status=pool.status,
        created_at=pool.created_at,
        curve_tag=pool.curve_tag,
        curve_params=pool.curve_params,
    )
    settlement = replace(
        settlement,
        lp_deltas=(*settlement.lp_deltas, LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0)),
    )
    price_packet = _price_packet(asset0, asset1)
    packet = build_settlement_endogenous_lp_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
        pool_snapshots=(pool_with_unit_reserve,),
    ).to_dict()
    pool_snapshot_payload = dict(packet["pool_snapshots"][0])
    pool_snapshot_payload["reserve0"] = True
    packet["pool_snapshots"][0]["reserve0"] = True

    with pytest.raises(ValueError, match="reserve0 must be an int"):
        SettlementEndogenousLPValuePacket.from_dict(packet)

    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        pool_snapshots_payload=[pool_snapshot_payload],
        packet_payload=packet,
    )

    assert ok is False
    assert err == "reserve0 must be an int"


def test_endogenous_lp_value_packet_price_packet_parse_programmer_error_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, _asset0, _asset1, _pool_id, _pool, settlement = _swap_context()

    def broken_from_dict(_payload: object) -> object:
        raise RuntimeError("endogenous price packet parser bug")

    monkeypatch.setattr(
        endogenous_packet_mod.SettlementSpotPricePacket,
        "from_dict",
        staticmethod(broken_from_dict),
    )

    with pytest.raises(RuntimeError, match="endogenous price packet parser bug"):
        verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload={},
            pool_snapshots_payload=(),
            packet_payload={},
        )


def test_endogenous_lp_value_packet_pool_snapshot_programmer_error_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _swap_context()
    price_packet = _price_packet(asset0, asset1)

    def broken_pool_from_dict(_payload: object) -> object:
        raise RuntimeError("pool snapshot parser bug")

    monkeypatch.setattr(endogenous_packet_mod, "_pool_from_dict", broken_pool_from_dict)

    with pytest.raises(RuntimeError, match="pool snapshot parser bug"):
        verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            pool_snapshots_payload=(_pool_snapshot_payload(pool),),
            packet_payload={},
        )


def test_endogenous_lp_value_packet_expected_builder_programmer_error_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _swap_context()
    price_packet = _price_packet(asset0, asset1)

    def broken_builder(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("endogenous value packet builder bug")

    monkeypatch.setattr(
        endogenous_packet_mod,
        "build_settlement_endogenous_lp_value_packet_from_price_packet",
        broken_builder,
    )

    with pytest.raises(RuntimeError, match="endogenous value packet builder bug"):
        verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            pool_snapshots_payload=(_pool_snapshot_payload(pool),),
            packet_payload={},
        )


def test_endogenous_lp_value_packet_payload_rebuild_programmer_error_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _swap_context()
    price_packet = _price_packet(asset0, asset1)

    def broken_packet_from_dict(_payload: object) -> object:
        raise RuntimeError("endogenous value packet parser bug")

    monkeypatch.setattr(
        endogenous_packet_mod.SettlementEndogenousLPValuePacket,
        "from_dict",
        staticmethod(broken_packet_from_dict),
    )

    with pytest.raises(RuntimeError, match="endogenous value packet parser bug"):
        verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            pool_snapshots_payload=(_pool_snapshot_payload(pool),),
            packet_payload={},
        )


def _pool_snapshot_payload(pool: PoolState) -> dict[str, object]:
    return {
        "pool_id": str(pool.pool_id),
        "asset0": str(pool.asset0),
        "asset1": str(pool.asset1),
        "reserve0": int(pool.reserve0),
        "reserve1": int(pool.reserve1),
        "fee_bps": int(pool.fee_bps),
        "lp_supply": int(pool.lp_supply),
        "status": str(pool.status.name),
        "created_at": int(pool.created_at),
        "curve_tag": str(pool.curve_tag),
        "curve_params": str(pool.curve_params),
    }
