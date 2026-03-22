from __future__ import annotations

from tests.integration._attestation_policy_helper import make_attestation_policy

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
    attestation_policy = make_attestation_policy(attestation)

    packet = build_settlement_endogenous_lp_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        pool_snapshots=(pool,),
        attestation_policy=attestation_policy,
    )
    assert packet.price_input_kind == "attestation"
    assert packet.price_attestation is not None
    assert packet.packet_ok is True
    assert packet.attestation_policy_id == attestation_policy.policy_id
    assert packet.attestation_policy_epoch == attestation_policy.policy_epoch
    assert packet.attestation_policy_root == attestation_policy.registry_root
    assert packet.attestation_policy_hash == attestation_policy.policy_hash_hex()

    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation(
        settlement=settlement,
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        pool_snapshots_payload=list(packet.pool_snapshots),
        packet_payload=packet.to_dict(),
        attestation_policy=attestation_policy,
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
