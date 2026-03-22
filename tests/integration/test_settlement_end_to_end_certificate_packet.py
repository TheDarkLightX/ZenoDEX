from __future__ import annotations

from tests.integration._attestation_policy_helper import make_attestation_policy

from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import LPDelta
from src.integration.settlement_feature_extension_packet import SettlementFeatureExtensionInputs
from src.integration.settlement_end_to_end_certificate_packet import (
    SETTLEMENT_END_TO_END_CERTIFICATE_PACKET_SCHEMA,
    build_settlement_end_to_end_certificate_packet_from_price_attestation,
    build_settlement_end_to_end_certificate_packet_from_price_packet,
    verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation,
    verify_settlement_end_to_end_certificate_packet_payload_from_price_packet,
)
from src.integration.settlement_price_attestation import build_settlement_spot_price_attestation
from src.integration.settlement_price_provenance import SettlementSpotPriceEntry, build_settlement_spot_price_packet
from src.integration.settlement_strong_certificate import SettlementProofFlags
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
        intent_id=_iid(4400),
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


def _four_swap_context():
    pk = "0x" + "22" * 48
    asset0 = "0x" + "03" * 32
    asset1 = "0x" + "04" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 100_000)
    balances.set(pk, asset1, 0)
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(idx + 1),
            sender_pubkey=pk,
            deadline=9_999_999_999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            },
        )
        for idx in range(4)
    ]
    settlement = compute_settlement(intents, {pool_id: pool}, balances, LPTable())
    return pk, asset0, asset1, pool_id, pool, settlement


def _feature_extension_inputs() -> SettlementFeatureExtensionInputs:
    return SettlementFeatureExtensionInputs(
        trade_amount=100,
        fee_charged=1,
        buyback_amount=1,
        burned_amount=1,
        supply_before=1_000,
        supply_after=999,
        supply_floor=500,
        unit_scale=1,
        rebate_rate_bps=500,
        rebate_amount=1,
        rebate_cap=1,
        lock_days=60,
        stake_amount=50,
        tier1_days=30,
        tier2_days=90,
        weight_t1=1,
        weight_t2=2,
        weight_t3=3,
        weight_claimed=2,
        weighted_stake=100,
    )


def test_end_to_end_certificate_packet_round_trips_for_spot_packet() -> None:
    _pk, asset0, asset1, _pool_id, _pool, settlement = _four_swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    packet = build_settlement_end_to_end_certificate_packet_from_price_packet(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        price_history=(100, 110, 120),
        feature_extension_inputs=_feature_extension_inputs(),
        price_packet=price_packet,
    )
    assert packet.schema == SETTLEMENT_END_TO_END_CERTIFICATE_PACKET_SCHEMA
    assert packet.value_packet_kind == "declared_value"
    assert packet.strong_certificate_ok is True
    assert packet.full_price_rails_ok is True
    assert packet.packet_ok is True

    ok, err = verify_settlement_end_to_end_certificate_packet_payload_from_price_packet(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        price_history=(100, 110, 120),
        feature_extension_inputs_payload=_feature_extension_inputs().to_dict(),
        price_packet_payload=price_packet.to_dict(),
        packet_payload=packet.to_dict(),
    )
    assert ok is True
    assert err is None


def test_end_to_end_certificate_packet_round_trips_for_endogenous_attestation() -> None:
    pk, asset0, asset1, pool_id, pool, settlement = _four_swap_context()
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
    packet = build_settlement_end_to_end_certificate_packet_from_price_attestation(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        price_history=(100, 110, 120),
        feature_extension_inputs=_feature_extension_inputs(),
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        pool_snapshots=(pool,),
        attestation_policy=attestation_policy,
    )
    assert packet.value_packet_kind == "endogenous_lp_value"
    assert packet.price_input_kind == "attestation"
    assert packet.lp_liability_balanced_ok is True
    assert packet.packet_ok is True
    assert packet.endogenous_lp_value_packet is not None
    assert packet.endogenous_lp_value_packet.attestation_policy_id == attestation_policy.policy_id

    ok, err = verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        price_history=(100, 110, 120),
        feature_extension_inputs_payload=_feature_extension_inputs().to_dict(),
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        pool_snapshots_payload=[{
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
        }],
        packet_payload=packet.to_dict(),
        attestation_policy=attestation_policy,
    )
    assert ok is True
    assert err is None


def test_end_to_end_certificate_packet_rejects_tampering() -> None:
    _pk, asset0, asset1, _pool_id, _pool, settlement = _four_swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    packet = build_settlement_end_to_end_certificate_packet_from_price_packet(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        price_history=(100, 110, 120),
        feature_extension_inputs=_feature_extension_inputs(),
        price_packet=price_packet,
    )
    bad = dict(packet.to_dict())
    bad["packet_ok"] = False

    ok, err = verify_settlement_end_to_end_certificate_packet_payload_from_price_packet(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        price_history=(100, 110, 120),
        feature_extension_inputs_payload=_feature_extension_inputs().to_dict(),
        price_packet_payload=price_packet.to_dict(),
        packet_payload=bad,
    )
    assert ok is False
    assert err == "settlement end-to-end certificate packet mismatch"


def test_end_to_end_certificate_packet_from_attestation_requires_policy() -> None:
    _pk, asset0, asset1, _pool_id, pool, settlement = _four_swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    attestation = build_settlement_spot_price_attestation(packet=price_packet, signer_privkey=7)

    try:
        build_settlement_end_to_end_certificate_packet_from_price_attestation(
            settlement=settlement,
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_attestation=attestation,
            consumer_now_epoch=103,
            max_attestation_age_epochs=5,
            pool_snapshots=(pool,),
            attestation_policy=None,
        )
    except ValueError as exc:
        assert str(exc).startswith(
            "invalid settlement spot price attestation: settlement spot price attestation requires attestation_policy"
        )
    else:
        raise AssertionError("expected attestation packet build without policy to fail")
