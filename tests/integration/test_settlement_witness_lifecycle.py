from __future__ import annotations

from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.integration.settlement_end_to_end_certificate_packet import (
    SettlementEndToEndCertificateInputs,
)
from src.integration.settlement_feature_extension_packet import SettlementFeatureExtensionInputs
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)
from src.integration.settlement_strong_certificate import SettlementProofFlags
from src.integration.settlement_witness_lifecycle import (
    SETTLEMENT_WITNESS_LIFECYCLE_PACKET_SCHEMA,
    build_settlement_witness_lifecycle_packet,
    verify_settlement_witness_lifecycle_packet_payload,
)
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


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


def _settlement_context(
    *,
    deadline: int = 9_999_999_999,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: str | None = None,
):
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
            deadline=deadline,
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
    settlement = compute_settlement(
        intents,
        {pool_id: pool},
        balances,
        LPTable(),
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    certificate_inputs = SettlementEndToEndCertificateInputs(
        proof_flags=SettlementProofFlags.all_true(),
        price_history=(100, 110, 120),
        feature_extension_inputs=_feature_extension_inputs(),
        price_packet=price_packet,
    )
    return intents, settlement, balances, {pool_id: pool}, certificate_inputs


def test_settlement_witness_lifecycle_packet_accepts_valid_witness_before_expiry() -> None:
    intents, settlement, balances, pools, certificate_inputs = _settlement_context()

    packet = build_settlement_witness_lifecycle_packet(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_end_to_end_certificate_inputs=certificate_inputs,
    )

    assert packet.schema == SETTLEMENT_WITNESS_LIFECYCLE_PACKET_SCHEMA
    assert packet.packet_built is True
    assert packet.end_to_end_packet_ok is True
    assert packet.witness_present is True
    assert packet.witness_valid is True
    assert packet.before_expiry is True
    assert packet.settled is True
    assert packet.rejected_with_reason is False
    assert packet.rejection_reason is None
    assert packet.lifecycle_ok is True

    ok, err = verify_settlement_witness_lifecycle_packet_payload(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_end_to_end_certificate_inputs=certificate_inputs,
        packet_payload=packet.to_dict(),
    )
    assert ok is True
    assert err is None


def test_settlement_witness_lifecycle_packet_rejects_with_reason_when_packet_fails() -> None:
    intents, settlement, balances, pools, certificate_inputs = _settlement_context()
    bad_inputs = SettlementEndToEndCertificateInputs(
        proof_flags=certificate_inputs.proof_flags,
        price_history=(0, 60, 70),
        feature_extension_inputs=certificate_inputs.feature_extension_inputs,
        price_packet=certificate_inputs.price_packet,
    )

    packet = build_settlement_witness_lifecycle_packet(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_end_to_end_certificate_inputs=bad_inputs,
    )

    assert packet.packet_built is True
    assert packet.end_to_end_packet_ok is False
    assert packet.witness_present is False
    assert packet.witness_valid is False
    assert packet.settled is False
    assert packet.rejected_with_reason is True
    assert packet.rejection_reason == "settlement end-to-end certificate full price rails rejected"
    assert packet.lifecycle_ok is True


def test_settlement_witness_lifecycle_packet_rejects_expired_witness_with_reason() -> None:
    intents, settlement, balances, pools, certificate_inputs = _settlement_context(deadline=50)

    packet = build_settlement_witness_lifecycle_packet(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=51,
        settlement_end_to_end_certificate_inputs=certificate_inputs,
    )

    assert packet.packet_built is True
    assert packet.end_to_end_packet_ok is True
    assert packet.witness_valid is True
    assert packet.before_expiry is False
    assert packet.settled is False
    assert packet.rejected_with_reason is True
    assert packet.rejection_reason == f"Intent expired: {intents[0].intent_id}"
    assert packet.lifecycle_ok is True


def test_settlement_witness_lifecycle_packet_rejects_tampering() -> None:
    intents, settlement, balances, pools, certificate_inputs = _settlement_context()
    packet = build_settlement_witness_lifecycle_packet(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_end_to_end_certificate_inputs=certificate_inputs,
    )
    payload = packet.to_dict()
    payload["settled"] = False

    ok, err = verify_settlement_witness_lifecycle_packet_payload(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_end_to_end_certificate_inputs=certificate_inputs,
        packet_payload=payload,
    )
    assert ok is False
    assert err == "settlement witness lifecycle packet payload mismatch"


def test_witness_lifecycle_preserves_protocol_fee_policy() -> None:
    protocol_recipient = "0x" + "ff" * 48
    intents, settlement, balances, pools, certificate_inputs = _settlement_context(
        protocol_fee_share_bps=10_000,
        protocol_fee_recipient_pubkey=protocol_recipient,
    )
    assert sum(fill.protocol_fee_paid for fill in settlement.fills) > 0

    packet = build_settlement_witness_lifecycle_packet(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_end_to_end_certificate_inputs=certificate_inputs,
        protocol_fee_share_bps=10_000,
        protocol_fee_recipient_pubkey=protocol_recipient,
    )

    assert packet.settled is True
    assert packet.witness_valid is True

    ok, err = verify_settlement_witness_lifecycle_packet_payload(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_end_to_end_certificate_inputs=certificate_inputs,
        packet_payload=packet.to_dict(),
        protocol_fee_share_bps=10_000,
        protocol_fee_recipient_pubkey=protocol_recipient,
    )

    assert ok is True
    assert err is None
