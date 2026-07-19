from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import LPDelta
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)
from src.integration.settlement_value_contract import (
    SETTLEMENT_SPOT_VALUE_CONTRACT_SCHEMA,
    build_settlement_spot_value_contract,
    build_settlement_spot_value_contract_from_price_attestation,
    build_settlement_spot_value_contract_from_price_packet,
    verify_settlement_spot_value_contract,
)
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
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
        intent_id=_iid(2200),
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
    return pk, asset0, asset1, pool_id, settlement


def test_settlement_spot_value_contract_round_trips_and_zeroes_net_value() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    prices = {
        asset0: 100,
        asset1: 120,
    }

    contract = build_settlement_spot_value_contract(settlement=settlement, asset_prices=prices)

    assert contract.schema == SETTLEMENT_SPOT_VALUE_CONTRACT_SCHEMA
    assert contract.asset_conservation_ok is True
    assert contract.value_conservation_ok is True
    assert contract.net_value_sum == 0
    assert contract.balance_value_sum == -contract.reserve_value_sum
    assert len(contract.asset_nets) == 2
    assert all(entry.net_delta == 0 for entry in contract.asset_nets)

    ok, err = verify_settlement_spot_value_contract(
        settlement=settlement,
        asset_prices=prices,
        contract=contract,
    )
    assert ok is True
    assert err is None


def test_settlement_spot_value_contract_rejects_missing_price_coverage() -> None:
    _pk, asset0, _asset1, _pool_id, settlement = _swap_context()

    with pytest.raises(ValueError, match="missing asset price"):
        build_settlement_spot_value_contract(
            settlement=settlement,
            asset_prices={asset0: 100},
        )


def test_settlement_spot_value_contract_rejects_lp_delta_scope_violation() -> None:
    pk, asset0, _asset1, pool_id, settlement = _swap_context()
    settlement = replace(
        settlement,
        lp_deltas=(*settlement.lp_deltas, LPDelta(pubkey=pk, pool_id=pool_id, delta_add=1, delta_sub=0)),
    )

    with pytest.raises(ValueError, match="empty lp_deltas"):
        build_settlement_spot_value_contract(
            settlement=settlement,
            asset_prices={asset0: 100, "0x" + "02" * 32: 120},
        )


def test_settlement_spot_value_contract_rejects_tampering() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    prices = {
        asset0: 100,
        asset1: 120,
    }
    contract = build_settlement_spot_value_contract(settlement=settlement, asset_prices=prices)
    bad = replace(contract, net_value_sum=1)

    ok, err = verify_settlement_spot_value_contract(
        settlement=settlement,
        asset_prices=prices,
        contract=bad,
    )
    assert ok is False
    assert err == "settlement spot value contract mismatch"


def test_settlement_spot_value_contract_builds_from_provenance_packet() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )

    contract = build_settlement_spot_value_contract_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
    )
    assert contract.schema == SETTLEMENT_SPOT_VALUE_CONTRACT_SCHEMA
    assert contract.value_conservation_ok is True
    assert contract.net_value_sum == 0


def test_settlement_spot_value_contract_builds_from_attested_price_packet() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    price_attestation = build_settlement_spot_price_attestation(
        packet=price_packet,
        signer_privkey=7,
    )

    contract = build_settlement_spot_value_contract_from_price_attestation(
        settlement=settlement,
        price_attestation=price_attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        allowed_signers={price_attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    )
    assert contract.schema == SETTLEMENT_SPOT_VALUE_CONTRACT_SCHEMA
    assert contract.value_conservation_ok is True
    assert contract.net_value_sum == 0
