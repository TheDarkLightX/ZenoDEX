from __future__ import annotations

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import LPDelta
import src.integration.settlement_lp_value_contract as lp_value_contract
import src.integration.settlement_price_attestation as price_attestation
from src.integration.settlement_lp_value_contract import (
    SETTLEMENT_LP_VALUE_CONTRACT_SCHEMA,
    build_settlement_lp_value_contract,
    build_settlement_lp_value_contract_from_price_attestation,
    build_settlement_lp_value_contract_from_price_packet,
    verify_settlement_lp_value_contract,
    verify_settlement_lp_value_contract_payload,
    verify_settlement_lp_value_contract_payload_from_price_attestation,
    verify_settlement_lp_value_contract_payload_from_price_packet,
)
from src.integration.settlement_price_attestation import build_settlement_spot_price_attestation
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)
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
    return pk, asset0, asset1, pool_id, settlement


def test_settlement_lp_value_contract_round_trips_with_explicit_lp_liability() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=5, delta_sub=0))
    contract = build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices={asset0: 100, asset1: 120},
        lp_unit_values={pool_id: 77},
    )

    assert contract.schema == SETTLEMENT_LP_VALUE_CONTRACT_SCHEMA
    assert contract.lp_user_value_sum == 5 * 77
    assert contract.lp_protocol_liability_value_sum == -(5 * 77)
    assert contract.lp_liability_balanced_ok is True
    assert contract.value_conservation_ok is True
    assert contract.net_value_sum == 0

    ok, err = verify_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices={asset0: 100, asset1: 120},
        lp_unit_values={pool_id: 77},
        contract=contract,
    )
    assert ok is True
    assert err is None


def test_settlement_lp_value_contract_rejects_missing_lp_unit_value() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=5, delta_sub=0))

    try:
        build_settlement_lp_value_contract(
            settlement=settlement,
            asset_prices={asset0: 100, asset1: 120},
            lp_unit_values={},
        )
    except ValueError as exc:
        assert "lp_unit_values" in str(exc) or "missing lp unit value" in str(exc)
    else:
        raise AssertionError("expected missing lp unit value failure")


def test_settlement_lp_value_contract_builds_from_price_attestation() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    attestation = build_settlement_spot_price_attestation(packet=packet, signer_privkey=7)

    contract = build_settlement_lp_value_contract_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        lp_unit_values={pool_id: 91},
        allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    )
    assert contract.lp_user_value_sum == 3 * 91
    assert contract.lp_protocol_liability_value_sum == -(3 * 91)
    assert contract.value_conservation_ok is True


def test_verify_lp_value_contract_payload_rejects_expected_contract_parse_error() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=5, delta_sub=0))

    ok, err = verify_settlement_lp_value_contract_payload(
        settlement=settlement,
        asset_prices={asset0: 100, asset1: 120},
        lp_unit_values={pool_id: 77},
        contract_payload={"asset_prices": "not-a-list"},
    )

    assert ok is False
    assert err == "contract.asset_prices must be a list"


def test_verify_lp_value_contract_payload_caps_malformed_contract_error() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=5, delta_sub=0))

    ok, err = verify_settlement_lp_value_contract_payload(
        settlement=settlement,
        asset_prices={asset0: 100, asset1: 120},
        lp_unit_values={pool_id: 77},
        contract_payload={
            "asset_prices": [{"asset": asset0, "price": "9" * 1_000 + "x"}],
            "lp_unit_values": [{"pool_id": pool_id, "unit_value": 77}],
            "asset_nets": [],
            "lp_nets": [],
        },
    )

    assert ok is False
    assert err is not None
    assert len(err) <= 200
    assert "9" * 201 not in err


def test_verify_lp_value_contract_payload_surfaces_unexpected_contract_parse_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=5, delta_sub=0))

    def fail_from_dict(
        cls: type[lp_value_contract.SettlementLPValueContract],
        payload: object,
    ) -> lp_value_contract.SettlementLPValueContract:
        raise RuntimeError("unexpected lp value contract parse fault")

    monkeypatch.setattr(
        lp_value_contract.SettlementLPValueContract,
        "from_dict",
        classmethod(fail_from_dict),
    )

    with pytest.raises(RuntimeError, match="unexpected lp value contract parse fault"):
        verify_settlement_lp_value_contract_payload(
            settlement=settlement,
            asset_prices={asset0: 100, asset1: 120},
            lp_unit_values={pool_id: 77},
            contract_payload={},
        )


def test_verify_lp_value_contract_payload_from_price_packet_surfaces_unexpected_packet_parse_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=5, delta_sub=0))
    contract = build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices={asset0: 100, asset1: 120},
        lp_unit_values={pool_id: 77},
    )

    def fail_from_dict(
        cls: type[lp_value_contract.SettlementSpotPricePacket],
        payload: object,
    ) -> lp_value_contract.SettlementSpotPricePacket:
        raise RuntimeError("unexpected lp price packet parse fault")

    monkeypatch.setattr(
        lp_value_contract.SettlementSpotPricePacket,
        "from_dict",
        classmethod(fail_from_dict),
    )

    with pytest.raises(RuntimeError, match="unexpected lp price packet parse fault"):
        verify_settlement_lp_value_contract_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload={},
            lp_unit_values={pool_id: 77},
            contract_payload=contract.to_dict(),
        )


def test_verify_lp_value_contract_payload_from_price_attestation_surfaces_unexpected_attestation_parse_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=5, delta_sub=0))
    contract = build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices={asset0: 100, asset1: 120},
        lp_unit_values={pool_id: 77},
    )

    def fail_from_dict(
        cls: type[price_attestation.SettlementSpotPriceAttestation],
        payload: object,
    ) -> price_attestation.SettlementSpotPriceAttestation:
        raise RuntimeError("unexpected lp price attestation parse fault")

    monkeypatch.setattr(
        price_attestation.SettlementSpotPriceAttestation,
        "from_dict",
        classmethod(fail_from_dict),
    )

    with pytest.raises(RuntimeError, match="unexpected lp price attestation parse fault"):
        verify_settlement_lp_value_contract_payload_from_price_attestation(
            settlement=settlement,
            price_attestation_payload={},
            consumer_now_epoch=103,
            max_attestation_age_epochs=5,
            lp_unit_values={pool_id: 77},
            contract_payload=contract.to_dict(),
        )


def test_verify_lp_value_contract_payload_from_price_packet_rejects_expected_contract_parse_error() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=5, delta_sub=0))
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )

    ok, err = verify_settlement_lp_value_contract_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=packet.to_dict(),
        lp_unit_values={pool_id: 77},
        contract_payload={"asset_prices": "not-a-list"},
    )

    assert ok is False
    assert err == "contract.asset_prices must be a list"


def test_settlement_lp_value_contract_builds_from_price_packet() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )

    contract = build_settlement_lp_value_contract_from_price_packet(
        settlement=settlement,
        price_packet=packet,
        lp_unit_values={pool_id: 91},
    )

    assert contract.lp_user_value_sum == 3 * 91
    assert contract.lp_protocol_liability_value_sum == -(3 * 91)
    assert contract.value_conservation_ok is True
