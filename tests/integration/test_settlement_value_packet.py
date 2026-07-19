from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import LPDelta
from src.integration import settlement_value_packet as value_packet_mod
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)
from src.integration.settlement_value_packet import (
    SETTLEMENT_VALUE_PACKET_SCHEMA,
    SettlementValuePacket,
    build_settlement_value_packet_from_price_attestation,
    build_settlement_value_packet_from_price_packet,
    verify_settlement_value_packet_payload_from_price_attestation,
    verify_settlement_value_packet_payload_from_price_packet,
)
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from tests.support.settlement_price_attestation_signer import (
    build_settlement_spot_price_attestation,
)


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _swap_context(intent_index: int = 3300):
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
        intent_id=_iid(intent_index),
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


def test_settlement_value_packet_round_trips_for_spot_packet() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )

    packet = build_settlement_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
    )
    assert packet.schema == SETTLEMENT_VALUE_PACKET_SCHEMA
    assert packet.mode == "spot_only"
    assert packet.price_input_kind == "packet"
    assert packet.spot_value_contract is not None
    assert packet.lp_value_contract is None
    assert packet.packet_ok is True

    ok, err = verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        packet_payload=packet.to_dict(),
    )
    assert ok is True
    assert err is None


def test_settlement_value_packet_round_trips_for_lp_attestation() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
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
    attestation = build_settlement_spot_price_attestation(packet=price_packet, signer_privkey=7)

    packet = build_settlement_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        lp_unit_values={pool_id: 50},
        allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    )
    assert packet.schema == SETTLEMENT_VALUE_PACKET_SCHEMA
    assert packet.mode == "lp_aware"
    assert packet.price_input_kind == "attestation"
    assert packet.spot_value_contract is None
    assert packet.lp_value_contract is not None
    assert packet.lp_liability_balanced_ok is True
    assert packet.packet_ok is True

    ok, err = verify_settlement_value_packet_payload_from_price_attestation(
        settlement=settlement,
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        packet_payload=packet.to_dict(),
        lp_unit_values={pool_id: 50},
        allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    )
    assert ok is True
    assert err is None


def test_settlement_value_packet_rejects_lp_unit_value_snapshot_mismatch() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
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
    attestation = build_settlement_spot_price_attestation(packet=price_packet, signer_privkey=7)

    packet = build_settlement_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        lp_unit_values={pool_id: 50},
        allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    )

    ok, err = verify_settlement_value_packet_payload_from_price_attestation(
        settlement=settlement,
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        packet_payload=packet.to_dict(),
        lp_unit_values={pool_id: 51},
        allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    )
    assert ok is False
    assert err == "settlement value packet mismatch"


def test_settlement_value_packet_rejects_replay_with_different_settlement_identity() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context(3300)
    _pk2, _asset0b, _asset1b, _pool_id2, replay_settlement = _swap_context(3301)
    settlement = replace(
        settlement,
        lp_deltas=(*settlement.lp_deltas, LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0)),
    )
    replay_settlement = replace(
        replay_settlement,
        lp_deltas=(
            *replay_settlement.lp_deltas,
            LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0),
        ),
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
    allowed_signers = {attestation.signer_pubkey: ["oracle:a", "oracle:b"]}

    packet = build_settlement_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        lp_unit_values={pool_id: 50},
        allowed_signers=allowed_signers,
    )
    replay_packet = build_settlement_value_packet_from_price_attestation(
        settlement=replay_settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        lp_unit_values={pool_id: 50},
        allowed_signers=allowed_signers,
    )
    assert packet.lp_value_contract is not None
    assert replay_packet.lp_value_contract is not None
    assert (
        packet.lp_value_contract.settlement_commitment_sha256
        != replay_packet.lp_value_contract.settlement_commitment_sha256
    )

    ok, err = verify_settlement_value_packet_payload_from_price_attestation(
        settlement=replay_settlement,
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        packet_payload=packet.to_dict(),
        lp_unit_values={pool_id: 50},
        allowed_signers=allowed_signers,
    )
    assert ok is False
    assert err == "settlement value packet mismatch"


def test_settlement_value_packet_rejects_missing_lp_projection_entry() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    second_pool_id = f"{pool_id}:secondary"
    settlement = replace(
        settlement,
        lp_deltas=(
            *settlement.lp_deltas,
            LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0),
            LPDelta(pubkey=pk, pool_id=second_pool_id, delta_add=5, delta_sub=0),
        ),
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
    allowed_signers = {attestation.signer_pubkey: ["oracle:a", "oracle:b"]}

    packet = build_settlement_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        lp_unit_values={pool_id: 50, second_pool_id: 75},
        allowed_signers=allowed_signers,
    )
    assert packet.packet_ok is True
    assert packet.lp_value_contract is not None
    assert len(packet.lp_value_contract.lp_unit_values) == 2

    ok, err = verify_settlement_value_packet_payload_from_price_attestation(
        settlement=settlement,
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        packet_payload=packet.to_dict(),
        lp_unit_values={pool_id: 50},
        allowed_signers=allowed_signers,
    )
    assert ok is False
    assert err == f"missing lp unit value for settlement lp value contract: {second_pool_id}"


def test_settlement_value_packet_rejects_lp_aware_packet_ok_floor_downgrade() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
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
    attestation = build_settlement_spot_price_attestation(packet=price_packet, signer_privkey=7)
    allowed_signers = {attestation.signer_pubkey: ["oracle:a", "oracle:b"]}
    packet = build_settlement_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        lp_unit_values={pool_id: 50},
        allowed_signers=allowed_signers,
    )
    assert packet.packet_ok is True

    downgraded = dict(packet.to_dict())
    downgraded["packet_ok"] = False
    ok, err = verify_settlement_value_packet_payload_from_price_attestation(
        settlement=settlement,
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        packet_payload=downgraded,
        lp_unit_values={pool_id: 50},
        allowed_signers=allowed_signers,
    )
    assert ok is False
    assert err == "settlement value packet mismatch"


def test_settlement_value_packet_rejects_missing_attestation_source_allowlist_assumption() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
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
    attestation = build_settlement_spot_price_attestation(packet=price_packet, signer_privkey=7)
    full_allowlist = {attestation.signer_pubkey: ["oracle:a", "oracle:b"]}
    packet = build_settlement_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        lp_unit_values={pool_id: 50},
        allowed_signers=full_allowlist,
    )
    assert packet.packet_ok is True

    ok, err = verify_settlement_value_packet_payload_from_price_attestation(
        settlement=settlement,
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        packet_payload=packet.to_dict(),
        lp_unit_values={pool_id: 50},
        allowed_signers={attestation.signer_pubkey: ["oracle:a"]},
    )
    assert ok is False
    assert err == "invalid settlement spot price attestation: source_id not allowlisted for signer: oracle:b"


def test_settlement_value_packet_rejects_tampering() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )

    packet = build_settlement_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
    )
    bad = dict(packet.to_dict())
    bad["packet_ok"] = False

    ok, err = verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        packet_payload=bad,
    )
    assert ok is False
    assert err == "settlement value packet mismatch"


def test_settlement_value_packet_payload_rejects_string_boolean_flags() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    packet = build_settlement_value_packet_from_price_packet(settlement=settlement, price_packet=price_packet).to_dict()
    packet["packet_ok"] = "yes"

    ok, err = verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        packet_payload=packet,
    )

    assert ok is False
    assert err == "packet_ok must be a bool"


def test_settlement_value_packet_rejects_bool_spot_contract_numeric_fields() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=1, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=1, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    packet = build_settlement_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
    ).to_dict()
    packet["spot_value_contract"]["asset_prices"][0]["price"] = True

    ok, err = verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        packet_payload=packet,
    )

    assert ok is False
    assert err == "price must be an int"


def test_settlement_value_packet_rejects_bool_lp_contract_numeric_fields() -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement = replace(
        settlement,
        lp_deltas=(*settlement.lp_deltas, LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0)),
    )
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=1, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=1, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    attestation = build_settlement_spot_price_attestation(packet=price_packet, signer_privkey=7)
    packet = build_settlement_value_packet_from_price_attestation(
        settlement=settlement,
        price_attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        lp_unit_values={pool_id: 1},
        allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    ).to_dict()
    packet["lp_value_contract"]["lp_unit_values"][0]["unit_value"] = True

    ok, err = verify_settlement_value_packet_payload_from_price_attestation(
        settlement=settlement,
        price_attestation_payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        packet_payload=packet,
        lp_unit_values={pool_id: 1},
        allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
    )

    assert ok is False
    assert err == "unit_value must be an int"


def test_settlement_value_packet_from_dict_round_trips() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    packet = build_settlement_value_packet_from_price_packet(settlement=settlement, price_packet=price_packet)
    rebuilt = SettlementValuePacket.from_dict(packet.to_dict())
    assert rebuilt == packet


def test_settlement_value_packet_price_packet_parse_programmer_error_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, _asset0, _asset1, _pool_id, settlement = _swap_context()

    def broken_from_dict(_payload: object) -> object:
        raise RuntimeError("price packet parser bug")

    monkeypatch.setattr(
        value_packet_mod.SettlementSpotPricePacket,
        "from_dict",
        staticmethod(broken_from_dict),
    )

    with pytest.raises(RuntimeError, match="price packet parser bug"):
        verify_settlement_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload={},
            packet_payload={},
        )


def test_settlement_value_packet_expected_builder_programmer_error_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )

    def broken_builder(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("value packet builder bug")

    monkeypatch.setattr(
        value_packet_mod,
        "build_settlement_value_packet_from_price_packet",
        broken_builder,
    )

    with pytest.raises(RuntimeError, match="value packet builder bug"):
        verify_settlement_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            packet_payload={},
        )


def test_settlement_value_packet_payload_rebuild_programmer_error_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="local:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="local:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )

    def broken_packet_from_dict(_payload: object) -> object:
        raise RuntimeError("value packet parser bug")

    monkeypatch.setattr(
        value_packet_mod.SettlementValuePacket,
        "from_dict",
        staticmethod(broken_packet_from_dict),
    )

    with pytest.raises(RuntimeError, match="value packet parser bug"):
        verify_settlement_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            packet_payload={},
        )
