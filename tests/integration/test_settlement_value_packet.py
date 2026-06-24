from __future__ import annotations

import pytest

import src.integration.settlement_value_packet as value_packet
from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import LPDelta
from src.integration.settlement_price_attestation import build_settlement_spot_price_attestation
from src.integration.settlement_price_provenance import SettlementSpotPriceEntry, build_settlement_spot_price_packet
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


def _price_packet_for(asset0: str, asset1: str, *, source_prefix: str = "local"):
    return build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(
                asset=asset0,
                price=100,
                observed_epoch=95,
                age_epochs=5,
                source_id=f"{source_prefix}:a",
            ),
            SettlementSpotPriceEntry(
                asset=asset1,
                price=120,
                observed_epoch=97,
                age_epochs=3,
                source_id=f"{source_prefix}:b",
            ),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )


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
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
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
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
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
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
    replay_settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
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
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=second_pool_id, delta_add=5, delta_sub=0))
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
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
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
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
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


@pytest.mark.parametrize(
    "flag_name",
    (
        "price_provenance_ok",
        "attestation_ok",
        "asset_conservation_ok",
        "lp_liability_balanced_ok",
        "value_conservation_ok",
        "packet_ok",
    ),
)
def test_verify_settlement_value_packet_rejects_int_bool_flags(flag_name: str) -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)
    packet = build_settlement_value_packet_from_price_packet(settlement=settlement, price_packet=price_packet)
    payload = packet.to_dict()
    payload[flag_name] = int(payload[flag_name])

    ok, err = verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        packet_payload=payload,
    )

    assert ok is False
    assert err == f"{flag_name} must be bool"


def test_verify_value_packet_rejects_expected_price_packet_parse_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _reject_from_dict(*args: object, **kwargs: object) -> object:
        raise ValueError("value price packet payload invalid")

    monkeypatch.setattr(value_packet.SettlementSpotPricePacket, "from_dict", _reject_from_dict)

    ok, err = verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        packet_payload={},
    )

    assert ok is False
    assert err == "value price packet payload invalid"


def test_verify_value_packet_surfaces_unexpected_price_packet_parse_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _boom_from_dict(*args: object, **kwargs: object) -> object:
        raise RuntimeError("value price packet parser internal fault")

    monkeypatch.setattr(value_packet.SettlementSpotPricePacket, "from_dict", _boom_from_dict)

    with pytest.raises(RuntimeError, match="value price packet parser internal fault"):
        verify_settlement_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            packet_payload={},
        )


def test_verify_value_packet_rejects_expected_builder_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _reject_build(*args: object, **kwargs: object) -> object:
        raise ValueError("value packet input invalid")

    monkeypatch.setattr(value_packet, "build_settlement_value_packet_from_price_packet", _reject_build)

    ok, err = verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        packet_payload={},
    )

    assert ok is False
    assert err == "value packet input invalid"


def test_verify_value_packet_surfaces_unexpected_builder_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _boom_build(*args: object, **kwargs: object) -> object:
        raise RuntimeError("value packet builder internal fault")

    monkeypatch.setattr(value_packet, "build_settlement_value_packet_from_price_packet", _boom_build)

    with pytest.raises(RuntimeError, match="value packet builder internal fault"):
        verify_settlement_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            packet_payload={},
        )


def test_verify_value_packet_rejects_expected_packet_payload_parse_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _reject_packet(*args: object, **kwargs: object) -> object:
        raise ValueError("value packet payload invalid")

    monkeypatch.setattr(value_packet.SettlementValuePacket, "from_dict", _reject_packet)

    ok, err = verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        packet_payload={},
    )

    assert ok is False
    assert err == "value packet payload invalid"


def test_verify_value_packet_caps_malformed_packet_payload_error() -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)
    packet = build_settlement_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
    )
    bad_packet_payload = packet.to_dict()
    assert bad_packet_payload["spot_value_contract"] is not None
    bad_packet_payload["spot_value_contract"]["asset_prices"][0]["price"] = "9" * 1_000 + "x"

    ok, err = verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=price_packet.to_dict(),
        packet_payload=bad_packet_payload,
    )

    assert ok is False
    assert err is not None
    assert len(err) <= 200
    assert "9" * 201 not in err


def test_verify_value_packet_surfaces_unexpected_packet_payload_parse_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _pk, asset0, asset1, _pool_id, settlement = _swap_context()
    price_packet = _price_packet_for(asset0, asset1)

    def _boom_packet(*args: object, **kwargs: object) -> object:
        raise RuntimeError("value packet payload parser internal fault")

    monkeypatch.setattr(value_packet.SettlementValuePacket, "from_dict", _boom_packet)

    with pytest.raises(RuntimeError, match="value packet payload parser internal fault"):
        verify_settlement_value_packet_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=price_packet.to_dict(),
            packet_payload={},
        )


def test_verify_attestation_value_packet_surfaces_unexpected_builder_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pk, asset0, asset1, pool_id, settlement = _swap_context()
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
    price_packet = _price_packet_for(asset0, asset1, source_prefix="oracle")
    attestation = build_settlement_spot_price_attestation(packet=price_packet, signer_privkey=7)

    def _boom_build(*args: object, **kwargs: object) -> object:
        raise RuntimeError("attestation value packet builder internal fault")

    monkeypatch.setattr(value_packet, "build_settlement_value_packet_from_price_attestation", _boom_build)

    with pytest.raises(RuntimeError, match="attestation value packet builder internal fault"):
        verify_settlement_value_packet_payload_from_price_attestation(
            settlement=settlement,
            price_attestation_payload=attestation.to_dict(),
            consumer_now_epoch=103,
            max_attestation_age_epochs=5,
            packet_payload={},
            lp_unit_values={pool_id: 50},
            allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
        )
