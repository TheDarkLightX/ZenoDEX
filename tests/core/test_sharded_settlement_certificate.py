from __future__ import annotations

from copy import deepcopy

from src.core.sharded_settlement_certificate import (
    CrossShardLegV1,
    ShardedSettlementCertificateV1,
    ShardedSettlementShardV1,
    build_sharded_settlement_certificate,
    shard_ids_hash,
    sharded_settlement_certificate_hash,
    verify_sharded_settlement_certificate_payload,
)


def _hash(label: str) -> str:
    return "0x" + label * 64


def _shards() -> tuple[ShardedSettlementShardV1, ...]:
    return (
        ShardedSettlementShardV1(
            shard_id="shard-a",
            settlement_root_hash=_hash("a"),
            dx_atoms=100,
            dy_atoms=-100,
        ),
        ShardedSettlementShardV1(
            shard_id="shard-b",
            settlement_root_hash=_hash("b"),
            dx_atoms=50,
            dy_atoms=-50,
        ),
    )


def _legs() -> tuple[CrossShardLegV1, ...]:
    return (
        CrossShardLegV1(
            transfer_id="transfer-1",
            side="credit",
            shard_id="shard-b",
            counterparty_shard_id="shard-a",
            asset_id="quote",
            amount_atoms=1_000,
        ),
        CrossShardLegV1(
            transfer_id="transfer-1",
            side="debit",
            shard_id="shard-a",
            counterparty_shard_id="shard-b",
            asset_id="quote",
            amount_atoms=1_000,
        ),
    )


def _payload() -> dict[str, object]:
    cert = build_sharded_settlement_certificate(
        batch_id="batch-1",
        shards=_shards(),
        cross_shard_legs=_legs(),
    )
    return cert.to_payload()


def test_sharded_settlement_certificate_accepts_balanced_shards_and_matched_legs() -> None:
    payload = _payload()

    result = verify_sharded_settlement_certificate_payload(
        payload,
        expected_shard_ids=("shard-a", "shard-b"),
    )

    assert result.ok is True
    assert result.error is None
    assert result.shard_count == 2
    assert result.cross_shard_transfer_count == 1
    assert result.shard_ids_hash == shard_ids_hash(("shard-a", "shard-b"))
    assert result.certificate_hash == sharded_settlement_certificate_hash(payload)


def test_sharded_settlement_certificate_rejects_missing_expected_shard() -> None:
    result = verify_sharded_settlement_certificate_payload(
        _payload(),
        expected_shard_ids=("shard-a", "shard-b", "shard-c"),
    )

    assert result == result.__class__(
        ok=False,
        error="certificate shard ids do not match expected shard ids",
    )


def test_sharded_settlement_certificate_rejects_duplicate_shard_id() -> None:
    payload = _payload()
    payload["shards"] = [
        payload["shards"][0],
        {**payload["shards"][0], "settlement_root_hash": _hash("c")},
    ]
    payload["shard_ids_hash"] = shard_ids_hash(("shard-a", "shard-a"))

    result = verify_sharded_settlement_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="duplicate shard_id in certificate.shards",
    )


def test_sharded_settlement_certificate_rejects_unbalanced_shard() -> None:
    payload = _payload()
    payload["shards"][0]["dy_atoms"] = -99
    payload["shard_ids_hash"] = shard_ids_hash(("shard-a", "shard-b"))

    result = verify_sharded_settlement_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="shard shard-a is not balanced",
    )


def test_sharded_settlement_certificate_rejects_shard_ids_hash_mismatch() -> None:
    payload = _payload()
    payload["shard_ids_hash"] = _hash("f")

    result = verify_sharded_settlement_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="certificate.shard_ids_hash mismatch",
    )


def test_sharded_settlement_certificate_rejects_unmatched_cross_shard_leg() -> None:
    payload = _payload()
    payload["cross_shard_legs"] = [payload["cross_shard_legs"][0]]

    result = verify_sharded_settlement_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="cross-shard transfer transfer-1 must have exactly two legs",
    )


def test_sharded_settlement_certificate_rejects_cross_shard_amount_mismatch() -> None:
    payload = _payload()
    payload["cross_shard_legs"][1]["amount_atoms"] = 999

    result = verify_sharded_settlement_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="cross-shard transfer transfer-1 amount mismatch",
    )


def test_sharded_settlement_certificate_rejects_unknown_shard_reference() -> None:
    payload = _payload()
    payload["cross_shard_legs"][1]["shard_id"] = "shard-z"

    result = verify_sharded_settlement_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="cross-shard leg references unknown shard_id",
    )


def test_sharded_settlement_certificate_rejects_unsorted_cross_shard_legs() -> None:
    payload = _payload()
    payload["cross_shard_legs"] = list(reversed(payload["cross_shard_legs"]))

    result = verify_sharded_settlement_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="certificate.cross_shard_legs must be strictly sorted",
    )


def test_sharded_settlement_certificate_rejects_unknown_certificate_field() -> None:
    payload = _payload()
    payload["unexpected"] = True

    result = verify_sharded_settlement_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="certificate has unsupported fields: unexpected",
    )


def test_sharded_settlement_certificate_rejects_bool_delta() -> None:
    payload = deepcopy(_payload())
    payload["shards"][0]["dx_atoms"] = True

    result = verify_sharded_settlement_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="shard.dx_atoms must be an int",
    )


def test_sharded_settlement_certificate_constructor_rejects_non_shard_record() -> None:
    try:
        ShardedSettlementCertificateV1(
            batch_id="batch-1",
            shard_ids_hash=shard_ids_hash(("shard-a",)),
            shards=("shard-a",),
        )
    except TypeError as exc:
        assert str(exc) == "certificate.shards must contain shard records"
        return
    raise AssertionError("expected constructor to reject non-shard record")


def test_sharded_settlement_certificate_constructor_rejects_non_leg_record() -> None:
    try:
        ShardedSettlementCertificateV1(
            batch_id="batch-1",
            shard_ids_hash=shard_ids_hash(("shard-a",)),
            shards=(
                ShardedSettlementShardV1(
                    shard_id="shard-a",
                    settlement_root_hash=_hash("a"),
                    dx_atoms=0,
                    dy_atoms=0,
                ),
            ),
            cross_shard_legs=("transfer-1",),
        )
    except TypeError as exc:
        assert str(exc) == "certificate.cross_shard_legs must contain leg records"
        return
    raise AssertionError("expected constructor to reject non-leg record")
