from __future__ import annotations

from src.core.perp_oi_depth_certificate import (
    certificate_payload,
    certificate_payload_from_fields,
    oi_depth_source_authority_hash,
    source_authority_binding_payload_from_fields,
    source_authority_payload_from_fields,
    source_set_hash,
    verify_oi_depth_certificate_payload,
    verify_oi_depth_source_authority_binding_payload,
    verify_oi_depth_source_authority_payload,
)

STATE_ROOT = "sha256:" + "11" * 32
OTHER_STATE_ROOT = "sha256:" + "12" * 32
POLICY_HASH = "sha256:" + "22" * 32
OTHER_POLICY_HASH = "sha256:" + "23" * 32


def _payload(**updates: object) -> dict[str, object]:
    payload = certificate_payload_from_fields(
        market_id="perp:btc-usd",
        valid_from_epoch=2,
        valid_until_epoch=4,
        spot_depth_quote=1_000_000,
        arbitrage_absorb_bps=5_000,
        source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    payload.update(updates)
    return payload


def _authority(**updates: object) -> dict[str, object]:
    payload = source_authority_payload_from_fields(
        market_id="perp:btc-usd",
        valid_from_epoch=2,
        valid_until_epoch=4,
        authorized_source_ids=(
            "depth:amm:btc-usd",
            "depth:orderbook:btc-usd",
            "depth:vwap:btc-usd",
        ),
    )
    payload.update(updates)
    return payload


def _authority_object():
    verdict = verify_oi_depth_source_authority_payload(
        _authority(),
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        required_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    assert verdict.ok is True
    assert verdict.authority is not None
    return verdict.authority


def _binding(**updates: object) -> dict[str, object]:
    authority = _authority_object()
    payload = source_authority_binding_payload_from_fields(
        market_id="perp:btc-usd",
        valid_from_epoch=2,
        valid_until_epoch=4,
        authority_hash=oi_depth_source_authority_hash(authority),
        authority_state_root_hash=STATE_ROOT,
        policy_hash=POLICY_HASH,
        signer_privkey=1,
    )
    payload.update(updates)
    return payload


def _allowed_signer_from(payload: dict[str, object]) -> tuple[str, ...]:
    signer = payload["signer_pubkey"]
    assert isinstance(signer, str)
    return (signer,)


def test_oi_depth_certificate_accepts_market_epoch_and_scalar_binding() -> None:
    verdict = verify_oi_depth_certificate_payload(
        _payload(),
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        expected_spot_depth_quote=1_000_000,
        expected_arbitrage_absorb_bps=5_000,
    )

    assert verdict.ok is True
    assert verdict.error is None
    assert verdict.certificate is not None
    assert verdict.certificate.spot_depth_quote == 1_000_000


def test_oi_depth_certificate_rejects_cross_market_replay() -> None:
    verdict = verify_oi_depth_certificate_payload(
        _payload(),
        expected_market_id="perp:eth-usd",
        now_epoch=3,
    )

    assert verdict.ok is False
    assert verdict.error == "market_id mismatch"


def test_oi_depth_certificate_rejects_stale_epoch_replay() -> None:
    verdict = verify_oi_depth_certificate_payload(
        _payload(),
        expected_market_id="perp:btc-usd",
        now_epoch=5,
    )

    assert verdict.ok is False
    assert verdict.error == "certificate epoch out of range"


def test_oi_depth_certificate_rejects_source_set_hash_mismatch() -> None:
    verdict = verify_oi_depth_certificate_payload(
        _payload(source_set_hash=source_set_hash(("depth:amm:other",))),
        expected_market_id="perp:btc-usd",
        now_epoch=3,
    )

    assert verdict.ok is False
    assert verdict.error == "source_set_hash mismatch"


def test_oi_depth_certificate_rejects_scalar_mismatch() -> None:
    verdict = verify_oi_depth_certificate_payload(
        _payload(),
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        expected_spot_depth_quote=900_000,
    )

    assert verdict.ok is False
    assert verdict.error == "spot_depth_quote mismatch"


def test_oi_depth_certificate_rejects_unsorted_sources() -> None:
    payload = certificate_payload_from_fields(
        market_id="perp:btc-usd",
        valid_from_epoch=2,
        valid_until_epoch=4,
        spot_depth_quote=1_000_000,
        arbitrage_absorb_bps=5_000,
        source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    payload["source_ids"] = ["depth:orderbook:btc-usd", "depth:amm:btc-usd"]

    verdict = verify_oi_depth_certificate_payload(
        payload,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
    )

    assert verdict.ok is False
    assert verdict.error == "source_ids must be sorted"


def test_oi_depth_certificate_rejects_canonical_hash_mismatch() -> None:
    payload = _payload()
    payload["spot_depth_quote"] = 1_000_001

    verdict = verify_oi_depth_certificate_payload(
        payload,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
    )

    assert verdict.ok is False
    assert verdict.error == "canonical_sha256 mismatch"


def test_oi_depth_certificate_rejects_market_id_type_coercion() -> None:
    payload = certificate_payload_from_fields(
        market_id="123",
        valid_from_epoch=2,
        valid_until_epoch=4,
        spot_depth_quote=1_000_000,
        arbitrage_absorb_bps=5_000,
        source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    payload["market_id"] = 123

    verdict = verify_oi_depth_certificate_payload(
        payload,
        expected_market_id="123",
        now_epoch=3,
    )

    assert verdict.ok is False
    assert verdict.error == "market_id must be a str"


def test_certificate_payload_rejects_wrong_type() -> None:
    try:
        certificate_payload({"not": "a certificate"})  # type: ignore[arg-type]
    except TypeError as exc:
        assert str(exc) == "certificate must be an OIDepthCertificate"
    else:
        raise AssertionError("expected TypeError")


def test_oi_depth_source_authority_accepts_authorized_subset() -> None:
    verdict = verify_oi_depth_source_authority_payload(
        _authority(),
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        required_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )

    assert verdict.ok is True
    assert verdict.error is None
    assert verdict.authority is not None


def test_oi_depth_source_authority_rejects_unauthorized_source() -> None:
    verdict = verify_oi_depth_source_authority_payload(
        _authority(authorized_source_ids=["depth:amm:btc-usd"]),
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        required_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )

    assert verdict.ok is False
    assert verdict.error == "canonical_sha256 mismatch"

    structurally_valid = source_authority_payload_from_fields(
        market_id="perp:btc-usd",
        valid_from_epoch=2,
        valid_until_epoch=4,
        authorized_source_ids=("depth:amm:btc-usd",),
    )
    verdict = verify_oi_depth_source_authority_payload(
        structurally_valid,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        required_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )

    assert verdict.ok is False
    assert verdict.error == "source_id not authorized: depth:orderbook:btc-usd"


def test_oi_depth_source_authority_rejects_cross_market_replay() -> None:
    verdict = verify_oi_depth_source_authority_payload(
        _authority(),
        expected_market_id="perp:eth-usd",
        now_epoch=3,
        required_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )

    assert verdict.ok is False
    assert verdict.error == "source authority market_id mismatch"


def test_oi_depth_source_authority_rejects_stale_epoch_replay() -> None:
    verdict = verify_oi_depth_source_authority_payload(
        _authority(valid_from_epoch=2, valid_until_epoch=2),
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        required_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )

    assert verdict.ok is False
    assert verdict.error == "canonical_sha256 mismatch"

    structurally_valid = source_authority_payload_from_fields(
        market_id="perp:btc-usd",
        valid_from_epoch=2,
        valid_until_epoch=2,
        authorized_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    verdict = verify_oi_depth_source_authority_payload(
        structurally_valid,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        required_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )

    assert verdict.ok is False
    assert verdict.error == "source authority epoch out of range"


def test_oi_depth_source_authority_rejects_market_id_type_coercion() -> None:
    payload = source_authority_payload_from_fields(
        market_id="123",
        valid_from_epoch=2,
        valid_until_epoch=4,
        authorized_source_ids=("depth:amm:btc-usd",),
    )
    payload["market_id"] = 123

    verdict = verify_oi_depth_source_authority_payload(
        payload,
        expected_market_id="123",
        now_epoch=3,
        required_source_ids=("depth:amm:btc-usd",),
    )

    assert verdict.ok is False
    assert verdict.error == "market_id must be a str"


def test_oi_depth_source_authority_binding_accepts_root_policy_and_signer() -> None:
    authority = _authority_object()
    payload = _binding()
    verdict = verify_oi_depth_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        expected_authority_state_root_hash=STATE_ROOT,
        expected_policy_hash=POLICY_HASH,
        allowed_signer_pubkeys=_allowed_signer_from(payload),
    )

    assert verdict.ok is True
    assert verdict.error is None
    assert verdict.binding is not None


def test_oi_depth_source_authority_binding_rejects_wrong_state_root() -> None:
    authority = _authority_object()
    payload = _binding()
    verdict = verify_oi_depth_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        expected_authority_state_root_hash=OTHER_STATE_ROOT,
        expected_policy_hash=POLICY_HASH,
        allowed_signer_pubkeys=_allowed_signer_from(payload),
    )

    assert verdict.ok is False
    assert verdict.error == "source authority binding state_root_hash mismatch"


def test_oi_depth_source_authority_binding_rejects_wrong_policy_hash() -> None:
    authority = _authority_object()
    payload = _binding()
    verdict = verify_oi_depth_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        expected_authority_state_root_hash=STATE_ROOT,
        expected_policy_hash=OTHER_POLICY_HASH,
        allowed_signer_pubkeys=_allowed_signer_from(payload),
    )

    assert verdict.ok is False
    assert verdict.error == "source authority binding policy_hash mismatch"


def test_oi_depth_source_authority_binding_rejects_unallowed_signer() -> None:
    authority = _authority_object()
    payload = _binding()
    other_binding = source_authority_binding_payload_from_fields(
        market_id="perp:btc-usd",
        valid_from_epoch=2,
        valid_until_epoch=4,
        authority_hash=oi_depth_source_authority_hash(authority),
        authority_state_root_hash=STATE_ROOT,
        policy_hash=POLICY_HASH,
        signer_privkey=2,
    )
    verdict = verify_oi_depth_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        expected_authority_state_root_hash=STATE_ROOT,
        expected_policy_hash=POLICY_HASH,
        allowed_signer_pubkeys=_allowed_signer_from(other_binding),
    )

    assert verdict.ok is False
    assert verdict.error == "source authority binding signer not allowed"


def test_oi_depth_source_authority_binding_rejects_signature_tamper() -> None:
    authority = _authority_object()
    payload = _binding()
    signature = payload["signature"]
    assert isinstance(signature, str)
    payload["signature"] = signature[:-1] + ("0" if signature[-1] != "0" else "1")

    verdict = verify_oi_depth_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        expected_authority_state_root_hash=STATE_ROOT,
        expected_policy_hash=POLICY_HASH,
        allowed_signer_pubkeys=_allowed_signer_from(_binding()),
    )

    assert verdict.ok is False
    assert verdict.error == "source authority binding signature invalid"


def test_oi_depth_source_authority_binding_rejects_authority_hash_mismatch() -> None:
    authority = _authority_object()
    payload = source_authority_binding_payload_from_fields(
        market_id="perp:btc-usd",
        valid_from_epoch=2,
        valid_until_epoch=4,
        authority_hash="sha256:" + "33" * 32,
        authority_state_root_hash=STATE_ROOT,
        policy_hash=POLICY_HASH,
        signer_privkey=1,
    )

    verdict = verify_oi_depth_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        expected_authority_state_root_hash=STATE_ROOT,
        expected_policy_hash=POLICY_HASH,
        allowed_signer_pubkeys=_allowed_signer_from(payload),
    )

    assert verdict.ok is False
    assert verdict.error == "source authority binding authority_hash mismatch"


def test_oi_depth_source_authority_binding_rejects_stale_epoch() -> None:
    authority = _authority_object()
    payload = source_authority_binding_payload_from_fields(
        market_id="perp:btc-usd",
        valid_from_epoch=2,
        valid_until_epoch=2,
        authority_hash=oi_depth_source_authority_hash(authority),
        authority_state_root_hash=STATE_ROOT,
        policy_hash=POLICY_HASH,
        signer_privkey=1,
    )

    verdict = verify_oi_depth_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id="perp:btc-usd",
        now_epoch=3,
        expected_authority_state_root_hash=STATE_ROOT,
        expected_policy_hash=POLICY_HASH,
        allowed_signer_pubkeys=_allowed_signer_from(payload),
    )

    assert verdict.ok is False
    assert verdict.error == "source authority binding epoch out of range"


def test_oi_depth_source_authority_binding_rejects_market_id_type_coercion() -> None:
    authority = _authority_object()
    payload = source_authority_binding_payload_from_fields(
        market_id="123",
        valid_from_epoch=2,
        valid_until_epoch=4,
        authority_hash=oi_depth_source_authority_hash(authority),
        authority_state_root_hash=STATE_ROOT,
        policy_hash=POLICY_HASH,
        signer_privkey=1,
    )
    payload["market_id"] = 123

    verdict = verify_oi_depth_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id="123",
        now_epoch=3,
        expected_authority_state_root_hash=STATE_ROOT,
        expected_policy_hash=POLICY_HASH,
        allowed_signer_pubkeys=_allowed_signer_from(
            source_authority_binding_payload_from_fields(
                market_id="123",
                valid_from_epoch=2,
                valid_until_epoch=4,
                authority_hash=oi_depth_source_authority_hash(authority),
                authority_state_root_hash=STATE_ROOT,
                policy_hash=POLICY_HASH,
                signer_privkey=1,
            )
        ),
    )

    assert verdict.ok is False
    assert verdict.error == "market_id must be a str"
