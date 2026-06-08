from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_settlement_endogenous_lp_value_packet_routes import (
    maybe_handle_settlement_endogenous_lp_value_packet_route,
)


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "settlement": {"kind": "fake-settlement"},
        "price_packet": {"packet": "present"},
        "pool_snapshots": [{"pool_id": "pool-1"}],
    }
    request.update(overrides)
    return request


class _FakePacket:
    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "fake-settlement-endogenous-lp-value-packet",
            "packet_ok": True,
        }


def _fail_on_settlement_import(monkeypatch: Any) -> None:
    real_import = builtins.__import__

    def guarded_import(
        name: str,
        globals: Any = None,
        locals: Any = None,
        fromlist: Any = (),
        level: int = 0,
    ) -> object:
        if name in {
            "src.integration.operations",
            "src.integration.settlement_endogenous_lp_value_packet",
            "src.integration.settlement_price_provenance",
            "src.integration.settlement_price_attestation",
        }:
            raise AssertionError("settlement modules imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def _patch_parse_settlement(monkeypatch: Any, parsed: object) -> None:
    monkeypatch.setattr("src.integration.operations._parse_settlement", lambda payload: ("settlement", payload, parsed))


def test_unknown_endogenous_lp_value_packet_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/not_endogenous_lp_value_packet",
        obj={},
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_build_endogenous_lp_value_packet_rejects_bad_settlement_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/build_settlement_endogenous_lp_value_packet",
        obj=_request(settlement=[]),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_settlement"})]


def test_build_endogenous_lp_value_packet_rejects_missing_price_input_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/build_settlement_endogenous_lp_value_packet",
        obj={"settlement": {"kind": "fake-settlement"}, "pool_snapshots": [{"pool_id": "pool-1"}]},
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "missing_price_input"})]


def test_build_endogenous_lp_value_packet_rejects_bad_containers_before_import(monkeypatch: Any) -> None:
    _fail_on_settlement_import(monkeypatch)

    cases = [
        (_request(price_packet=[]), "bad_price_packet"),
        (_request(price_attestation=[]), "bad_price_attestation"),
        (_request(pool_snapshots={}), "bad_pool_snapshots"),
        (_request(pool_snapshots=[]), "bad_pool_snapshots"),
        (
            _request(
                price_attestation={},
                consumer_now_epoch=True,
                max_attestation_age_epochs=5,
            ),
            "bad_consumer_now_epoch",
        ),
        (
            _request(
                price_attestation={},
                consumer_now_epoch=3,
                max_attestation_age_epochs=True,
            ),
            "bad_max_attestation_age_epochs",
        ),
        (
            _request(
                price_attestation={},
                consumer_now_epoch=3,
                max_attestation_age_epochs=5,
                allowed_signers=[],
            ),
            "bad_allowed_signers",
        ),
    ]
    for obj, error in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
            path="/api/dex/build_settlement_endogenous_lp_value_packet",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error})]


def test_build_endogenous_lp_value_packet_rejects_bad_price_packet_even_when_attestation_present(
    monkeypatch: Any,
) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/build_settlement_endogenous_lp_value_packet",
        obj=_request(
            price_packet=[],
            price_attestation={},
            consumer_now_epoch=7,
            max_attestation_age_epochs=3,
        ),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_price_packet"})]


def test_build_endogenous_lp_value_packet_price_packet_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    parsed_settlement = object()
    parsed_pool = object()
    fake_packet = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)

    monkeypatch.setattr(
        "src.integration.settlement_endogenous_lp_value_packet._pool_from_dict",
        lambda payload: ("pool", payload, parsed_pool),
    )
    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.SettlementSpotPricePacket.from_dict",
        staticmethod(lambda payload: ("packet", payload, fake_packet)),
    )

    def build_from_packet(**kwargs: object) -> _FakePacket:
        captured.update(kwargs)
        return _FakePacket()

    monkeypatch.setattr(
        "src.integration.settlement_endogenous_lp_value_packet."
        "build_settlement_endogenous_lp_value_packet_from_price_packet",
        build_from_packet,
    )

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/build_settlement_endogenous_lp_value_packet",
        obj=_request(),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "price_packet": ("packet", {"packet": "present"}, fake_packet),
        "pool_snapshots": (("pool", {"pool_id": "pool-1"}, parsed_pool),),
    }
    assert writes == [
        (
            200,
            {
                "ok": True,
                "packet": {
                    "schema": "fake-settlement-endogenous-lp-value-packet",
                    "packet_ok": True,
                },
            },
        )
    ]


def test_build_endogenous_lp_value_packet_invalid_pool_snapshot_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/build_settlement_endogenous_lp_value_packet",
        obj=_request(pool_snapshots=[[]]),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "build_settlement_endogenous_lp_value_packet_error",
                "details": "request failed",
            },
        )
    ]


def test_build_endogenous_lp_value_packet_uses_attestation_before_price_packet(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    parsed_settlement = object()
    parsed_pool = object()
    fake_attestation = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)

    monkeypatch.setattr(
        "src.integration.settlement_endogenous_lp_value_packet._pool_from_dict",
        lambda payload: ("pool", payload, parsed_pool),
    )
    monkeypatch.setattr(
        "src.integration.settlement_price_attestation.SettlementSpotPriceAttestation.from_dict",
        staticmethod(lambda payload: ("attestation", payload, fake_attestation)),
    )

    def build_from_attestation(**kwargs: object) -> _FakePacket:
        captured.update(kwargs)
        return _FakePacket()

    def packet_builder_should_not_run(**_kwargs: object) -> _FakePacket:
        raise AssertionError("price packet builder should not run when attestation is present")

    monkeypatch.setattr(
        "src.integration.settlement_endogenous_lp_value_packet."
        "build_settlement_endogenous_lp_value_packet_from_price_attestation",
        build_from_attestation,
    )
    monkeypatch.setattr(
        "src.integration.settlement_endogenous_lp_value_packet."
        "build_settlement_endogenous_lp_value_packet_from_price_packet",
        packet_builder_should_not_run,
    )

    obj = _request(
        price_attestation={"attestation": "present"},
        consumer_now_epoch=7,
        max_attestation_age_epochs=3,
        allowed_signers={"signer": ["oracle:a"]},
    )
    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/build_settlement_endogenous_lp_value_packet",
        obj=obj,
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "price_attestation": ("attestation", {"attestation": "present"}, fake_attestation),
        "consumer_now_epoch": 7,
        "max_attestation_age_epochs": 3,
        "pool_snapshots": (("pool", {"pool_id": "pool-1"}, parsed_pool),),
        "allowed_signers": {"signer": ["oracle:a"]},
    }
    assert writes[0][0] == 200


def test_verify_endogenous_lp_value_packet_rejects_bad_packet_before_attestation_fields(
    monkeypatch: Any,
) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/verify_settlement_endogenous_lp_value_packet",
        obj=_request(
            price_attestation={},
            consumer_now_epoch=True,
            max_attestation_age_epochs=True,
            packet=[],
        ),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_packet"})]


def test_verify_endogenous_lp_value_packet_attestation_errors_after_good_packet_before_import(
    monkeypatch: Any,
) -> None:
    _fail_on_settlement_import(monkeypatch)

    cases = [
        (
            _request(price_attestation={}, consumer_now_epoch=True, max_attestation_age_epochs=5, packet={}),
            "bad_consumer_now_epoch",
        ),
        (
            _request(price_attestation={}, consumer_now_epoch=3, max_attestation_age_epochs=True, packet={}),
            "bad_max_attestation_age_epochs",
        ),
        (
            _request(
                price_attestation={},
                consumer_now_epoch=3,
                max_attestation_age_epochs=5,
                allowed_signers=[],
                packet={},
            ),
            "bad_allowed_signers",
        ),
    ]
    for obj, error in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
            path="/api/dex/verify_settlement_endogenous_lp_value_packet",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error})]


def test_verify_endogenous_lp_value_packet_rejects_bad_price_packet_even_when_attestation_present(
    monkeypatch: Any,
) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/verify_settlement_endogenous_lp_value_packet",
        obj=_request(
            price_packet=[],
            price_attestation={},
            consumer_now_epoch=7,
            max_attestation_age_epochs=3,
            packet={},
        ),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_price_packet"})]


def test_verify_endogenous_lp_value_packet_price_packet_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    packet_payload = {"schema": "fake-packet"}
    _patch_parse_settlement(monkeypatch, object())

    def verify_from_price_packet(**kwargs: object) -> tuple[bool, None]:
        captured.update(kwargs)
        return True, None

    monkeypatch.setattr(
        "src.integration.settlement_endogenous_lp_value_packet."
        "verify_settlement_endogenous_lp_value_packet_payload_from_price_packet",
        verify_from_price_packet,
    )

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/verify_settlement_endogenous_lp_value_packet",
        obj=_request(packet=packet_payload),
        write_json=write_json,
    )

    assert handled is True
    assert captured["price_packet_payload"] == {"packet": "present"}
    assert captured["pool_snapshots_payload"] == [{"pool_id": "pool-1"}]
    assert captured["packet_payload"] is packet_payload
    assert writes == [(200, {"ok": True, "error": None})]


def test_verify_endogenous_lp_value_packet_preserves_rejection_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())

    def verify_from_price_packet(**_kwargs: object) -> tuple[bool, str]:
        return False, "settlement endogenous lp value packet mismatch"

    monkeypatch.setattr(
        "src.integration.settlement_endogenous_lp_value_packet."
        "verify_settlement_endogenous_lp_value_packet_payload_from_price_packet",
        verify_from_price_packet,
    )

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/verify_settlement_endogenous_lp_value_packet",
        obj=_request(packet={"schema": "fake-packet"}),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "settlement endogenous lp value packet mismatch"})]


def test_verify_endogenous_lp_value_packet_snapshot_rejection_stays_verifier_result(
    monkeypatch: Any,
) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())

    def verify_from_price_packet(**kwargs: object) -> tuple[bool, str]:
        assert kwargs["pool_snapshots_payload"] == [[]]
        return False, "pool snapshot payload must be an object"

    monkeypatch.setattr(
        "src.integration.settlement_endogenous_lp_value_packet."
        "verify_settlement_endogenous_lp_value_packet_payload_from_price_packet",
        verify_from_price_packet,
    )

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/verify_settlement_endogenous_lp_value_packet",
        obj=_request(packet={"schema": "fake-packet"}, pool_snapshots=[[]]),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "pool snapshot payload must be an object"})]


def test_verify_endogenous_lp_value_packet_attestation_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    packet_payload = {"schema": "fake-packet"}
    parsed_settlement = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)

    def verify_from_attestation(**kwargs: object) -> tuple[bool, None]:
        captured.update(kwargs)
        return True, None

    monkeypatch.setattr(
        "src.integration.settlement_endogenous_lp_value_packet."
        "verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation",
        verify_from_attestation,
    )

    handled = maybe_handle_settlement_endogenous_lp_value_packet_route(
        path="/api/dex/verify_settlement_endogenous_lp_value_packet",
        obj=_request(
            price_attestation={"attestation": "present"},
            consumer_now_epoch=7,
            max_attestation_age_epochs=3,
            allowed_signers={"signer": ["oracle:a"]},
            packet=packet_payload,
        ),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "price_attestation_payload": {"attestation": "present"},
        "consumer_now_epoch": 7,
        "max_attestation_age_epochs": 3,
        "pool_snapshots_payload": [{"pool_id": "pool-1"}],
        "packet_payload": packet_payload,
        "allowed_signers": {"signer": ["oracle:a"]},
    }
    assert writes == [(200, {"ok": True, "error": None})]
