from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_settlement_end_to_end_certificate_routes import (
    maybe_handle_settlement_end_to_end_certificate_route,
)


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "settlement": {"kind": "fake-settlement"},
        "proof_flags": {"flag": True},
        "price_history": {"history": "present"},
        "feature_extension_inputs": {"trade_amount": 100},
        "price_packet": {"packet": "present"},
        "packet": {"schema": "fake-certificate-packet"},
    }
    request.update(overrides)
    return request


class _FakePacket:
    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "fake-settlement-end-to-end-certificate-packet",
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
            "src.integration.api_server_settlement_parsers",
            "src.integration.operations",
            "src.integration.settlement_end_to_end_certificate_packet",
            "src.integration.settlement_endogenous_lp_value_packet",
            "src.integration.settlement_price_attestation",
            "src.integration.settlement_price_provenance",
        }:
            raise AssertionError("settlement modules imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def _patch_parse_settlement(monkeypatch: Any, parsed: object) -> None:
    monkeypatch.setattr("src.integration.operations._parse_settlement", lambda payload: ("settlement", payload, parsed))


def _patch_common_build_parsers(monkeypatch: Any) -> None:
    monkeypatch.setattr(
        "src.integration.api_server_settlement_parsers._parse_settlement_proof_flags_payload",
        lambda payload: ("proof-flags", payload),
    )
    monkeypatch.setattr(
        "src.integration.api_server_settlement_parsers._parse_price_history_payload",
        lambda payload: ("price-history", payload),
    )
    monkeypatch.setattr(
        "src.integration.api_server_settlement_parsers._parse_settlement_feature_extension_inputs_payload",
        lambda payload: ("feature-inputs", payload),
    )


def _patch_common_verify_parsers(monkeypatch: Any) -> None:
    monkeypatch.setattr(
        "src.integration.api_server_settlement_parsers._parse_settlement_proof_flags_payload",
        lambda payload: ("proof-flags", payload),
    )
    monkeypatch.setattr(
        "src.integration.api_server_settlement_parsers._parse_price_history_payload",
        lambda payload: ("price-history", payload),
    )


def test_unknown_end_to_end_certificate_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/not_end_to_end_certificate",
        obj={},
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_build_end_to_end_certificate_rejects_bad_settlement_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/build_settlement_end_to_end_certificate_packet",
        obj=_request(settlement=[]),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_settlement"})]


def test_build_end_to_end_certificate_rejects_missing_price_input_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/build_settlement_end_to_end_certificate_packet",
        obj=_request(price_packet=None, price_attestation=None),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "missing_price_input"})]


def test_build_end_to_end_certificate_rejects_bad_containers_before_import(monkeypatch: Any) -> None:
    _fail_on_settlement_import(monkeypatch)

    cases = [
        (_request(price_packet=[]), "bad_price_packet"),
        (_request(price_attestation=[]), "bad_price_attestation"),
        (_request(pool_snapshots={}), "bad_pool_snapshots"),
        (_request(pool_snapshots=[]), "bad_pool_snapshots"),
        (_request(lp_unit_values=[]), "bad_lp_unit_values"),
        (_request(lp_unit_values={}), "bad_lp_unit_values"),
        (_request(pool_snapshots=[{}], lp_unit_values={"pool-1": 1}), "conflicting_value_mode_inputs"),
        (
            _request(price_attestation={}, consumer_now_epoch=True, max_attestation_age_epochs=5),
            "bad_consumer_now_epoch",
        ),
        (
            _request(price_attestation={}, consumer_now_epoch=3, max_attestation_age_epochs=True),
            "bad_max_attestation_age_epochs",
        ),
        (
            _request(price_attestation={}, consumer_now_epoch=3, max_attestation_age_epochs=5, allowed_signers=[]),
            "bad_allowed_signers",
        ),
    ]
    for obj, error in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_end_to_end_certificate_route(
            path="/api/dex/build_settlement_end_to_end_certificate_packet",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error})]


def test_build_end_to_end_certificate_rejects_bad_price_packet_even_with_attestation(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/build_settlement_end_to_end_certificate_packet",
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


def test_build_end_to_end_certificate_price_packet_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    parsed_settlement = object()
    fake_price_packet = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)
    _patch_common_build_parsers(monkeypatch)

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.SettlementSpotPricePacket.from_dict",
        staticmethod(lambda payload: ("price-packet", payload, fake_price_packet)),
    )

    def build_from_price_packet(**kwargs: object) -> _FakePacket:
        captured.update(kwargs)
        return _FakePacket()

    monkeypatch.setattr(
        "src.integration.settlement_end_to_end_certificate_packet."
        "build_settlement_end_to_end_certificate_packet_from_price_packet",
        build_from_price_packet,
    )

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/build_settlement_end_to_end_certificate_packet",
        obj=_request(lp_unit_values={" pool-1 ": 77}),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "proof_flags": ("proof-flags", {"flag": True}),
        "price_history": ("price-history", {"history": "present"}),
        "feature_extension_inputs": ("feature-inputs", {"trade_amount": 100}),
        "price_packet": ("price-packet", {"packet": "present"}, fake_price_packet),
        "lp_unit_values": {"pool-1": 77},
        "pool_snapshots": None,
    }
    assert writes == [
        (
            200,
            {
                "ok": True,
                "packet": {
                    "schema": "fake-settlement-end-to-end-certificate-packet",
                    "packet_ok": True,
                },
            },
        )
    ]


def test_build_end_to_end_certificate_invalid_lp_values_map_to_generic_error(monkeypatch: Any) -> None:
    _patch_parse_settlement(monkeypatch, object())
    _patch_common_build_parsers(monkeypatch)

    cases = [
        {"": 7},
        {"   ": 7},
        {"pool-1": True},
        {"pool-1": -1},
        {"pool-1": "7"},
    ]
    for lp_unit_values in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_end_to_end_certificate_route(
            path="/api/dex/build_settlement_end_to_end_certificate_packet",
            obj=_request(lp_unit_values=lp_unit_values),
            write_json=write_json,
        )

        assert handled is True
        assert writes == [
            (
                400,
                {
                    "ok": False,
                    "error": "build_settlement_end_to_end_certificate_packet_error",
                    "details": "request failed",
                },
            )
        ]


def test_build_end_to_end_certificate_invalid_pool_snapshot_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())
    _patch_common_build_parsers(monkeypatch)

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/build_settlement_end_to_end_certificate_packet",
        obj=_request(pool_snapshots=[[]]),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "build_settlement_end_to_end_certificate_packet_error",
                "details": "request failed",
            },
        )
    ]


def test_build_end_to_end_certificate_uses_attestation_before_price_packet(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    parsed_settlement = object()
    parsed_pool = object()
    fake_attestation = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)
    _patch_common_build_parsers(monkeypatch)

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

    def price_packet_builder_should_not_run(**_kwargs: object) -> _FakePacket:
        raise AssertionError("price packet builder should not run when attestation is present")

    monkeypatch.setattr(
        "src.integration.settlement_end_to_end_certificate_packet."
        "build_settlement_end_to_end_certificate_packet_from_price_attestation",
        build_from_attestation,
    )
    monkeypatch.setattr(
        "src.integration.settlement_end_to_end_certificate_packet."
        "build_settlement_end_to_end_certificate_packet_from_price_packet",
        price_packet_builder_should_not_run,
    )

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/build_settlement_end_to_end_certificate_packet",
        obj=_request(
            price_attestation={"attestation": "present"},
            pool_snapshots=[{"pool_id": "pool-1"}],
            consumer_now_epoch=9,
            max_attestation_age_epochs=4,
            allowed_signers={"signer-a": True},
        ),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "proof_flags": ("proof-flags", {"flag": True}),
        "price_history": ("price-history", {"history": "present"}),
        "feature_extension_inputs": ("feature-inputs", {"trade_amount": 100}),
        "price_attestation": ("attestation", {"attestation": "present"}, fake_attestation),
        "consumer_now_epoch": 9,
        "max_attestation_age_epochs": 4,
        "lp_unit_values": None,
        "pool_snapshots": (("pool", {"pool_id": "pool-1"}, parsed_pool),),
        "allowed_signers": {"signer-a": True},
    }
    assert writes == [
        (
            200,
            {
                "ok": True,
                "packet": {
                    "schema": "fake-settlement-end-to-end-certificate-packet",
                    "packet_ok": True,
                },
            },
        )
    ]


def test_build_end_to_end_certificate_exception_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())
    _patch_common_build_parsers(monkeypatch)

    def build_from_price_packet(**_kwargs: object) -> _FakePacket:
        raise RuntimeError("build failed")

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.SettlementSpotPricePacket.from_dict",
        staticmethod(lambda payload: ("price-packet", payload)),
    )
    monkeypatch.setattr(
        "src.integration.settlement_end_to_end_certificate_packet."
        "build_settlement_end_to_end_certificate_packet_from_price_packet",
        build_from_price_packet,
    )

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/build_settlement_end_to_end_certificate_packet",
        obj=_request(),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "build_settlement_end_to_end_certificate_packet_error", "details": "request failed"},
        )
    ]


def test_verify_end_to_end_certificate_rejects_bad_packet_before_attestation_fields(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/verify_settlement_end_to_end_certificate_packet",
        obj=_request(
            price_attestation={},
            packet=[],
            consumer_now_epoch=True,
            max_attestation_age_epochs=True,
        ),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_packet"})]


def test_verify_end_to_end_certificate_validates_attestation_fields_after_packet(monkeypatch: Any) -> None:
    _fail_on_settlement_import(monkeypatch)

    cases = [
        (
            _request(price_attestation={}, consumer_now_epoch=True, max_attestation_age_epochs=5),
            "bad_consumer_now_epoch",
        ),
        (
            _request(price_attestation={}, consumer_now_epoch=3, max_attestation_age_epochs=True),
            "bad_max_attestation_age_epochs",
        ),
        (
            _request(price_attestation={}, consumer_now_epoch=3, max_attestation_age_epochs=5, allowed_signers=[]),
            "bad_allowed_signers",
        ),
    ]
    for obj, error in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_end_to_end_certificate_route(
            path="/api/dex/verify_settlement_end_to_end_certificate_packet",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error})]


def test_verify_end_to_end_certificate_rejects_bad_price_packet_even_with_attestation(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/verify_settlement_end_to_end_certificate_packet",
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


def test_verify_end_to_end_certificate_price_packet_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    packet = {"schema": "fake-certificate-packet"}
    parsed_settlement = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)
    _patch_common_verify_parsers(monkeypatch)

    def verify_from_price_packet(**kwargs: object) -> tuple[bool, None]:
        captured.update(kwargs)
        return True, None

    monkeypatch.setattr(
        "src.integration.settlement_end_to_end_certificate_packet."
        "verify_settlement_end_to_end_certificate_packet_payload_from_price_packet",
        verify_from_price_packet,
    )

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/verify_settlement_end_to_end_certificate_packet",
        obj=_request(packet=packet, lp_unit_values={" pool-1 ": 77}, pool_snapshots=None),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "proof_flags": ("proof-flags", {"flag": True}),
        "price_history": ("price-history", {"history": "present"}),
        "feature_extension_inputs_payload": {"trade_amount": 100},
        "price_packet_payload": {"packet": "present"},
        "packet_payload": packet,
        "lp_unit_values": {"pool-1": 77},
        "pool_snapshots_payload": None,
    }
    assert writes == [(200, {"ok": True, "error": None})]


def test_verify_end_to_end_certificate_preserves_rejection_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())
    _patch_common_verify_parsers(monkeypatch)

    def verify_from_price_packet(**_kwargs: object) -> tuple[bool, str]:
        return False, "settlement end-to-end certificate packet mismatch"

    monkeypatch.setattr(
        "src.integration.settlement_end_to_end_certificate_packet."
        "verify_settlement_end_to_end_certificate_packet_payload_from_price_packet",
        verify_from_price_packet,
    )

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/verify_settlement_end_to_end_certificate_packet",
        obj=_request(),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "settlement end-to-end certificate packet mismatch"})]


def test_verify_end_to_end_certificate_keeps_feature_and_pool_payloads_verifier_scoped(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    _patch_parse_settlement(monkeypatch, object())
    _patch_common_verify_parsers(monkeypatch)

    def verify_from_price_packet(**kwargs: object) -> tuple[bool, str]:
        captured.update(kwargs)
        return False, "pool snapshot payload must be an object"

    monkeypatch.setattr(
        "src.integration.settlement_end_to_end_certificate_packet."
        "verify_settlement_end_to_end_certificate_packet_payload_from_price_packet",
        verify_from_price_packet,
    )

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/verify_settlement_end_to_end_certificate_packet",
        obj=_request(
            feature_extension_inputs=[],
            pool_snapshots=[[]],
        ),
        write_json=write_json,
    )

    assert handled is True
    assert captured["feature_extension_inputs_payload"] == []
    assert captured["pool_snapshots_payload"] == [[]]
    assert writes == [(200, {"ok": False, "error": "pool snapshot payload must be an object"})]


def test_verify_end_to_end_certificate_invalid_lp_values_map_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())
    _patch_common_verify_parsers(monkeypatch)

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/verify_settlement_end_to_end_certificate_packet",
        obj=_request(lp_unit_values={"pool-1": True}),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "verify_settlement_end_to_end_certificate_packet_error", "details": "request failed"},
        )
    ]


def test_verify_end_to_end_certificate_exception_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())
    _patch_common_verify_parsers(monkeypatch)

    def verify_from_price_packet(**_kwargs: object) -> tuple[bool, None]:
        raise RuntimeError("verify failed")

    monkeypatch.setattr(
        "src.integration.settlement_end_to_end_certificate_packet."
        "verify_settlement_end_to_end_certificate_packet_payload_from_price_packet",
        verify_from_price_packet,
    )

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/verify_settlement_end_to_end_certificate_packet",
        obj=_request(),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "verify_settlement_end_to_end_certificate_packet_error", "details": "request failed"},
        )
    ]


def test_verify_end_to_end_certificate_attestation_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    packet = {"schema": "fake-certificate-packet"}
    parsed_settlement = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)
    _patch_common_verify_parsers(monkeypatch)

    def verify_from_attestation(**kwargs: object) -> tuple[bool, None]:
        captured.update(kwargs)
        return True, None

    monkeypatch.setattr(
        "src.integration.settlement_end_to_end_certificate_packet."
        "verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation",
        verify_from_attestation,
    )

    handled = maybe_handle_settlement_end_to_end_certificate_route(
        path="/api/dex/verify_settlement_end_to_end_certificate_packet",
        obj=_request(
            packet=packet,
            price_attestation={"attestation": "present"},
            consumer_now_epoch=8,
            max_attestation_age_epochs=4,
            allowed_signers={"signer-a": True},
        ),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "proof_flags": ("proof-flags", {"flag": True}),
        "price_history": ("price-history", {"history": "present"}),
        "feature_extension_inputs_payload": {"trade_amount": 100},
        "price_attestation_payload": {"attestation": "present"},
        "consumer_now_epoch": 8,
        "max_attestation_age_epochs": 4,
        "packet_payload": packet,
        "lp_unit_values": None,
        "pool_snapshots_payload": None,
        "allowed_signers": {"signer-a": True},
    }
    assert writes == [(200, {"ok": True, "error": None})]
