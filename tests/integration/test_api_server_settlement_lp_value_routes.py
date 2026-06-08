from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_settlement_lp_value_routes import (
    maybe_handle_settlement_lp_value_route,
)


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "settlement": {"kind": "fake-settlement"},
        "asset_prices": {" A ": 100, "B": 120},
        "lp_unit_values": {" pool-1 ": 77},
    }
    request.update(overrides)
    return request


class _FakeContract:
    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "fake-settlement-lp-value-contract",
            "value_conservation_ok": True,
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
            "src.integration.settlement_lp_value_contract",
            "src.integration.settlement_price_provenance",
            "src.integration.settlement_price_attestation",
        }:
            raise AssertionError("settlement modules imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def _patch_parse_settlement(monkeypatch: Any, parsed: object) -> None:
    monkeypatch.setattr("src.integration.operations._parse_settlement", lambda payload: ("settlement", payload, parsed))


def test_unknown_lp_value_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/not_lp_value",
        obj={},
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_build_lp_value_rejects_bad_settlement_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/build_settlement_lp_value_contract",
        obj=_request(settlement=[]),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_settlement"})]


def test_build_lp_value_rejects_missing_price_input_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/build_settlement_lp_value_contract",
        obj={"settlement": {"kind": "fake-settlement"}, "lp_unit_values": {"pool": 77}},
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "missing_price_input"})]


def test_build_lp_value_rejects_bad_containers_before_import(monkeypatch: Any) -> None:
    _fail_on_settlement_import(monkeypatch)

    cases = [
        (_request(asset_prices=[]), "bad_asset_prices"),
        (_request(asset_prices={}), "bad_asset_prices"),
        (_request(price_packet=[]), "bad_price_packet"),
        (_request(price_attestation=[]), "bad_price_attestation"),
        (_request(lp_unit_values=[]), "bad_lp_unit_values"),
        (_request(lp_unit_values={}), "bad_lp_unit_values"),
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

        handled = maybe_handle_settlement_lp_value_route(
            path="/api/dex/build_settlement_lp_value_contract",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error})]


def test_build_lp_value_asset_prices_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    parsed_settlement = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)

    def build_settlement_lp_value_contract(**kwargs: object) -> _FakeContract:
        captured.update(kwargs)
        return _FakeContract()

    monkeypatch.setattr(
        "src.integration.settlement_lp_value_contract.build_settlement_lp_value_contract",
        build_settlement_lp_value_contract,
    )

    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/build_settlement_lp_value_contract",
        obj=_request(),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "asset_prices": {"A": 100, "B": 120},
        "lp_unit_values": {"pool-1": 77},
    }
    assert writes == [
        (
            200,
            {
                "ok": True,
                "contract": {
                    "schema": "fake-settlement-lp-value-contract",
                    "value_conservation_ok": True,
                },
            },
        )
    ]


def test_build_lp_value_invalid_prices_and_lp_values_map_to_generic_error(monkeypatch: Any) -> None:
    _patch_parse_settlement(monkeypatch, object())

    cases = [
        (_request(asset_prices={" ": 100}), "build_settlement_lp_value_contract_error"),
        (_request(lp_unit_values={" ": 77}), "build_settlement_lp_value_contract_error"),
        (_request(lp_unit_values={"pool-1": True}), "build_settlement_lp_value_contract_error"),
    ]
    for obj, error in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_lp_value_route(
            path="/api/dex/build_settlement_lp_value_contract",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error, "details": "request failed"})]


def test_build_lp_value_uses_attestation_before_packet_or_asset_prices(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    parsed_settlement = object()
    fake_attestation = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)

    monkeypatch.setattr(
        "src.integration.settlement_price_attestation.SettlementSpotPriceAttestation.from_dict",
        staticmethod(lambda payload: ("attestation", payload, fake_attestation)),
    )

    def build_from_attestation(**kwargs: object) -> _FakeContract:
        captured.update(kwargs)
        return _FakeContract()

    def packet_builder_should_not_run(**_kwargs: object) -> _FakeContract:
        raise AssertionError("price packet builder should not run when attestation is present")

    monkeypatch.setattr(
        "src.integration.settlement_lp_value_contract.build_settlement_lp_value_contract_from_price_attestation",
        build_from_attestation,
    )
    monkeypatch.setattr(
        "src.integration.settlement_lp_value_contract.build_settlement_lp_value_contract_from_price_packet",
        packet_builder_should_not_run,
    )

    obj = _request(
        price_packet={"packet": "present"},
        price_attestation={"attestation": "present"},
        consumer_now_epoch=7,
        max_attestation_age_epochs=3,
        allowed_signers={"signer": ["oracle:a"]},
    )
    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/build_settlement_lp_value_contract",
        obj=obj,
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "price_attestation": ("attestation", {"attestation": "present"}, fake_attestation),
        "consumer_now_epoch": 7,
        "max_attestation_age_epochs": 3,
        "lp_unit_values": {"pool-1": 77},
        "allowed_signers": {"signer": ["oracle:a"]},
    }
    assert writes[0][0] == 200


def test_build_lp_value_uses_price_packet_before_asset_prices(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    parsed_settlement = object()
    fake_packet = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.SettlementSpotPricePacket.from_dict",
        staticmethod(lambda payload: ("packet", payload, fake_packet)),
    )

    def build_from_packet(**kwargs: object) -> _FakeContract:
        captured.update(kwargs)
        return _FakeContract()

    monkeypatch.setattr(
        "src.integration.settlement_lp_value_contract.build_settlement_lp_value_contract_from_price_packet",
        build_from_packet,
    )

    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/build_settlement_lp_value_contract",
        obj=_request(price_packet={"packet": "present"}),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "price_packet": ("packet", {"packet": "present"}, fake_packet),
        "lp_unit_values": {"pool-1": 77},
    }
    assert writes[0][0] == 200


def test_verify_lp_value_rejects_bad_contract_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_settlement_import(monkeypatch)

    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/verify_settlement_lp_value_contract",
        obj=_request(contract=[]),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_contract"})]


def test_verify_lp_value_asset_prices_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    contract = {"schema": "fake-contract"}
    _patch_parse_settlement(monkeypatch, object())

    def verify_settlement_lp_value_contract_payload(**kwargs: object) -> tuple[bool, None]:
        captured.update(kwargs)
        return True, None

    monkeypatch.setattr(
        "src.integration.settlement_lp_value_contract.verify_settlement_lp_value_contract_payload",
        verify_settlement_lp_value_contract_payload,
    )

    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/verify_settlement_lp_value_contract",
        obj=_request(contract=contract),
        write_json=write_json,
    )

    assert handled is True
    assert captured["contract_payload"] is contract
    assert captured["asset_prices"] == {"A": 100, "B": 120}
    assert captured["lp_unit_values"] == {"pool-1": 77}
    assert writes == [(200, {"ok": True, "error": None})]


def test_verify_lp_value_invalid_prices_and_lp_values_map_to_generic_error(monkeypatch: Any) -> None:
    _patch_parse_settlement(monkeypatch, object())
    contract = {"schema": "fake-contract"}

    cases = [
        _request(asset_prices={" ": 100}, contract=contract),
        _request(lp_unit_values={" ": 77}, contract=contract),
        _request(lp_unit_values={"pool-1": True}, contract=contract),
    ]
    for obj in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_lp_value_route(
            path="/api/dex/verify_settlement_lp_value_contract",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [
            (
                400,
                {"ok": False, "error": "verify_settlement_lp_value_contract_error", "details": "request failed"},
            )
        ]


def test_verify_lp_value_preserves_rejection_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())

    def verify_settlement_lp_value_contract_payload(**_kwargs: object) -> tuple[bool, str]:
        return False, "settlement lp value contract mismatch"

    monkeypatch.setattr(
        "src.integration.settlement_lp_value_contract.verify_settlement_lp_value_contract_payload",
        verify_settlement_lp_value_contract_payload,
    )

    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/verify_settlement_lp_value_contract",
        obj=_request(contract={"schema": "fake-contract"}),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "settlement lp value contract mismatch"})]


def test_verify_lp_value_price_packet_and_attestation_arguments(monkeypatch: Any) -> None:
    parsed_settlement = object()
    _patch_parse_settlement(monkeypatch, parsed_settlement)
    contract = {"schema": "fake-contract"}
    packet_captured: dict[str, object] = {}
    attestation_captured: dict[str, object] = {}

    def verify_from_price_packet(**kwargs: object) -> tuple[bool, None]:
        packet_captured.update(kwargs)
        return True, None

    def verify_from_price_attestation(**kwargs: object) -> tuple[bool, None]:
        attestation_captured.update(kwargs)
        return True, None

    monkeypatch.setattr(
        "src.integration.settlement_lp_value_contract.verify_settlement_lp_value_contract_payload_from_price_packet",
        verify_from_price_packet,
    )
    monkeypatch.setattr(
        "src.integration.settlement_lp_value_contract.verify_settlement_lp_value_contract_payload_from_price_attestation",
        verify_from_price_attestation,
    )

    writes_packet, write_packet = _capture()
    handled_packet = maybe_handle_settlement_lp_value_route(
        path="/api/dex/verify_settlement_lp_value_contract",
        obj=_request(price_packet={"packet": "present"}, contract=contract),
        write_json=write_packet,
    )
    assert handled_packet is True
    assert packet_captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "price_packet_payload": {"packet": "present"},
        "lp_unit_values": {"pool-1": 77},
        "contract_payload": contract,
    }
    assert writes_packet == [(200, {"ok": True, "error": None})]

    writes_attestation, write_attestation = _capture()
    handled_attestation = maybe_handle_settlement_lp_value_route(
        path="/api/dex/verify_settlement_lp_value_contract",
        obj=_request(
            price_packet={"packet": "present"},
            price_attestation={"attestation": "present"},
            consumer_now_epoch=7,
            max_attestation_age_epochs=3,
            allowed_signers={"signer": ["oracle:a"]},
            contract=contract,
        ),
        write_json=write_attestation,
    )
    assert handled_attestation is True
    assert attestation_captured == {
        "settlement": ("settlement", {"kind": "fake-settlement"}, parsed_settlement),
        "price_attestation_payload": {"attestation": "present"},
        "consumer_now_epoch": 7,
        "max_attestation_age_epochs": 3,
        "lp_unit_values": {"pool-1": 77},
        "contract_payload": contract,
        "allowed_signers": {"signer": ["oracle:a"]},
    }
    assert writes_attestation == [(200, {"ok": True, "error": None})]


def test_verify_lp_value_exception_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _patch_parse_settlement(monkeypatch, object())

    def verify_settlement_lp_value_contract_payload(**_kwargs: object) -> tuple[bool, str]:
        raise RuntimeError("verify failed")

    monkeypatch.setattr(
        "src.integration.settlement_lp_value_contract.verify_settlement_lp_value_contract_payload",
        verify_settlement_lp_value_contract_payload,
    )

    handled = maybe_handle_settlement_lp_value_route(
        path="/api/dex/verify_settlement_lp_value_contract",
        obj=_request(contract={"schema": "fake-contract"}),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "verify_settlement_lp_value_contract_error", "details": "request failed"},
        )
    ]
