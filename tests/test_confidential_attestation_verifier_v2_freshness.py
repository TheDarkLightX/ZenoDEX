"""Freshness checks for TEE attestation verifier v2."""

from __future__ import annotations

import struct

import pytest

import src.integration.confidential_attestation_verifier_v2 as attestation_v2
from src.integration.confidential_attestation_verifier_v2 import (
    ProductionAttestationVerifier,
    ProductionAttestationVerifierConfig,
    parse_sgx_quote,
    sgx_measurement_from_quote,
)


def _build_sgx_quote() -> bytes:
    quote = bytearray(48 + 384 + 64)
    struct.pack_into("<H", quote, 0, 1)
    quote[176:208] = b"\xab" * 32
    quote[240:272] = b"\xcd" * 32
    struct.pack_into("<H", quote, 288, 1)
    struct.pack_into("<H", quote, 290, 2)
    return bytes(quote)


def _verifier(*, current_time_s: int, max_attestation_age_s: int = 300) -> ProductionAttestationVerifier:
    quote = _build_sgx_quote()
    measurement = sgx_measurement_from_quote(parse_sgx_quote(quote))
    return ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(
            allowlist=(measurement,),
            require_certificate_binding=False,
            current_time_s=current_time_s,
            max_attestation_age_s=max_attestation_age_s,
        )
    )


def test_attestation_rejects_stale_issued_at_when_freshness_enabled() -> None:
    quote = _build_sgx_quote()
    result, err = _verifier(current_time_s=1_700_001_000).verify(
        {"provider": "sgx", "quote": quote.hex()},
        issued_at_s=1_700_000_000,
    )

    assert result is None
    assert err == "attestation is older than max_attestation_age_s"


def test_attestation_rejects_future_issued_at_when_freshness_enabled() -> None:
    quote = _build_sgx_quote()
    result, err = _verifier(current_time_s=1_700_000_000).verify(
        {"provider": "sgx", "quote": quote.hex()},
        issued_at_s=1_700_000_001,
    )

    assert result is None
    assert err == "attestation issued_at_s is in the future"


def test_attestation_accepts_current_issued_at_when_freshness_enabled() -> None:
    quote = _build_sgx_quote()
    result, err = _verifier(current_time_s=1_700_000_100).verify(
        {"provider": "sgx", "quote": quote.hex()},
        issued_at_s=1_700_000_000,
    )

    assert err is None
    assert result is not None


def test_attestation_freshness_disabled_when_current_time_is_zero() -> None:
    quote = _build_sgx_quote()
    result, err = _verifier(current_time_s=0).verify(
        {"provider": "sgx", "quote": quote.hex()},
        issued_at_s=1,
    )

    assert err is None
    assert result is not None


def test_attestation_verifier_rejects_malformed_hex_without_raising() -> None:
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(
            allowlist=(),
            require_certificate_binding=False,
        )
    )

    result, err = verifier.verify(
        {"provider": "nitro", "attestation_document": "not-hex"},
    )
    assert result is None
    assert err == "nitro attestation_document must be hex"

    result, err = verifier.verify(
        {"provider": "sgx", "quote": "not-hex"},
    )
    assert result is None
    assert err == "sgx quote must be hex"


def test_attestation_verifier_caps_parser_error_details(monkeypatch: pytest.MonkeyPatch) -> None:
    long_detail = "x" * 300
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(
            allowlist=(),
            require_certificate_binding=False,
            local_testnet_mode=True,
        )
    )

    with monkeypatch.context() as m:
        m.setattr(
            attestation_v2,
            "_decode_cose_sign1",
            lambda data: (_ for _ in ()).throw(RuntimeError(long_detail)),
        )
        result, err = verifier.verify(
            {"provider": "nitro", "attestation_document": "00"},
        )
        assert result is None
        assert err == "failed to parse nitro attestation document: " + ("x" * 200)

    with monkeypatch.context() as m:
        m.setattr(
            attestation_v2,
            "nitro_measurement_from_summary",
            lambda summary: (_ for _ in ()).throw(RuntimeError(long_detail)),
        )
        result, err = verifier.verify(
            {"provider": "nitro", "summary": {"pcrs": {}}},
        )
        assert result is None
        assert err == "invalid nitro summary: " + ("x" * 200)

        result, err = verifier.verify(
            {"provider": "smoke", "summary": {"pcrs": {}}},
        )
        assert result is None
        assert err == "invalid smoke summary: " + ("x" * 200)

    with monkeypatch.context() as m:
        m.setattr(
            attestation_v2,
            "parse_sgx_quote",
            lambda quote: (_ for _ in ()).throw(RuntimeError(long_detail)),
        )
        result, err = verifier.verify(
            {"provider": "sgx", "quote": "0011"},
        )
        assert result is None
        assert err == "failed to parse SGX quote: " + ("x" * 200)
