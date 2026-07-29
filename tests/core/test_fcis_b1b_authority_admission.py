from __future__ import annotations

import json

import pytest

from src.core.fcis_b1b_authority_admission import decode_fcis_b1b_authority_v2
from src.core.fcis_b1b_authority_values import (
    FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
    B1BAuthorityAdmissionCodeV2,
    B1BAuthorityAdmissionRejectV2,
    FCISAuthorityHeaderV2,
)

ROOT = "0x" + ("1" * 64)


def _canonical(value: dict[str, object]) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")


def _document(**overrides: object) -> dict[str, object]:
    value: dict[str, object] = {
        "chain_deployment_id": "zenodex:testnet:α",
        "sequence": 0,
        "fee_distribution_configuration_root": ROOT,
    }
    value.update(overrides)
    return {"schema": FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2, "value": value}


def _reject(payload: bytes) -> B1BAuthorityAdmissionRejectV2:
    result = decode_fcis_b1b_authority_v2(payload)
    assert type(result) is B1BAuthorityAdmissionRejectV2
    return result


def test_strict_decoder_accepts_only_the_unique_canonical_encoding() -> None:
    canonical = _canonical(_document())
    assert type(decode_fcis_b1b_authority_v2(canonical)) is FCISAuthorityHeaderV2

    variants = (
        canonical + b"\n",
        canonical.replace(b'"schema":', b'"schema": '),
        b'{"value":'
        + canonical.split(b'"value":', 1)[1].rsplit(b"}", 1)[0]
        + b',"schema":"'
        + FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2.encode()
        + b'"}',
    )
    for variant in variants:
        assert _reject(variant).code is B1BAuthorityAdmissionCodeV2.NONCANONICAL_ENCODING


def test_duplicate_unknown_and_missing_fields_have_stable_rejections() -> None:
    duplicate = (
        b'{"schema":"'
        + FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2.encode()
        + b'","value":{"chain_deployment_id":"deployment",'
        + b'"chain_deployment_id":"mallory","fee_distribution_configuration_root":"'
        + ROOT.encode()
        + b'","sequence":0}}'
    )
    assert _reject(duplicate).code is B1BAuthorityAdmissionCodeV2.DUPLICATE_FIELD

    unknown = _document(extra=1)
    reject = _reject(_canonical(unknown))
    assert reject.code is B1BAuthorityAdmissionCodeV2.UNKNOWN_FIELD
    assert reject.path == ("value", "extra")

    missing = _document()
    del missing["value"]["sequence"]  # type: ignore[index]
    reject = _reject(_canonical(missing))
    assert reject.code is B1BAuthorityAdmissionCodeV2.MISSING_FIELD
    assert reject.path == ("value", "sequence")


def test_wrong_schema_envelope_and_top_level_types_fail_closed() -> None:
    wrong_schema = _document()
    wrong_schema["schema"] = "zenodex/fcis/unknown/v2"
    assert _reject(_canonical(wrong_schema)).code is B1BAuthorityAdmissionCodeV2.UNKNOWN_SCHEMA

    assert _reject(b"[]").code is B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE
    assert _reject(b"not-json").code is B1BAuthorityAdmissionCodeV2.INVALID_JSON
    assert _reject(b"\xff").code is B1BAuthorityAdmissionCodeV2.INVALID_UTF8
    assert _reject(_canonical({"schema": FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2})).code is (
        B1BAuthorityAdmissionCodeV2.MISSING_FIELD
    )


@pytest.mark.parametrize(
    "field,value",
    (
        ("sequence", True),
        ("sequence", -1),
        ("sequence", 1 << 256),
        ("chain_deployment_id", ""),
        ("fee_distribution_configuration_root", "0x" + ("A" * 64)),
    ),
)
def test_exact_value_failures_are_closed(field: str, value: object) -> None:
    reject = _reject(_canonical(_document(**{field: value})))
    assert reject.code is B1BAuthorityAdmissionCodeV2.INVALID_VALUE


def test_float_and_surrogate_payloads_reject() -> None:
    floating = _canonical(_document()).replace(b'"sequence":0', b'"sequence":0.0')
    assert _reject(floating).code is B1BAuthorityAdmissionCodeV2.INVALID_JSON

    surrogate = (
        '{"schema":"'
        + FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2
        + '","value":{"chain_deployment_id":"\\ud800",'
        + '"fee_distribution_configuration_root":"'
        + ROOT
        + '","sequence":0}}'
    ).encode("ascii")
    assert _reject(surrogate).code is B1BAuthorityAdmissionCodeV2.INVALID_VALUE
