"""E01 authenticated request-identity boundary tests."""

from __future__ import annotations

from typing import cast

import pytest

from experiments.fcis_m6_e01_request_identity_check import run_checks
from src.core.fcis_m6_e01_request_identity import (
    E01AuthenticatedCommandV1,
    E01CommandFamilyV1,
    E01Error,
    E01RequestIdentityV1,
    derive_request_identity_v1,
    request_identity_root_from_body_v1,
)
from tools.build_fcis_m6_e01_request_identity import build_payload


def test_e01_checker_passes() -> None:
    run_checks()


def test_e01_public_identity_constructor_is_verifier_owned() -> None:
    raw = build_payload()["request_identity"]
    assert type(raw) is dict
    fields = raw
    with pytest.raises(E01Error, match="verifier-owned"):
        E01RequestIdentityV1(
            deployment_config_root=fields["deployment_config_root"],
            authentication_profile_root=fields["authentication_profile_root"],
            sender_id=fields["sender_id"],
            command_root=fields["command_root"],
            command_family=E01CommandFamilyV1.STATE_CHANGE,
            nonce=fields["nonce"],
            expected_sequence=fields["expected_sequence"],
            authority_epoch_index=fields["authority_epoch_index"],
            request_identity_root=fields["request_identity_root"],
        )


def test_e01_exact_class_without_verifier_provenance_is_rejected() -> None:
    payload = build_payload()
    raw = payload["authenticated_command"]
    assert type(raw) is dict
    forged = object.__new__(E01AuthenticatedCommandV1)
    object.__setattr__(forged, "command_root", raw["command_root"])
    object.__setattr__(forged, "sender_id", raw["sender_id"])
    object.__setattr__(forged, "command_family", E01CommandFamilyV1(raw["command_family"]))
    object.__setattr__(forged, "nonce", raw["nonce"])
    object.__setattr__(forged, "authentication_profile_root", raw["authentication_profile_root"])
    object.__setattr__(forged, "authentication_evidence_root", raw["authentication_evidence_root"])
    identity = cast(dict[str, object], payload["request_identity"])
    with pytest.raises(E01Error, match="provenance"):
        derive_request_identity_v1(
            authenticated_command=forged,
            deployment_config_root=cast(str, identity["deployment_config_root"]),
            expected_sequence=cast(int, identity["expected_sequence"]),
            authority_epoch_index=cast(int, identity["authority_epoch_index"]),
        )


def test_e01_root_codec_rejects_extra_missing_and_malformed_fields() -> None:
    raw = build_payload()["request_identity"]
    assert type(raw) is dict
    body = {
        key: value for key, value in raw.items() if key not in {"schema", "request_identity_root"}
    }
    with pytest.raises(E01Error):
        request_identity_root_from_body_v1({**body, "extra": "rejected"})
    with pytest.raises(E01Error):
        request_identity_root_from_body_v1(
            {key: value for key, value in body.items() if key != "nonce"}
        )
    with pytest.raises(E01Error):
        request_identity_root_from_body_v1({**body, "expected_sequence": True})


def test_e01_identity_root_changes_when_authenticated_command_changes() -> None:
    raw = build_payload()["request_identity"]
    assert type(raw) is dict
    body = {
        key: value for key, value in raw.items() if key not in {"schema", "request_identity_root"}
    }
    original = request_identity_root_from_body_v1(body)
    changed_body = dict(body)
    changed_body["command_root"] = "0" * 64
    assert request_identity_root_from_body_v1(changed_body) != original
