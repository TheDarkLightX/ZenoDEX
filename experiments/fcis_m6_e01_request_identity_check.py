"""Independent checks for the FCIS M6 E01 request-identity vector."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_m6_e01_request_identity import (  # noqa: E402
    E01AuthenticatedCommandV1,
    E01CommandFamilyV1,
    E01Error,
    E01RequestIdentityV1,
    _mint_authenticated_command_v1,
    derive_request_identity_v1,
    request_identity_root_from_body_v1,
    same_request_identity_v1,
)
from tools.build_fcis_m6_e01_request_identity import (  # noqa: E402
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    build_payload,
)


def _read_vector() -> dict[str, object]:
    value = json.loads((_ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("E01 vector must be an object")
    return cast(dict[str, object], value)


def _identity_from_payload(payload: dict[str, object]) -> E01RequestIdentityV1:
    raw_command = payload.get("authenticated_command")
    raw_identity = payload.get("request_identity")
    if type(raw_command) is not dict or type(raw_identity) is not dict:
        raise AssertionError("E01 vector command/identity objects are malformed")
    command_family = raw_command.get("command_family")
    if type(command_family) is not str:
        raise AssertionError("E01 command family is malformed")
    command = _mint_authenticated_command_v1(
        command_root=cast(str, raw_command["command_root"]),
        sender_id=cast(str, raw_command["sender_id"]),
        command_family=E01CommandFamilyV1(command_family),
        nonce=cast(int, raw_command["nonce"]),
        authentication_profile_root=cast(str, raw_command["authentication_profile_root"]),
        authentication_evidence_root=cast(str, raw_command["authentication_evidence_root"]),
    )
    return derive_request_identity_v1(
        authenticated_command=command,
        deployment_config_root=cast(str, raw_identity["deployment_config_root"]),
        expected_sequence=cast(int, raw_identity["expected_sequence"]),
        authority_epoch_index=cast(int, raw_identity["authority_epoch_index"]),
    )


def run_checks() -> None:
    baseline = build_payload(_ROOT / DEFAULT_CONFIG_PATH)
    vector = _read_vector()
    if baseline != vector:
        raise AssertionError("E01 vector is not the independently regenerated payload")
    identity = _identity_from_payload(baseline)
    raw_identity = cast(dict[str, object], baseline["request_identity"])
    if identity.to_wire() != raw_identity:
        raise AssertionError("E01 identity does not round-trip through its vector")
    if not same_request_identity_v1(identity, _identity_from_payload(baseline)):
        raise AssertionError("same authenticated invocation did not produce a stable retry ID")

    body = {
        key: value
        for key, value in raw_identity.items()
        if key not in {"schema", "request_identity_root"}
    }
    changed_sequence = dict(body)
    changed_sequence["expected_sequence"] = identity.expected_sequence + 1
    if request_identity_root_from_body_v1(changed_sequence) == identity.request_identity_root:
        raise AssertionError("sequence mutation preserved the request identity")

    malformed = dict(body)
    malformed["nonce"] = True
    try:
        request_identity_root_from_body_v1(malformed)
    except E01Error:
        pass
    else:
        raise AssertionError("boolean nonce crossed the E01 integer boundary")

    try:
        E01AuthenticatedCommandV1(
            command_root=identity.command_root,
            sender_id=identity.sender_id,
            command_family=identity.command_family,
            nonce=identity.nonce,
            authentication_profile_root=identity.authentication_profile_root,
            authentication_evidence_root=cast(
                str,
                cast(dict[str, object], baseline["authenticated_command"])[
                    "authentication_evidence_root"
                ],
            ),
        )
    except E01Error:
        pass
    else:
        raise AssertionError("caller minted an authenticated-command witness")

    print("E01_REQUEST_IDENTITY_MATCH", identity.request_identity_root)


if __name__ == "__main__":
    run_checks()
