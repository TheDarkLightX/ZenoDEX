"""Independent checks for the FCIS M6 E02 nonce/nullifier vector."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core import fcis_m6_e02_nonce_nullifier as e02  # noqa: E402
from src.core.fcis_m6_e01_request_identity import (  # noqa: E402
    E01CommandFamilyV1,
    E01RequestIdentityV1,
    _mint_authenticated_command_v1,
    derive_request_identity_v1,
)
from src.core.fcis_m6_e02_nonce_nullifier import (  # noqa: E402
    FCIS_M6_E02_SCHEMA_V1,
    MAX_E02_CURRENT_NONCE_V1,
    E02Error,
    E02NullifierV1,
    derive_nonce_nullifier_v1,
    is_verified_nullifier_v1,
    nullifier_root_from_body_v1,
    same_nullifier_v1,
)
from tools.build_fcis_m6_e01_request_identity import (  # noqa: E402
    DEFAULT_OUTPUT_PATH as E01_OUTPUT_PATH,
)
from tools.build_fcis_m6_e02_nonce_nullifier import (  # noqa: E402
    DEFAULT_OUTPUT_PATH,
    build_payload,
)


def _read_vector() -> dict[str, object]:
    value = json.loads((_ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("E02 vector must be an object")
    return cast(dict[str, object], value)


def _identity_from_vector() -> E01RequestIdentityV1:
    e01 = json.loads((_ROOT / E01_OUTPUT_PATH).read_text(encoding="utf-8"))
    if type(e01) is not dict:
        raise AssertionError("E01 vector must be an object")
    raw_command = e01.get("authenticated_command")
    raw_identity = e01.get("request_identity")
    if type(raw_command) is not dict or type(raw_identity) is not dict:
        raise AssertionError("E01 command/identity objects are malformed")
    family_raw = raw_command.get("command_family")
    if type(family_raw) is not str:
        raise AssertionError("E01 command family is malformed")
    command = _mint_authenticated_command_v1(
        command_root=cast(str, raw_command["command_root"]),
        sender_id=cast(str, raw_command["sender_id"]),
        command_family=E01CommandFamilyV1(family_raw),
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


def _forge_identity(identity: E01RequestIdentityV1) -> E01RequestIdentityV1:
    forged = object.__new__(E01RequestIdentityV1)
    for name in (
        "deployment_config_root",
        "authentication_profile_root",
        "sender_id",
        "command_root",
        "command_family",
        "nonce",
        "expected_sequence",
        "authority_epoch_index",
        "request_identity_root",
    ):
        object.__setattr__(forged, name, object.__getattribute__(identity, name))
    return forged


def _forge_nullifier(nullifier: E02NullifierV1) -> E02NullifierV1:
    forged = object.__new__(E02NullifierV1)
    for name in ("request_identity", "current_nonce", "nullifier_root"):
        object.__setattr__(forged, name, object.__getattribute__(nullifier, name))
    return forged


def run_checks() -> None:
    baseline = build_payload()
    vector = _read_vector()
    if baseline != vector:
        raise AssertionError("E02 vector is not the independently regenerated payload")
    if baseline.get("schema") != FCIS_M6_E02_SCHEMA_V1:
        raise AssertionError("E02 schema is not canonical")
    identity = _identity_from_vector()
    current_nonce = cast(int, baseline["current_nonce"])
    nullifier = derive_nonce_nullifier_v1(
        request_identity=identity,
        current_nonce=current_nonce,
    )
    raw_nullifier = baseline.get("nullifier")
    if type(raw_nullifier) is not dict or nullifier.to_wire() != raw_nullifier:
        raise AssertionError("E02 nullifier does not round-trip through its vector")
    if not is_verified_nullifier_v1(nullifier):
        raise AssertionError("derived E02 nullifier lost verifier provenance")
    second = derive_nonce_nullifier_v1(
        request_identity=identity,
        current_nonce=current_nonce,
    )
    if not same_nullifier_v1(nullifier, second):
        raise AssertionError("same sender/nonce did not produce a stable nullifier")

    for invalid_current in (current_nonce - 1, current_nonce + 1, MAX_E02_CURRENT_NONCE_V1):
        try:
            derive_nonce_nullifier_v1(
                request_identity=identity,
                current_nonce=invalid_current,
            )
        except E02Error:
            pass
        else:
            raise AssertionError("non-next or overflowing current nonce was accepted")

    body = dict(nullifier.preimage_body())
    original_root = nullifier_root_from_body_v1(body)
    for field, changed in (
        ("deployment_config_root", "f" * 64),
        ("sender_id", "mallory"),
        ("nonce", nullifier.nonce + 1),
        ("command_family", E01CommandFamilyV1.MIGRATION.value),
    ):
        candidate = dict(body)
        candidate[field] = changed
        if nullifier_root_from_body_v1(candidate) == original_root:
            raise AssertionError(f"E02 nullifier root ignored {field} substitution")

    for malformed in (
        {**body, "extra": "rejected"},
        {key: value for key, value in body.items() if key != "nonce"},
        {**body, "nonce": True},
        {**body, "command_family": "unknown"},
    ):
        try:
            nullifier_root_from_body_v1(malformed)
        except E02Error:
            pass
        else:
            raise AssertionError("malformed E02 body crossed its strict codec")

    try:
        E02NullifierV1(
            request_identity=identity,
            current_nonce=current_nonce,
            nullifier_root=nullifier.nullifier_root,
        )
    except E02Error:
        pass
    else:
        raise AssertionError("caller minted an E02 nullifier witness")

    forged_identity = _forge_identity(identity)
    try:
        derive_nonce_nullifier_v1(
            request_identity=forged_identity,
            current_nonce=current_nonce,
        )
    except E02Error:
        pass
    else:
        raise AssertionError("exact-class forged E01 identity crossed E02")

    forged_nullifier = _forge_nullifier(nullifier)
    if not is_verified_nullifier_v1(forged_nullifier):
        raise AssertionError("source-equivalent E02 certificate did not replay")
    if not same_nullifier_v1(nullifier, forged_nullifier):
        raise AssertionError("source-equivalent E02 certificates differed")

    for name in ("_E02_NULLIFIERS_V1", "_E02_NULLIFIER_SNAPSHOTS_V1"):
        if hasattr(e02, name):
            raise AssertionError("E02 still depends on a process-local provenance registry")

    object.__setattr__(nullifier, "current_nonce", current_nonce - 1)
    if is_verified_nullifier_v1(nullifier):
        raise AssertionError("crossed E02 source retained verifier provenance")

    print("E02_NONCE_NULLIFIER_MATCH", raw_nullifier["nullifier_root"])


if __name__ == "__main__":
    run_checks()
