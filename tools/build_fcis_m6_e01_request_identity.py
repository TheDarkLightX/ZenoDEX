"""Build the source-bound FCIS M6 E01 request-identity vector."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_m6_e01_request_identity import (  # noqa: E402
    FCIS_M6_E01_SCHEMA_V1,
    E01CommandFamilyV1,
    E01Error,
    _mint_authenticated_command_v1,
    derive_request_identity_v1,
)
from src.core.fcis_m6_profile_ids import (  # noqa: E402
    M6_PROFILE_REGISTRY_VERSION_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402

DEFAULT_CONFIG_PATH = Path("config/deploy/fcis_m6_e01_request_identity_v1.json")
DEFAULT_OUTPUT_PATH = Path("docs/research/m6_tasks/TASK_E01_REQUEST_IDENTITY_V1.json")
E01_CONFIG_SCHEMA_V1 = "zenodex/fcis/m6/e01/request-identity-config/v1"


class _DuplicateJsonKey(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateJsonKey(key)
        result[key] = value
    return result


def _load_json(path: Path) -> dict[str, object]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_strict_object,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, _DuplicateJsonKey) as exc:
        raise E01Error(f"strict JSON load failed for {path}") from exc
    if type(value) is not dict:
        raise E01Error(f"JSON root is not an object: {path}")
    return cast(dict[str, object], value)


def _text(value: object, name: str, *, maximum_bytes: int = 2048) -> str:
    if type(value) is not str or not value:
        raise E01Error(f"{name} must be a nonempty exact string")
    if len(value.encode("utf-8")) > maximum_bytes:
        raise E01Error(f"{name} exceeds its byte bound")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if len(checked) != 64 or any(character not in "0123456789abcdef" for character in checked):
        raise E01Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _integer(value: object, name: str, maximum: int, *, positive: bool = False) -> int:
    if type(value) is not int or value < (1 if positive else 0) or value > maximum:
        raise E01Error(f"{name} is outside its closed integer bound")
    return value


def _load_config(path: Path) -> dict[str, object]:
    raw = _load_json(path)
    expected = {
        "schema",
        "profile_id",
        "identifier_registry_version",
        "semantic_allocator_profile_id",
        "deployment_config_root",
        "authentication_profile_root",
        "authentication_evidence_root",
        "command_root",
        "sender_id",
        "command_family",
        "nonce",
        "expected_sequence",
        "authority_epoch_index",
        "pinned_request_identity_root",
        "nonclaims",
    }
    if set(raw) != expected:
        raise E01Error("E01 configuration fields are not exact")
    if raw["schema"] != E01_CONFIG_SCHEMA_V1:
        raise E01Error("E01 configuration schema is wrong")
    _text(raw["profile_id"], "profile_id")
    if raw["identifier_registry_version"] != M6_PROFILE_REGISTRY_VERSION_V1:
        raise E01Error("E01 identifier registry version is not the frozen profile")
    if raw["semantic_allocator_profile_id"] != SEMANTIC_ALLOCATOR_PROFILE_ID_V1:
        raise E01Error("E01 semantic allocator profile is not the frozen profile")
    for name in (
        "deployment_config_root",
        "authentication_profile_root",
        "authentication_evidence_root",
        "command_root",
        "pinned_request_identity_root",
    ):
        _digest(raw[name], name)
    _text(raw["sender_id"], "sender_id", maximum_bytes=128)
    command_family_raw = raw["command_family"]
    if type(command_family_raw) is not str:
        raise E01Error("command_family must be an exact string")
    try:
        E01CommandFamilyV1(command_family_raw)
    except ValueError as exc:
        raise E01Error("command_family is outside the closed enum") from exc
    _integer(raw["nonce"], "nonce", (1 << 64) - 1)
    _integer(raw["expected_sequence"], "expected_sequence", (1 << 32) - 1, positive=True)
    _integer(raw["authority_epoch_index"], "authority_epoch_index", (1 << 32) - 1)
    nonclaims = raw["nonclaims"]
    if (
        type(nonclaims) is not list
        or not nonclaims
        or any(type(item) is not str or not item for item in nonclaims)
    ):
        raise E01Error("nonclaims must be a nonempty string list")
    return raw


def derive_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Derive the E01 vector from the strict configuration premise."""

    config = _load_config(config_path.resolve())
    family = E01CommandFamilyV1(cast(str, config["command_family"]))
    command = _mint_authenticated_command_v1(
        command_root=_digest(config["command_root"], "command_root"),
        sender_id=_text(config["sender_id"], "sender_id", maximum_bytes=128),
        command_family=family,
        nonce=_integer(config["nonce"], "nonce", (1 << 64) - 1),
        authentication_profile_root=_digest(
            config["authentication_profile_root"], "authentication_profile_root"
        ),
        authentication_evidence_root=_digest(
            config["authentication_evidence_root"], "authentication_evidence_root"
        ),
    )
    identity = derive_request_identity_v1(
        authenticated_command=command,
        deployment_config_root=_digest(config["deployment_config_root"], "deployment_config_root"),
        expected_sequence=_integer(
            config["expected_sequence"],
            "expected_sequence",
            (1 << 32) - 1,
            positive=True,
        ),
        authority_epoch_index=_integer(
            config["authority_epoch_index"],
            "authority_epoch_index",
            (1 << 32) - 1,
        ),
    )
    return {
        "schema": FCIS_M6_E01_SCHEMA_V1,
        "profile_id": _text(config["profile_id"], "profile_id"),
        "identifier_registry_version": M6_PROFILE_REGISTRY_VERSION_V1,
        "semantic_allocator_profile_id": SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        "authenticated_command": command.to_wire(),
        "request_identity": identity.to_wire(),
        "pinned_request_identity_root": _digest(
            config["pinned_request_identity_root"], "pinned_request_identity_root"
        ),
        "nonclaims": cast(list[str], config["nonclaims"]),
    }


def build_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Derive E01 and require the configured identity root pin."""

    config = _load_config(config_path.resolve())
    payload = derive_payload(config_path)
    identity = payload.get("request_identity")
    if (
        type(identity) is not dict
        or identity.get("request_identity_root") != config["pinned_request_identity_root"]
    ):
        raise E01Error("derived E01 root differs from the pinned root")
    return payload


def main(argv: list[str] | None = None) -> int:
    args = list(argv or sys.argv[1:])
    config = _ROOT / DEFAULT_CONFIG_PATH
    output = _ROOT / DEFAULT_OUTPUT_PATH
    check = False
    print_derived = False
    index = 0
    while index < len(args):
        token = args[index]
        if token == "--check":
            check = True
        elif token == "--print-derived":
            print_derived = True
        elif token == "--config" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            config = candidate if candidate.is_absolute() else _ROOT / candidate
        elif token == "--output" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            output = candidate if candidate.is_absolute() else _ROOT / candidate
        else:
            raise SystemExit(f"unknown or incomplete argument: {token}")
        index += 1
    payload = derive_payload(config) if print_derived else build_payload(config)
    if print_derived:
        identity = cast(dict[str, object], payload["request_identity"])
        print("E01_DERIVED_REQUEST_IDENTITY_ROOT", identity["request_identity_root"])
        return 0
    encoded = canonical_json_bytes(payload) + b"\n"
    if check:
        if output.read_bytes() != encoded:
            raise SystemExit("FAIL: E01 request-identity vector is stale")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(encoded)
    identity = cast(dict[str, object], payload["request_identity"])
    print("E01_REQUEST_IDENTITY_MATCH", identity["request_identity_root"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
