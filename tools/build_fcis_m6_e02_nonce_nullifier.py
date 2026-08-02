"""Build the source-bound FCIS M6 E02 nonce/nullifier vector."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

import tools.build_fcis_m6_e01_request_identity as e01_builder  # noqa: E402
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
    derive_nonce_nullifier_v1,
)
from src.core.fcis_m6_profile_ids import (  # noqa: E402
    M6_PROFILE_REGISTRY_VERSION_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402

E01_DEFAULT_CONFIG_PATH = e01_builder.DEFAULT_CONFIG_PATH
build_e01_payload = e01_builder.build_payload

DEFAULT_CONFIG_PATH = Path("config/deploy/fcis_m6_e02_nonce_nullifier_v1.json")
DEFAULT_OUTPUT_PATH = Path("docs/research/m6_tasks/TASK_E02_NONCE_NULLIFIER_V1.json")
E02_CONFIG_SCHEMA_V1 = "zenodex/fcis/m6/e02/nonce-nullifier-config/v1"
MAX_E02_NONCLAIMS_V1 = 32
MAX_E02_NONCLAIM_BYTES_V1 = 512
MAX_E02_NONCLAIMS_TOTAL_BYTES_V1 = 16 * 1024


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
        raise E02Error(f"strict JSON load failed for {path}") from exc
    if type(value) is not dict:
        raise E02Error(f"JSON root is not an object: {path}")
    return cast(dict[str, object], value)


def _text(value: object, name: str, *, maximum_bytes: int = 2048) -> str:
    if type(value) is not str or not value:
        raise E02Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise E02Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise E02Error(f"{name} exceeds its byte bound")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if len(checked) != 64 or any(character not in "0123456789abcdef" for character in checked):
        raise E02Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _integer(value: object, name: str, maximum: int) -> int:
    if type(value) is not int or value < 0 or value > maximum:
        raise E02Error(f"{name} is outside its closed integer bound")
    return value


def _load_config(path: Path) -> dict[str, object]:
    raw = _load_json(path)
    expected = {
        "schema",
        "profile_id",
        "identifier_registry_version",
        "semantic_allocator_profile_id",
        "current_nonce",
        "pinned_request_identity_root",
        "pinned_nullifier_root",
        "nonclaims",
    }
    if set(raw) != expected:
        raise E02Error("E02 configuration fields are not exact")
    if raw["schema"] != E02_CONFIG_SCHEMA_V1:
        raise E02Error("E02 configuration schema is wrong")
    _text(raw["profile_id"], "profile_id")
    if raw["identifier_registry_version"] != M6_PROFILE_REGISTRY_VERSION_V1:
        raise E02Error("E02 identifier registry version is not the frozen profile")
    if raw["semantic_allocator_profile_id"] != SEMANTIC_ALLOCATOR_PROFILE_ID_V1:
        raise E02Error("E02 semantic allocator profile is not the frozen profile")
    _integer(raw["current_nonce"], "current_nonce", MAX_E02_CURRENT_NONCE_V1)
    _digest(raw["pinned_request_identity_root"], "pinned_request_identity_root")
    _digest(raw["pinned_nullifier_root"], "pinned_nullifier_root")
    nonclaims = raw["nonclaims"]
    if (
        type(nonclaims) is not list
        or not nonclaims
        or len(nonclaims) > MAX_E02_NONCLAIMS_V1
        or any(type(item) is not str or not item for item in nonclaims)
    ):
        raise E02Error("nonclaims must be a bounded nonempty string list")
    checked_nonclaims = tuple(
        _text(item, f"nonclaims[{index}]", maximum_bytes=MAX_E02_NONCLAIM_BYTES_V1)
        for index, item in enumerate(nonclaims)
    )
    if len(set(checked_nonclaims)) != len(checked_nonclaims):
        raise E02Error("nonclaims must be unique")
    if sum(len(item.encode("utf-8")) for item in checked_nonclaims) > (
        MAX_E02_NONCLAIMS_TOTAL_BYTES_V1
    ):
        raise E02Error("nonclaims exceed their total byte bound")
    return raw


def _identity_from_e01_payload(payload: dict[str, object]) -> E01RequestIdentityV1:
    raw_command = payload.get("authenticated_command")
    raw_identity = payload.get("request_identity")
    if type(raw_command) is not dict or type(raw_identity) is not dict:
        raise E02Error("E01 payload command/identity objects are malformed")
    family_raw = raw_command.get("command_family")
    if type(family_raw) is not str:
        raise E02Error("E01 command family is malformed")
    command = _mint_authenticated_command_v1(
        command_root=_digest(raw_command["command_root"], "command_root"),
        sender_id=_text(raw_command["sender_id"], "sender_id", maximum_bytes=128),
        command_family=E01CommandFamilyV1(family_raw),
        nonce=_integer(raw_command["nonce"], "nonce", (1 << 64) - 1),
        authentication_profile_root=_digest(
            raw_command["authentication_profile_root"], "authentication_profile_root"
        ),
        authentication_evidence_root=_digest(
            raw_command["authentication_evidence_root"], "authentication_evidence_root"
        ),
    )
    identity = derive_request_identity_v1(
        authenticated_command=command,
        deployment_config_root=_digest(
            raw_identity["deployment_config_root"], "deployment_config_root"
        ),
        expected_sequence=_integer(
            raw_identity["expected_sequence"], "expected_sequence", (1 << 32) - 1
        ),
        authority_epoch_index=_integer(
            raw_identity["authority_epoch_index"], "authority_epoch_index", (1 << 32) - 1
        ),
    )
    if identity.to_wire() != raw_identity:
        raise E02Error("E01 identity payload is not canonically regenerated")
    return identity


def derive_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Derive E02 from the independently pinned E01 configuration."""

    config = _load_config(config_path.resolve())
    e01_payload = build_e01_payload(_ROOT / E01_DEFAULT_CONFIG_PATH)
    identity = _identity_from_e01_payload(e01_payload)
    if identity.request_identity_root != config["pinned_request_identity_root"]:
        raise E02Error("E02 source E01 identity root differs from its pin")
    nullifier = derive_nonce_nullifier_v1(
        request_identity=identity,
        current_nonce=_integer(config["current_nonce"], "current_nonce", MAX_E02_CURRENT_NONCE_V1),
    )
    if nullifier.nullifier_root != config["pinned_nullifier_root"]:
        raise E02Error("derived E02 nullifier root differs from its pin")
    return {
        "schema": FCIS_M6_E02_SCHEMA_V1,
        "profile_id": _text(config["profile_id"], "profile_id"),
        "identifier_registry_version": M6_PROFILE_REGISTRY_VERSION_V1,
        "semantic_allocator_profile_id": SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        "current_nonce": _integer(
            config["current_nonce"], "current_nonce", MAX_E02_CURRENT_NONCE_V1
        ),
        "request_identity": identity.to_wire(),
        "nullifier": nullifier.to_wire(),
        "pinned_request_identity_root": _digest(
            config["pinned_request_identity_root"], "pinned_request_identity_root"
        ),
        "pinned_nullifier_root": _digest(config["pinned_nullifier_root"], "pinned_nullifier_root"),
        "nonclaims": cast(list[str], config["nonclaims"]),
    }


def build_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Derive E02 and require both configured roots to match."""

    return derive_payload(config_path)


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
    payload = derive_payload(config)
    nullifier = cast(dict[str, object], payload["nullifier"])
    if print_derived:
        print("E02_DERIVED_NULLIFIER_ROOT", nullifier["nullifier_root"])
        return 0
    encoded = canonical_json_bytes(payload) + b"\n"
    if check:
        if output.read_bytes() != encoded:
            raise SystemExit("FAIL: E02 nonce/nullifier vector is stale")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(encoded)
    print("E02_NONCE_NULLIFIER_MATCH", nullifier["nullifier_root"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
