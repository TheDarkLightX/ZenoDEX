"""Build the source-bound FCIS M6 E03 uniqueness vector."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_m6_e01_request_identity import (  # noqa: E402
    E01CommandFamilyV1,
    E01Error,
    E01RequestIdentityV1,
    _mint_authenticated_command_v1,
    derive_request_identity_v1,
)
from src.core.fcis_m6_e02_nonce_nullifier import (  # noqa: E402
    E02Error,
    derive_nonce_nullifier_v1,
)
from src.core.fcis_m6_e03_unique_commit_port import (  # noqa: E402
    FCIS_M6_E03_SCHEMA_V1,
    E03CommitIdentityV1,
    E03EffectSpecV1,
    E03Error,
    _mint_e03_commit_identity_v1,
)
from src.core.fcis_m6_profile_ids import (  # noqa: E402
    M6_PROFILE_REGISTRY_VERSION_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402
from tools.build_fcis_m6_e01_request_identity import (  # noqa: E402
    build_payload as build_e01_payload,
)
from tools.build_fcis_m6_e02_nonce_nullifier import (  # noqa: E402
    build_payload as build_e02_payload,
)

DEFAULT_CONFIG_PATH = Path("config/deploy/fcis_m6_e03_uniqueness_v1.json")
DEFAULT_MIGRATION_PATH = Path("config/deploy/fcis_m6_e03_uniqueness_v1.sql")
DEFAULT_OUTPUT_PATH = Path("docs/research/m6_tasks/TASK_E03_DATABASE_UNIQUENESS_V1.json")
E03_CONFIG_SCHEMA_V1 = "zenodex/fcis/m6/e03/unique-commit-port-config/v1"
MAX_E03_NONCLAIMS_V1 = 32
MAX_E03_NONCLAIM_BYTES_V1 = 512
MAX_E03_NONCLAIMS_TOTAL_BYTES_V1 = 16 * 1024


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
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object)
    except (OSError, UnicodeError, json.JSONDecodeError, _DuplicateJsonKey) as exc:
        raise E03Error(f"strict JSON load failed for {path}") from exc
    if type(value) is not dict:
        raise E03Error(f"JSON root is not an object: {path}")
    return cast(dict[str, object], value)


def _text(value: object, name: str, *, maximum_bytes: int = 2048) -> str:
    if type(value) is not str or not value:
        raise E03Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise E03Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise E03Error(f"{name} exceeds its byte bound")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if len(checked) != 64 or any(character not in "0123456789abcdef" for character in checked):
        raise E03Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _integer(value: object, name: str, maximum: int, *, positive: bool = False) -> int:
    if type(value) is not int or value < (1 if positive else 0) or value > maximum:
        raise E03Error(f"{name} is outside its closed integer bound")
    return value


def _load_config(path: Path) -> dict[str, object]:
    raw = _load_json(path)
    expected = {
        "schema",
        "profile_id",
        "identifier_registry_version",
        "semantic_allocator_profile_id",
        "migration_sql_sha256",
        "sequence",
        "commit_id",
        "destination",
        "payload_root",
        "writer_profile_root",
        "adapter_profile_root",
        "pinned_nullifier_root",
        "pinned_fingerprint",
        "pinned_effect_id",
        "nonclaims",
    }
    if set(raw) != expected:
        raise E03Error("E03 configuration fields are not exact")
    if raw["schema"] != E03_CONFIG_SCHEMA_V1:
        raise E03Error("E03 configuration schema is wrong")
    _text(raw["profile_id"], "profile_id")
    if raw["identifier_registry_version"] != M6_PROFILE_REGISTRY_VERSION_V1:
        raise E03Error("E03 identifier registry version is not the frozen profile")
    if raw["semantic_allocator_profile_id"] != SEMANTIC_ALLOCATOR_PROFILE_ID_V1:
        raise E03Error("E03 semantic allocator profile is not the frozen profile")
    _digest(raw["migration_sql_sha256"], "migration_sql_sha256")
    _integer(raw["sequence"], "sequence", 128, positive=True)
    for name in (
        "commit_id",
        "payload_root",
        "writer_profile_root",
        "adapter_profile_root",
        "pinned_nullifier_root",
        "pinned_fingerprint",
        "pinned_effect_id",
    ):
        _digest(raw[name], name)
    _text(raw["destination"], "destination", maximum_bytes=256)
    nonclaims = raw["nonclaims"]
    if (
        type(nonclaims) is not list
        or not nonclaims
        or len(nonclaims) > MAX_E03_NONCLAIMS_V1
        or any(type(item) is not str or not item for item in nonclaims)
    ):
        raise E03Error("nonclaims must be a bounded nonempty string list")
    checked_nonclaims = tuple(
        _text(item, f"nonclaims[{index}]", maximum_bytes=MAX_E03_NONCLAIM_BYTES_V1)
        for index, item in enumerate(nonclaims)
    )
    if len(set(checked_nonclaims)) != len(checked_nonclaims):
        raise E03Error("nonclaims must be unique")
    if sum(len(item.encode("utf-8")) for item in checked_nonclaims) > (
        MAX_E03_NONCLAIMS_TOTAL_BYTES_V1
    ):
        raise E03Error("nonclaims exceed their total byte bound")
    return raw


def _identity_from_e02_payload(payload: dict[str, object]) -> E01RequestIdentityV1:
    raw_identity = payload.get("request_identity")
    raw_command = build_e01_payload().get("authenticated_command")
    if type(raw_identity) is not dict or type(raw_command) is not dict:
        raise E03Error("E02 payload command/identity objects are malformed")
    family_raw = raw_command.get("command_family")
    if type(family_raw) is not str:
        raise E03Error("E02 command family is malformed")
    try:
        command = _mint_authenticated_command_v1(
            command_root=_digest(raw_command["command_root"], "command_root"),
            sender_id=_text(raw_command["sender_id"], "sender_id", maximum_bytes=128),
            command_family=E01CommandFamilyV1(family_raw),
            nonce=_integer(raw_command["nonce"], "nonce", (1 << 64) - 1),
            authentication_profile_root=_digest(
                raw_command["authentication_profile_root"],
                "authentication_profile_root",
            ),
            authentication_evidence_root=_digest(
                raw_command["authentication_evidence_root"],
                "authentication_evidence_root",
            ),
        )
        identity = derive_request_identity_v1(
            authenticated_command=command,
            deployment_config_root=_digest(
                raw_identity["deployment_config_root"],
                "deployment_config_root",
            ),
            expected_sequence=_integer(
                raw_identity["expected_sequence"],
                "expected_sequence",
                (1 << 32) - 1,
            ),
            authority_epoch_index=_integer(
                raw_identity["authority_epoch_index"],
                "authority_epoch_index",
                (1 << 32) - 1,
            ),
        )
    except (E01Error, TypeError, ValueError, ArithmeticError, OverflowError) as exc:
        raise E03Error("E02 request identity could not be reconstructed") from exc
    if identity.to_wire() != raw_identity:
        raise E03Error("E02 request identity is not canonically regenerated")
    return identity


def _migration_sha256(path: Path = _ROOT / DEFAULT_MIGRATION_PATH) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for block in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(block)
    except OSError as exc:
        raise E03Error("E03 migration SQL cannot be hashed") from exc
    return digest.hexdigest()


def _build_candidate(
    config: dict[str, object],
    *,
    check_pins: bool = True,
) -> E03CommitIdentityV1:
    e02_payload = build_e02_payload()
    identity = _identity_from_e02_payload(e02_payload)
    current_nonce = e02_payload.get("current_nonce")
    current_nonce = _integer(current_nonce, "current_nonce", (1 << 64) - 2)
    try:
        nullifier = derive_nonce_nullifier_v1(
            request_identity=identity,
            current_nonce=current_nonce,
        )
        if nullifier.nullifier_root != config["pinned_nullifier_root"]:
            raise E03Error("E02 nullifier root differs from the E03 pin")
        effect = E03EffectSpecV1(
            ordinal=0,
            destination=_text(config["destination"], "destination", maximum_bytes=256),
            payload_root=_digest(config["payload_root"], "payload_root"),
            writer_profile_root=_digest(config["writer_profile_root"], "writer_profile_root"),
            adapter_profile_root=_digest(
                config["adapter_profile_root"],
                "adapter_profile_root",
            ),
        )
        candidate = _mint_e03_commit_identity_v1(
            sequence=_integer(config["sequence"], "sequence", 128, positive=True),
            commit_id=_digest(config["commit_id"], "commit_id"),
            nullifier=nullifier,
            effects=(effect,),
        )
    except (E02Error, E03Error, TypeError, ValueError, ArithmeticError, OverflowError) as exc:
        if isinstance(exc, E03Error):
            raise
        raise E03Error("E03 candidate could not be derived") from exc
    if check_pins:
        if candidate.fingerprint != config["pinned_fingerprint"]:
            raise E03Error("E03 fingerprint differs from its pin")
        if candidate.effects[0].derive_effect_id(candidate.commit_id) != config["pinned_effect_id"]:
            raise E03Error("E03 effect identity differs from its pin")
    return candidate


def build_candidate(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> E03CommitIdentityV1:
    """Derive the verifier-owned E03 candidate from the E02 source vector."""

    config = _load_config(config_path.resolve())
    if _migration_sha256() != config["migration_sql_sha256"]:
        raise E03Error("E03 migration SQL differs from its configured hash")
    return _build_candidate(config)


def build_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Derive E03 and require the configured migration and identity pins."""

    config = _load_config(config_path.resolve())
    migration_hash = _migration_sha256()
    if migration_hash != config["migration_sql_sha256"]:
        raise E03Error("E03 migration SQL differs from its configured hash")
    candidate = _build_candidate(config)
    return {
        "schema": FCIS_M6_E03_SCHEMA_V1,
        "profile_id": _text(config["profile_id"], "profile_id"),
        "identifier_registry_version": M6_PROFILE_REGISTRY_VERSION_V1,
        "semantic_allocator_profile_id": SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        "migration_sql_sha256": migration_hash,
        "candidate": candidate.to_wire(),
        "pinned_nullifier_root": _digest(config["pinned_nullifier_root"], "pinned_nullifier_root"),
        "pinned_fingerprint": _digest(config["pinned_fingerprint"], "pinned_fingerprint"),
        "pinned_effect_id": _digest(config["pinned_effect_id"], "pinned_effect_id"),
        "nonclaims": cast(list[str], config["nonclaims"]),
    }


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
            config_candidate = Path(args[index])
            config = (
                config_candidate if config_candidate.is_absolute() else _ROOT / config_candidate
            )
        elif token == "--output" and index + 1 < len(args):
            index += 1
            output_candidate = Path(args[index])
            output = (
                output_candidate if output_candidate.is_absolute() else _ROOT / output_candidate
            )
        else:
            raise SystemExit(f"unknown or incomplete argument: {token}")
        index += 1
    if print_derived:
        raw_config = _load_config(config.resolve())
        candidate_identity = _build_candidate(raw_config, check_pins=False)
        print("E03_DERIVED_FINGERPRINT", candidate_identity.fingerprint)
        print(
            "E03_DERIVED_EFFECT_ID",
            candidate_identity.effects[0].derive_effect_id(candidate_identity.commit_id),
        )
        return 0
    payload = build_payload(config)
    candidate_wire = cast(dict[str, object], payload["candidate"])
    encoded = canonical_json_bytes(payload) + b"\n"
    if check:
        if output.read_bytes() != encoded:
            raise SystemExit("FAIL: E03 uniqueness vector is stale")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(encoded)
    print("E03_UNIQUENESS_VECTOR_MATCH", candidate_wire["fingerprint"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
