"""Trusted release binding for recursive STARK verifier and replay artifacts.

The loader returns an immutable value only after canonical release bytes match
an independently supplied config digest and exact chain, epoch, and proof-profile
expectations. Proofs, verifier reports, and replay transcripts have no input
channel at this boundary.

The trusted value is a nominal Python type, not an authorization capability.
Same-process code can bypass Python constructors with ``object.__new__``.
Consumers must therefore validate the canonical bytes and independently trusted
expectations with this loader at the consuming boundary; possession of an
instance alone grants no authority.

This module claims deterministic byte identity and scope binding only. It does
not authenticate the source of the expected config digest, verify a RISC0
receipt, inspect the authority manifest, check the replay bundle, authorize
settlement, or establish production readiness. Ledger, governance, release, and
runtime-admission integration remain pending.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import re
from dataclasses import dataclass
from typing import NoReturn, Self, final

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, encode_bytes

RECURSIVE_STARK_RELEASE_BINDING_SCHEMA_V1 = "zenodex.recursive_stark_release_binding.v1"
MAX_RELEASE_BINDING_BYTES_V1 = 4 * 1024
MAX_CHAIN_ID_BYTES_V1 = 128
MAX_PROOF_PROFILE_BYTES_V1 = 128
MAX_EPOCH_ID_V1 = (1 << 64) - 1

_CONFIG_DIGEST_DOMAIN_V1 = domain_sep_bytes(
    "recursive_stark_release_binding_config",
    version=1,
)
_TOKEN_RE = re.compile(r"^[A-Za-z0-9._:-]+$")
_BARE_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_SHA256_REF_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_CONFIG_DIGEST_RE = re.compile(r"^0x[0-9a-f]{64}$")
_FIELDS_V1 = frozenset(
    {
        "schema",
        "chain_id",
        "epoch_id",
        "proof_profile",
        "authority_manifest_sha256",
        "replay_manifest_sha256",
    }
)


class RecursiveStarkReleaseBindingError(ValueError):
    """Stable fail-closed error at the trusted release-binding boundary."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


@dataclass(frozen=True, slots=True)
class _ParsedRecursiveStarkReleaseBinding:
    schema: str
    chain_id: str
    epoch_id: int
    proof_profile: str
    authority_manifest_sha256: str
    replay_manifest_sha256: str


@final
@dataclass(frozen=True, init=False, slots=True)
class TrustedRecursiveStarkReleaseBinding:
    """A nominal marker for a release record validated at one consuming boundary."""

    schema: str
    chain_id: str
    epoch_id: int
    proof_profile: str
    authority_manifest_sha256: str
    replay_manifest_sha256: str

    def __new__(cls) -> Self:
        raise TypeError("trusted recursive STARK release bindings must be created by the loader")

    def __init_subclass__(cls, **kwargs: object) -> NoReturn:
        raise TypeError("trusted recursive STARK release bindings cannot be subclassed")

    def __reduce__(self) -> NoReturn:
        raise TypeError("trusted recursive STARK release bindings cannot be pickled")

    def __reduce_ex__(self, protocol: object) -> NoReturn:
        raise TypeError("trusted recursive STARK release bindings cannot be pickled")

    def __setstate__(self, state: object) -> NoReturn:
        raise TypeError("trusted recursive STARK release bindings cannot be reconstructed")


def _reject(code: str, detail: str) -> RecursiveStarkReleaseBindingError:
    return RecursiveStarkReleaseBindingError(code, detail)


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise _reject(
                "DUPLICATE_JSON_KEY",
                "release binding contains a duplicate JSON key",
            )
        value[key] = item
    return value


def _reject_float(value: str) -> object:
    raise _reject("FLOAT_FORBIDDEN", value)


def _reject_nonfinite(value: str) -> object:
    raise _reject("NONFINITE_FORBIDDEN", value)


def _require_token(value: object, *, name: str, max_bytes: int, code: str) -> str:
    if type(value) is not str or not value:
        raise _reject(code, f"{name} must be a non-empty string")
    try:
        encoded = value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise _reject(code, f"{name} must be ASCII") from exc
    if len(encoded) > max_bytes:
        raise _reject(code, f"{name} exceeds {max_bytes} bytes")
    if _TOKEN_RE.fullmatch(value) is None:
        raise _reject(code, f"{name} contains unsupported characters")
    return value


def _require_epoch(value: object, *, name: str, code: str) -> int:
    if type(value) is not int:
        raise _reject(code, f"{name} must be an integer")
    if value < 0 or value > MAX_EPOCH_ID_V1:
        raise _reject(code, f"{name} must be in the unsigned 64-bit range")
    return value


def _require_digest(value: object, *, name: str, pattern: re.Pattern[str], code: str) -> str:
    if type(value) is not str or pattern.fullmatch(value) is None:
        raise _reject(code, f"{name} has invalid canonical form")
    return value


def _parse_canonical_binding_v1(raw: bytes) -> _ParsedRecursiveStarkReleaseBinding:
    if type(raw) is not bytes:
        raise _reject("BINDING_TYPE", "release binding must be bytes")
    if len(raw) > MAX_RELEASE_BINDING_BYTES_V1:
        raise _reject(
            "BINDING_BYTE_LIMIT",
            f"release binding exceeds {MAX_RELEASE_BINDING_BYTES_V1} bytes",
        )
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise _reject("ASCII_REQUIRED", "release binding bytes must be ASCII") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_nonfinite,
        )
    except RecursiveStarkReleaseBindingError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject("INVALID_JSON", "release binding must contain bounded JSON") from exc
    if not isinstance(value, dict):
        raise _reject("OBJECT_REQUIRED", "release binding must be a JSON object")

    observed_fields = frozenset(value)
    if observed_fields != _FIELDS_V1:
        missing = sorted(_FIELDS_V1 - observed_fields)
        unknown = sorted(observed_fields - _FIELDS_V1)
        raise _reject(
            "FIELD_SET_MISMATCH",
            f"missing={missing};unknown={unknown}",
        )
    if value.get("schema") != RECURSIVE_STARK_RELEASE_BINDING_SCHEMA_V1:
        raise _reject("SCHEMA_MISMATCH", "release binding schema is unsupported")

    parsed = _ParsedRecursiveStarkReleaseBinding(
        schema=RECURSIVE_STARK_RELEASE_BINDING_SCHEMA_V1,
        chain_id=_require_token(
            value.get("chain_id"),
            name="chain_id",
            max_bytes=MAX_CHAIN_ID_BYTES_V1,
            code="CHAIN_ID_INVALID",
        ),
        epoch_id=_require_epoch(
            value.get("epoch_id"),
            name="epoch_id",
            code="EPOCH_ID_INVALID",
        ),
        proof_profile=_require_token(
            value.get("proof_profile"),
            name="proof_profile",
            max_bytes=MAX_PROOF_PROFILE_BYTES_V1,
            code="PROOF_PROFILE_INVALID",
        ),
        authority_manifest_sha256=_require_digest(
            value.get("authority_manifest_sha256"),
            name="authority_manifest_sha256",
            pattern=_BARE_SHA256_RE,
            code="AUTHORITY_MANIFEST_SHA256_INVALID",
        ),
        replay_manifest_sha256=_require_digest(
            value.get("replay_manifest_sha256"),
            name="replay_manifest_sha256",
            pattern=_SHA256_REF_RE,
            code="REPLAY_MANIFEST_SHA256_INVALID",
        ),
    )
    if canonical_json_bytes(value) != raw:
        raise _reject("NONCANONICAL_JSON", "release binding bytes are not canonical JSON")
    return parsed


def _config_digest_from_canonical_bytes_v1(raw: bytes) -> str:
    return "0x" + hashlib.sha256(_CONFIG_DIGEST_DOMAIN_V1 + encode_bytes(raw)).hexdigest()


def recursive_stark_release_binding_config_digest_v1(raw: bytes) -> str:
    """Return the domain-separated config digest for one canonical v1 record."""

    _parse_canonical_binding_v1(raw)
    return _config_digest_from_canonical_bytes_v1(raw)


def load_recursive_stark_release_binding_v1(
    raw: bytes,
    *,
    expected_config_digest: str,
    expected_chain_id: str,
    expected_epoch_id: int,
    expected_proof_profile: str,
) -> TrustedRecursiveStarkReleaseBinding:
    """Load a trusted binding after digest and exact-scope verification.

    The expected values are bootstrap inputs owned by the future ledger or
    governance integration. This function performs no I/O and emits no partial
    value when any validation fails.
    """

    trusted_digest = _require_digest(
        expected_config_digest,
        name="expected_config_digest",
        pattern=_CONFIG_DIGEST_RE,
        code="EXPECTED_CONFIG_DIGEST_INVALID",
    )
    trusted_chain_id = _require_token(
        expected_chain_id,
        name="expected_chain_id",
        max_bytes=MAX_CHAIN_ID_BYTES_V1,
        code="EXPECTED_CHAIN_ID_INVALID",
    )
    trusted_epoch_id = _require_epoch(
        expected_epoch_id,
        name="expected_epoch_id",
        code="EXPECTED_EPOCH_ID_INVALID",
    )
    trusted_proof_profile = _require_token(
        expected_proof_profile,
        name="expected_proof_profile",
        max_bytes=MAX_PROOF_PROFILE_BYTES_V1,
        code="EXPECTED_PROOF_PROFILE_INVALID",
    )

    parsed = _parse_canonical_binding_v1(raw)
    actual_digest = _config_digest_from_canonical_bytes_v1(raw)
    if not hmac.compare_digest(actual_digest, trusted_digest):
        raise _reject("CONFIG_DIGEST_MISMATCH", "release binding config digest mismatch")
    if parsed.chain_id != trusted_chain_id:
        raise _reject("CHAIN_ID_MISMATCH", "release binding chain_id mismatch")
    if parsed.epoch_id != trusted_epoch_id:
        raise _reject("EPOCH_ID_MISMATCH", "release binding epoch_id mismatch")
    if parsed.proof_profile != trusted_proof_profile:
        raise _reject("PROOF_PROFILE_MISMATCH", "release binding proof_profile mismatch")

    binding = object.__new__(TrustedRecursiveStarkReleaseBinding)
    object.__setattr__(binding, "schema", parsed.schema)
    object.__setattr__(binding, "chain_id", parsed.chain_id)
    object.__setattr__(binding, "epoch_id", parsed.epoch_id)
    object.__setattr__(binding, "proof_profile", parsed.proof_profile)
    object.__setattr__(
        binding,
        "authority_manifest_sha256",
        parsed.authority_manifest_sha256,
    )
    object.__setattr__(binding, "replay_manifest_sha256", parsed.replay_manifest_sha256)
    return binding
