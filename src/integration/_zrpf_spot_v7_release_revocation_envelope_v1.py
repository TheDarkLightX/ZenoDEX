"""Canonical authority-neutral Spot V7 release-revocation envelope V1.

The envelope is the exact statement signed by a revocation quorum. Parsing
establishes canonical bytes and field validity only. Registry governance,
durable replay prevention, revocation authority, and runtime authority belong
to later boundaries.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from typing import Final, NoReturn, final

from src.integration.zeno_ledger_signature import (
    SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, encode_bytes

SPOT_V7_RELEASE_REVOCATION_ENVELOPE_SCHEMA_V1: Final = (
    "zenodex.zrpf.spot_v7.release_revocation_envelope.v1"
)
SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1: Final = "zrpf_spot_v7_release_revocation"
SPOT_V7_RELEASE_REVOCATION_PRIOR_STATE_V1: Final = "current_not_previously_revoked"
MAX_SPOT_V7_RELEASE_REVOCATION_ENVELOPE_BYTES_V1: Final = 24 * 1_024
MAX_SPOT_V7_RELEASE_REVOCATION_ENVELOPE_DEPTH_V1: Final = 4
MAX_U64_V1: Final = (1 << 64) - 1
MAX_U32_V1: Final = (1 << 32) - 1

_PAYLOAD_HASH_DOMAIN_V1: Final = domain_sep_bytes(
    "zrpf_spot_v7_release_revocation_envelope_payload",
    version=1,
)
_ROOT_RE: Final = re.compile(r"^0x[0-9a-f]{64}$")
_TOKEN_RE: Final = re.compile(r"^[A-Za-z0-9._:-]{1,128}$")
_TOP_FIELDS_V1: Final = frozenset(
    {"schema", "scope", "current_selection", "revocation", "signer_registry"}
)
_SCOPE_FIELDS_V1: Final = frozenset({"application_id", "chain_id", "domain_id", "release_profile"})
_CURRENT_FIELDS_V1: Final = frozenset(
    {
        "candidate_activation_epoch",
        "candidate_expiration_epoch",
        "current_candidate_id",
        "current_candidate_sha256",
        "current_parent_candidate_id",
        "current_release_revision",
        "current_select_input_id",
        "evaluation_epoch",
        "expected_database_revision",
        "last_evaluation_epoch",
        "minimum_rollback_revision",
        "revocation_selector_input_id",
        "rollback_policy_root",
    }
)
_REVOCATION_FIELDS_V1: Final = frozenset(
    {
        "effective_epoch",
        "issuer_set_root",
        "prior_state",
        "reason_code",
        "record_id",
        "record_revision",
        "record_sha256",
        "revocation_policy_root",
        "revocation_registry_root",
    }
)
_REGISTRY_FIELDS_V1: Final = frozenset(
    {
        "activation_epoch",
        "payload_kind",
        "quorum_threshold",
        "registry_hash",
        "registry_id",
        "registry_revision",
        "revocation_epoch",
        "signature_algorithm",
    }
)


class SpotV7ReleaseRevocationEnvelopeRejectV1(ValueError):
    """Stable fail-closed error at the canonical revocation-envelope boundary."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def _reject(code: str, detail: str) -> SpotV7ReleaseRevocationEnvelopeRejectV1:
    return SpotV7ReleaseRevocationEnvelopeRejectV1(code, detail)


@final
@dataclass(frozen=True, slots=True)
class SpotV7ReleaseRevocationEnvelopeV1:
    """Parsed canonical revocation statement carrying no authority."""

    canonical_bytes: bytes
    revocation_selector_input_id: bytes
    current_candidate_id: bytes
    current_candidate_sha256: bytes
    current_release_revision: int
    current_select_input_id: bytes
    expected_database_revision: int
    last_evaluation_epoch: int
    evaluation_epoch: int
    current_parent_candidate_id: bytes | None
    minimum_rollback_revision: int
    rollback_policy_root: bytes
    candidate_activation_epoch: int
    candidate_expiration_epoch: int | None
    revocation_record_id: bytes
    revocation_record_sha256: bytes
    revocation_effective_epoch: int
    revocation_record_revision: int
    revocation_reason_code: int
    revocation_issuer_set_root: bytes
    revocation_policy_root: bytes
    revocation_registry_root: bytes
    application_id: str
    chain_id: str
    domain_id: str
    release_profile: str
    signer_registry_id: str
    signer_registry_hash: str
    signer_registry_revision: int
    signer_registry_activation_epoch: int
    signer_registry_revocation_epoch: int | None
    quorum_threshold: int

    @property
    def signature_quorum_authenticated(self) -> bool:
        return False

    @property
    def revocation_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def recompose_spot_v7_release_revocation_envelope_v1(
    *,
    revocation_selector_input_id: bytes,
    current_candidate_id: bytes,
    current_candidate_sha256: bytes,
    current_release_revision: int,
    current_select_input_id: bytes,
    expected_database_revision: int,
    last_evaluation_epoch: int,
    evaluation_epoch: int,
    current_parent_candidate_id: bytes | None,
    minimum_rollback_revision: int,
    rollback_policy_root: bytes,
    candidate_activation_epoch: int,
    candidate_expiration_epoch: int | None,
    revocation_record_id: bytes,
    revocation_record_sha256: bytes,
    revocation_effective_epoch: int,
    revocation_record_revision: int,
    revocation_reason_code: int,
    revocation_issuer_set_root: bytes,
    revocation_policy_root: bytes,
    revocation_registry_root: bytes,
    application_id: str,
    chain_id: str,
    domain_id: str,
    release_profile: str,
    signer_registry_id: str,
    signer_registry_hash: str,
    signer_registry_revision: int,
    signer_registry_activation_epoch: int,
    signer_registry_revocation_epoch: int | None,
    quorum_threshold: int,
) -> bytes:
    """Build the only accepted byte representation of one signed revocation."""

    document: dict[str, object] = {
        "current_selection": {
            "candidate_activation_epoch": _require_u64(
                candidate_activation_epoch,
                name="candidate_activation_epoch",
            ),
            "candidate_expiration_epoch": _require_optional_u64(
                candidate_expiration_epoch,
                name="candidate_expiration_epoch",
            ),
            "current_candidate_id": _root_from_bytes(
                current_candidate_id,
                name="current_candidate_id",
            ),
            "current_candidate_sha256": _root_from_bytes(
                current_candidate_sha256,
                name="current_candidate_sha256",
            ),
            "current_parent_candidate_id": _optional_root_from_bytes(
                current_parent_candidate_id,
                name="current_parent_candidate_id",
            ),
            "current_release_revision": _require_positive_u64(
                current_release_revision,
                name="current_release_revision",
            ),
            "current_select_input_id": _root_from_bytes(
                current_select_input_id,
                name="current_select_input_id",
            ),
            "evaluation_epoch": _require_u64(evaluation_epoch, name="evaluation_epoch"),
            "expected_database_revision": _require_positive_u64(
                expected_database_revision,
                name="expected_database_revision",
            ),
            "last_evaluation_epoch": _require_u64(
                last_evaluation_epoch,
                name="last_evaluation_epoch",
            ),
            "minimum_rollback_revision": _require_u64(
                minimum_rollback_revision,
                name="minimum_rollback_revision",
            ),
            "revocation_selector_input_id": _root_from_bytes(
                revocation_selector_input_id,
                name="revocation_selector_input_id",
            ),
            "rollback_policy_root": _root_from_bytes(
                rollback_policy_root,
                name="rollback_policy_root",
            ),
        },
        "revocation": {
            "effective_epoch": _require_u64(
                revocation_effective_epoch,
                name="revocation_effective_epoch",
            ),
            "issuer_set_root": _root_from_bytes(
                revocation_issuer_set_root,
                name="revocation_issuer_set_root",
            ),
            "prior_state": SPOT_V7_RELEASE_REVOCATION_PRIOR_STATE_V1,
            "reason_code": _require_positive_u32(
                revocation_reason_code,
                name="revocation_reason_code",
            ),
            "record_id": _root_from_bytes(revocation_record_id, name="revocation_record_id"),
            "record_revision": _require_positive_u64(
                revocation_record_revision,
                name="revocation_record_revision",
            ),
            "record_sha256": _root_from_bytes(
                revocation_record_sha256,
                name="revocation_record_sha256",
            ),
            "revocation_policy_root": _root_from_bytes(
                revocation_policy_root,
                name="revocation_policy_root",
            ),
            "revocation_registry_root": _root_from_bytes(
                revocation_registry_root,
                name="revocation_registry_root",
            ),
        },
        "schema": SPOT_V7_RELEASE_REVOCATION_ENVELOPE_SCHEMA_V1,
        "scope": {
            "application_id": _require_token(application_id, name="application_id"),
            "chain_id": _require_token(chain_id, name="chain_id"),
            "domain_id": _require_token(domain_id, name="domain_id"),
            "release_profile": _require_token(release_profile, name="release_profile"),
        },
        "signer_registry": {
            "activation_epoch": _require_u64(
                signer_registry_activation_epoch,
                name="signer_registry_activation_epoch",
            ),
            "payload_kind": SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
            "quorum_threshold": _require_positive_u64(
                quorum_threshold,
                name="quorum_threshold",
            ),
            "registry_hash": _require_root(
                signer_registry_hash,
                name="signer_registry_hash",
            ),
            "registry_id": _require_token(signer_registry_id, name="signer_registry_id"),
            "registry_revision": _require_positive_u64(
                signer_registry_revision,
                name="signer_registry_revision",
            ),
            "revocation_epoch": _require_optional_u64(
                signer_registry_revocation_epoch,
                name="signer_registry_revocation_epoch",
            ),
            "signature_algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
        },
    }
    raw = canonical_json_bytes(document)
    parse_exact_spot_v7_release_revocation_envelope_v1(raw)
    return raw


def parse_exact_spot_v7_release_revocation_envelope_v1(
    raw: bytes,
) -> SpotV7ReleaseRevocationEnvelopeV1:
    """Decode exact bytes, reject ambiguity, and return authority-neutral facts."""

    document = _decode_exact_document(raw)
    current = _require_exact_fields(
        document["current_selection"],
        expected=_CURRENT_FIELDS_V1,
        name="current_selection",
    )
    revocation = _require_exact_fields(
        document["revocation"],
        expected=_REVOCATION_FIELDS_V1,
        name="revocation",
    )
    scope = _require_exact_fields(document["scope"], expected=_SCOPE_FIELDS_V1, name="scope")
    registry = _require_exact_fields(
        document["signer_registry"],
        expected=_REGISTRY_FIELDS_V1,
        name="signer_registry",
    )
    activation_epoch = _require_u64(
        registry["activation_epoch"],
        name="signer_registry_activation_epoch",
    )
    registry_revocation = _require_optional_u64(
        registry["revocation_epoch"],
        name="signer_registry_revocation_epoch",
    )
    if registry_revocation is not None and registry_revocation <= activation_epoch:
        raise _reject(
            "REGISTRY_LIFECYCLE_INVALID",
            "registry revocation must follow activation",
        )
    if revocation["prior_state"] != SPOT_V7_RELEASE_REVOCATION_PRIOR_STATE_V1:
        raise _reject(
            "PRIOR_REVOCATION_STATE_INVALID",
            "only a currently unrevoked candidate may be revoked",
        )
    if registry["payload_kind"] != SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1:
        raise _reject("PAYLOAD_KIND_MISMATCH", "release-revocation payload kind required")
    if registry["signature_algorithm"] != SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0:
        raise _reject("SIGNATURE_ALGORITHM_MISMATCH", "BLS basic signatures required")
    candidate_activation = _require_u64(
        current["candidate_activation_epoch"],
        name="candidate_activation_epoch",
    )
    candidate_expiration = _require_optional_u64(
        current["candidate_expiration_epoch"],
        name="candidate_expiration_epoch",
    )
    if candidate_expiration is not None and candidate_expiration <= candidate_activation:
        raise _reject(
            "CANDIDATE_LIFECYCLE_INVALID",
            "candidate expiration must follow activation",
        )
    evaluation_epoch = _require_u64(current["evaluation_epoch"], name="evaluation_epoch")
    last_evaluation_epoch = _require_u64(
        current["last_evaluation_epoch"],
        name="last_evaluation_epoch",
    )
    if evaluation_epoch < last_evaluation_epoch:
        raise _reject(
            "EVALUATION_EPOCH_ROLLBACK",
            "revocation evaluation precedes the durable current cursor",
        )
    effective_epoch = _require_u64(
        revocation["effective_epoch"],
        name="revocation_effective_epoch",
    )
    if effective_epoch > evaluation_epoch:
        raise _reject(
            "REVOCATION_EFFECTIVE_EPOCH_FUTURE",
            "revocation cannot take effect after its evaluation epoch",
        )
    return SpotV7ReleaseRevocationEnvelopeV1(
        canonical_bytes=raw,
        revocation_selector_input_id=_root_to_bytes(
            current["revocation_selector_input_id"],
            name="revocation_selector_input_id",
        ),
        current_candidate_id=_root_to_bytes(
            current["current_candidate_id"],
            name="current_candidate_id",
        ),
        current_candidate_sha256=_root_to_bytes(
            current["current_candidate_sha256"],
            name="current_candidate_sha256",
        ),
        current_release_revision=_require_positive_u64(
            current["current_release_revision"],
            name="current_release_revision",
        ),
        current_select_input_id=_root_to_bytes(
            current["current_select_input_id"],
            name="current_select_input_id",
        ),
        expected_database_revision=_require_positive_u64(
            current["expected_database_revision"],
            name="expected_database_revision",
        ),
        last_evaluation_epoch=last_evaluation_epoch,
        evaluation_epoch=evaluation_epoch,
        current_parent_candidate_id=_optional_root_to_bytes(
            current["current_parent_candidate_id"],
            name="current_parent_candidate_id",
        ),
        minimum_rollback_revision=_require_u64(
            current["minimum_rollback_revision"],
            name="minimum_rollback_revision",
        ),
        rollback_policy_root=_root_to_bytes(
            current["rollback_policy_root"],
            name="rollback_policy_root",
        ),
        candidate_activation_epoch=candidate_activation,
        candidate_expiration_epoch=candidate_expiration,
        revocation_record_id=_root_to_bytes(
            revocation["record_id"],
            name="revocation_record_id",
        ),
        revocation_record_sha256=_root_to_bytes(
            revocation["record_sha256"],
            name="revocation_record_sha256",
        ),
        revocation_effective_epoch=effective_epoch,
        revocation_record_revision=_require_positive_u64(
            revocation["record_revision"],
            name="revocation_record_revision",
        ),
        revocation_reason_code=_require_positive_u32(
            revocation["reason_code"],
            name="revocation_reason_code",
        ),
        revocation_issuer_set_root=_root_to_bytes(
            revocation["issuer_set_root"],
            name="revocation_issuer_set_root",
        ),
        revocation_policy_root=_root_to_bytes(
            revocation["revocation_policy_root"],
            name="revocation_policy_root",
        ),
        revocation_registry_root=_root_to_bytes(
            revocation["revocation_registry_root"],
            name="revocation_registry_root",
        ),
        application_id=_require_token(scope["application_id"], name="application_id"),
        chain_id=_require_token(scope["chain_id"], name="chain_id"),
        domain_id=_require_token(scope["domain_id"], name="domain_id"),
        release_profile=_require_token(scope["release_profile"], name="release_profile"),
        signer_registry_id=_require_token(
            registry["registry_id"],
            name="signer_registry_id",
        ),
        signer_registry_hash=_require_root(
            registry["registry_hash"],
            name="signer_registry_hash",
        ),
        signer_registry_revision=_require_positive_u64(
            registry["registry_revision"],
            name="signer_registry_revision",
        ),
        signer_registry_activation_epoch=activation_epoch,
        signer_registry_revocation_epoch=registry_revocation,
        quorum_threshold=_require_positive_u64(
            registry["quorum_threshold"],
            name="quorum_threshold",
        ),
    )


def spot_v7_release_revocation_envelope_payload_hash_v1(raw: bytes) -> str:
    """Return the domain-separated hash signed by the revocation quorum."""

    parse_exact_spot_v7_release_revocation_envelope_v1(raw)
    return "0x" + hashlib.sha256(_PAYLOAD_HASH_DOMAIN_V1 + encode_bytes(raw)).hexdigest()


def _decode_exact_document(raw: bytes) -> dict[str, object]:
    if type(raw) is not bytes:
        raise _reject("ENVELOPE_TYPE", "release-revocation envelope must be exact bytes")
    if not raw or len(raw) > MAX_SPOT_V7_RELEASE_REVOCATION_ENVELOPE_BYTES_V1:
        raise _reject("ENVELOPE_SIZE", "release-revocation envelope is empty or oversized")
    _require_bounded_json_depth(raw)
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise _reject("ASCII_REQUIRED", "release-revocation envelope must be ASCII") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_nonfinite,
        )
    except SpotV7ReleaseRevocationEnvelopeRejectV1:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject("INVALID_JSON", "release-revocation envelope is invalid JSON") from exc
    document = _require_exact_fields(value, expected=_TOP_FIELDS_V1, name="envelope")
    if document["schema"] != SPOT_V7_RELEASE_REVOCATION_ENVELOPE_SCHEMA_V1:
        raise _reject("SCHEMA_MISMATCH", "release-revocation envelope schema is unsupported")
    if canonical_json_bytes(document) != raw:
        raise _reject("NONCANONICAL_JSON", "release-revocation envelope is not canonical JSON")
    return document


def _require_bounded_json_depth(raw: bytes) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in {0x5B, 0x7B}:
            depth += 1
            if depth > MAX_SPOT_V7_RELEASE_REVOCATION_ENVELOPE_DEPTH_V1:
                raise _reject("JSON_DEPTH", "release-revocation envelope is too deeply nested")
        elif byte in {0x5D, 0x7D}:
            depth -= 1
            if depth < 0:
                raise _reject("INVALID_JSON", "release-revocation envelope has invalid framing")
    if depth != 0 or in_string or escaped:
        raise _reject("INVALID_JSON", "release-revocation envelope has invalid framing")


def _require_exact_fields(
    value: object,
    *,
    expected: frozenset[str],
    name: str,
) -> dict[str, object]:
    if type(value) is not dict:
        raise _reject("EXACT_OBJECT_REQUIRED", f"{name} must be an exact object")
    keys = frozenset(value)
    if keys != expected:
        raise _reject(
            "FIELD_SET_MISMATCH",
            f"{name} missing={sorted(expected - keys)} extra={sorted(keys - expected)}",
        )
    return value


def _require_u64(value: object, *, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64_V1:
        raise _reject("U64_REQUIRED", f"{name} must be a u64")
    return value


def _require_positive_u64(value: object, *, name: str) -> int:
    output = _require_u64(value, name=name)
    if output == 0:
        raise _reject("POSITIVE_U64_REQUIRED", f"{name} must be positive")
    return output


def _require_optional_u64(value: object, *, name: str) -> int | None:
    if value is None:
        return None
    return _require_u64(value, name=name)


def _require_positive_u32(value: object, *, name: str) -> int:
    if type(value) is not int or not 0 < value <= MAX_U32_V1:
        raise _reject("POSITIVE_U32_REQUIRED", f"{name} must be a positive u32")
    return value


def _require_token(value: object, *, name: str) -> str:
    if type(value) is not str or _TOKEN_RE.fullmatch(value) is None:
        raise _reject("TOKEN_REQUIRED", f"{name} must be a bounded ASCII token")
    return value


def _require_root(value: object, *, name: str) -> str:
    if type(value) is not str or _ROOT_RE.fullmatch(value) is None:
        raise _reject("ROOT_REQUIRED", f"{name} must be canonical lowercase 0x hex")
    if value == "0x" + ("00" * 32):
        raise _reject("ROOT_REQUIRED", f"{name} must be nonzero")
    return value


def _root_from_bytes(value: object, *, name: str) -> str:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise _reject("DIGEST_REQUIRED", f"{name} must be a nonzero 32-byte digest")
    return "0x" + value.hex()


def _optional_root_from_bytes(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    return _root_from_bytes(value, name=name)


def _root_to_bytes(value: object, *, name: str) -> bytes:
    return bytes.fromhex(_require_root(value, name=name)[2:])


def _optional_root_to_bytes(value: object, *, name: str) -> bytes | None:
    if value is None:
        return None
    return _root_to_bytes(value, name=name)


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    output: dict[str, object] = {}
    for key, value in pairs:
        if key in output:
            raise _reject("DUPLICATE_JSON_KEY", "release-revocation envelope has a duplicate key")
        output[key] = value
    return output


def _reject_float(value: str) -> NoReturn:
    raise _reject("FLOAT_FORBIDDEN", value)


def _reject_nonfinite(value: str) -> NoReturn:
    raise _reject("NONFINITE_FORBIDDEN", value)


__all__ = [
    "MAX_SPOT_V7_RELEASE_REVOCATION_ENVELOPE_BYTES_V1",
    "SPOT_V7_RELEASE_REVOCATION_ENVELOPE_SCHEMA_V1",
    "SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1",
    "SPOT_V7_RELEASE_REVOCATION_PRIOR_STATE_V1",
    "SpotV7ReleaseRevocationEnvelopeRejectV1",
    "SpotV7ReleaseRevocationEnvelopeV1",
    "parse_exact_spot_v7_release_revocation_envelope_v1",
    "recompose_spot_v7_release_revocation_envelope_v1",
    "spot_v7_release_revocation_envelope_payload_hash_v1",
]
