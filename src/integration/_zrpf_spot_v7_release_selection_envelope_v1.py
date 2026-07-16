"""Canonical authority-neutral Spot V7 release-selection envelope V1.

The envelope is the exact statement signed by the release-selection quorum.
Parsing proves canonical bytes and field validity only.  Signature authority,
registry trust, release selection, and durable activation belong to later
boundaries.
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

SPOT_V7_RELEASE_SELECTION_ENVELOPE_SCHEMA_V1: Final = (
    "zenodex.zrpf.spot_v7.release_selection_envelope.v1"
)
SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1: Final = "zrpf_spot_v7_release_selection"
SPOT_V7_RELEASE_SELECTION_REVOCATION_STATE_V1: Final = "candidate_not_revoked"
MAX_SPOT_V7_RELEASE_SELECTION_ENVELOPE_BYTES_V1: Final = 16 * 1_024
MAX_SPOT_V7_RELEASE_SELECTION_ENVELOPE_DEPTH_V1: Final = 4
MAX_U64_V1: Final = (1 << 64) - 1

_PAYLOAD_HASH_DOMAIN_V1: Final = domain_sep_bytes(
    "zrpf_spot_v7_release_selection_envelope_payload",
    version=1,
)
_ROOT_RE: Final = re.compile(r"^0x[0-9a-f]{64}$")
_TOKEN_RE: Final = re.compile(r"^[A-Za-z0-9._:-]{1,128}$")
_TOP_FIELDS_V1: Final = frozenset({"schema", "scope", "selection", "signer_registry"})
_SCOPE_FIELDS_V1: Final = frozenset({"application_id", "chain_id", "domain_id", "release_profile"})
_SELECTION_FIELDS_V1: Final = frozenset(
    {
        "candidate_id",
        "candidate_revocation_state",
        "candidate_sha256",
        "evaluation_epoch",
        "expected_current_candidate_id",
        "expected_current_select_input_id",
        "expected_database_revision",
        "minimum_rollback_revision",
        "release_revision",
        "revocation_policy_root",
        "revocation_registry_root",
        "rollback_policy_root",
        "selector_input_id",
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


class SpotV7ReleaseSelectionEnvelopeRejectV1(ValueError):
    """Stable fail-closed error at the canonical selection-envelope boundary."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def _reject(code: str, detail: str) -> SpotV7ReleaseSelectionEnvelopeRejectV1:
    return SpotV7ReleaseSelectionEnvelopeRejectV1(code, detail)


@final
@dataclass(frozen=True, slots=True)
class SpotV7ReleaseSelectionEnvelopeV1:
    """Parsed canonical statement carrying no authentication or authority."""

    canonical_bytes: bytes
    selector_input_id: bytes
    candidate_id: bytes
    candidate_sha256: bytes
    release_revision: int
    evaluation_epoch: int
    expected_database_revision: int
    expected_current_candidate_id: bytes | None
    expected_current_select_input_id: bytes | None
    minimum_rollback_revision: int
    rollback_policy_root: bytes
    revocation_policy_root: bytes
    revocation_registry_root: bytes
    candidate_revocation_state: str
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
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def recompose_spot_v7_release_selection_envelope_v1(
    *,
    selector_input_id: bytes,
    candidate_id: bytes,
    candidate_sha256: bytes,
    release_revision: int,
    evaluation_epoch: int,
    expected_database_revision: int,
    expected_current_candidate_id: bytes | None,
    expected_current_select_input_id: bytes | None,
    minimum_rollback_revision: int,
    rollback_policy_root: bytes,
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
    """Build the only accepted byte representation of one signed statement."""

    expected_candidate = _optional_root_from_bytes(
        expected_current_candidate_id,
        name="expected_current_candidate_id",
    )
    expected_input = _optional_root_from_bytes(
        expected_current_select_input_id,
        name="expected_current_select_input_id",
    )
    if (expected_candidate is None) != (expected_input is None):
        raise _reject(
            "CURRENT_SELECTION_PAIR_REQUIRED",
            "current candidate and selector identities must be both present or both absent",
        )
    document: dict[str, object] = {
        "schema": SPOT_V7_RELEASE_SELECTION_ENVELOPE_SCHEMA_V1,
        "scope": {
            "application_id": _require_token(application_id, name="application_id"),
            "chain_id": _require_token(chain_id, name="chain_id"),
            "domain_id": _require_token(domain_id, name="domain_id"),
            "release_profile": _require_token(release_profile, name="release_profile"),
        },
        "selection": {
            "candidate_id": _root_from_bytes(candidate_id, name="candidate_id"),
            "candidate_revocation_state": (SPOT_V7_RELEASE_SELECTION_REVOCATION_STATE_V1),
            "candidate_sha256": _root_from_bytes(
                candidate_sha256,
                name="candidate_sha256",
            ),
            "evaluation_epoch": _require_u64(
                evaluation_epoch,
                name="evaluation_epoch",
            ),
            "expected_current_candidate_id": expected_candidate,
            "expected_current_select_input_id": expected_input,
            "expected_database_revision": _require_u64(
                expected_database_revision,
                name="expected_database_revision",
            ),
            "minimum_rollback_revision": _require_u64(
                minimum_rollback_revision,
                name="minimum_rollback_revision",
            ),
            "release_revision": _require_positive_u64(
                release_revision,
                name="release_revision",
            ),
            "revocation_policy_root": _root_from_bytes(
                revocation_policy_root,
                name="revocation_policy_root",
            ),
            "revocation_registry_root": _root_from_bytes(
                revocation_registry_root,
                name="revocation_registry_root",
            ),
            "rollback_policy_root": _root_from_bytes(
                rollback_policy_root,
                name="rollback_policy_root",
            ),
            "selector_input_id": _root_from_bytes(
                selector_input_id,
                name="selector_input_id",
            ),
        },
        "signer_registry": {
            "activation_epoch": _require_u64(
                signer_registry_activation_epoch,
                name="signer_registry_activation_epoch",
            ),
            "payload_kind": SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
            "quorum_threshold": _require_positive_u64(
                quorum_threshold,
                name="quorum_threshold",
            ),
            "registry_hash": _require_root(
                signer_registry_hash,
                name="signer_registry_hash",
            ),
            "registry_id": _require_token(
                signer_registry_id,
                name="signer_registry_id",
            ),
            "registry_revision": _require_positive_u64(
                signer_registry_revision,
                name="signer_registry_revision",
            ),
            "revocation_epoch": _require_optional_u64(
                signer_registry_revocation_epoch,
                name="signer_registry_revocation_epoch",
            ),
            "signature_algorithm": (SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0),
        },
    }
    raw = canonical_json_bytes(document)
    parse_exact_spot_v7_release_selection_envelope_v1(raw)
    return raw


def parse_exact_spot_v7_release_selection_envelope_v1(
    raw: bytes,
) -> SpotV7ReleaseSelectionEnvelopeV1:
    """Decode exact bytes, reject ambiguity, and return authority-neutral facts."""

    document = _decode_exact_document(raw)
    scope = _require_exact_fields(
        document["scope"],
        expected=_SCOPE_FIELDS_V1,
        name="scope",
    )
    selection = _require_exact_fields(
        document["selection"],
        expected=_SELECTION_FIELDS_V1,
        name="selection",
    )
    registry = _require_exact_fields(
        document["signer_registry"],
        expected=_REGISTRY_FIELDS_V1,
        name="signer_registry",
    )
    expected_candidate = _optional_root_to_bytes(
        selection["expected_current_candidate_id"],
        name="expected_current_candidate_id",
    )
    expected_input = _optional_root_to_bytes(
        selection["expected_current_select_input_id"],
        name="expected_current_select_input_id",
    )
    if (expected_candidate is None) != (expected_input is None):
        raise _reject(
            "CURRENT_SELECTION_PAIR_REQUIRED",
            "current candidate and selector identities must be both present or both absent",
        )
    revocation_epoch = _require_optional_u64(
        registry["revocation_epoch"],
        name="signer_registry_revocation_epoch",
    )
    activation_epoch = _require_u64(
        registry["activation_epoch"],
        name="signer_registry_activation_epoch",
    )
    if revocation_epoch is not None and revocation_epoch <= activation_epoch:
        raise _reject(
            "REGISTRY_LIFECYCLE_INVALID",
            "registry revocation must follow activation",
        )
    if selection["candidate_revocation_state"] != (SPOT_V7_RELEASE_SELECTION_REVOCATION_STATE_V1):
        raise _reject(
            "CANDIDATE_REVOCATION_STATE_INVALID",
            "only an explicitly not-revoked candidate may be selected",
        )
    if registry["payload_kind"] != SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1:
        raise _reject("PAYLOAD_KIND_MISMATCH", "release-selection payload kind required")
    if registry["signature_algorithm"] != (SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0):
        raise _reject("SIGNATURE_ALGORITHM_MISMATCH", "BLS basic signatures required")
    return SpotV7ReleaseSelectionEnvelopeV1(
        canonical_bytes=raw,
        selector_input_id=_root_to_bytes(
            selection["selector_input_id"],
            name="selector_input_id",
        ),
        candidate_id=_root_to_bytes(selection["candidate_id"], name="candidate_id"),
        candidate_sha256=_root_to_bytes(
            selection["candidate_sha256"],
            name="candidate_sha256",
        ),
        release_revision=_require_positive_u64(
            selection["release_revision"],
            name="release_revision",
        ),
        evaluation_epoch=_require_u64(
            selection["evaluation_epoch"],
            name="evaluation_epoch",
        ),
        expected_database_revision=_require_u64(
            selection["expected_database_revision"],
            name="expected_database_revision",
        ),
        expected_current_candidate_id=expected_candidate,
        expected_current_select_input_id=expected_input,
        minimum_rollback_revision=_require_u64(
            selection["minimum_rollback_revision"],
            name="minimum_rollback_revision",
        ),
        rollback_policy_root=_root_to_bytes(
            selection["rollback_policy_root"],
            name="rollback_policy_root",
        ),
        revocation_policy_root=_root_to_bytes(
            selection["revocation_policy_root"],
            name="revocation_policy_root",
        ),
        revocation_registry_root=_root_to_bytes(
            selection["revocation_registry_root"],
            name="revocation_registry_root",
        ),
        candidate_revocation_state=SPOT_V7_RELEASE_SELECTION_REVOCATION_STATE_V1,
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
        signer_registry_revocation_epoch=revocation_epoch,
        quorum_threshold=_require_positive_u64(
            registry["quorum_threshold"],
            name="quorum_threshold",
        ),
    )


def spot_v7_release_selection_envelope_payload_hash_v1(raw: bytes) -> str:
    """Return the domain-separated hash signed by the release-selection quorum."""

    parse_exact_spot_v7_release_selection_envelope_v1(raw)
    return "0x" + hashlib.sha256(_PAYLOAD_HASH_DOMAIN_V1 + encode_bytes(raw)).hexdigest()


def _decode_exact_document(raw: bytes) -> dict[str, object]:
    if type(raw) is not bytes:
        raise _reject("ENVELOPE_TYPE", "release-selection envelope must be exact bytes")
    if not raw or len(raw) > MAX_SPOT_V7_RELEASE_SELECTION_ENVELOPE_BYTES_V1:
        raise _reject("ENVELOPE_SIZE", "release-selection envelope is empty or oversized")
    _require_bounded_json_depth(raw)
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise _reject("ASCII_REQUIRED", "release-selection envelope must be ASCII") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_nonfinite,
        )
    except SpotV7ReleaseSelectionEnvelopeRejectV1:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject("INVALID_JSON", "release-selection envelope is invalid JSON") from exc
    document = _require_exact_fields(value, expected=_TOP_FIELDS_V1, name="envelope")
    if document["schema"] != SPOT_V7_RELEASE_SELECTION_ENVELOPE_SCHEMA_V1:
        raise _reject("SCHEMA_MISMATCH", "release-selection envelope schema is unsupported")
    if canonical_json_bytes(document) != raw:
        raise _reject("NONCANONICAL_JSON", "release-selection envelope is not canonical JSON")
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
            if depth > MAX_SPOT_V7_RELEASE_SELECTION_ENVELOPE_DEPTH_V1:
                raise _reject("JSON_DEPTH", "release-selection envelope is too deeply nested")
        elif byte in {0x5D, 0x7D}:
            depth -= 1
            if depth < 0:
                raise _reject("INVALID_JSON", "release-selection envelope has invalid framing")
    if depth != 0 or in_string or escaped:
        raise _reject("INVALID_JSON", "release-selection envelope has invalid framing")


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
            raise _reject("DUPLICATE_JSON_KEY", "release-selection envelope has a duplicate key")
        output[key] = value
    return output


def _reject_float(value: str) -> NoReturn:
    raise _reject("FLOAT_FORBIDDEN", value)


def _reject_nonfinite(value: str) -> NoReturn:
    raise _reject("NONFINITE_FORBIDDEN", value)


__all__ = [
    "MAX_SPOT_V7_RELEASE_SELECTION_ENVELOPE_BYTES_V1",
    "SPOT_V7_RELEASE_SELECTION_ENVELOPE_SCHEMA_V1",
    "SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1",
    "SPOT_V7_RELEASE_SELECTION_REVOCATION_STATE_V1",
    "SpotV7ReleaseSelectionEnvelopeRejectV1",
    "SpotV7ReleaseSelectionEnvelopeV1",
    "parse_exact_spot_v7_release_selection_envelope_v1",
    "recompose_spot_v7_release_selection_envelope_v1",
    "spot_v7_release_selection_envelope_payload_hash_v1",
]
