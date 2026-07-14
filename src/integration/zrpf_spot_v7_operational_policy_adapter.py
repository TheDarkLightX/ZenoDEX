"""Release-bound Spot V7 operational policy adapter.

This module converts one exact canonical policy manifest into the private Spot V7
operational-policy capability only after the manifest matches independently
supplied release and scope anchors. Proofs, receipts, DA certificates, finality
evidence, reports, and caller verdict booleans have no input channel here.

The returned binding establishes deterministic policy-byte identity and scope
binding only. It does not authenticate the origin of the expected anchors,
verify a proof, establish retrievability or external finality, authorize a
settlement, or enable production authority.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import re
from dataclasses import dataclass
from typing import NoReturn, Self, final

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    _GovernedOperationalPolicyMaterialV2,
    _GovernedSpotV7OperationalPolicyV2,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, encode_bytes

SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V1 = (
    "zenodex/zrpf_spot_v7_operational_policy_manifest/v1"
)
MAX_SPOT_V7_OPERATIONAL_POLICY_MANIFEST_BYTES_V1 = 16 * 1024
MAX_U64 = (1 << 64) - 1
MAX_FULL_BLOB_BYTES_V1 = 8 * 1024 * 1024

_MANIFEST_DIGEST_DOMAIN_V1 = domain_sep_bytes(
    "zrpf_spot_v7_operational_policy_manifest",
    version=1,
)
_HASH_RE = re.compile(r"^0x[0-9a-f]{64}$")
_BARE_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_FIELDS_V1 = frozenset(
    {
        "schema",
        "application_id",
        "chain_or_domain_id",
        "data_schema_id",
        "storage_policy_hash",
        "minimum_retention_epochs",
        "minimum_remaining_epochs",
        "maximum_blob_bytes",
        "finality_network_id",
        "finality_protocol_id",
        "external_finality_policy_hash",
        "finality_verifier_set_root",
        "genesis_application_checkpoint_sequence",
        "genesis_application_checkpoint_hash",
        "valid_from_epoch",
        "valid_through_epoch",
        "authority_manifest_sha256",
        "release_binding_config_digest",
    }
)


class SpotV7OperationalPolicyBindingError(ValueError):
    """Stable fail-closed error at the governed operational-policy boundary."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


@dataclass(frozen=True, slots=True)
class _ParsedOperationalPolicyManifestV1:
    application_id: str
    chain_or_domain_id: str
    data_schema_id: str
    storage_policy_hash: str
    minimum_retention_epochs: int
    minimum_remaining_epochs: int
    maximum_blob_bytes: int
    finality_network_id: str
    finality_protocol_id: str
    external_finality_policy_hash: str
    finality_verifier_set_root: str
    genesis_application_checkpoint_sequence: int
    genesis_application_checkpoint_hash: str
    valid_from_epoch: int
    valid_through_epoch: int
    authority_manifest_sha256: str
    release_binding_config_digest: str


@final
@dataclass(frozen=True, init=False, slots=True)
class TrustedSpotV7OperationalPolicyBindingV1:
    """Nominal release-bound policy value consumed by the operational adapter.

    Possession of this Python object is not a same-interpreter security boundary.
    The consuming path must obtain it from :func:`load_spot_v7_operational_policy_v1`
    with independently governed expected anchors.
    """

    manifest_digest: str
    authority_manifest_sha256: str
    release_binding_config_digest: str
    valid_from_epoch: int
    valid_through_epoch: int
    _capability: _GovernedSpotV7OperationalPolicyV2

    def __new__(cls) -> Self:
        raise TypeError("trusted Spot V7 operational policies must be created by the loader")

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("trusted Spot V7 operational policies cannot be subclassed")

    def __reduce__(self) -> NoReturn:
        raise TypeError("trusted Spot V7 operational policies cannot be serialized")

    def __reduce_ex__(self, _protocol: object) -> NoReturn:
        raise TypeError("trusted Spot V7 operational policies cannot be serialized")

    def _capability_for_operational_gate(self) -> _GovernedSpotV7OperationalPolicyV2:
        capability = self._capability
        if type(capability) is not _GovernedSpotV7OperationalPolicyV2:
            raise TypeError("trusted operational policy lost its exact capability type")
        if not capability._has_private_seal():
            raise TypeError("trusted operational policy lost its private governed seal")
        capability._policy_for_atomic_store()
        return capability



def spot_v7_operational_policy_manifest_digest_v1(raw: bytes) -> str:
    """Return the domain-separated digest of one exact canonical manifest."""

    _parse_manifest_v1(raw)
    return _manifest_digest_v1(raw)



def load_spot_v7_operational_policy_v1(
    raw: bytes,
    *,
    expected_manifest_digest: str,
    expected_application_id: str,
    expected_chain_or_domain_id: str,
    expected_authority_manifest_sha256: str,
    expected_release_binding_config_digest: str,
    current_epoch: int,
) -> TrustedSpotV7OperationalPolicyBindingV1:
    """Validate exact policy bytes and mint the private policy capability.

    Every ``expected_*`` value and ``current_epoch`` is a bootstrap input owned by
    the future release/ledger boundary. A proof, receipt, report, or supplied
    success boolean cannot replace any expected value.
    """

    trusted_manifest_digest = _require_hash(
        expected_manifest_digest,
        name="expected_manifest_digest",
        code="EXPECTED_MANIFEST_DIGEST_INVALID",
    )
    trusted_application_id = _require_hash(
        expected_application_id,
        name="expected_application_id",
        code="EXPECTED_APPLICATION_ID_INVALID",
    )
    trusted_domain_id = _require_hash(
        expected_chain_or_domain_id,
        name="expected_chain_or_domain_id",
        code="EXPECTED_DOMAIN_ID_INVALID",
    )
    trusted_authority_manifest = _require_bare_sha256(
        expected_authority_manifest_sha256,
        name="expected_authority_manifest_sha256",
        code="EXPECTED_AUTHORITY_MANIFEST_INVALID",
    )
    trusted_release_binding = _require_hash(
        expected_release_binding_config_digest,
        name="expected_release_binding_config_digest",
        code="EXPECTED_RELEASE_BINDING_INVALID",
    )
    trusted_epoch = _require_u64(
        current_epoch,
        name="current_epoch",
        code="CURRENT_EPOCH_INVALID",
    )

    parsed = _parse_manifest_v1(raw)
    actual_manifest_digest = _manifest_digest_v1(raw)
    if not hmac.compare_digest(actual_manifest_digest, trusted_manifest_digest):
        raise _reject("MANIFEST_DIGEST_MISMATCH", "operational policy digest mismatch")
    if parsed.application_id != trusted_application_id:
        raise _reject("APPLICATION_ID_MISMATCH", "operational policy application mismatch")
    if parsed.chain_or_domain_id != trusted_domain_id:
        raise _reject("DOMAIN_ID_MISMATCH", "operational policy domain mismatch")
    if not hmac.compare_digest(parsed.authority_manifest_sha256, trusted_authority_manifest):
        raise _reject(
            "AUTHORITY_MANIFEST_MISMATCH",
            "operational policy authority manifest mismatch",
        )
    if not hmac.compare_digest(parsed.release_binding_config_digest, trusted_release_binding):
        raise _reject(
            "RELEASE_BINDING_MISMATCH",
            "operational policy release binding mismatch",
        )
    if trusted_epoch < parsed.valid_from_epoch or trusted_epoch > parsed.valid_through_epoch:
        raise _reject("POLICY_NOT_CURRENT", "operational policy is outside its validity range")

    material = _GovernedOperationalPolicyMaterialV2(
        application_id=parsed.application_id,
        chain_or_domain_id=parsed.chain_or_domain_id,
        data_schema_id=parsed.data_schema_id,
        storage_policy_hash=parsed.storage_policy_hash,
        minimum_retention_epochs=parsed.minimum_retention_epochs,
        minimum_remaining_epochs=parsed.minimum_remaining_epochs,
        maximum_blob_bytes=parsed.maximum_blob_bytes,
        finality_network_id=parsed.finality_network_id,
        finality_protocol_id=parsed.finality_protocol_id,
        external_finality_policy_hash=parsed.external_finality_policy_hash,
        finality_verifier_set_root=parsed.finality_verifier_set_root,
        genesis_application_checkpoint_sequence=(
            parsed.genesis_application_checkpoint_sequence
        ),
        genesis_application_checkpoint_hash=parsed.genesis_application_checkpoint_hash,
    )
    capability = _GovernedSpotV7OperationalPolicyV2(
        material,
        seal=_GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    )
    binding = object.__new__(TrustedSpotV7OperationalPolicyBindingV1)
    object.__setattr__(binding, "manifest_digest", actual_manifest_digest)
    object.__setattr__(
        binding,
        "authority_manifest_sha256",
        parsed.authority_manifest_sha256,
    )
    object.__setattr__(
        binding,
        "release_binding_config_digest",
        parsed.release_binding_config_digest,
    )
    object.__setattr__(binding, "valid_from_epoch", parsed.valid_from_epoch)
    object.__setattr__(binding, "valid_through_epoch", parsed.valid_through_epoch)
    object.__setattr__(binding, "_capability", capability)
    return binding



def _parse_manifest_v1(raw: bytes) -> _ParsedOperationalPolicyManifestV1:
    if type(raw) is not bytes:
        raise _reject("MANIFEST_TYPE", "operational policy manifest must be bytes")
    if not raw or len(raw) > MAX_SPOT_V7_OPERATIONAL_POLICY_MANIFEST_BYTES_V1:
        raise _reject(
            "MANIFEST_BYTE_LIMIT",
            "operational policy manifest is empty or exceeds the byte limit",
        )
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise _reject("ASCII_REQUIRED", "operational policy manifest must be ASCII") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_nonfinite,
        )
    except SpotV7OperationalPolicyBindingError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject("INVALID_JSON", "operational policy manifest must be bounded JSON") from exc
    if type(value) is not dict:
        raise _reject("OBJECT_REQUIRED", "operational policy manifest must be an object")
    observed = frozenset(value)
    if observed != _FIELDS_V1:
        raise _reject(
            "FIELD_SET_MISMATCH",
            f"missing={sorted(_FIELDS_V1 - observed)};unknown={sorted(observed - _FIELDS_V1)}",
        )
    if value.get("schema") != SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V1:
        raise _reject("SCHEMA_MISMATCH", "operational policy schema is unsupported")

    valid_from = _require_u64(
        value.get("valid_from_epoch"),
        name="valid_from_epoch",
        code="VALID_FROM_EPOCH_INVALID",
    )
    valid_through = _require_u64(
        value.get("valid_through_epoch"),
        name="valid_through_epoch",
        code="VALID_THROUGH_EPOCH_INVALID",
    )
    if valid_from > valid_through:
        raise _reject("VALIDITY_RANGE_INVALID", "policy validity range is reversed")

    maximum_blob_bytes = _require_u64(
        value.get("maximum_blob_bytes"),
        name="maximum_blob_bytes",
        code="MAXIMUM_BLOB_BYTES_INVALID",
    )
    if maximum_blob_bytes == 0 or maximum_blob_bytes > MAX_FULL_BLOB_BYTES_V1:
        raise _reject(
            "MAXIMUM_BLOB_BYTES_INVALID",
            f"maximum_blob_bytes must be in 1..={MAX_FULL_BLOB_BYTES_V1}",
        )

    parsed = _ParsedOperationalPolicyManifestV1(
        application_id=_require_hash(
            value.get("application_id"),
            name="application_id",
            code="APPLICATION_ID_INVALID",
        ),
        chain_or_domain_id=_require_hash(
            value.get("chain_or_domain_id"),
            name="chain_or_domain_id",
            code="DOMAIN_ID_INVALID",
        ),
        data_schema_id=_require_hash(
            value.get("data_schema_id"),
            name="data_schema_id",
            code="DATA_SCHEMA_ID_INVALID",
        ),
        storage_policy_hash=_require_hash(
            value.get("storage_policy_hash"),
            name="storage_policy_hash",
            code="STORAGE_POLICY_HASH_INVALID",
        ),
        minimum_retention_epochs=_require_u64(
            value.get("minimum_retention_epochs"),
            name="minimum_retention_epochs",
            code="MINIMUM_RETENTION_EPOCHS_INVALID",
        ),
        minimum_remaining_epochs=_require_u64(
            value.get("minimum_remaining_epochs"),
            name="minimum_remaining_epochs",
            code="MINIMUM_REMAINING_EPOCHS_INVALID",
        ),
        maximum_blob_bytes=maximum_blob_bytes,
        finality_network_id=_require_hash(
            value.get("finality_network_id"),
            name="finality_network_id",
            code="FINALITY_NETWORK_ID_INVALID",
        ),
        finality_protocol_id=_require_hash(
            value.get("finality_protocol_id"),
            name="finality_protocol_id",
            code="FINALITY_PROTOCOL_ID_INVALID",
        ),
        external_finality_policy_hash=_require_hash(
            value.get("external_finality_policy_hash"),
            name="external_finality_policy_hash",
            code="EXTERNAL_FINALITY_POLICY_HASH_INVALID",
        ),
        finality_verifier_set_root=_require_hash(
            value.get("finality_verifier_set_root"),
            name="finality_verifier_set_root",
            code="FINALITY_VERIFIER_SET_ROOT_INVALID",
        ),
        genesis_application_checkpoint_sequence=_require_u64(
            value.get("genesis_application_checkpoint_sequence"),
            name="genesis_application_checkpoint_sequence",
            code="GENESIS_CHECKPOINT_SEQUENCE_INVALID",
        ),
        genesis_application_checkpoint_hash=_require_hash(
            value.get("genesis_application_checkpoint_hash"),
            name="genesis_application_checkpoint_hash",
            code="GENESIS_CHECKPOINT_HASH_INVALID",
        ),
        valid_from_epoch=valid_from,
        valid_through_epoch=valid_through,
        authority_manifest_sha256=_require_bare_sha256(
            value.get("authority_manifest_sha256"),
            name="authority_manifest_sha256",
            code="AUTHORITY_MANIFEST_SHA256_INVALID",
        ),
        release_binding_config_digest=_require_hash(
            value.get("release_binding_config_digest"),
            name="release_binding_config_digest",
            code="RELEASE_BINDING_CONFIG_DIGEST_INVALID",
        ),
    )
    if canonical_json_bytes(value) != raw:
        raise _reject("NONCANONICAL_JSON", "operational policy bytes are not canonical JSON")
    return parsed



def _manifest_digest_v1(raw: bytes) -> str:
    return "0x" + hashlib.sha256(_MANIFEST_DIGEST_DOMAIN_V1 + encode_bytes(raw)).hexdigest()



def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise _reject("DUPLICATE_JSON_KEY", "manifest contains a duplicate JSON key")
        value[key] = item
    return value



def _reject_float(value: str) -> object:
    raise _reject("FLOAT_FORBIDDEN", value)



def _reject_nonfinite(value: str) -> object:
    raise _reject("NONFINITE_FORBIDDEN", value)



def _require_hash(value: object, *, name: str, code: str) -> str:
    if type(value) is not str or _HASH_RE.fullmatch(value) is None or value == "0x" + "00" * 32:
        raise _reject(code, f"{name} must be nonzero canonical lowercase 0x-prefixed SHA-256")
    return value



def _require_bare_sha256(value: object, *, name: str, code: str) -> str:
    if type(value) is not str or _BARE_SHA256_RE.fullmatch(value) is None:
        raise _reject(code, f"{name} must be lowercase 64-character hex")
    return value



def _require_u64(value: object, *, name: str, code: str) -> int:
    if type(value) is not int or value < 0 or value > MAX_U64:
        raise _reject(code, f"{name} must be an unsigned 64-bit integer")
    return value



def _reject(code: str, detail: str) -> SpotV7OperationalPolicyBindingError:
    return SpotV7OperationalPolicyBindingError(code, detail)


__all__ = [
    "MAX_SPOT_V7_OPERATIONAL_POLICY_MANIFEST_BYTES_V1",
    "SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V1",
    "SpotV7OperationalPolicyBindingError",
    "TrustedSpotV7OperationalPolicyBindingV1",
    "load_spot_v7_operational_policy_v1",
    "spot_v7_operational_policy_manifest_digest_v1",
]
