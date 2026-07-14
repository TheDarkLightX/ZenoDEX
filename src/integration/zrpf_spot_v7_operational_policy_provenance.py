"""Canonical, quorum-authenticated provenance for the Spot V7 operational policy.

The loader in this module is the production mint path for
``_GovernedSpotV7OperationalPolicyV2``. It requires an exact canonical manifest,
an exact private handoff of independently authenticated release pins and epoch,
an active policy and registry revision, and a valid BLS signature quorum over
the exact manifest bytes.

This tranche deliberately provides no production mint for that private release
handoff. A future ledger, release, or governance adapter must own it. Coherent
edits to caller manifest, registry, signature, pin, or epoch data cannot mint a
governed policy through this module. A code or trusted-configuration change
remains a separately governed operation.

Successful loading establishes scoped policy-release provenance only. The
resulting policy deliberately keeps settlement and production authority false.
Data availability, checkpoint finality, economic settlement, and the final
atomic authority join remain separate gates.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import re
from dataclasses import dataclass
from typing import Any, Mapping, NoReturn, Sequence, SupportsIndex, cast, final

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    _GovernedOperationalPolicyMaterialV2,
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration.zeno_ledger_signer_registry import verify_signature_quorum_v0
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, encode_bytes

SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V1 = (
    "zenodex.zrpf.spot_v7.operational_policy_manifest.v1"
)
SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1 = "zrpf_spot_v7_operational_policy"
MAX_SPOT_V7_OPERATIONAL_POLICY_MANIFEST_BYTES_V1 = 16 * 1024
MAX_SPOT_V7_OPERATIONAL_POLICY_SIGNERS_V1 = 64
MAX_SPOT_V7_OPERATIONAL_POLICY_SIGNATURES_V1 = 64
MAX_SPOT_V7_OPERATIONAL_POLICY_PLAIN_JSON_NODES_V1 = 4_096
MAX_SPOT_V7_OPERATIONAL_POLICY_PLAIN_JSON_UTF8_BYTES_V1 = 256 * 1024
MAX_U64 = (1 << 64) - 1

_PAYLOAD_HASH_DOMAIN_V1 = domain_sep_bytes(
    "zrpf_spot_v7_operational_policy_manifest_payload",
    version=1,
)
_BARE_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_ROOT_RE = re.compile(r"^0x[0-9a-f]{64}$")
_TOKEN_RE = re.compile(r"^[A-Za-z0-9._:-]+$")
_TOP_LEVEL_FIELDS_V1 = frozenset(
    {
        "schema",
        "policy_material",
        "policy_context",
        "signer_registry_context",
    }
)
_POLICY_MATERIAL_FIELDS_V1 = frozenset(
    {
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
    }
)
_POLICY_CONTEXT_FIELDS_V1 = frozenset(
    {
        "policy_revision",
        "activation_epoch",
        "revocation_epoch",
    }
)
_REGISTRY_CONTEXT_FIELDS_V1 = frozenset(
    {
        "registry_id",
        "registry_hash",
        "registry_revision",
        "activation_epoch",
        "revocation_epoch",
    }
)


class SpotV7OperationalPolicyProvenanceErrorV1(ValueError):
    """Stable fail-closed error from the governed policy provenance boundary."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


@final
@dataclass(frozen=True, slots=True)
class SpotV7OperationalPolicyReleasePinsV1:
    """Independent release/config pins; this data object grants no authority."""

    manifest_sha256: str
    application_id: str
    chain_or_domain_id: str
    policy_revision: int
    signer_registry_id: str
    signer_registry_hash: str
    signer_registry_revision: int

    def __post_init__(self) -> None:
        _require_bare_sha256(
            self.manifest_sha256,
            name="manifest_sha256",
            code="EXPECTED_MANIFEST_SHA256_INVALID",
        )
        _require_root(
            self.application_id,
            name="application_id",
            code="EXPECTED_APPLICATION_ID_INVALID",
        )
        _require_root(
            self.chain_or_domain_id,
            name="chain_or_domain_id",
            code="EXPECTED_DOMAIN_ID_INVALID",
        )
        _require_u64(
            self.policy_revision,
            name="policy_revision",
            code="EXPECTED_POLICY_REVISION_INVALID",
        )
        _require_token(
            self.signer_registry_id,
            name="signer_registry_id",
            code="EXPECTED_REGISTRY_ID_INVALID",
        )
        _require_root(
            self.signer_registry_hash,
            name="signer_registry_hash",
            code="EXPECTED_REGISTRY_HASH_INVALID",
        )
        _require_u64(
            self.signer_registry_revision,
            name="signer_registry_revision",
            code="EXPECTED_REGISTRY_REVISION_INVALID",
        )


class _AuthenticatedOperationalPolicyReleasePinsSealV1:
    __slots__ = ()


_AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V1 = (
    _AuthenticatedOperationalPolicyReleasePinsSealV1()
)


@final
class _AuthenticatedSpotV7OperationalPolicyReleasePinsV1:
    """Private handoff from a future independently governed release boundary."""

    __slots__ = ("_evaluation_epoch", "_pins", "_seal")

    def __init__(
        self,
        pins: SpotV7OperationalPolicyReleasePinsV1,
        *,
        trusted_evaluation_epoch: int,
        seal: _AuthenticatedOperationalPolicyReleasePinsSealV1,
    ) -> None:
        if type(pins) is not SpotV7OperationalPolicyReleasePinsV1:
            raise TypeError("authenticated release pins require the exact pin type")
        if seal is not _AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V1:
            raise TypeError("authenticated release pins require the module-private seal")
        object.__setattr__(self, "_pins", pins)
        object.__setattr__(
            self,
            "_evaluation_epoch",
            _require_u64(
                trusted_evaluation_epoch,
                name="trusted_evaluation_epoch",
                code="EVALUATION_EPOCH_INVALID",
            ),
        )
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return (
            getattr(self, "_seal", None) is _AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V1
        )

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("authenticated release pins cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated release pins cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated release pins cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated release pins cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("authenticated release pins cannot be serialized")


@dataclass(frozen=True, slots=True)
class _PolicyContextV1:
    revision: int
    activation_epoch: int
    revocation_epoch: int | None


@dataclass(frozen=True, slots=True)
class _SignerRegistryContextV1:
    registry_id: str
    registry_hash: str
    revision: int
    activation_epoch: int
    revocation_epoch: int | None


@dataclass(frozen=True, slots=True)
class _ParsedOperationalPolicyManifestV1:
    material: _GovernedOperationalPolicyMaterialV2
    policy: _PolicyContextV1
    registry: _SignerRegistryContextV1


@dataclass(slots=True)
class _PlainJsonBudgetV1:
    remaining_nodes: int = MAX_SPOT_V7_OPERATIONAL_POLICY_PLAIN_JSON_NODES_V1
    remaining_utf8_bytes: int = MAX_SPOT_V7_OPERATIONAL_POLICY_PLAIN_JSON_UTF8_BYTES_V1

    def consume_node(self, *, name: str) -> None:
        self.remaining_nodes -= 1
        if self.remaining_nodes < 0:
            raise _reject("PLAIN_DATA_REQUIRED", f"{name} exceeds the node bound")

    def consume_text(self, value: str, *, name: str) -> None:
        if len(value) > self.remaining_utf8_bytes:
            raise _reject("PLAIN_DATA_REQUIRED", f"{name} exceeds the byte bound")
        encoded = value.encode("utf-8")
        self.remaining_utf8_bytes -= len(encoded)
        if self.remaining_utf8_bytes < 0:
            raise _reject("PLAIN_DATA_REQUIRED", f"{name} exceeds the byte bound")


def _reject(code: str, detail: str) -> SpotV7OperationalPolicyProvenanceErrorV1:
    return SpotV7OperationalPolicyProvenanceErrorV1(code, detail)


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _reject(
                "DUPLICATE_JSON_KEY",
                "operational policy manifest contains a duplicate JSON key",
            )
        result[key] = value
    return result


def _reject_float(value: str) -> object:
    raise _reject("FLOAT_FORBIDDEN", value)


def _reject_nonfinite(value: str) -> object:
    raise _reject("NONFINITE_FORBIDDEN", value)


def _require_exact_fields(
    value: object,
    *,
    expected: frozenset[str],
    name: str,
) -> dict[str, object]:
    if type(value) is not dict:
        raise _reject("FIELD_SET_MISMATCH", f"{name} must be an exact JSON object")
    observed = frozenset(value)
    if observed != expected:
        raise _reject(
            "FIELD_SET_MISMATCH",
            f"{name}:missing={sorted(expected - observed)};unknown={sorted(observed - expected)}",
        )
    return value


def _require_u64(value: object, *, name: str, code: str) -> int:
    if type(value) is not int or value < 0 or value > MAX_U64:
        raise _reject(code, f"{name} must be an unsigned 64-bit integer")
    return value


def _require_optional_u64(value: object, *, name: str, code: str) -> int | None:
    if value is None:
        return None
    return _require_u64(value, name=name, code=code)


def _require_token(value: object, *, name: str, code: str) -> str:
    if type(value) is not str or not value or len(value.encode("utf-8")) > 128:
        raise _reject(code, f"{name} must be a non-empty token of at most 128 bytes")
    try:
        value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise _reject(code, f"{name} must be ASCII") from exc
    if _TOKEN_RE.fullmatch(value) is None:
        raise _reject(code, f"{name} contains unsupported characters")
    return value


def _require_bare_sha256(value: object, *, name: str, code: str) -> str:
    if type(value) is not str or _BARE_SHA256_RE.fullmatch(value) is None:
        raise _reject(code, f"{name} must be lowercase 64-character hex")
    return value


def _require_root(value: object, *, name: str, code: str) -> str:
    if type(value) is not str or _ROOT_RE.fullmatch(value) is None:
        raise _reject(code, f"{name} must be canonical 32-byte lowercase hex")
    if value == "0x" + "00" * 32:
        raise _reject(code, f"{name} must be nonzero")
    return value


def _require_lifecycle(
    *,
    activation_epoch: int,
    revocation_epoch: int | None,
    name: str,
) -> None:
    if revocation_epoch is not None and revocation_epoch < activation_epoch:
        raise _reject(
            "LIFECYCLE_INVALID",
            f"{name} revocation_epoch precedes activation_epoch",
        )


def _material_document(material: _GovernedOperationalPolicyMaterialV2) -> dict[str, object]:
    if type(material) is not _GovernedOperationalPolicyMaterialV2:
        raise TypeError("material must be exact _GovernedOperationalPolicyMaterialV2")
    material._to_authority_false_store_policy()
    return {
        "application_id": material.application_id,
        "chain_or_domain_id": material.chain_or_domain_id,
        "data_schema_id": material.data_schema_id,
        "storage_policy_hash": material.storage_policy_hash,
        "minimum_retention_epochs": material.minimum_retention_epochs,
        "minimum_remaining_epochs": material.minimum_remaining_epochs,
        "maximum_blob_bytes": material.maximum_blob_bytes,
        "finality_network_id": material.finality_network_id,
        "finality_protocol_id": material.finality_protocol_id,
        "external_finality_policy_hash": material.external_finality_policy_hash,
        "finality_verifier_set_root": material.finality_verifier_set_root,
        "genesis_application_checkpoint_sequence": (
            material.genesis_application_checkpoint_sequence
        ),
        "genesis_application_checkpoint_hash": material.genesis_application_checkpoint_hash,
    }


def _build_policy_context(
    *,
    revision: int,
    activation_epoch: int,
    revocation_epoch: int | None,
) -> _PolicyContextV1:
    context = _PolicyContextV1(
        revision=_require_u64(
            revision,
            name="policy_revision",
            code="POLICY_CONTEXT_INVALID",
        ),
        activation_epoch=_require_u64(
            activation_epoch,
            name="policy_activation_epoch",
            code="POLICY_CONTEXT_INVALID",
        ),
        revocation_epoch=_require_optional_u64(
            revocation_epoch,
            name="policy_revocation_epoch",
            code="POLICY_CONTEXT_INVALID",
        ),
    )
    _require_lifecycle(
        activation_epoch=context.activation_epoch,
        revocation_epoch=context.revocation_epoch,
        name="policy",
    )
    return context


def _build_registry_context(
    *,
    registry_id: str,
    registry_hash: str,
    revision: int,
    activation_epoch: int,
    revocation_epoch: int | None,
) -> _SignerRegistryContextV1:
    context = _SignerRegistryContextV1(
        registry_id=_require_token(
            registry_id,
            name="signer_registry_id",
            code="REGISTRY_CONTEXT_INVALID",
        ),
        registry_hash=_require_root(
            registry_hash,
            name="signer_registry_hash",
            code="REGISTRY_CONTEXT_INVALID",
        ),
        revision=_require_u64(
            revision,
            name="signer_registry_revision",
            code="REGISTRY_CONTEXT_INVALID",
        ),
        activation_epoch=_require_u64(
            activation_epoch,
            name="signer_registry_activation_epoch",
            code="REGISTRY_CONTEXT_INVALID",
        ),
        revocation_epoch=_require_optional_u64(
            revocation_epoch,
            name="signer_registry_revocation_epoch",
            code="REGISTRY_CONTEXT_INVALID",
        ),
    )
    _require_lifecycle(
        activation_epoch=context.activation_epoch,
        revocation_epoch=context.revocation_epoch,
        name="signer registry",
    )
    return context


def _manifest_document(
    material: _GovernedOperationalPolicyMaterialV2,
    policy: _PolicyContextV1,
    registry: _SignerRegistryContextV1,
) -> dict[str, object]:
    return {
        "schema": SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V1,
        "policy_material": _material_document(material),
        "policy_context": {
            "policy_revision": policy.revision,
            "activation_epoch": policy.activation_epoch,
            "revocation_epoch": policy.revocation_epoch,
        },
        "signer_registry_context": {
            "registry_id": registry.registry_id,
            "registry_hash": registry.registry_hash,
            "registry_revision": registry.revision,
            "activation_epoch": registry.activation_epoch,
            "revocation_epoch": registry.revocation_epoch,
        },
    }


def spot_v7_operational_policy_manifest_bytes_v1(
    material: _GovernedOperationalPolicyMaterialV2,
    *,
    policy_revision: int,
    policy_activation_epoch: int,
    policy_revocation_epoch: int | None,
    signer_registry_id: str,
    signer_registry_hash: str,
    signer_registry_revision: int,
    signer_registry_activation_epoch: int,
    signer_registry_revocation_epoch: int | None,
) -> bytes:
    """Build exact canonical bytes for signer review and release publication."""

    policy = _build_policy_context(
        revision=policy_revision,
        activation_epoch=policy_activation_epoch,
        revocation_epoch=policy_revocation_epoch,
    )
    registry = _build_registry_context(
        registry_id=signer_registry_id,
        registry_hash=signer_registry_hash,
        revision=signer_registry_revision,
        activation_epoch=signer_registry_activation_epoch,
        revocation_epoch=signer_registry_revocation_epoch,
    )
    raw = canonical_json_bytes(_manifest_document(material, policy, registry))
    _parse_manifest_v1(raw)
    return raw


def _parse_material(value: object) -> _GovernedOperationalPolicyMaterialV2:
    material = _require_exact_fields(
        value,
        expected=_POLICY_MATERIAL_FIELDS_V1,
        name="policy_material",
    )
    try:
        return _GovernedOperationalPolicyMaterialV2(
            application_id=material["application_id"],
            chain_or_domain_id=material["chain_or_domain_id"],
            data_schema_id=material["data_schema_id"],
            storage_policy_hash=material["storage_policy_hash"],
            minimum_retention_epochs=material["minimum_retention_epochs"],
            minimum_remaining_epochs=material["minimum_remaining_epochs"],
            maximum_blob_bytes=material["maximum_blob_bytes"],
            finality_network_id=material["finality_network_id"],
            finality_protocol_id=material["finality_protocol_id"],
            external_finality_policy_hash=material["external_finality_policy_hash"],
            finality_verifier_set_root=material["finality_verifier_set_root"],
            genesis_application_checkpoint_sequence=material[
                "genesis_application_checkpoint_sequence"
            ],
            genesis_application_checkpoint_hash=material["genesis_application_checkpoint_hash"],
        )
    except (TypeError, ValueError) as exc:
        raise _reject("POLICY_MATERIAL_INVALID", str(exc)) from exc


def _parse_policy_context(value: object) -> _PolicyContextV1:
    context = _require_exact_fields(
        value,
        expected=_POLICY_CONTEXT_FIELDS_V1,
        name="policy_context",
    )
    result = _PolicyContextV1(
        revision=_require_u64(
            context["policy_revision"],
            name="policy_revision",
            code="POLICY_CONTEXT_INVALID",
        ),
        activation_epoch=_require_u64(
            context["activation_epoch"],
            name="policy activation_epoch",
            code="POLICY_CONTEXT_INVALID",
        ),
        revocation_epoch=_require_optional_u64(
            context["revocation_epoch"],
            name="policy revocation_epoch",
            code="POLICY_CONTEXT_INVALID",
        ),
    )
    _require_lifecycle(
        activation_epoch=result.activation_epoch,
        revocation_epoch=result.revocation_epoch,
        name="policy",
    )
    return result


def _parse_registry_context(value: object) -> _SignerRegistryContextV1:
    context = _require_exact_fields(
        value,
        expected=_REGISTRY_CONTEXT_FIELDS_V1,
        name="signer_registry_context",
    )
    result = _SignerRegistryContextV1(
        registry_id=_require_token(
            context["registry_id"],
            name="signer registry id",
            code="REGISTRY_CONTEXT_INVALID",
        ),
        registry_hash=_require_root(
            context["registry_hash"],
            name="signer registry hash",
            code="REGISTRY_CONTEXT_INVALID",
        ),
        revision=_require_u64(
            context["registry_revision"],
            name="signer registry revision",
            code="REGISTRY_CONTEXT_INVALID",
        ),
        activation_epoch=_require_u64(
            context["activation_epoch"],
            name="signer registry activation_epoch",
            code="REGISTRY_CONTEXT_INVALID",
        ),
        revocation_epoch=_require_optional_u64(
            context["revocation_epoch"],
            name="signer registry revocation_epoch",
            code="REGISTRY_CONTEXT_INVALID",
        ),
    )
    _require_lifecycle(
        activation_epoch=result.activation_epoch,
        revocation_epoch=result.revocation_epoch,
        name="signer registry",
    )
    return result


def _parse_manifest_v1(raw: bytes) -> _ParsedOperationalPolicyManifestV1:
    if type(raw) is not bytes:
        raise _reject("MANIFEST_TYPE", "operational policy manifest must be exact bytes")
    if not raw or len(raw) > MAX_SPOT_V7_OPERATIONAL_POLICY_MANIFEST_BYTES_V1:
        raise _reject(
            "MANIFEST_BYTE_LIMIT",
            "operational policy manifest is empty or exceeds its byte limit",
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
    except SpotV7OperationalPolicyProvenanceErrorV1:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject("INVALID_JSON", "operational policy manifest is invalid JSON") from exc
    document = _require_exact_fields(
        value,
        expected=_TOP_LEVEL_FIELDS_V1,
        name="operational policy manifest",
    )
    if document["schema"] != SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V1:
        raise _reject("SCHEMA_MISMATCH", "operational policy manifest schema is unsupported")
    if canonical_json_bytes(document) != raw:
        raise _reject("NONCANONICAL_JSON", "operational policy manifest is not canonical JSON")
    return _ParsedOperationalPolicyManifestV1(
        material=_parse_material(document["policy_material"]),
        policy=_parse_policy_context(document["policy_context"]),
        registry=_parse_registry_context(document["signer_registry_context"]),
    )


def spot_v7_operational_policy_manifest_payload_hash_v1(raw: bytes) -> str:
    """Return the exact domain-separated payload hash signed by release keys."""

    _parse_manifest_v1(raw)
    return "0x" + hashlib.sha256(_PAYLOAD_HASH_DOMAIN_V1 + encode_bytes(raw)).hexdigest()


def _plain_json_copy(
    value: object,
    *,
    name: str,
    budget: _PlainJsonBudgetV1,
    depth: int = 0,
) -> object:
    if depth > 16:
        raise _reject("PLAIN_DATA_REQUIRED", f"{name} exceeds the nesting bound")
    budget.consume_node(name=name)
    if type(value) is dict:
        result: dict[str, object] = {}
        for key, item in value.items():
            if type(key) is not str:
                raise _reject("PLAIN_DATA_REQUIRED", f"{name} keys must be exact strings")
            budget.consume_text(key, name=name)
            result[key] = _plain_json_copy(
                item,
                name=name,
                budget=budget,
                depth=depth + 1,
            )
        return result
    if type(value) is list:
        return [
            _plain_json_copy(
                item,
                name=name,
                budget=budget,
                depth=depth + 1,
            )
            for item in value
        ]
    if type(value) is str:
        budget.consume_text(value, name=name)
        return value
    if type(value) is int:
        if value < -MAX_U64 or value > MAX_U64:
            raise _reject("PLAIN_DATA_REQUIRED", f"{name} integer exceeds the width bound")
        return value
    if type(value) in {bool, type(None)}:
        return value
    raise _reject("PLAIN_DATA_REQUIRED", f"{name} must contain only exact JSON values")


def _snapshot_registry(value: object) -> dict[str, Any]:
    if type(value) is not dict:
        raise _reject("PLAIN_DATA_REQUIRED", "signer_registry must be an exact dict")
    copied = _plain_json_copy(
        value,
        name="signer_registry",
        budget=_PlainJsonBudgetV1(),
    )
    if type(copied) is not dict:
        raise _reject("PLAIN_DATA_REQUIRED", "signer_registry snapshot failed")
    signers = copied.get("signers")
    if (
        type(signers) is not list
        or not 1 <= len(signers) <= MAX_SPOT_V7_OPERATIONAL_POLICY_SIGNERS_V1
    ):
        raise _reject("SIGNER_REGISTRY_INVALID", "signer registry count is outside the bound")
    return copied


def _snapshot_envelopes(value: object) -> tuple[dict[str, Any], ...]:
    if type(value) not in {tuple, list}:
        raise _reject("PLAIN_DATA_REQUIRED", "signature_envelopes must be an exact tuple or list")
    sequence = cast(tuple[object, ...] | list[object], value)
    if not 1 <= len(sequence) <= MAX_SPOT_V7_OPERATIONAL_POLICY_SIGNATURES_V1:
        raise _reject("SIGNATURE_QUORUM_INVALID", "signature envelope count is outside the bound")
    result: list[dict[str, Any]] = []
    budget = _PlainJsonBudgetV1()
    for index, envelope in enumerate(sequence):
        if type(envelope) is not dict:
            raise _reject(
                "PLAIN_DATA_REQUIRED",
                f"signature_envelopes[{index}] must be an exact dict",
            )
        copied = _plain_json_copy(
            envelope,
            name=f"signature_envelopes[{index}]",
            budget=budget,
        )
        if type(copied) is not dict:
            raise _reject("PLAIN_DATA_REQUIRED", "signature envelope snapshot failed")
        result.append(copied)
    return tuple(result)


def _require_active(
    *,
    context: _PolicyContextV1 | _SignerRegistryContextV1,
    evaluation_epoch: int,
    name: str,
) -> None:
    if type(context) is _PolicyContextV1:
        not_active_code = "POLICY_NOT_ACTIVE"
        revoked_code = "POLICY_REVOKED"
    else:
        not_active_code = "REGISTRY_NOT_ACTIVE"
        revoked_code = "REGISTRY_REVOKED"
    if evaluation_epoch < context.activation_epoch:
        raise _reject(not_active_code, f"{name} is not active at evaluation_epoch")
    if context.revocation_epoch is not None and evaluation_epoch >= context.revocation_epoch:
        raise _reject(revoked_code, f"{name} is revoked at evaluation_epoch")


def _require_manifest_binding(
    *,
    raw_manifest: bytes,
    parsed: _ParsedOperationalPolicyManifestV1,
    pins: SpotV7OperationalPolicyReleasePinsV1,
) -> None:
    actual_manifest_sha256 = hashlib.sha256(raw_manifest).hexdigest()
    if not hmac.compare_digest(actual_manifest_sha256, pins.manifest_sha256):
        raise _reject("MANIFEST_SHA256_MISMATCH", "policy manifest SHA-256 is not trusted")
    checks = (
        (
            parsed.material.application_id == pins.application_id,
            "APPLICATION_ID_MISMATCH",
            "policy application_id is not trusted",
        ),
        (
            parsed.material.chain_or_domain_id == pins.chain_or_domain_id,
            "DOMAIN_ID_MISMATCH",
            "policy chain_or_domain_id is not trusted",
        ),
        (
            parsed.policy.revision == pins.policy_revision,
            "POLICY_REVISION_MISMATCH",
            "policy revision is not trusted",
        ),
        (
            parsed.registry.registry_id == pins.signer_registry_id,
            "REGISTRY_ID_MISMATCH",
            "signer registry id is not trusted",
        ),
        (
            hmac.compare_digest(parsed.registry.registry_hash, pins.signer_registry_hash),
            "REGISTRY_HASH_MISMATCH",
            "signer registry hash is not trusted",
        ),
        (
            parsed.registry.revision == pins.signer_registry_revision,
            "REGISTRY_REVISION_MISMATCH",
            "signer registry revision is not trusted",
        ),
    )
    for accepted, code, detail in checks:
        if not accepted:
            raise _reject(code, detail)


def _require_active_release_context(
    parsed: _ParsedOperationalPolicyManifestV1,
    trusted_evaluation_epoch: int,
) -> None:
    _require_active(
        context=parsed.policy,
        evaluation_epoch=trusted_evaluation_epoch,
        name="operational policy",
    )
    _require_active(
        context=parsed.registry,
        evaluation_epoch=trusted_evaluation_epoch,
        name="signer registry",
    )


def _verify_release_quorum(
    *,
    raw_manifest: bytes,
    parsed: _ParsedOperationalPolicyManifestV1,
    signer_registry: object,
    signature_envelopes: object,
) -> None:
    registry = _snapshot_registry(signer_registry)
    envelopes = _snapshot_envelopes(signature_envelopes)
    if registry.get("registry_id") != parsed.registry.registry_id:
        raise _reject("SIGNER_REGISTRY_ID_MISMATCH", "signer registry id differs from manifest")
    if registry.get("registry_hash") != parsed.registry.registry_hash:
        raise _reject(
            "SIGNER_REGISTRY_HASH_MISMATCH",
            "signer registry hash differs from manifest",
        )
    try:
        verify_signature_quorum_v0(
            registry=registry,
            payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V1,
            payload_hash=spot_v7_operational_policy_manifest_payload_hash_v1(raw_manifest),
            envelopes=envelopes,
        )
    except (RuntimeError, TypeError, ValueError) as exc:
        raise _reject("SIGNATURE_QUORUM_INVALID", str(exc)) from exc


def _open_authenticated_release_context(
    value: object,
) -> tuple[SpotV7OperationalPolicyReleasePinsV1, int]:
    if type(value) is not _AuthenticatedSpotV7OperationalPolicyReleasePinsV1:
        raise _reject(
            "AUTHENTICATED_RELEASE_PINS_REQUIRED",
            "caller-provided release pins cannot mint an operational policy",
        )
    if not value._has_private_seal():
        raise _reject(
            "AUTHENTICATED_RELEASE_PINS_REQUIRED",
            "operational-policy release pins lack their private authority seal",
        )
    pins = object.__getattribute__(value, "_pins")
    evaluation_epoch = object.__getattribute__(value, "_evaluation_epoch")
    if type(pins) is not SpotV7OperationalPolicyReleasePinsV1:
        raise _reject(
            "AUTHENTICATED_RELEASE_PINS_REQUIRED",
            "authenticated operational-policy pins have the wrong type",
        )
    return pins, _require_u64(
        evaluation_epoch,
        name="trusted_evaluation_epoch",
        code="EVALUATION_EPOCH_INVALID",
    )


def load_governed_spot_v7_operational_policy_v2(
    raw_manifest: bytes,
    *,
    authenticated_release: _AuthenticatedSpotV7OperationalPolicyReleasePinsV1,
    signer_registry: Mapping[str, Any],
    signature_envelopes: Sequence[Mapping[str, Any]],
) -> _GovernedSpotV7OperationalPolicyV2:
    """Authenticate exact policy-release provenance and mint the sealed policy.

    ``authenticated_release`` has no production mint in this tranche. A future
    release, ledger, or governance adapter must mint it from independently
    authenticated state. Raw pins, epochs, manifests, registries, envelopes,
    and caller-provided booleans cannot substitute for that private handoff.
    """

    release_pins, checked_epoch = _open_authenticated_release_context(authenticated_release)
    parsed = _parse_manifest_v1(raw_manifest)
    _require_manifest_binding(raw_manifest=raw_manifest, parsed=parsed, pins=release_pins)
    _require_active_release_context(parsed, checked_epoch)
    _verify_release_quorum(
        raw_manifest=raw_manifest,
        parsed=parsed,
        signer_registry=signer_registry,
        signature_envelopes=signature_envelopes,
    )
    return _GovernedSpotV7OperationalPolicyV2(
        parsed.material,
        seal=_GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    )
