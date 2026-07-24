"""Canonical signed provenance for Spot V7 operational policy manifest V2.

Manifest V2 signs the complete legacy full-blob/finality material together with
the exact ZenoLedger chain identifier, sampled-retrievability policy, provider
key lifecycles, and acyclic lagged-checkpoint beacon policy.  Its successful
loader mints only the private authority-false V3 policy capability.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import re
from dataclasses import dataclass
from typing import Any, NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    BeaconPolicyV1,
    _GovernedOperationalPolicyMaterialV3,
    _GovernedOperationalPolicyProvenanceV2,
    _GovernedSpotV7OperationalPolicyV3,
    _mint_governed_spot_v7_operational_policy_v3,
)
from src.integration.zeno_ledger_signer_registry import verify_signature_quorum_v0
from src.integration.zrpf_sampled_retrievability_v1.model import (
    ProviderKeyLifecycleV1,
    SampledRetrievabilityPolicyV1,
    require_bls_public_key,
)
from src.integration.zrpf_spot_v7_operational_policy_provenance import (
    SpotV7OperationalPolicyProvenanceErrorV1,
    _build_policy_context,
    _build_registry_context,
    _PolicyContextV1,
    _SignerRegistryContextV1,
    _snapshot_envelopes,
    _snapshot_registry,
)
from src.integration.zrpf_spot_v7_operational_policy_provenance import (
    _material_document as _base_material_document,
)
from src.integration.zrpf_spot_v7_operational_policy_provenance import (
    _parse_material as _parse_base_material,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, encode_bytes

SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V2 = (
    "zenodex.zrpf.spot_v7.operational_policy_manifest.v2"
)
# The signer registry governs the operational-policy purpose.  Version
# separation is provided by the V2 schema and V2 domain-separated payload hash,
# so existing registries need no new generic payload-kind branch.
SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V2 = "zrpf_spot_v7_operational_policy"
SPOT_V7_OPERATIONAL_POLICY_PROVENANCE_SCHEMA_V2 = (
    "zenodex.zrpf.spot_v7.operational_policy_provenance.v2"
)
MAX_SPOT_V7_OPERATIONAL_POLICY_MANIFEST_BYTES_V2 = 32 * 1_024
MAX_U64 = (1 << 64) - 1

_PAYLOAD_HASH_DOMAIN_V2 = domain_sep_bytes(
    "zrpf_spot_v7_operational_policy_manifest_payload",
    version=2,
)
_BARE_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_ROOT_RE = re.compile(r"^0x[0-9a-f]{64}$")
_TOKEN_RE = re.compile(r"^[A-Za-z0-9._:-]{1,128}$")
_TOP_FIELDS = frozenset(
    {"schema", "policy_material", "policy_context", "signer_registry_context"}
)
_MATERIAL_FIELDS = frozenset(
    {
        "base_operational_policy",
        "beacon_source_finality_policy",
        "zeno_ledger_chain_id",
        "sampled_retrievability_policy",
        "beacon_policy",
    }
)
_SAMPLED_FIELDS = frozenset(
    {
        "activation_epoch",
        "application_id",
        "beacon_policy_hash",
        "beacon_source_id",
        "chain_or_domain_id",
        "challenge_count",
        "minimum_provider_responses",
        "minimum_remaining_epochs",
        "minimum_retention_epochs",
        "policy_revision",
        "providers",
        "response_window_epochs",
        "revocation_epoch",
        "storage_policy_hash",
    }
)
_PROVIDER_FIELDS = frozenset(
    {"activation_epoch", "key_id", "provider_id", "public_key", "revocation_epoch"}
)
_BEACON_FIELDS = frozenset(
    {
        "activation_epoch",
        "policy_revision",
        "revocation_epoch",
        "source_epoch_lag",
        "source_id",
        "source_network_id",
        "source_protocol_id",
    }
)
_POLICY_CONTEXT_FIELDS = frozenset(
    {"policy_revision", "activation_epoch", "revocation_epoch"}
)
_REGISTRY_CONTEXT_FIELDS = frozenset(
    {
        "registry_id",
        "registry_hash",
        "registry_revision",
        "activation_epoch",
        "revocation_epoch",
    }
)


class SpotV7OperationalPolicyProvenanceErrorV2(ValueError):
    """Stable fail-closed error from the V2 signed policy boundary."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


def _reject(code: str, detail: str) -> SpotV7OperationalPolicyProvenanceErrorV2:
    return SpotV7OperationalPolicyProvenanceErrorV2(code, detail)


@final
@dataclass(frozen=True, slots=True)
class SpotV7OperationalPolicyReleasePinsV2:
    """Independent V2 release pins; this data object grants no authority."""

    manifest_sha256: str
    application_id: str
    chain_or_domain_id: str
    zeno_ledger_chain_id: str
    policy_revision: int
    sampled_policy_root: str
    beacon_policy_root: str
    beacon_source_finality_policy_root: str
    signer_registry_id: str
    signer_registry_hash: str
    signer_registry_revision: int

    def __post_init__(self) -> None:
        _require_bare_sha256(self.manifest_sha256, name="manifest_sha256")
        for name in (
            "application_id",
            "chain_or_domain_id",
            "sampled_policy_root",
            "beacon_policy_root",
            "beacon_source_finality_policy_root",
            "signer_registry_hash",
        ):
            _require_root(getattr(self, name), name=name)
        _require_token(self.zeno_ledger_chain_id, name="zeno_ledger_chain_id")
        _require_token(self.signer_registry_id, name="signer_registry_id")
        _require_u64(self.policy_revision, name="policy_revision")
        _require_u64(self.signer_registry_revision, name="signer_registry_revision")


class _AuthenticatedOperationalPolicyReleasePinsSealV2:
    __slots__ = ()


_AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V2 = (
    _AuthenticatedOperationalPolicyReleasePinsSealV2()
)


@final
class _AuthenticatedSpotV7OperationalPolicyReleasePinsV2:
    """Private handoff from a future independently governed release boundary."""

    __slots__ = ("_evaluation_epoch", "_pins", "_seal")

    _evaluation_epoch: int
    _pins: SpotV7OperationalPolicyReleasePinsV2
    _seal: _AuthenticatedOperationalPolicyReleasePinsSealV2

    def __init__(
        self,
        pins: SpotV7OperationalPolicyReleasePinsV2,
        *,
        trusted_evaluation_epoch: int,
        seal: _AuthenticatedOperationalPolicyReleasePinsSealV2,
    ) -> None:
        if type(pins) is not SpotV7OperationalPolicyReleasePinsV2:
            raise TypeError("authenticated V2 release pins require the exact pin type")
        if seal is not _AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V2:
            raise TypeError("authenticated V2 release pins require the module-private seal")
        object.__setattr__(self, "_pins", pins)
        object.__setattr__(
            self,
            "_evaluation_epoch",
            _require_u64(trusted_evaluation_epoch, name="trusted_evaluation_epoch"),
        )
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return (
            getattr(self, "_seal", None)
            is _AUTHENTICATED_OPERATIONAL_POLICY_RELEASE_PINS_SEAL_V2
        )

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("authenticated V2 release pins cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated V2 release pins cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated V2 release pins cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated V2 release pins cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("authenticated V2 release pins cannot be serialized")


@dataclass(frozen=True, slots=True)
class _ParsedManifestV2:
    material: _GovernedOperationalPolicyMaterialV3
    policy: _PolicyContextV1
    registry: _SignerRegistryContextV1


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _reject("DUPLICATE_JSON_KEY", "manifest contains a duplicate JSON key")
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
        raise _reject("EXACT_OBJECT_REQUIRED", f"{name} must be an exact object")
    keys = frozenset(value)
    if keys != expected:
        missing = sorted(expected - keys)
        extra = sorted(keys - expected)
        raise _reject("FIELD_SET_MISMATCH", f"{name} missing={missing} extra={extra}")
    return value


def _require_u64(value: object, *, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64:
        raise _reject("U64_REQUIRED", f"{name} must be a u64")
    return value


def _require_optional_u64(value: object, *, name: str) -> int | None:
    if value is None:
        return None
    return _require_u64(value, name=name)


def _require_token(value: object, *, name: str) -> str:
    if type(value) is not str or _TOKEN_RE.fullmatch(value) is None:
        raise _reject("TOKEN_REQUIRED", f"{name} must be a bounded canonical token")
    return value


def _require_root(value: object, *, name: str) -> str:
    if type(value) is not str or _ROOT_RE.fullmatch(value) is None:
        raise _reject("ROOT_REQUIRED", f"{name} must be canonical lowercase hex")
    if value == "0x" + "00" * 32:
        raise _reject("ROOT_REQUIRED", f"{name} must be nonzero")
    return value


def _require_bare_sha256(value: object, *, name: str) -> str:
    if type(value) is not str or _BARE_SHA256_RE.fullmatch(value) is None:
        raise _reject("SHA256_REQUIRED", f"{name} must be lowercase 64-character hex")
    return value


def _material_document(material: _GovernedOperationalPolicyMaterialV3) -> dict[str, object]:
    if type(material) is not _GovernedOperationalPolicyMaterialV3:
        raise TypeError("material must be exact _GovernedOperationalPolicyMaterialV3")
    material._to_authority_false_store_policy()
    return {
        "base_operational_policy": _base_material_document(material.base_material),
        "beacon_source_finality_policy": _base_material_document(
            material.beacon_source_finality_material
        ),
        "beacon_policy": material.beacon_policy.to_document(),
        "sampled_retrievability_policy": (
            material.sampled_retrievability_policy.to_document()
        ),
        "zeno_ledger_chain_id": material.zeno_ledger_chain_id,
    }


def _manifest_document(
    material: _GovernedOperationalPolicyMaterialV3,
    policy: _PolicyContextV1,
    registry: _SignerRegistryContextV1,
) -> dict[str, object]:
    return {
        "policy_context": {
            "activation_epoch": policy.activation_epoch,
            "policy_revision": policy.revision,
            "revocation_epoch": policy.revocation_epoch,
        },
        "policy_material": _material_document(material),
        "schema": SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V2,
        "signer_registry_context": {
            "activation_epoch": registry.activation_epoch,
            "registry_hash": registry.registry_hash,
            "registry_id": registry.registry_id,
            "registry_revision": registry.revision,
            "revocation_epoch": registry.revocation_epoch,
        },
    }


def spot_v7_operational_policy_manifest_bytes_v2(
    material: _GovernedOperationalPolicyMaterialV3,
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
    """Build exact V2 policy bytes for signer review and release publication."""

    try:
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
    except SpotV7OperationalPolicyProvenanceErrorV1 as exc:
        raise _reject("CONTEXT_INVALID", exc.detail) from exc
    raw = canonical_json_bytes(_manifest_document(material, policy, registry))
    _parse_manifest_v2(raw)
    return raw


def _parse_provider(value: object) -> ProviderKeyLifecycleV1:
    item = _require_exact_fields(value, expected=_PROVIDER_FIELDS, name="provider")
    try:
        return ProviderKeyLifecycleV1(
            provider_id=_require_token(item["provider_id"], name="provider_id"),
            key_id=_require_token(item["key_id"], name="key_id"),
            public_key=require_bls_public_key(
                item["public_key"],
                name="provider public_key",
            ),
            activation_epoch=_require_u64(
                item["activation_epoch"], name="provider activation_epoch"
            ),
            revocation_epoch=_require_optional_u64(
                item["revocation_epoch"], name="provider revocation_epoch"
            ),
        )
    except (TypeError, ValueError) as exc:
        raise _reject("PROVIDER_INVALID", str(exc)) from exc


def _parse_sampled_policy(value: object) -> SampledRetrievabilityPolicyV1:
    item = _require_exact_fields(value, expected=_SAMPLED_FIELDS, name="sampled policy")
    providers_raw = item["providers"]
    if type(providers_raw) is not list:
        raise _reject("PROVIDERS_INVALID", "sampled providers must be an exact array")
    providers = tuple(_parse_provider(provider) for provider in providers_raw)
    try:
        return SampledRetrievabilityPolicyV1.validated(
            application_id=_require_root(item["application_id"], name="sampled application"),
            chain_or_domain_id=_require_root(
                item["chain_or_domain_id"], name="sampled domain"
            ),
            policy_revision=_require_u64(
                item["policy_revision"], name="sampled policy_revision"
            ),
            activation_epoch=_require_u64(
                item["activation_epoch"], name="sampled activation_epoch"
            ),
            revocation_epoch=_require_optional_u64(
                item["revocation_epoch"], name="sampled revocation_epoch"
            ),
            storage_policy_hash=_require_root(
                item["storage_policy_hash"], name="sampled storage policy"
            ),
            beacon_source_id=_require_root(
                item["beacon_source_id"], name="sampled beacon source"
            ),
            beacon_policy_hash=_require_root(
                item["beacon_policy_hash"], name="sampled beacon policy"
            ),
            minimum_retention_epochs=_require_u64(
                item["minimum_retention_epochs"], name="sampled minimum retention"
            ),
            minimum_remaining_epochs=_require_u64(
                item["minimum_remaining_epochs"], name="sampled remaining retention"
            ),
            challenge_count=_require_u64(
                item["challenge_count"], name="sampled challenge_count"
            ),
            response_window_epochs=_require_u64(
                item["response_window_epochs"], name="sampled response window"
            ),
            minimum_provider_responses=_require_u64(
                item["minimum_provider_responses"], name="sampled provider threshold"
            ),
            providers=providers,
        )
    except (TypeError, ValueError) as exc:
        raise _reject("SAMPLED_POLICY_INVALID", str(exc)) from exc


def _parse_beacon_policy(value: object) -> BeaconPolicyV1:
    item = _require_exact_fields(value, expected=_BEACON_FIELDS, name="beacon policy")
    try:
        return BeaconPolicyV1(
            policy_revision=_require_u64(
                item["policy_revision"], name="beacon policy_revision"
            ),
            activation_epoch=_require_u64(
                item["activation_epoch"], name="beacon activation_epoch"
            ),
            revocation_epoch=_require_optional_u64(
                item["revocation_epoch"], name="beacon revocation_epoch"
            ),
            source_id=_require_root(item["source_id"], name="beacon source_id"),
            source_network_id=_require_root(
                item["source_network_id"], name="beacon source network"
            ),
            source_protocol_id=_require_root(
                item["source_protocol_id"], name="beacon source protocol"
            ),
            source_epoch_lag=_require_u64(
                item["source_epoch_lag"], name="beacon source lag"
            ),
        )
    except (TypeError, ValueError) as exc:
        raise _reject("BEACON_POLICY_INVALID", str(exc)) from exc


def _parse_material(value: object) -> _GovernedOperationalPolicyMaterialV3:
    item = _require_exact_fields(value, expected=_MATERIAL_FIELDS, name="policy material")
    try:
        base = _parse_base_material(item["base_operational_policy"])
        source_finality = _parse_base_material(item["beacon_source_finality_policy"])
    except SpotV7OperationalPolicyProvenanceErrorV1 as exc:
        raise _reject("BASE_POLICY_INVALID", exc.detail) from exc
    try:
        return _GovernedOperationalPolicyMaterialV3(
            base_material=base,
            beacon_source_finality_material=source_finality,
            zeno_ledger_chain_id=_require_token(
                item["zeno_ledger_chain_id"], name="zeno_ledger_chain_id"
            ),
            sampled_retrievability_policy=_parse_sampled_policy(
                item["sampled_retrievability_policy"]
            ),
            beacon_policy=_parse_beacon_policy(item["beacon_policy"]),
        )
    except (TypeError, ValueError) as exc:
        raise _reject("POLICY_MATERIAL_INVALID", str(exc)) from exc


def _parse_policy_context(value: object) -> _PolicyContextV1:
    item = _require_exact_fields(value, expected=_POLICY_CONTEXT_FIELDS, name="policy context")
    try:
        return _build_policy_context(
            revision=_require_u64(item["policy_revision"], name="policy revision"),
            activation_epoch=_require_u64(
                item["activation_epoch"], name="policy activation"
            ),
            revocation_epoch=_require_optional_u64(
                item["revocation_epoch"], name="policy revocation"
            ),
        )
    except SpotV7OperationalPolicyProvenanceErrorV1 as exc:
        raise _reject("POLICY_CONTEXT_INVALID", exc.detail) from exc


def _parse_registry_context(value: object) -> _SignerRegistryContextV1:
    item = _require_exact_fields(
        value,
        expected=_REGISTRY_CONTEXT_FIELDS,
        name="registry context",
    )
    try:
        return _build_registry_context(
            registry_id=_require_token(item["registry_id"], name="registry id"),
            registry_hash=_require_root(item["registry_hash"], name="registry hash"),
            revision=_require_u64(item["registry_revision"], name="registry revision"),
            activation_epoch=_require_u64(
                item["activation_epoch"], name="registry activation"
            ),
            revocation_epoch=_require_optional_u64(
                item["revocation_epoch"], name="registry revocation"
            ),
        )
    except SpotV7OperationalPolicyProvenanceErrorV1 as exc:
        raise _reject("REGISTRY_CONTEXT_INVALID", exc.detail) from exc


def _parse_manifest_v2(raw: bytes) -> _ParsedManifestV2:
    if type(raw) is not bytes:
        raise _reject("MANIFEST_TYPE", "manifest must be exact bytes")
    if not raw or len(raw) > MAX_SPOT_V7_OPERATIONAL_POLICY_MANIFEST_BYTES_V2:
        raise _reject("MANIFEST_BYTE_LIMIT", "manifest is empty or oversized")
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise _reject("ASCII_REQUIRED", "manifest must be ASCII") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_nonfinite,
        )
    except SpotV7OperationalPolicyProvenanceErrorV2:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject("INVALID_JSON", "manifest is invalid JSON") from exc
    document = _require_exact_fields(value, expected=_TOP_FIELDS, name="manifest")
    if document["schema"] != SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V2:
        raise _reject("SCHEMA_MISMATCH", "manifest schema is unsupported")
    if canonical_json_bytes(document) != raw:
        raise _reject("NONCANONICAL_JSON", "manifest is not canonical JSON")
    material = _parse_material(document["policy_material"])
    policy = _parse_policy_context(document["policy_context"])
    registry = _parse_registry_context(document["signer_registry_context"])
    if policy.activation_epoch < material.sampled_retrievability_policy.activation_epoch:
        raise _reject("POLICY_LIFECYCLE_INVALID", "outer policy activates before sampled policy")
    if policy.activation_epoch < material.beacon_policy.activation_epoch:
        raise _reject("POLICY_LIFECYCLE_INVALID", "outer policy activates before beacon policy")
    return _ParsedManifestV2(material=material, policy=policy, registry=registry)


def spot_v7_operational_policy_manifest_payload_hash_v2(raw: bytes) -> str:
    """Return the exact domain-separated payload hash signed by V2 release keys."""

    _parse_manifest_v2(raw)
    return "0x" + hashlib.sha256(_PAYLOAD_HASH_DOMAIN_V2 + encode_bytes(raw)).hexdigest()


def _open_authenticated_release(
    value: object,
) -> tuple[SpotV7OperationalPolicyReleasePinsV2, int]:
    if type(value) is not _AuthenticatedSpotV7OperationalPolicyReleasePinsV2:
        raise _reject("AUTHENTICATED_RELEASE_REQUIRED", "release handoff has the wrong type")
    if not value._has_private_seal():
        raise _reject("AUTHENTICATED_RELEASE_REQUIRED", "release handoff lacks its seal")
    return value._pins, value._evaluation_epoch


def _require_active(parsed: _ParsedManifestV2, evaluation_epoch: int) -> None:
    for context, name in (
        (parsed.policy, "policy"),
        (parsed.registry, "registry"),
    ):
        if evaluation_epoch < context.activation_epoch:
            raise _reject("RELEASE_CONTEXT_INACTIVE", f"{name} is not active")
        if context.revocation_epoch is not None and evaluation_epoch >= context.revocation_epoch:
            raise _reject("RELEASE_CONTEXT_REVOKED", f"{name} is revoked")
    sampled = parsed.material.sampled_retrievability_policy
    beacon = parsed.material.beacon_policy
    if not sampled.is_active_at(evaluation_epoch) or not beacon.is_active_at(evaluation_epoch):
        raise _reject("NESTED_POLICY_INACTIVE", "sampled or beacon policy is inactive")
    if len(sampled.active_provider_ids_at(evaluation_epoch)) < sampled.minimum_provider_responses:
        raise _reject("NESTED_POLICY_INACTIVE", "active provider set is below threshold")


def _require_manifest_binding(
    *,
    raw: bytes,
    parsed: _ParsedManifestV2,
    pins: SpotV7OperationalPolicyReleasePinsV2,
) -> None:
    material = parsed.material
    checks = (
        (
            hmac.compare_digest(hashlib.sha256(raw).hexdigest(), pins.manifest_sha256),
            "MANIFEST_SHA256_MISMATCH",
        ),
        (material.base_material.application_id == pins.application_id, "APPLICATION_ID_MISMATCH"),
        (
            material.base_material.chain_or_domain_id == pins.chain_or_domain_id,
            "DOMAIN_ID_MISMATCH",
        ),
        (material.zeno_ledger_chain_id == pins.zeno_ledger_chain_id, "CHAIN_ID_MISMATCH"),
        (parsed.policy.revision == pins.policy_revision, "POLICY_REVISION_MISMATCH"),
        (
            material.sampled_retrievability_policy.policy_root == pins.sampled_policy_root,
            "SAMPLED_POLICY_ROOT_MISMATCH",
        ),
        (material.beacon_policy.policy_root == pins.beacon_policy_root, "BEACON_POLICY_ROOT_MISMATCH"),
        (
            material._to_authority_false_beacon_source_policy().checkpoint_finality_policy_root
            == pins.beacon_source_finality_policy_root,
            "BEACON_SOURCE_FINALITY_POLICY_ROOT_MISMATCH",
        ),
        (parsed.registry.registry_id == pins.signer_registry_id, "REGISTRY_ID_MISMATCH"),
        (
            hmac.compare_digest(parsed.registry.registry_hash, pins.signer_registry_hash),
            "REGISTRY_HASH_MISMATCH",
        ),
        (
            parsed.registry.revision == pins.signer_registry_revision,
            "REGISTRY_REVISION_MISMATCH",
        ),
    )
    for accepted, code in checks:
        if not accepted:
            raise _reject(code, "signed policy does not match the independent release pin")


def _verify_quorum(
    *,
    raw: bytes,
    parsed: _ParsedManifestV2,
    signer_registry: object,
    signature_envelopes: object,
) -> tuple[dict[str, Any], tuple[dict[str, Any], ...], dict[str, Any]]:
    try:
        registry = _snapshot_registry(signer_registry)
        envelopes = tuple(
            sorted(_snapshot_envelopes(signature_envelopes), key=canonical_json_bytes)
        )
    except SpotV7OperationalPolicyProvenanceErrorV1 as exc:
        raise _reject("PLAIN_QUORUM_DATA_REQUIRED", exc.detail) from exc
    if registry.get("registry_id") != parsed.registry.registry_id:
        raise _reject("SIGNER_REGISTRY_ID_MISMATCH", "registry id differs from manifest")
    if registry.get("registry_hash") != parsed.registry.registry_hash:
        raise _reject("SIGNER_REGISTRY_HASH_MISMATCH", "registry hash differs from manifest")
    try:
        report = verify_signature_quorum_v0(
            registry=registry,
            payload_kind=SPOT_V7_OPERATIONAL_POLICY_PAYLOAD_KIND_V2,
            payload_hash=spot_v7_operational_policy_manifest_payload_hash_v2(raw),
            envelopes=envelopes,
        )
    except (RuntimeError, TypeError, ValueError) as exc:
        raise _reject("SIGNATURE_QUORUM_INVALID", str(exc)) from exc
    return registry, envelopes, report


def _build_provenance(
    *,
    raw: bytes,
    parsed: _ParsedManifestV2,
    pins: SpotV7OperationalPolicyReleasePinsV2,
    evaluation_epoch: int,
    registry: dict[str, Any],
    envelopes: tuple[dict[str, Any], ...],
    report: dict[str, Any],
) -> _GovernedOperationalPolicyProvenanceV2:
    quorum_hash = _require_root(
        report.get("quorum_report_hash"),
        name="signature quorum report hash",
    )
    evidence = canonical_json_bytes(
        {
            "evaluation_epoch": evaluation_epoch,
            "manifest_bytes_hex": raw.hex(),
            "manifest_sha256": pins.manifest_sha256,
            "schema": SPOT_V7_OPERATIONAL_POLICY_PROVENANCE_SCHEMA_V2,
            "signature_envelopes": list(envelopes),
            "signature_quorum_report": report,
            "signer_registry": registry,
        }
    )
    return _GovernedOperationalPolicyProvenanceV2(
        evidence_root="0x" + hashlib.sha256(evidence).hexdigest(),
        exact_evidence_bytes=evidence,
        manifest_sha256=pins.manifest_sha256,
        signer_registry_hash=parsed.registry.registry_hash,
        signature_quorum_report_hash=quorum_hash,
        policy_revision=parsed.policy.revision,
        policy_activation_epoch=parsed.policy.activation_epoch,
        policy_revocation_epoch=parsed.policy.revocation_epoch,
        signer_registry_revision=parsed.registry.revision,
        signer_registry_activation_epoch=parsed.registry.activation_epoch,
        signer_registry_revocation_epoch=parsed.registry.revocation_epoch,
        evaluation_epoch=evaluation_epoch,
    )


def load_governed_spot_v7_operational_policy_v3(
    raw_manifest: bytes,
    *,
    authenticated_release: object,
    signer_registry: object,
    signature_envelopes: object,
) -> _GovernedSpotV7OperationalPolicyV3:
    """Verify V2 signed policy provenance and mint the private V3 capability."""

    parsed = _parse_manifest_v2(raw_manifest)
    pins, evaluation_epoch = _open_authenticated_release(authenticated_release)
    _require_manifest_binding(raw=raw_manifest, parsed=parsed, pins=pins)
    _require_active(parsed, evaluation_epoch)
    registry, envelopes, report = _verify_quorum(
        raw=raw_manifest,
        parsed=parsed,
        signer_registry=signer_registry,
        signature_envelopes=signature_envelopes,
    )
    provenance = _build_provenance(
        raw=raw_manifest,
        parsed=parsed,
        pins=pins,
        evaluation_epoch=evaluation_epoch,
        registry=registry,
        envelopes=envelopes,
        report=report,
    )
    return _mint_governed_spot_v7_operational_policy_v3(
        parsed.material,
        provenance=provenance,
    )
