"""Quorum-authenticated, authority-neutral Spot V7 release revocation V1.

The adapter binds one current release candidate, its current selection cursor,
one fixed-width revocation selector, one fixed-width revocation record, exact
external trust pins, and an individually verified BLS quorum. The private
result authenticates that statement only. Durable replay prevention, registry
governance, revocation authority, and runtime authority remain false.
"""

from __future__ import annotations

import hashlib
import json
import re
from copy import deepcopy
from dataclasses import dataclass
from typing import Any, Final, Mapping, NoReturn, Sequence, SupportsIndex, cast, final

from src.integration._zrpf_spot_v7_release_revocation_envelope_v1 import (
    SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
    SpotV7ReleaseRevocationEnvelopeRejectV1,
    SpotV7ReleaseRevocationEnvelopeV1,
    parse_exact_spot_v7_release_revocation_envelope_v1,
    recompose_spot_v7_release_revocation_envelope_v1,
    spot_v7_release_revocation_envelope_payload_hash_v1,
)
from src.integration.zeno_ledger_signer_registry import (
    validate_signer_registry_v0,
    verify_signature_quorum_v0,
)
from src.state.canonical import bounded_json_utf8_size, canonical_json_bytes
from tools.zrpf_spot_v7_governed_release_selector_input_v1 import (
    GovernedReleaseSelectorInputV1,
    SelectorOperationV1,
    SpotV7RevocationRecordV1,
    SpotV7SelectorInputRejectV1,
    parse_exact_governed_release_selector_input_v1,
    parse_exact_spot_v7_revocation_record_v1,
)
from tools.zrpf_spot_v7_release_candidate_manifest_v1 import (
    SPOT_V7_RELEASE_PROFILE_V1,
    SpotV7ReleaseCandidateManifestV1,
    SpotV7ReleaseCandidateRejectV1,
    check_exact_spot_v7_release_candidate_manifest_v1,
)

MAX_U64_V1: Final = (1 << 64) - 1
MAX_U32_V1: Final = (1 << 32) - 1
MAX_SIGNER_REGISTRY_BYTES_V1: Final = 256 * 1_024
MAX_SIGNER_REGISTRY_JSON_DEPTH_V1: Final = 4
MAX_SIGNER_REGISTRY_JSON_ITEMS_V1: Final = 2_048
MAX_SIGNATURE_ENVELOPE_BYTES_V1: Final = 8 * 1_024
MAX_SIGNATURE_ENVELOPE_JSON_DEPTH_V1: Final = 2
MAX_SIGNATURE_ENVELOPE_JSON_ITEMS_V1: Final = 32
MAX_SIGNATURE_ENVELOPES_V1: Final = 128
MAX_AUTHENTICATION_EVIDENCE_BYTES_V1: Final = 2 * 1_024 * 1_024
SPOT_V7_RELEASE_REVOCATION_AUTHENTICATION_EVIDENCE_SCHEMA_V1: Final = (
    "zenodex.zrpf.spot_v7.release_revocation_authentication_evidence.v1"
)

_ROOT_RE: Final = re.compile(r"^0x[0-9a-f]{64}$")
_BARE_HEX_RE: Final = re.compile(r"^[0-9a-f]+$")
_TOKEN_RE: Final = re.compile(r"^[A-Za-z0-9._:-]{1,128}$")
_AUTHENTICATION_EVIDENCE_FIELDS_V1: Final = frozenset(
    {
        "current_candidate_bytes_hex",
        "external_trust_pins",
        "release_revocation_envelope_hex",
        "revocation_record_bytes_hex",
        "revocation_selector_input_bytes_hex",
        "revocation_selector_input_id",
        "schema",
        "signature_envelopes",
        "signature_quorum_report",
        "signer_registry",
    }
)
_EXTERNAL_TRUST_PIN_FIELDS_V1: Final = frozenset(
    {
        "application_id",
        "chain_id",
        "current_revocation_record_id",
        "domain_id",
        "expected_current_candidate_id",
        "expected_current_candidate_sha256",
        "expected_current_release_revision",
        "expected_current_select_input_id",
        "expected_database_revision",
        "expected_last_evaluation_epoch",
        "expected_quorum_threshold",
        "expected_revocation_effective_epoch",
        "expected_revocation_issuer_set_root",
        "expected_revocation_reason_code",
        "expected_revocation_record_id",
        "expected_revocation_record_revision",
        "expected_signer_registry_hash",
        "release_profile",
        "revocation_policy_root",
        "revocation_registry_root",
        "rollback_policy_root",
        "signer_registry_activation_epoch",
        "signer_registry_id",
        "signer_registry_revision",
        "signer_registry_revocation_epoch",
        "trusted_evaluation_epoch",
    }
)


class SpotV7ReleaseRevocationAuthenticationErrorV1(ValueError):
    """Stable fail-closed error from the release-revocation auth boundary."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def _reject(code: str, detail: str) -> SpotV7ReleaseRevocationAuthenticationErrorV1:
    return SpotV7ReleaseRevocationAuthenticationErrorV1(code, detail)


@final
@dataclass(frozen=True, slots=True)
class SpotV7ReleaseRevocationExternalTrustPinsV1:
    """Independent caller-supplied expectations carrying no authority."""

    application_id: str
    chain_id: str
    domain_id: str
    release_profile: str
    trusted_evaluation_epoch: int
    expected_database_revision: int
    expected_last_evaluation_epoch: int
    expected_current_candidate_id: bytes
    expected_current_candidate_sha256: bytes
    expected_current_release_revision: int
    expected_current_select_input_id: bytes
    current_revocation_record_id: bytes | None
    rollback_policy_root: bytes
    revocation_policy_root: bytes
    revocation_registry_root: bytes
    expected_revocation_record_id: bytes
    expected_revocation_effective_epoch: int
    expected_revocation_record_revision: int
    expected_revocation_reason_code: int
    expected_revocation_issuer_set_root: bytes
    signer_registry_id: str
    expected_signer_registry_hash: str
    signer_registry_revision: int
    signer_registry_activation_epoch: int
    signer_registry_revocation_epoch: int | None
    expected_quorum_threshold: int

    def __post_init__(self) -> None:
        _require_token(self.application_id, name="application_id")
        _require_token(self.chain_id, name="chain_id")
        _require_token(self.domain_id, name="domain_id")
        _require_token(self.release_profile, name="release_profile")
        if self.release_profile != SPOT_V7_RELEASE_PROFILE_V1:
            raise _reject("RELEASE_PROFILE_INVALID", "Spot V7 release profile required")
        if self.chain_id == self.domain_id:
            raise _reject("SCOPE_INVALID", "chain and domain identifiers must differ")
        _require_u64(self.trusted_evaluation_epoch, name="trusted_evaluation_epoch")
        _require_positive_u64(
            self.expected_database_revision,
            name="expected_database_revision",
        )
        _require_u64(
            self.expected_last_evaluation_epoch,
            name="expected_last_evaluation_epoch",
        )
        _require_digest(self.expected_current_candidate_id, name="expected_current_candidate_id")
        _require_digest(
            self.expected_current_candidate_sha256,
            name="expected_current_candidate_sha256",
        )
        _require_positive_u64(
            self.expected_current_release_revision,
            name="expected_current_release_revision",
        )
        _require_digest(
            self.expected_current_select_input_id,
            name="expected_current_select_input_id",
        )
        _require_optional_digest(
            self.current_revocation_record_id,
            name="current_revocation_record_id",
        )
        _require_digest(self.rollback_policy_root, name="rollback_policy_root")
        _require_digest(self.revocation_policy_root, name="revocation_policy_root")
        _require_digest(self.revocation_registry_root, name="revocation_registry_root")
        _require_digest(
            self.expected_revocation_record_id,
            name="expected_revocation_record_id",
        )
        _require_u64(
            self.expected_revocation_effective_epoch,
            name="expected_revocation_effective_epoch",
        )
        _require_positive_u64(
            self.expected_revocation_record_revision,
            name="expected_revocation_record_revision",
        )
        _require_positive_u32(
            self.expected_revocation_reason_code,
            name="expected_revocation_reason_code",
        )
        _require_digest(
            self.expected_revocation_issuer_set_root,
            name="expected_revocation_issuer_set_root",
        )
        _require_token(self.signer_registry_id, name="signer_registry_id")
        _require_root(
            self.expected_signer_registry_hash,
            name="expected_signer_registry_hash",
        )
        _require_positive_u64(
            self.signer_registry_revision,
            name="signer_registry_revision",
        )
        activation = _require_u64(
            self.signer_registry_activation_epoch,
            name="signer_registry_activation_epoch",
        )
        revocation = _require_optional_u64(
            self.signer_registry_revocation_epoch,
            name="signer_registry_revocation_epoch",
        )
        if revocation is not None and revocation <= activation:
            raise _reject(
                "REGISTRY_LIFECYCLE_INVALID",
                "signer registry revocation must follow activation",
            )
        _require_positive_u64(
            self.expected_quorum_threshold,
            name="expected_quorum_threshold",
        )

    @property
    def release_governed_registry_pin_authenticated(self) -> bool:
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


@dataclass(frozen=True, slots=True)
class _RevocationArtifactsV1:
    selector: GovernedReleaseSelectorInputV1
    candidate: SpotV7ReleaseCandidateManifestV1
    record: SpotV7RevocationRecordV1
    application_id: str
    chain_id: str
    domain_id: str
    release_profile: str
    parent_candidate_id: bytes | None
    minimum_rollback_revision: int
    rollback_policy_root: bytes
    revocation_policy_root: bytes
    activation_epoch: int
    expiration_epoch: int | None


@dataclass(frozen=True, slots=True)
class _ParsedAuthenticationEvidenceV1:
    envelope_bytes: bytes
    selector_input_bytes: bytes
    expected_selector_input_id: bytes
    candidate_bytes: bytes
    record_bytes: bytes
    pins: SpotV7ReleaseRevocationExternalTrustPinsV1
    external_trust_pins_bytes: bytes
    registry: dict[str, Any]
    signer_registry_bytes: bytes
    envelopes: tuple[dict[str, Any], ...]
    signature_envelopes_bytes: bytes
    report: dict[str, Any]
    quorum_report_bytes: bytes


class _AuthenticatedReleaseRevocationDurableArtifactsSealV1:
    __slots__ = ()


_AUTHENTICATED_DURABLE_ARTIFACTS_SEAL_V1 = _AuthenticatedReleaseRevocationDurableArtifactsSealV1()


@final
@dataclass(frozen=True, slots=True, init=False)
class _AuthenticatedReleaseRevocationDurableArtifactsV1:
    """Private immutable bytes-only handoff to a future revocation store."""

    envelope_bytes: bytes
    revocation_selector_input_bytes: bytes
    current_candidate_bytes: bytes
    revocation_record_bytes: bytes
    signer_registry_bytes: bytes
    signature_envelopes_bytes: bytes
    quorum_report_bytes: bytes
    external_trust_pins_bytes: bytes
    authentication_evidence_bytes: bytes

    def __new__(cls) -> _AuthenticatedReleaseRevocationDurableArtifactsV1:
        raise TypeError("authenticated durable artifacts require revalidated construction")

    @classmethod
    def _from_revalidated(
        cls,
        *,
        envelope_bytes: bytes,
        revocation_selector_input_bytes: bytes,
        current_candidate_bytes: bytes,
        revocation_record_bytes: bytes,
        signer_registry_bytes: bytes,
        signature_envelopes_bytes: bytes,
        quorum_report_bytes: bytes,
        external_trust_pins_bytes: bytes,
        authentication_evidence_bytes: bytes,
        seal: _AuthenticatedReleaseRevocationDurableArtifactsSealV1,
    ) -> _AuthenticatedReleaseRevocationDurableArtifactsV1:
        if seal is not _AUTHENTICATED_DURABLE_ARTIFACTS_SEAL_V1:
            raise TypeError("authenticated durable artifacts require the module-private seal")
        values = {
            "authentication_evidence_bytes": authentication_evidence_bytes,
            "current_candidate_bytes": current_candidate_bytes,
            "envelope_bytes": envelope_bytes,
            "external_trust_pins_bytes": external_trust_pins_bytes,
            "quorum_report_bytes": quorum_report_bytes,
            "revocation_record_bytes": revocation_record_bytes,
            "revocation_selector_input_bytes": revocation_selector_input_bytes,
            "signature_envelopes_bytes": signature_envelopes_bytes,
            "signer_registry_bytes": signer_registry_bytes,
        }
        for name, value in values.items():
            if type(value) is not bytes or not value:
                raise TypeError(f"{name} must be exact nonempty bytes")
        output = object.__new__(cls)
        for name, value in values.items():
            object.__setattr__(output, name, value)
        return output

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated durable artifacts cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated durable artifacts cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated durable artifacts cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("authenticated durable artifacts cannot be serialized")

    @property
    def durable_revocation_committed(self) -> bool:
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


class _AuthenticatedReleaseRevocationSealV1:
    __slots__ = ()


_AUTHENTICATED_RELEASE_REVOCATION_SEAL_V1 = _AuthenticatedReleaseRevocationSealV1()


@final
class _AuthenticatedSpotV7ReleaseRevocationV1:
    """Private non-copyable result of exact artifact and quorum verification."""

    __slots__ = (
        "_candidate_id",
        "_candidate_sha256",
        "_chain_id",
        "_current_release_revision",
        "_current_select_input_id",
        "_domain_id",
        "_evaluation_epoch",
        "_evidence_bytes",
        "_evidence_sha256",
        "_quorum_report_hash",
        "_quorum_threshold",
        "_revocation_effective_epoch",
        "_revocation_issuer_set_root",
        "_revocation_reason_code",
        "_revocation_record_id",
        "_revocation_record_revision",
        "_revocation_selector_input_id",
        "_seal",
        "_signer_registry_hash",
        "_signer_registry_revision",
    )

    _candidate_id: bytes
    _candidate_sha256: bytes
    _chain_id: str
    _current_release_revision: int
    _current_select_input_id: bytes
    _domain_id: str
    _evaluation_epoch: int
    _evidence_bytes: bytes
    _evidence_sha256: str
    _quorum_report_hash: str
    _quorum_threshold: int
    _revocation_effective_epoch: int
    _revocation_issuer_set_root: bytes
    _revocation_reason_code: int
    _revocation_record_id: bytes
    _revocation_record_revision: int
    _revocation_selector_input_id: bytes
    _seal: _AuthenticatedReleaseRevocationSealV1
    _signer_registry_hash: str
    _signer_registry_revision: int

    def __new__(cls) -> _AuthenticatedSpotV7ReleaseRevocationV1:
        raise TypeError("authenticated release revocation requires verified construction")

    @classmethod
    def _from_verified(
        cls,
        *,
        envelope: SpotV7ReleaseRevocationEnvelopeV1,
        evidence_bytes: bytes,
        quorum_report_hash: str,
        seal: _AuthenticatedReleaseRevocationSealV1,
    ) -> _AuthenticatedSpotV7ReleaseRevocationV1:
        if seal is not _AUTHENTICATED_RELEASE_REVOCATION_SEAL_V1:
            raise TypeError("authenticated release revocation requires the module-private seal")
        if type(envelope) is not SpotV7ReleaseRevocationEnvelopeV1:
            raise TypeError("authenticated release revocation requires exact envelope facts")
        if type(evidence_bytes) is not bytes or not evidence_bytes:
            raise TypeError("authenticated release revocation requires exact evidence bytes")
        value = object.__new__(cls)
        assignments = {
            "_candidate_id": envelope.current_candidate_id,
            "_candidate_sha256": envelope.current_candidate_sha256,
            "_chain_id": envelope.chain_id,
            "_current_release_revision": envelope.current_release_revision,
            "_current_select_input_id": envelope.current_select_input_id,
            "_domain_id": envelope.domain_id,
            "_evaluation_epoch": envelope.evaluation_epoch,
            "_evidence_bytes": evidence_bytes,
            "_evidence_sha256": hashlib.sha256(evidence_bytes).hexdigest(),
            "_quorum_report_hash": quorum_report_hash,
            "_quorum_threshold": envelope.quorum_threshold,
            "_revocation_effective_epoch": envelope.revocation_effective_epoch,
            "_revocation_issuer_set_root": envelope.revocation_issuer_set_root,
            "_revocation_reason_code": envelope.revocation_reason_code,
            "_revocation_record_id": envelope.revocation_record_id,
            "_revocation_record_revision": envelope.revocation_record_revision,
            "_revocation_selector_input_id": envelope.revocation_selector_input_id,
            "_seal": seal,
            "_signer_registry_hash": envelope.signer_registry_hash,
            "_signer_registry_revision": envelope.signer_registry_revision,
        }
        for name, assignment in assignments.items():
            object.__setattr__(value, name, assignment)
        return value

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("authenticated release revocation cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated release revocation cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated release revocation cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated release revocation cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("authenticated release revocation cannot be serialized")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _AUTHENTICATED_RELEASE_REVOCATION_SEAL_V1

    def _artifacts_for_durable_store_v1(
        self,
    ) -> _AuthenticatedReleaseRevocationDurableArtifactsV1:
        return _revalidate_durable_artifacts_v1(self)

    @property
    def revocation_selector_input_id(self) -> bytes:
        return self._revocation_selector_input_id

    @property
    def current_candidate_id(self) -> bytes:
        return self._candidate_id

    @property
    def current_candidate_sha256(self) -> bytes:
        return self._candidate_sha256

    @property
    def current_release_revision(self) -> int:
        return self._current_release_revision

    @property
    def current_select_input_id(self) -> bytes:
        return self._current_select_input_id

    @property
    def revocation_record_id(self) -> bytes:
        return self._revocation_record_id

    @property
    def revocation_effective_epoch(self) -> int:
        return self._revocation_effective_epoch

    @property
    def revocation_record_revision(self) -> int:
        return self._revocation_record_revision

    @property
    def revocation_reason_code(self) -> int:
        return self._revocation_reason_code

    @property
    def revocation_issuer_set_root(self) -> bytes:
        return self._revocation_issuer_set_root

    @property
    def evaluation_epoch(self) -> int:
        return self._evaluation_epoch

    @property
    def chain_id(self) -> str:
        return self._chain_id

    @property
    def domain_id(self) -> str:
        return self._domain_id

    @property
    def signer_registry_hash(self) -> str:
        return self._signer_registry_hash

    @property
    def signer_registry_revision(self) -> int:
        return self._signer_registry_revision

    @property
    def quorum_threshold(self) -> int:
        return self._quorum_threshold

    @property
    def quorum_report_hash(self) -> str:
        return self._quorum_report_hash

    @property
    def evidence_sha256(self) -> str:
        if hashlib.sha256(self._evidence_bytes).hexdigest() != self._evidence_sha256:
            raise RuntimeError("authenticated release revocation evidence drift")
        return self._evidence_sha256

    @property
    def signature_quorum_authenticated(self) -> bool:
        return True

    @property
    def exact_current_selection_bound(self) -> bool:
        return True

    @property
    def exact_revocation_record_bound(self) -> bool:
        return True

    @property
    def release_governed_registry_pin_authenticated(self) -> bool:
        return False

    @property
    def durable_revocation_committed(self) -> bool:
        return False

    @property
    def replay_prevention_established(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
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


def build_spot_v7_release_revocation_envelope_v1(
    *,
    revocation_selector_input_bytes: bytes,
    expected_revocation_selector_input_id: bytes,
    current_candidate_bytes: bytes,
    revocation_record_bytes: bytes,
    expected_revocation_record_id: bytes,
    external_trust_pins: SpotV7ReleaseRevocationExternalTrustPinsV1,
    trusted_signer_registry: object,
) -> bytes:
    """Build exact signer-review bytes after all external-pin cross-checks."""

    pins = _require_exact_pins(external_trust_pins)
    artifacts = _authenticate_artifact_bindings(
        selector_input_bytes=revocation_selector_input_bytes,
        expected_selector_input_id=expected_revocation_selector_input_id,
        candidate_bytes=current_candidate_bytes,
        record_bytes=revocation_record_bytes,
        expected_record_id=expected_revocation_record_id,
        pins=pins,
    )
    registry = _snapshot_and_validate_registry(trusted_signer_registry)
    _require_registry_binding(registry=registry, pins=pins)
    return _recompose_envelope(artifacts=artifacts, pins=pins, registry=registry)


def authenticate_spot_v7_release_revocation_v1(
    raw_envelope: bytes,
    *,
    revocation_selector_input_bytes: bytes,
    expected_revocation_selector_input_id: bytes,
    current_candidate_bytes: bytes,
    revocation_record_bytes: bytes,
    expected_revocation_record_id: bytes,
    external_trust_pins: SpotV7ReleaseRevocationExternalTrustPinsV1,
    trusted_signer_registry: object,
    signature_envelopes: object,
) -> _AuthenticatedSpotV7ReleaseRevocationV1:
    """Authenticate one exact revocation statement without granting authority."""

    try:
        parsed = parse_exact_spot_v7_release_revocation_envelope_v1(raw_envelope)
    except SpotV7ReleaseRevocationEnvelopeRejectV1 as exc:
        raise _reject("REVOCATION_ENVELOPE_INVALID", str(exc)) from exc
    pins = _require_exact_pins(external_trust_pins)
    artifacts = _authenticate_artifact_bindings(
        selector_input_bytes=revocation_selector_input_bytes,
        expected_selector_input_id=expected_revocation_selector_input_id,
        candidate_bytes=current_candidate_bytes,
        record_bytes=revocation_record_bytes,
        expected_record_id=expected_revocation_record_id,
        pins=pins,
    )
    registry = _snapshot_and_validate_registry(trusted_signer_registry)
    _require_registry_binding(registry=registry, pins=pins)
    expected_envelope = _recompose_envelope(artifacts=artifacts, pins=pins, registry=registry)
    if raw_envelope != expected_envelope:
        raise _reject(
            "REVOCATION_ENVELOPE_BINDING_MISMATCH",
            "signed envelope differs from exact selector, candidate, record, or trust pins",
        )
    envelopes = _snapshot_signature_envelopes(signature_envelopes)
    try:
        report = verify_signature_quorum_v0(
            registry=registry,
            payload_kind=SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
            payload_hash=spot_v7_release_revocation_envelope_payload_hash_v1(raw_envelope),
            envelopes=envelopes,
        )
    except (RuntimeError, TypeError, ValueError) as exc:
        raise _reject("SIGNATURE_QUORUM_INVALID", str(exc)) from exc
    quorum_report_hash = _require_root(
        report.get("quorum_report_hash"),
        name="quorum_report_hash",
    )
    if report.get("registry_hash") != pins.expected_signer_registry_hash:
        raise _reject("QUORUM_REPORT_REGISTRY_MISMATCH", "quorum report registry drift")
    if report.get("threshold") != pins.expected_quorum_threshold:
        raise _reject("QUORUM_REPORT_THRESHOLD_MISMATCH", "quorum report threshold drift")
    evidence = _build_evidence(
        raw_envelope=raw_envelope,
        selector_input_bytes=revocation_selector_input_bytes,
        expected_selector_input_id=expected_revocation_selector_input_id,
        candidate_bytes=current_candidate_bytes,
        record_bytes=revocation_record_bytes,
        pins=pins,
        registry=registry,
        envelopes=envelopes,
        report=report,
    )
    return _AuthenticatedSpotV7ReleaseRevocationV1._from_verified(
        envelope=parsed,
        evidence_bytes=evidence,
        quorum_report_hash=quorum_report_hash,
        seal=_AUTHENTICATED_RELEASE_REVOCATION_SEAL_V1,
    )


def _revalidate_durable_artifacts_v1(
    value: _AuthenticatedSpotV7ReleaseRevocationV1,
) -> _AuthenticatedReleaseRevocationDurableArtifactsV1:
    if type(value) is not _AuthenticatedSpotV7ReleaseRevocationV1 or not value._has_private_seal():
        raise _reject(
            "AUTHENTICATED_REVOCATION_REQUIRED",
            "durable handoff requires the exact sealed revocation capability",
        )
    if hashlib.sha256(value._evidence_bytes).hexdigest() != value._evidence_sha256:
        raise _reject(
            "AUTHENTICATION_EVIDENCE_DRIFT",
            "retained authentication evidence hash changed",
        )
    retained = _parse_authentication_evidence_v1(value._evidence_bytes)
    artifacts = _authenticate_artifact_bindings(
        selector_input_bytes=retained.selector_input_bytes,
        expected_selector_input_id=retained.expected_selector_input_id,
        candidate_bytes=retained.candidate_bytes,
        record_bytes=retained.record_bytes,
        expected_record_id=retained.pins.expected_revocation_record_id,
        pins=retained.pins,
    )
    _require_registry_binding(registry=retained.registry, pins=retained.pins)
    expected_envelope = _recompose_envelope(
        artifacts=artifacts,
        pins=retained.pins,
        registry=retained.registry,
    )
    if expected_envelope != retained.envelope_bytes:
        raise _reject(
            "RETAINED_ENVELOPE_RECOMPOSITION_MISMATCH",
            "retained envelope does not recompose from exact artifacts and pins",
        )
    parsed_envelope = parse_exact_spot_v7_release_revocation_envelope_v1(retained.envelope_bytes)
    report = _reverify_retained_quorum(retained)
    rebuilt_evidence = _build_evidence(
        raw_envelope=retained.envelope_bytes,
        selector_input_bytes=retained.selector_input_bytes,
        expected_selector_input_id=retained.expected_selector_input_id,
        candidate_bytes=retained.candidate_bytes,
        record_bytes=retained.record_bytes,
        pins=retained.pins,
        registry=retained.registry,
        envelopes=retained.envelopes,
        report=report,
    )
    if rebuilt_evidence != value._evidence_bytes:
        raise _reject(
            "AUTHENTICATION_EVIDENCE_RECOMPOSITION_MISMATCH",
            "retained evidence does not recompose from exact verified parts",
        )
    _require_retained_capability_binding(
        value=value,
        envelope=parsed_envelope,
        report=report,
    )
    return _AuthenticatedReleaseRevocationDurableArtifactsV1._from_revalidated(
        envelope_bytes=_fresh_bytes(retained.envelope_bytes),
        revocation_selector_input_bytes=_fresh_bytes(retained.selector_input_bytes),
        current_candidate_bytes=_fresh_bytes(retained.candidate_bytes),
        revocation_record_bytes=_fresh_bytes(retained.record_bytes),
        signer_registry_bytes=_fresh_bytes(retained.signer_registry_bytes),
        signature_envelopes_bytes=_fresh_bytes(retained.signature_envelopes_bytes),
        quorum_report_bytes=_fresh_bytes(retained.quorum_report_bytes),
        external_trust_pins_bytes=_fresh_bytes(retained.external_trust_pins_bytes),
        authentication_evidence_bytes=_fresh_bytes(value._evidence_bytes),
        seal=_AUTHENTICATED_DURABLE_ARTIFACTS_SEAL_V1,
    )


def _authenticate_artifact_bindings(
    *,
    selector_input_bytes: bytes,
    expected_selector_input_id: bytes,
    candidate_bytes: bytes,
    record_bytes: bytes,
    expected_record_id: bytes,
    pins: SpotV7ReleaseRevocationExternalTrustPinsV1,
) -> _RevocationArtifactsV1:
    if pins.current_revocation_record_id is not None:
        raise _reject(
            "CURRENT_SELECTION_ALREADY_REVOKED",
            "current release selection already carries a revocation record",
        )
    if pins.trusted_evaluation_epoch < pins.expected_last_evaluation_epoch:
        raise _reject(
            "EVALUATION_EPOCH_ROLLBACK",
            "trusted evaluation precedes the current durable cursor",
        )
    try:
        selector = parse_exact_governed_release_selector_input_v1(
            selector_input_bytes,
            expected_input_id=expected_selector_input_id,
        )
    except (SpotV7SelectorInputRejectV1, TypeError, ValueError) as exc:
        raise _reject("REVOCATION_SELECTOR_INVALID", str(exc)) from exc
    if selector.operation is not SelectorOperationV1.REVOKE:
        raise _reject("REVOKE_OPERATION_REQUIRED", "only release revocation is supported")
    try:
        candidate = check_exact_spot_v7_release_candidate_manifest_v1(
            candidate_bytes,
            expected_candidate_id=selector.target_candidate_id,
        )
    except (SpotV7ReleaseCandidateRejectV1, TypeError, ValueError) as exc:
        raise _reject("CURRENT_CANDIDATE_INVALID", str(exc)) from exc
    try:
        record = parse_exact_spot_v7_revocation_record_v1(
            record_bytes,
            expected_record_id=expected_record_id,
        )
    except (SpotV7SelectorInputRejectV1, TypeError, ValueError) as exc:
        raise _reject("REVOCATION_RECORD_INVALID", str(exc)) from exc
    document = cast(dict[str, Any], json.loads(candidate.canonical_bytes))
    scope = cast(dict[str, Any], document["scope"])
    lineage = cast(dict[str, Any], document["lineage"])
    artifacts = _RevocationArtifactsV1(
        selector=selector,
        candidate=candidate,
        record=record,
        application_id=str(scope["application_id"]),
        chain_id=str(scope["chain_id"]),
        domain_id=str(scope["domain_id"]),
        release_profile=str(scope["release_profile"]),
        parent_candidate_id=candidate.parent_candidate_id,
        minimum_rollback_revision=int(lineage["minimum_rollback_revision"]),
        rollback_policy_root=bytes.fromhex(str(lineage["rollback_policy_root"])),
        revocation_policy_root=bytes.fromhex(str(lineage["revocation_policy_root"])),
        activation_epoch=int(lineage["proposed_activation_epoch"]),
        expiration_epoch=(
            None
            if lineage["proposed_expiration_epoch"] is None
            else int(lineage["proposed_expiration_epoch"])
        ),
    )
    _require_revocation_binding(artifacts=artifacts, pins=pins, lineage=lineage)
    return artifacts


def _require_revocation_binding(
    *,
    artifacts: _RevocationArtifactsV1,
    pins: SpotV7ReleaseRevocationExternalTrustPinsV1,
    lineage: Mapping[str, Any],
) -> None:
    selector = artifacts.selector
    candidate = artifacts.candidate
    record = artifacts.record
    candidate_sha256 = hashlib.sha256(candidate.canonical_bytes).digest()
    checks: tuple[tuple[bool, str], ...] = (
        (selector.evaluation_epoch == pins.trusted_evaluation_epoch, "EVALUATION_EPOCH_MISMATCH"),
        (
            selector.expected_database_revision == pins.expected_database_revision,
            "DATABASE_REVISION_MISMATCH",
        ),
        (
            selector.expected_current_candidate_id == pins.expected_current_candidate_id,
            "CURRENT_CANDIDATE_MISMATCH",
        ),
        (
            selector.expected_current_select_input_id == pins.expected_current_select_input_id,
            "CURRENT_SELECTOR_MISMATCH",
        ),
        (
            selector.target_candidate_id == pins.expected_current_candidate_id,
            "TARGET_CANDIDATE_MISMATCH",
        ),
        (
            selector.target_candidate_sha256 == pins.expected_current_candidate_sha256,
            "CURRENT_CANDIDATE_SHA256_MISMATCH",
        ),
        (
            candidate_sha256 == pins.expected_current_candidate_sha256,
            "CURRENT_CANDIDATE_SHA256_MISMATCH",
        ),
        (
            candidate.release_revision == pins.expected_current_release_revision,
            "CURRENT_RELEASE_REVISION_MISMATCH",
        ),
        (
            selector.target_release_revision == pins.expected_current_release_revision,
            "TARGET_RELEASE_REVISION_MISMATCH",
        ),
        (artifacts.application_id == pins.application_id, "APPLICATION_ID_MISMATCH"),
        (artifacts.chain_id == pins.chain_id, "CHAIN_ID_MISMATCH"),
        (artifacts.domain_id == pins.domain_id, "DOMAIN_ID_MISMATCH"),
        (artifacts.release_profile == pins.release_profile, "RELEASE_PROFILE_MISMATCH"),
        (artifacts.rollback_policy_root == pins.rollback_policy_root, "ROLLBACK_POLICY_MISMATCH"),
        (
            selector.rollback_policy_root == pins.rollback_policy_root,
            "SELECTOR_ROLLBACK_POLICY_MISMATCH",
        ),
        (
            artifacts.revocation_policy_root == pins.revocation_policy_root,
            "REVOCATION_POLICY_MISMATCH",
        ),
        (
            record.revocation_policy_root == pins.revocation_policy_root,
            "RECORD_REVOCATION_POLICY_MISMATCH",
        ),
        (
            selector.revocation_registry_root == pins.revocation_registry_root,
            "SELECTOR_REVOCATION_REGISTRY_MISMATCH",
        ),
        (
            record.revocation_registry_root == pins.revocation_registry_root,
            "RECORD_REVOCATION_REGISTRY_MISMATCH",
        ),
        (selector.revocation_record_id == record.record_id, "SELECTOR_REVOCATION_RECORD_MISMATCH"),
        (record.record_id == pins.expected_revocation_record_id, "REVOCATION_RECORD_ID_MISMATCH"),
        (record.candidate_id == candidate.candidate_id, "REVOCATION_CANDIDATE_MISMATCH"),
        (
            record.effective_epoch == pins.expected_revocation_effective_epoch,
            "REVOCATION_EFFECTIVE_EPOCH_MISMATCH",
        ),
        (
            record.record_revision == pins.expected_revocation_record_revision,
            "REVOCATION_RECORD_REVISION_MISMATCH",
        ),
        (record.reason_code == pins.expected_revocation_reason_code, "REVOCATION_REASON_MISMATCH"),
        (
            record.issuer_set_root == pins.expected_revocation_issuer_set_root,
            "REVOCATION_ISSUER_SET_MISMATCH",
        ),
        (lineage["revocation_record_root"] is None, "CURRENT_CANDIDATE_ALREADY_REVOKED"),
    )
    for accepted, code in checks:
        if not accepted:
            raise _reject(code, "release-revocation binding differs from external trust pins")
    if record.effective_epoch > pins.trusted_evaluation_epoch:
        raise _reject(
            "REVOCATION_EFFECTIVE_EPOCH_FUTURE",
            "revocation effective epoch follows trusted evaluation",
        )


def _snapshot_and_validate_registry(value: object) -> dict[str, Any]:
    if type(value) is not dict:
        raise _reject("EXACT_SIGNER_REGISTRY_REQUIRED", "signer registry must be an exact dict")
    try:
        bounded_json_utf8_size(
            value,
            max_bytes=MAX_SIGNER_REGISTRY_BYTES_V1,
            max_depth=MAX_SIGNER_REGISTRY_JSON_DEPTH_V1,
            max_items=MAX_SIGNER_REGISTRY_JSON_ITEMS_V1,
        )
    except (TypeError, ValueError) as exc:
        raise _reject(
            "SIGNER_REGISTRY_SIZE",
            "signer registry exceeds the bounded in-memory JSON profile",
        ) from exc
    try:
        raw = canonical_json_bytes(value)
    except (TypeError, ValueError) as exc:
        raise _reject("SIGNER_REGISTRY_INVALID", str(exc)) from exc
    if not raw or len(raw) > MAX_SIGNER_REGISTRY_BYTES_V1:
        raise _reject("SIGNER_REGISTRY_SIZE", "signer registry is empty or oversized")
    snapshot = cast(dict[str, Any], json.loads(raw))
    try:
        validate_signer_registry_v0(snapshot)
    except (RuntimeError, TypeError, ValueError) as exc:
        raise _reject("SIGNER_REGISTRY_INVALID", str(exc)) from exc
    return snapshot


def _require_registry_binding(
    *,
    registry: Mapping[str, Any],
    pins: SpotV7ReleaseRevocationExternalTrustPinsV1,
) -> None:
    checks = (
        (registry.get("registry_id") == pins.signer_registry_id, "SIGNER_REGISTRY_ID_MISMATCH"),
        (
            registry.get("registry_hash") == pins.expected_signer_registry_hash,
            "SIGNER_REGISTRY_HASH_MISMATCH",
        ),
        (
            registry.get("payload_kind") == SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
            "SIGNER_REGISTRY_PAYLOAD_KIND_MISMATCH",
        ),
        (
            registry.get("threshold") == pins.expected_quorum_threshold,
            "SIGNER_REGISTRY_THRESHOLD_MISMATCH",
        ),
    )
    for accepted, code in checks:
        if not accepted:
            raise _reject(code, "canonical signer registry differs from external trust pins")
    epoch = pins.trusted_evaluation_epoch
    if epoch < pins.signer_registry_activation_epoch:
        raise _reject("SIGNER_REGISTRY_INACTIVE", "signer registry has not activated")
    if (
        pins.signer_registry_revocation_epoch is not None
        and epoch >= pins.signer_registry_revocation_epoch
    ):
        raise _reject("SIGNER_REGISTRY_REVOKED", "signer registry is revoked")


def _snapshot_signature_envelopes(value: object) -> tuple[dict[str, Any], ...]:
    if type(value) not in {list, tuple}:
        raise _reject(
            "EXACT_SIGNATURE_SET_REQUIRED", "signature set must be an exact list or tuple"
        )
    sequence = cast(Sequence[object], value)
    if not sequence or len(sequence) > MAX_SIGNATURE_ENVELOPES_V1:
        raise _reject("SIGNATURE_SET_SIZE", "signature set is empty or oversized")
    output: list[dict[str, Any]] = []
    for index, item in enumerate(sequence):
        if type(item) is not dict:
            raise _reject(
                "EXACT_SIGNATURE_ENVELOPE_REQUIRED",
                f"signature_envelopes[{index}] must be an exact dict",
            )
        try:
            bounded_json_utf8_size(
                item,
                max_bytes=MAX_SIGNATURE_ENVELOPE_BYTES_V1,
                max_depth=MAX_SIGNATURE_ENVELOPE_JSON_DEPTH_V1,
                max_items=MAX_SIGNATURE_ENVELOPE_JSON_ITEMS_V1,
            )
        except (TypeError, ValueError) as exc:
            raise _reject(
                "SIGNATURE_ENVELOPE_SIZE",
                f"signature_envelopes[{index}] exceeds the bounded in-memory JSON profile",
            ) from exc
        try:
            raw = canonical_json_bytes(item)
        except (TypeError, ValueError) as exc:
            raise _reject("SIGNATURE_ENVELOPE_INVALID", str(exc)) from exc
        if not raw or len(raw) > MAX_SIGNATURE_ENVELOPE_BYTES_V1:
            raise _reject("SIGNATURE_ENVELOPE_SIZE", "signature envelope is oversized")
        output.append(cast(dict[str, Any], json.loads(raw)))
    output.sort(key=canonical_json_bytes)
    return tuple(output)


def _recompose_envelope(
    *,
    artifacts: _RevocationArtifactsV1,
    pins: SpotV7ReleaseRevocationExternalTrustPinsV1,
    registry: Mapping[str, Any],
) -> bytes:
    return recompose_spot_v7_release_revocation_envelope_v1(
        revocation_selector_input_id=artifacts.selector.input_id,
        current_candidate_id=artifacts.candidate.candidate_id,
        current_candidate_sha256=hashlib.sha256(artifacts.candidate.canonical_bytes).digest(),
        current_release_revision=artifacts.candidate.release_revision,
        current_select_input_id=pins.expected_current_select_input_id,
        expected_database_revision=artifacts.selector.expected_database_revision,
        last_evaluation_epoch=pins.expected_last_evaluation_epoch,
        evaluation_epoch=artifacts.selector.evaluation_epoch,
        current_parent_candidate_id=artifacts.parent_candidate_id,
        minimum_rollback_revision=artifacts.minimum_rollback_revision,
        rollback_policy_root=artifacts.rollback_policy_root,
        candidate_activation_epoch=artifacts.activation_epoch,
        candidate_expiration_epoch=artifacts.expiration_epoch,
        revocation_record_id=artifacts.record.record_id,
        revocation_record_sha256=hashlib.sha256(artifacts.record.canonical_bytes).digest(),
        revocation_effective_epoch=artifacts.record.effective_epoch,
        revocation_record_revision=artifacts.record.record_revision,
        revocation_reason_code=artifacts.record.reason_code,
        revocation_issuer_set_root=artifacts.record.issuer_set_root,
        revocation_policy_root=artifacts.record.revocation_policy_root,
        revocation_registry_root=artifacts.record.revocation_registry_root,
        application_id=artifacts.application_id,
        chain_id=artifacts.chain_id,
        domain_id=artifacts.domain_id,
        release_profile=artifacts.release_profile,
        signer_registry_id=pins.signer_registry_id,
        signer_registry_hash=cast(str, registry["registry_hash"]),
        signer_registry_revision=pins.signer_registry_revision,
        signer_registry_activation_epoch=pins.signer_registry_activation_epoch,
        signer_registry_revocation_epoch=pins.signer_registry_revocation_epoch,
        quorum_threshold=cast(int, registry["threshold"]),
    )


def _build_evidence(
    *,
    raw_envelope: bytes,
    selector_input_bytes: bytes,
    expected_selector_input_id: bytes,
    candidate_bytes: bytes,
    record_bytes: bytes,
    pins: SpotV7ReleaseRevocationExternalTrustPinsV1,
    registry: dict[str, Any],
    envelopes: tuple[dict[str, Any], ...],
    report: dict[str, Any],
) -> bytes:
    return canonical_json_bytes(
        {
            "current_candidate_bytes_hex": candidate_bytes.hex(),
            "external_trust_pins": _pins_document(pins),
            "release_revocation_envelope_hex": raw_envelope.hex(),
            "revocation_record_bytes_hex": record_bytes.hex(),
            "revocation_selector_input_bytes_hex": selector_input_bytes.hex(),
            "revocation_selector_input_id": "0x" + expected_selector_input_id.hex(),
            "schema": SPOT_V7_RELEASE_REVOCATION_AUTHENTICATION_EVIDENCE_SCHEMA_V1,
            "signature_envelopes": list(deepcopy(envelopes)),
            "signature_quorum_report": deepcopy(report),
            "signer_registry": deepcopy(registry),
        }
    )


def _pins_document(pins: SpotV7ReleaseRevocationExternalTrustPinsV1) -> dict[str, object]:
    return {
        "application_id": pins.application_id,
        "chain_id": pins.chain_id,
        "current_revocation_record_id": _optional_digest_document(
            pins.current_revocation_record_id
        ),
        "domain_id": pins.domain_id,
        "expected_current_candidate_id": "0x" + pins.expected_current_candidate_id.hex(),
        "expected_current_candidate_sha256": ("0x" + pins.expected_current_candidate_sha256.hex()),
        "expected_current_release_revision": pins.expected_current_release_revision,
        "expected_current_select_input_id": ("0x" + pins.expected_current_select_input_id.hex()),
        "expected_database_revision": pins.expected_database_revision,
        "expected_last_evaluation_epoch": pins.expected_last_evaluation_epoch,
        "expected_quorum_threshold": pins.expected_quorum_threshold,
        "expected_revocation_effective_epoch": pins.expected_revocation_effective_epoch,
        "expected_revocation_issuer_set_root": (
            "0x" + pins.expected_revocation_issuer_set_root.hex()
        ),
        "expected_revocation_reason_code": pins.expected_revocation_reason_code,
        "expected_revocation_record_id": "0x" + pins.expected_revocation_record_id.hex(),
        "expected_revocation_record_revision": pins.expected_revocation_record_revision,
        "expected_signer_registry_hash": pins.expected_signer_registry_hash,
        "release_profile": pins.release_profile,
        "revocation_policy_root": "0x" + pins.revocation_policy_root.hex(),
        "revocation_registry_root": "0x" + pins.revocation_registry_root.hex(),
        "rollback_policy_root": "0x" + pins.rollback_policy_root.hex(),
        "signer_registry_activation_epoch": pins.signer_registry_activation_epoch,
        "signer_registry_id": pins.signer_registry_id,
        "signer_registry_revision": pins.signer_registry_revision,
        "signer_registry_revocation_epoch": pins.signer_registry_revocation_epoch,
        "trusted_evaluation_epoch": pins.trusted_evaluation_epoch,
    }


def _parse_authentication_evidence_v1(raw: bytes) -> _ParsedAuthenticationEvidenceV1:
    document = _decode_exact_authentication_evidence_v1(raw)
    pins_document = _require_exact_plain_dict(
        document["external_trust_pins"],
        expected=_EXTERNAL_TRUST_PIN_FIELDS_V1,
        name="external_trust_pins",
    )
    pins = _pins_from_document(pins_document)
    registry_document = _require_exact_plain_dict(
        document["signer_registry"],
        expected=None,
        name="signer_registry",
    )
    registry = _snapshot_and_validate_registry(registry_document)
    envelopes = _snapshot_signature_envelopes(document["signature_envelopes"])
    report = _require_exact_plain_dict(
        document["signature_quorum_report"],
        expected=None,
        name="signature_quorum_report",
    )
    return _ParsedAuthenticationEvidenceV1(
        envelope_bytes=_decode_evidence_hex(
            document["release_revocation_envelope_hex"],
            name="release_revocation_envelope_hex",
        ),
        selector_input_bytes=_decode_evidence_hex(
            document["revocation_selector_input_bytes_hex"],
            name="revocation_selector_input_bytes_hex",
        ),
        expected_selector_input_id=_root_string_to_digest(
            document["revocation_selector_input_id"],
            name="revocation_selector_input_id",
        ),
        candidate_bytes=_decode_evidence_hex(
            document["current_candidate_bytes_hex"],
            name="current_candidate_bytes_hex",
        ),
        record_bytes=_decode_evidence_hex(
            document["revocation_record_bytes_hex"],
            name="revocation_record_bytes_hex",
        ),
        pins=pins,
        external_trust_pins_bytes=canonical_json_bytes(pins_document),
        registry=registry,
        signer_registry_bytes=canonical_json_bytes(registry),
        envelopes=envelopes,
        signature_envelopes_bytes=canonical_json_bytes(list(envelopes)),
        report=report,
        quorum_report_bytes=canonical_json_bytes(report),
    )


def _decode_exact_authentication_evidence_v1(raw: bytes) -> dict[str, object]:
    if type(raw) is not bytes or not raw or len(raw) > MAX_AUTHENTICATION_EVIDENCE_BYTES_V1:
        raise _reject(
            "AUTHENTICATION_EVIDENCE_SIZE",
            "authentication evidence must be bounded nonempty exact bytes",
        )
    try:
        value = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_reject_evidence_duplicate_keys,
            parse_float=_reject_evidence_number,
            parse_constant=_reject_evidence_number,
        )
    except SpotV7ReleaseRevocationAuthenticationErrorV1:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject(
            "AUTHENTICATION_EVIDENCE_JSON",
            "authentication evidence is invalid JSON",
        ) from exc
    document = _require_exact_plain_dict(
        value,
        expected=_AUTHENTICATION_EVIDENCE_FIELDS_V1,
        name="authentication_evidence",
    )
    if document["schema"] != SPOT_V7_RELEASE_REVOCATION_AUTHENTICATION_EVIDENCE_SCHEMA_V1:
        raise _reject(
            "AUTHENTICATION_EVIDENCE_SCHEMA",
            "authentication evidence schema mismatch",
        )
    if canonical_json_bytes(document) != raw:
        raise _reject(
            "AUTHENTICATION_EVIDENCE_NONCANONICAL",
            "authentication evidence must be canonical JSON",
        )
    return document


def _pins_from_document(
    document: Mapping[str, object],
) -> SpotV7ReleaseRevocationExternalTrustPinsV1:
    return SpotV7ReleaseRevocationExternalTrustPinsV1(
        application_id=_require_token(document["application_id"], name="application_id"),
        chain_id=_require_token(document["chain_id"], name="chain_id"),
        domain_id=_require_token(document["domain_id"], name="domain_id"),
        release_profile=_require_token(document["release_profile"], name="release_profile"),
        trusted_evaluation_epoch=_require_u64(
            document["trusted_evaluation_epoch"],
            name="trusted_evaluation_epoch",
        ),
        expected_database_revision=_require_positive_u64(
            document["expected_database_revision"],
            name="expected_database_revision",
        ),
        expected_last_evaluation_epoch=_require_u64(
            document["expected_last_evaluation_epoch"],
            name="expected_last_evaluation_epoch",
        ),
        expected_current_candidate_id=_root_string_to_digest(
            document["expected_current_candidate_id"],
            name="expected_current_candidate_id",
        ),
        expected_current_candidate_sha256=_root_string_to_digest(
            document["expected_current_candidate_sha256"],
            name="expected_current_candidate_sha256",
        ),
        expected_current_release_revision=_require_positive_u64(
            document["expected_current_release_revision"],
            name="expected_current_release_revision",
        ),
        expected_current_select_input_id=_root_string_to_digest(
            document["expected_current_select_input_id"],
            name="expected_current_select_input_id",
        ),
        current_revocation_record_id=_optional_root_string_to_digest(
            document["current_revocation_record_id"],
            name="current_revocation_record_id",
        ),
        rollback_policy_root=_root_string_to_digest(
            document["rollback_policy_root"],
            name="rollback_policy_root",
        ),
        revocation_policy_root=_root_string_to_digest(
            document["revocation_policy_root"],
            name="revocation_policy_root",
        ),
        revocation_registry_root=_root_string_to_digest(
            document["revocation_registry_root"],
            name="revocation_registry_root",
        ),
        expected_revocation_record_id=_root_string_to_digest(
            document["expected_revocation_record_id"],
            name="expected_revocation_record_id",
        ),
        expected_revocation_effective_epoch=_require_u64(
            document["expected_revocation_effective_epoch"],
            name="expected_revocation_effective_epoch",
        ),
        expected_revocation_record_revision=_require_positive_u64(
            document["expected_revocation_record_revision"],
            name="expected_revocation_record_revision",
        ),
        expected_revocation_reason_code=_require_positive_u32(
            document["expected_revocation_reason_code"],
            name="expected_revocation_reason_code",
        ),
        expected_revocation_issuer_set_root=_root_string_to_digest(
            document["expected_revocation_issuer_set_root"],
            name="expected_revocation_issuer_set_root",
        ),
        signer_registry_id=_require_token(
            document["signer_registry_id"],
            name="signer_registry_id",
        ),
        expected_signer_registry_hash=_require_root(
            document["expected_signer_registry_hash"],
            name="expected_signer_registry_hash",
        ),
        signer_registry_revision=_require_positive_u64(
            document["signer_registry_revision"],
            name="signer_registry_revision",
        ),
        signer_registry_activation_epoch=_require_u64(
            document["signer_registry_activation_epoch"],
            name="signer_registry_activation_epoch",
        ),
        signer_registry_revocation_epoch=_require_optional_u64(
            document["signer_registry_revocation_epoch"],
            name="signer_registry_revocation_epoch",
        ),
        expected_quorum_threshold=_require_positive_u64(
            document["expected_quorum_threshold"],
            name="expected_quorum_threshold",
        ),
    )


def _reverify_retained_quorum(
    retained: _ParsedAuthenticationEvidenceV1,
) -> dict[str, Any]:
    try:
        report = verify_signature_quorum_v0(
            registry=retained.registry,
            payload_kind=SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
            payload_hash=spot_v7_release_revocation_envelope_payload_hash_v1(
                retained.envelope_bytes
            ),
            envelopes=retained.envelopes,
        )
    except (RuntimeError, TypeError, ValueError) as exc:
        raise _reject("RETAINED_SIGNATURE_QUORUM_INVALID", str(exc)) from exc
    if canonical_json_bytes(report) != retained.quorum_report_bytes:
        raise _reject(
            "RETAINED_QUORUM_REPORT_MISMATCH",
            "retained quorum report does not match fresh verification",
        )
    return report


def _require_retained_capability_binding(
    *,
    value: _AuthenticatedSpotV7ReleaseRevocationV1,
    envelope: SpotV7ReleaseRevocationEnvelopeV1,
    report: Mapping[str, Any],
) -> None:
    checks = (
        (
            value._revocation_selector_input_id == envelope.revocation_selector_input_id,
            "selector_input_id",
        ),
        (value._candidate_id == envelope.current_candidate_id, "candidate_id"),
        (value._candidate_sha256 == envelope.current_candidate_sha256, "candidate_sha256"),
        (value._current_release_revision == envelope.current_release_revision, "release_revision"),
        (
            value._current_select_input_id == envelope.current_select_input_id,
            "current_select_input_id",
        ),
        (value._revocation_record_id == envelope.revocation_record_id, "revocation_record_id"),
        (
            value._revocation_effective_epoch == envelope.revocation_effective_epoch,
            "effective_epoch",
        ),
        (
            value._revocation_record_revision == envelope.revocation_record_revision,
            "record_revision",
        ),
        (value._revocation_reason_code == envelope.revocation_reason_code, "reason_code"),
        (
            value._revocation_issuer_set_root == envelope.revocation_issuer_set_root,
            "issuer_set_root",
        ),
        (value._evaluation_epoch == envelope.evaluation_epoch, "evaluation_epoch"),
        (value._chain_id == envelope.chain_id, "chain_id"),
        (value._domain_id == envelope.domain_id, "domain_id"),
        (value._signer_registry_hash == envelope.signer_registry_hash, "registry_hash"),
        (value._signer_registry_revision == envelope.signer_registry_revision, "registry_revision"),
        (value._quorum_threshold == envelope.quorum_threshold, "quorum_threshold"),
        (value._quorum_report_hash == report.get("quorum_report_hash"), "quorum_report_hash"),
    )
    for accepted, name in checks:
        if not accepted:
            raise _reject(
                "AUTHENTICATED_CAPABILITY_FIELD_DRIFT",
                f"retained capability {name} differs from revalidated evidence",
            )


def _require_exact_plain_dict(
    value: object,
    *,
    expected: frozenset[str] | None,
    name: str,
) -> dict[str, Any]:
    if type(value) is not dict:
        raise _reject("EXACT_OBJECT_REQUIRED", f"{name} must be an exact object")
    output = cast(dict[str, Any], value)
    if expected is not None and frozenset(output) != expected:
        raise _reject(
            "FIELD_SET_MISMATCH",
            f"{name} missing={sorted(expected - frozenset(output))} "
            f"extra={sorted(frozenset(output) - expected)}",
        )
    return output


def _decode_evidence_hex(value: object, *, name: str) -> bytes:
    if type(value) is not str or len(value) % 2 != 0 or _BARE_HEX_RE.fullmatch(value) is None:
        raise _reject("CANONICAL_HEX_REQUIRED", f"{name} must be nonempty lowercase hex")
    try:
        output = bytes.fromhex(value)
    except ValueError as exc:
        raise _reject("CANONICAL_HEX_REQUIRED", f"{name} must be lowercase hex") from exc
    if not output:
        raise _reject("CANONICAL_HEX_REQUIRED", f"{name} must decode to nonempty bytes")
    return output


def _root_string_to_digest(value: object, *, name: str) -> bytes:
    return bytes.fromhex(_require_root(value, name=name)[2:])


def _optional_root_string_to_digest(value: object, *, name: str) -> bytes | None:
    if value is None:
        return None
    return _root_string_to_digest(value, name=name)


def _reject_evidence_duplicate_keys(
    pairs: list[tuple[str, object]],
) -> dict[str, object]:
    output: dict[str, object] = {}
    for key, value in pairs:
        if key in output:
            raise _reject(
                "AUTHENTICATION_EVIDENCE_DUPLICATE_KEY",
                "authentication evidence contains a duplicate JSON key",
            )
        output[key] = value
    return output


def _reject_evidence_number(value: str) -> NoReturn:
    raise _reject("AUTHENTICATION_EVIDENCE_NUMBER", value)


def _fresh_bytes(value: bytes) -> bytes:
    return memoryview(value).tobytes()


def _require_exact_pins(value: object) -> SpotV7ReleaseRevocationExternalTrustPinsV1:
    if type(value) is not SpotV7ReleaseRevocationExternalTrustPinsV1:
        raise _reject(
            "EXTERNAL_TRUST_PINS_REQUIRED",
            "release-revocation authentication requires exact external trust pins",
        )
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


def _require_digest(value: object, *, name: str) -> bytes:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise _reject("DIGEST_REQUIRED", f"{name} must be a nonzero 32-byte digest")
    return value


def _require_optional_digest(value: object, *, name: str) -> bytes | None:
    if value is None:
        return None
    return _require_digest(value, name=name)


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


def _optional_digest_document(value: bytes | None) -> str | None:
    return None if value is None else "0x" + value.hex()


__all__ = [
    "SPOT_V7_RELEASE_REVOCATION_AUTHENTICATION_EVIDENCE_SCHEMA_V1",
    "SpotV7ReleaseRevocationAuthenticationErrorV1",
    "SpotV7ReleaseRevocationExternalTrustPinsV1",
    "authenticate_spot_v7_release_revocation_v1",
    "build_spot_v7_release_revocation_envelope_v1",
]
