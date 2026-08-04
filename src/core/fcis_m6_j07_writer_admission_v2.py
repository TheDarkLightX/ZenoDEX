"""Policy-bound J07 writer-admission context research relation.

The J07 authority-switch context identifies the active writer and current
authority coordinates.  This downstream context additionally fixes the exact
promotion subject, eligibility source language, eligibility policy, and
selected verifier profile.  The downstream token machine consumes this
independently registered value and repeats its point-of-use binding checks.

The verifier adapter remains an imperative-shell premise.  These values are
research evidence and provide no datastore, deployment, or publication
authority.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Callable, Final, Mapping, Protocol, TypeAlias, cast, final
from weakref import WeakValueDictionary, finalize

from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_j07_authority_switch import (
    J07AuthorityContextV1,
    J07StateKindV1,
    is_verified_authority_context_v1,
)
from src.state.canonical import canonical_json_bytes

FCIS_M6_J07_WRITER_ADMISSION_CONTEXT_SCHEMA_V2: Final = (
    "zenodex/fcis/m6/j07/writer-admission-context/v2"
)
MAX_J07_WRITER_ADMISSION_CONTEXTS_V2: Final = 8_192
_ADMISSION_CONTEXT_CONSTRUCTION_TOKEN_V2 = object()
_HEX_DIGITS = frozenset("0123456789abcdef")


class J07WriterAdmissionError(ValueError):
    """Raised when a writer-admission value leaves its closed language."""


class J07WriterAdmissionRejectCodeV2(str, Enum):
    """Stable authority-empty reject classes for the V2/V3 relation."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    AUTHORITY_CONTEXT_REJECTED = "authority_context_rejected"
    INVALID_POLICY_CONTEXT = "invalid_policy_context"
    EXTERNAL_VERIFIER_REJECTED = "external_verifier_rejected"
    ADMISSION_CONTEXT_REJECTED = "admission_context_rejected"
    ELIGIBILITY_REJECTED = "eligibility_rejected"
    ELIGIBILITY_CONTEXT_MISMATCH = "eligibility_context_mismatch"
    TOKEN_REJECTED = "token_rejected"
    STALE_CONTEXT = "stale_context"
    WRITER_PROFILE_DISABLED = "writer_profile_disabled"


@final
@dataclass(frozen=True, slots=True)
class J07WriterAdmissionRejectV2:
    """Typed rejection carrying no token, accepted value, or effect."""

    code: J07WriterAdmissionRejectCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not J07WriterAdmissionRejectCodeV2:
            raise J07WriterAdmissionError("reject code has the wrong exact type")
        if type(self.path) is not tuple or not self.path or len(self.path) > 8:
            raise J07WriterAdmissionError("reject path is outside its closed bound")
        for part in self.path:
            if type(part) is not str or not part or len(part.encode("utf-8")) > 64:
                raise J07WriterAdmissionError("reject path component is invalid")


def _reject(
    code: J07WriterAdmissionRejectCodeV2,
    *path: str,
) -> J07WriterAdmissionRejectV2:
    return J07WriterAdmissionRejectV2(code=code, path=tuple(path))


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or value != value.lower()
        or any(character not in _HEX_DIGITS for character in value)
    ):
        raise J07WriterAdmissionError(f"{name} must be a lowercase SHA-256 digest")
    return value


def _derive(domain: str, body: Mapping[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(body)).hexdigest()


def _admission_context_body_from_values(values: Mapping[str, object]) -> dict[str, object]:
    return {
        "schema": FCIS_M6_J07_WRITER_ADMISSION_CONTEXT_SCHEMA_V2,
        "authority_context_root": values["authority_context_root"],
        "promotion_subject_root": values["promotion_subject_root"],
        "source_schema_root": values["source_schema_root"],
        "eligibility_policy_root": values["eligibility_policy_root"],
        "eligibility_verifier_profile_root": values["eligibility_verifier_profile_root"],
        "verification_evidence_root": values["verification_evidence_root"],
    }


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class J07WriterAdmissionContextV2:
    """Verifier-owned policy coordinates for one exact J07 context."""

    authority_context_root: str
    promotion_subject_root: str
    source_schema_root: str
    eligibility_policy_root: str
    eligibility_verifier_profile_root: str
    verification_evidence_root: str
    admission_context_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _ADMISSION_CONTEXT_CONSTRUCTION_TOKEN_V2:
            raise J07WriterAdmissionError("writer-admission context is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        for name in (
            "authority_context_root",
            "promotion_subject_root",
            "source_schema_root",
            "eligibility_policy_root",
            "eligibility_verifier_profile_root",
            "verification_evidence_root",
            "admission_context_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        expected = writer_admission_context_root_v2(self)
        if self.admission_context_root != expected:
            raise J07WriterAdmissionError("admission_context_root does not rederive")


def writer_admission_context_body_v2(
    context: J07WriterAdmissionContextV2,
) -> dict[str, object]:
    """Return the complete canonical body for an exact V2 context."""

    if type(context) is not J07WriterAdmissionContextV2:
        raise J07WriterAdmissionError("admission context has the wrong exact type")
    return _admission_context_body_from_values(
        {
            "authority_context_root": context.authority_context_root,
            "promotion_subject_root": context.promotion_subject_root,
            "source_schema_root": context.source_schema_root,
            "eligibility_policy_root": context.eligibility_policy_root,
            "eligibility_verifier_profile_root": (context.eligibility_verifier_profile_root),
            "verification_evidence_root": context.verification_evidence_root,
        }
    )


def writer_admission_context_root_v2(context: J07WriterAdmissionContextV2) -> str:
    return _derive(
        "zenodex/fcis/m6/j07/writer-admission-context/v2",
        writer_admission_context_body_v2(context),
    )


class J07WriterAdmissionVerifierAdapterV2(Protocol):
    """Shell-selected verifier for the state-bound policy coordinates."""

    def verify_j07_writer_admission_context(
        self,
        *,
        expected_authority_context_root: object,
        expected_current_state_root: object,
        expected_deployment_config_root: object,
        expected_authority_epoch: object,
        expected_authority_state_root: object,
        expected_head_root: object,
        expected_snapshot_root: object,
        expected_promotion_subject_root: object,
        expected_source_schema_root: object,
        expected_eligibility_policy_root: object,
        expected_eligibility_verifier_profile_root: object,
        expected_verification_evidence_root: object,
    ) -> object:
        """Return exact True only after checking the selected current policy."""


_ADMISSION_CONTEXTS_V2: WeakValueDictionary[int, J07WriterAdmissionContextV2] = (
    WeakValueDictionary()
)
_ADMISSION_CONTEXT_SNAPSHOTS_V2: dict[
    int,
    tuple[object, tuple[object, ...]],
] = {}


def _admission_context_snapshot(value: J07WriterAdmissionContextV2) -> tuple[object, ...]:
    return (
        value.authority_context_root,
        value.promotion_subject_root,
        value.source_schema_root,
        value.eligibility_policy_root,
        value.eligibility_verifier_profile_root,
        value.verification_evidence_root,
        value.admission_context_root,
    )


def _register_admission_context_v2(
    value: J07WriterAdmissionContextV2,
) -> J07WriterAdmissionContextV2:
    if len(_ADMISSION_CONTEXTS_V2) >= MAX_J07_WRITER_ADMISSION_CONTEXTS_V2:
        raise J07WriterAdmissionError("writer-admission registry capacity exceeded")
    identity = id(value)
    marker = object()
    _ADMISSION_CONTEXTS_V2[identity] = value
    _ADMISSION_CONTEXT_SNAPSHOTS_V2[identity] = (
        marker,
        _admission_context_snapshot(value),
    )
    finalize(value, _drop_admission_context_snapshot_v2, identity, marker)
    return value


def _drop_admission_context_snapshot_v2(identity: int, marker: object) -> None:
    retained = _ADMISSION_CONTEXT_SNAPSHOTS_V2.get(identity)
    if retained is not None and retained[0] is marker:
        _ADMISSION_CONTEXT_SNAPSHOTS_V2.pop(identity, None)


def is_verified_j07_writer_admission_context_v2(value: object) -> bool:
    """Revalidate construction provenance, bytes, and retained fields."""

    if type(value) is not J07WriterAdmissionContextV2:
        return False
    context = value
    if _ADMISSION_CONTEXTS_V2.get(id(context)) is not context:
        return False
    try:
        context._validate_fields()
        retained = _ADMISSION_CONTEXT_SNAPSHOTS_V2.get(id(context))
        return retained is not None and retained[1] == _admission_context_snapshot(context)
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


def _external_admission_verifier_accepts(
    authority_context: J07AuthorityContextV1,
    *,
    promotion_subject_root: str,
    source_schema_root: str,
    eligibility_policy_root: str,
    eligibility_verifier_profile_root: str,
    verification_evidence_root: str,
    verifier_adapter: object,
) -> bool:
    try:
        method = getattr(verifier_adapter, "verify_j07_writer_admission_context", None)
        if not callable(method):
            return False
        decision = cast(Callable[..., object], method)(
            expected_authority_context_root=authority_context.context_root,
            expected_current_state_root=authority_context.current_state_root,
            expected_deployment_config_root=authority_context.deployment_config_root,
            expected_authority_epoch=authority_context.epoch_index,
            expected_authority_state_root=authority_context.authority_state_root,
            expected_head_root=authority_context.current_head_root,
            expected_snapshot_root=authority_context.current_snapshot_root,
            expected_promotion_subject_root=promotion_subject_root,
            expected_source_schema_root=source_schema_root,
            expected_eligibility_policy_root=eligibility_policy_root,
            expected_eligibility_verifier_profile_root=(eligibility_verifier_profile_root),
            expected_verification_evidence_root=verification_evidence_root,
        )
    # The adapter is an untrusted imperative-shell boundary.  Expected adapter
    # and transport failures remain authority-empty rejections; process-control
    # exceptions and resource exhaustion are deliberately not swallowed.
    except (
        AttributeError,
        TypeError,
        ValueError,
        ArithmeticError,
        RuntimeError,
        RecursionError,
        OSError,
    ):
        return False
    return decision is True


J07WriterAdmissionContextResultV2: TypeAlias = (
    J07WriterAdmissionContextV2 | J07WriterAdmissionRejectV2
)


def _checked_admission_values(
    authority_context: J07AuthorityContextV1,
    *,
    promotion_subject_root: object,
    source_schema_root: object,
    eligibility_policy_root: object,
    eligibility_verifier_profile_root: object,
    verification_evidence_root: object,
) -> dict[str, object]:
    return {
        "authority_context_root": authority_context.context_root,
        "promotion_subject_root": _digest(
            promotion_subject_root,
            "promotion_subject_root",
        ),
        "source_schema_root": _digest(source_schema_root, "source_schema_root"),
        "eligibility_policy_root": _digest(
            eligibility_policy_root,
            "eligibility_policy_root",
        ),
        "eligibility_verifier_profile_root": _digest(
            eligibility_verifier_profile_root,
            "eligibility_verifier_profile_root",
        ),
        "verification_evidence_root": _digest(
            verification_evidence_root,
            "verification_evidence_root",
        ),
    }


def _mint_admission_context_v2(
    authority_context: J07AuthorityContextV1,
    values: Mapping[str, object],
) -> J07WriterAdmissionContextV2:
    root = _derive(
        "zenodex/fcis/m6/j07/writer-admission-context/v2",
        _admission_context_body_from_values(values),
    )
    return _register_admission_context_v2(
        J07WriterAdmissionContextV2(
            authority_context_root=authority_context.context_root,
            promotion_subject_root=cast(str, values["promotion_subject_root"]),
            source_schema_root=cast(str, values["source_schema_root"]),
            eligibility_policy_root=cast(str, values["eligibility_policy_root"]),
            eligibility_verifier_profile_root=cast(
                str,
                values["eligibility_verifier_profile_root"],
            ),
            verification_evidence_root=cast(str, values["verification_evidence_root"]),
            admission_context_root=root,
            _construction_token=_ADMISSION_CONTEXT_CONSTRUCTION_TOKEN_V2,
        )
    )


def verify_j07_writer_admission_context_v2(
    *,
    authority_context: object,
    promotion_subject_root: object,
    source_schema_root: object,
    eligibility_policy_root: object,
    eligibility_verifier_profile_root: object,
    verification_evidence_root: object,
    verifier_adapter: J07WriterAdmissionVerifierAdapterV2 | object,
) -> J07WriterAdmissionContextResultV2:
    """Verify and register the expected policy coordinates for one J07 head."""

    if not is_verified_authority_context_v1(authority_context):
        return _reject(
            J07WriterAdmissionRejectCodeV2.AUTHORITY_CONTEXT_REJECTED,
            "authority_context",
        )
    exact_context = cast(J07AuthorityContextV1, authority_context)
    if (
        exact_context.kind is not J07StateKindV1.POST_AUTHORITY_SWITCH
        or exact_context.phase is not dra.MigrationPhaseV1.AUTHORITY_SWITCH
    ):
        return _reject(
            J07WriterAdmissionRejectCodeV2.AUTHORITY_CONTEXT_REJECTED,
            "authority_context",
            "phase",
        )
    try:
        values = _checked_admission_values(
            exact_context,
            promotion_subject_root=promotion_subject_root,
            source_schema_root=source_schema_root,
            eligibility_policy_root=eligibility_policy_root,
            eligibility_verifier_profile_root=eligibility_verifier_profile_root,
            verification_evidence_root=verification_evidence_root,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(
            J07WriterAdmissionRejectCodeV2.INVALID_POLICY_CONTEXT,
            "policy_context",
        )
    if not _external_admission_verifier_accepts(
        exact_context,
        promotion_subject_root=cast(str, values["promotion_subject_root"]),
        source_schema_root=cast(str, values["source_schema_root"]),
        eligibility_policy_root=cast(str, values["eligibility_policy_root"]),
        eligibility_verifier_profile_root=cast(
            str,
            values["eligibility_verifier_profile_root"],
        ),
        verification_evidence_root=cast(str, values["verification_evidence_root"]),
        verifier_adapter=verifier_adapter,
    ):
        return _reject(
            J07WriterAdmissionRejectCodeV2.EXTERNAL_VERIFIER_REJECTED,
            "verifier",
        )
    if not is_verified_authority_context_v1(exact_context):
        return _reject(
            J07WriterAdmissionRejectCodeV2.AUTHORITY_CONTEXT_REJECTED,
            "authority_context",
            "post_verifier",
        )
    if len(_ADMISSION_CONTEXTS_V2) >= MAX_J07_WRITER_ADMISSION_CONTEXTS_V2:
        return _reject(
            J07WriterAdmissionRejectCodeV2.ADMISSION_CONTEXT_REJECTED,
            "admission_context",
            "capacity",
        )
    try:
        return _mint_admission_context_v2(exact_context, values)
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(
            J07WriterAdmissionRejectCodeV2.ADMISSION_CONTEXT_REJECTED,
            "admission_context",
            "construction",
        )


__all__ = (
    "FCIS_M6_J07_WRITER_ADMISSION_CONTEXT_SCHEMA_V2",
    "MAX_J07_WRITER_ADMISSION_CONTEXTS_V2",
    "J07WriterAdmissionContextResultV2",
    "J07WriterAdmissionContextV2",
    "J07WriterAdmissionError",
    "J07WriterAdmissionRejectCodeV2",
    "J07WriterAdmissionRejectV2",
    "J07WriterAdmissionVerifierAdapterV2",
    "is_verified_j07_writer_admission_context_v2",
    "verify_j07_writer_admission_context_v2",
    "writer_admission_context_body_v2",
    "writer_admission_context_root_v2",
)
