"""Research-only J05 shadow replay and dual-check model for FCIS M6."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, cast

from src.core import fcis_durable_retraction as dra


class J05Error(ValueError):
    """Typed validation failure in the isolated J05 model."""


def _digest(value: object, label: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise J05Error(f"{label} must be 64 lowercase hexadecimal characters")
    return value


def _text(value: object, label: str) -> str:
    if type(value) is not str or not value:
        raise J05Error(f"{label} must be a nonempty string")
    if len(value.encode("utf-8")) > dra.MAX_TEXT_BYTES:
        raise J05Error(f"{label} exceeds its byte bound")
    return value


def _u32(value: object, label: str) -> int:
    if type(value) is not int or value < 0 or value > dra.U32_MAX:
        raise J05Error(f"{label} must be an exact u32")
    return value


class J05ComparisonModeV1(Enum):
    EXACT_EQUALITY = "exact_equality"
    REVIEWED_REFINEMENT = "reviewed_refinement"


class J05OutcomeV1(Enum):
    EXACT_MATCH = "exact_match"
    REFINEMENT_MATCH = "refinement_match"
    DIVERGENCE_RETAINED = "divergence_retained"


class J05CodeV1(Enum):
    INVALID_CONTEXT = "invalid_context"
    INVALID_CANDIDATE = "invalid_candidate"
    PROFILE_MISMATCH = "profile_mismatch"
    SEQUENCE_MISMATCH = "sequence_mismatch"
    RELATION_MISMATCH = "relation_mismatch"
    SHADOW_AUTHORITY = "shadow_authority"


EXACT_RELATION_ID = "j05/exact-equality/v1"
REVIEWED_RELATION_ID = "j05/reviewed-state-refinement/v1"


@dataclass(frozen=True, slots=True)
class J05ReplayContextV1:
    """J04-bound source context consumed by shadow and dual-check paths."""

    manifest_root: str
    activation_sequence: int
    source_profile_root: str
    target_profile_root: str
    source_result_root: str

    def __post_init__(self) -> None:
        _digest(self.manifest_root, "manifest_root")
        _u32(self.activation_sequence, "activation_sequence")
        _digest(self.source_profile_root, "source_profile_root")
        _digest(self.target_profile_root, "target_profile_root")
        _digest(self.source_result_root, "source_result_root")
        if self.source_profile_root == self.target_profile_root:
            raise J05Error("source and target profiles must differ")


@dataclass(frozen=True, slots=True)
class J05ShadowOutputV1:
    """A target replay result with an explicit non-authority bit."""

    manifest_root: str
    activation_sequence: int
    target_profile_root: str
    target_result_root: str
    output_root: str
    is_authoritative: bool = False

    def __post_init__(self) -> None:
        _digest(self.manifest_root, "manifest_root")
        _u32(self.activation_sequence, "activation_sequence")
        _digest(self.target_profile_root, "target_profile_root")
        _digest(self.target_result_root, "target_result_root")
        _digest(self.output_root, "output_root")
        if type(self.is_authoritative) is not bool or self.is_authoritative:
            raise J05Error("shadow output cannot carry authority")
        if self.output_root != derive_shadow_output_root(self):
            raise J05Error("shadow output root is not canonical")


@dataclass(frozen=True, slots=True)
class J05DualCandidateV1:
    """Untrusted candidate equality/refinement evidence."""

    shadow: object
    mode: object
    relation_id: str
    relation_root: str

    def __post_init__(self) -> None:
        _text(self.relation_id, "relation_id")
        _digest(self.relation_root, "relation_root")


@dataclass(frozen=True, slots=True)
class J05DivergenceV1:
    """Retained mismatch evidence that cannot advance migration authority."""

    manifest_root: str
    activation_sequence: int
    source_result_root: str
    target_result_root: str
    reason: str
    retained: bool = True
    is_authoritative: bool = False

    def __post_init__(self) -> None:
        _digest(self.manifest_root, "manifest_root")
        _u32(self.activation_sequence, "activation_sequence")
        _digest(self.source_result_root, "source_result_root")
        _digest(self.target_result_root, "target_result_root")
        _text(self.reason, "reason")
        if self.source_result_root == self.target_result_root:
            raise J05Error("divergence requires distinct result roots")
        if self.retained is not True or self.is_authoritative is not False:
            raise J05Error("divergence must be retained and non-authoritative")


@dataclass(frozen=True, slots=True)
class J05DualCheckV1:
    outcome: J05OutcomeV1
    phase_advance_allowed: bool
    shadow: J05ShadowOutputV1
    divergence: J05DivergenceV1 | None = None

    def __post_init__(self) -> None:
        if type(self.outcome) is not J05OutcomeV1:
            raise J05Error("dual-check outcome has the wrong exact type")
        if type(self.phase_advance_allowed) is not bool:
            raise J05Error("phase_advance_allowed must be boolean")
        self.shadow.__post_init__()
        if self.outcome is J05OutcomeV1.DIVERGENCE_RETAINED:
            if self.phase_advance_allowed or self.divergence is None:
                raise J05Error("divergence must block phase advance")
            self.divergence.__post_init__()
        elif self.phase_advance_allowed is not True or self.divergence is not None:
            raise J05Error("matching dual check has invalid progression state")


@dataclass(frozen=True, slots=True)
class J05RejectV1:
    code: J05CodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not J05CodeV1:
            raise J05Error("J05 rejection code has the wrong exact type")
        if type(self.path) is not tuple or any(type(item) is not str for item in self.path):
            raise J05Error("J05 rejection path has the wrong exact type")


J05ShadowResultV1: TypeAlias = J05ShadowOutputV1 | J05RejectV1
J05DualResultV1: TypeAlias = J05DualCheckV1 | J05RejectV1


def derive_shadow_output_root(shadow: J05ShadowOutputV1) -> str:
    """Derive the non-authoritative shadow output identity."""

    return _derive_shadow_output_root(
        shadow.manifest_root,
        shadow.activation_sequence,
        shadow.target_profile_root,
        shadow.target_result_root,
    )


def _derive_shadow_output_root(
    manifest_root: str,
    activation_sequence: int,
    target_profile_root: str,
    target_result_root: str,
) -> str:
    return cast(
        str,
        dra.tagged_digest(
            "j05/shadow-output/v1/"
            f"{manifest_root}/{activation_sequence}/"
            f"{target_profile_root}/{target_result_root}"
        ),
    )


def derive_reviewed_refinement_result_root(context: J05ReplayContextV1) -> str:
    """Return the only bounded reviewed refinement target relation."""

    return cast(
        str,
        dra.tagged_digest(
            "j05/reviewed-target/v1/"
            f"{context.manifest_root}/{context.activation_sequence}/"
            f"{context.source_result_root}/{context.target_profile_root}"
        ),
    )


def derive_relation_root(
    context: J05ReplayContextV1,
    shadow: J05ShadowOutputV1,
    mode: J05ComparisonModeV1,
    relation_id: str,
) -> str:
    """Derive the canonical equality/refinement witness root."""

    if type(mode) is not J05ComparisonModeV1:
        raise J05Error("comparison mode has the wrong exact type")
    _text(relation_id, "relation_id")
    return cast(
        str,
        dra.tagged_digest(
            "j05/relation/v1/"
            f"{relation_id}/{mode.value}/{context.manifest_root}/"
            f"{context.activation_sequence}/{context.source_result_root}/"
            f"{shadow.target_result_root}/{shadow.target_profile_root}"
        ),
    )


def run_shadow_replay_v1(context: object, target_result_root: object) -> J05ShadowResultV1:
    """Produce a target replay result without authority."""

    if type(context) is not J05ReplayContextV1:
        return J05RejectV1(J05CodeV1.INVALID_CONTEXT, ("context",))
    exact_context = context
    try:
        exact_context.__post_init__()
        target_root = _digest(target_result_root, "target_result_root")
        shadow = J05ShadowOutputV1(
            manifest_root=exact_context.manifest_root,
            activation_sequence=exact_context.activation_sequence,
            target_profile_root=exact_context.target_profile_root,
            target_result_root=target_root,
            output_root=_derive_shadow_output_root(
                exact_context.manifest_root,
                exact_context.activation_sequence,
                exact_context.target_profile_root,
                target_root,
            ),
        )
        return shadow
    except (J05Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return J05RejectV1(J05CodeV1.INVALID_CONTEXT, ("context_or_target",))


def verify_dual_check_v1(context: object, candidate: object) -> J05DualResultV1:
    """Verify exact equality or the one reviewed refinement relation."""

    if type(context) is not J05ReplayContextV1:
        return J05RejectV1(J05CodeV1.INVALID_CONTEXT, ("context",))
    if type(candidate) is not J05DualCandidateV1:
        return J05RejectV1(J05CodeV1.INVALID_CANDIDATE, ("candidate",))
    exact_context = context
    exact_candidate = candidate
    try:
        exact_context.__post_init__()
        exact_candidate.__post_init__()
    except (J05Error, TypeError, ValueError):
        return J05RejectV1(J05CodeV1.INVALID_CANDIDATE, ("typed_fields",))
    if type(exact_candidate.shadow) is not J05ShadowOutputV1:
        return J05RejectV1(J05CodeV1.INVALID_CANDIDATE, ("shadow",))
    if type(exact_candidate.mode) is not J05ComparisonModeV1:
        return J05RejectV1(J05CodeV1.INVALID_CANDIDATE, ("mode",))
    shadow = exact_candidate.shadow
    mode = exact_candidate.mode
    try:
        shadow.__post_init__()
    except (J05Error, TypeError, ValueError):
        return J05RejectV1(J05CodeV1.SHADOW_AUTHORITY, ("shadow",))
    if shadow.manifest_root != exact_context.manifest_root:
        return J05RejectV1(J05CodeV1.PROFILE_MISMATCH, ("manifest_root",))
    if shadow.activation_sequence != exact_context.activation_sequence:
        return J05RejectV1(J05CodeV1.SEQUENCE_MISMATCH, ("activation_sequence",))
    if shadow.target_profile_root != exact_context.target_profile_root:
        return J05RejectV1(J05CodeV1.PROFILE_MISMATCH, ("target_profile_root",))
    expected_relation_id = (
        EXACT_RELATION_ID if mode is J05ComparisonModeV1.EXACT_EQUALITY else REVIEWED_RELATION_ID
    )
    if exact_candidate.relation_id != expected_relation_id:
        return J05RejectV1(J05CodeV1.RELATION_MISMATCH, ("relation_id",))
    expected_relation = derive_relation_root(
        exact_context,
        shadow,
        mode,
        expected_relation_id,
    )
    if exact_candidate.relation_root != expected_relation:
        return J05RejectV1(J05CodeV1.RELATION_MISMATCH, ("relation_root",))
    if mode is J05ComparisonModeV1.EXACT_EQUALITY:
        if shadow.target_result_root != exact_context.source_result_root:
            return _divergence(exact_context, shadow, "exact result roots differ")
        return J05DualCheckV1(
            outcome=J05OutcomeV1.EXACT_MATCH,
            phase_advance_allowed=True,
            shadow=shadow,
        )
    expected_target = derive_reviewed_refinement_result_root(exact_context)
    if shadow.target_result_root != expected_target:
        return _divergence(exact_context, shadow, "reviewed refinement relation differs")
    return J05DualCheckV1(
        outcome=J05OutcomeV1.REFINEMENT_MATCH,
        phase_advance_allowed=True,
        shadow=shadow,
    )


def _divergence(
    context: J05ReplayContextV1,
    shadow: J05ShadowOutputV1,
    reason: str,
) -> J05DualCheckV1:
    return J05DualCheckV1(
        outcome=J05OutcomeV1.DIVERGENCE_RETAINED,
        phase_advance_allowed=False,
        shadow=shadow,
        divergence=J05DivergenceV1(
            manifest_root=context.manifest_root,
            activation_sequence=context.activation_sequence,
            source_result_root=context.source_result_root,
            target_result_root=shadow.target_result_root,
            reason=reason,
        ),
    )


__all__ = (
    "EXACT_RELATION_ID",
    "J05CodeV1",
    "J05ComparisonModeV1",
    "J05DualCandidateV1",
    "J05DualCheckV1",
    "J05DualResultV1",
    "J05DivergenceV1",
    "J05Error",
    "J05OutcomeV1",
    "J05RejectV1",
    "J05ReplayContextV1",
    "J05ShadowOutputV1",
    "J05ShadowResultV1",
    "REVIEWED_RELATION_ID",
    "derive_relation_root",
    "derive_reviewed_refinement_result_root",
    "derive_shadow_output_root",
    "run_shadow_replay_v1",
    "verify_dual_check_v1",
)
