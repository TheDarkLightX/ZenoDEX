"""J07 writer token V3 issue and point-of-use authorization relation.

This machine consumes a verified J07 authority context, the independently
verified writer-admission context, and one exact eligibility receipt.  It owns
token identity and accepted/rejected writer-use observations.  It carries no
publication, datastore, deployment, or value-moving authority.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from hashlib import sha256
from typing import Final, Mapping, TypeAlias, cast, final
from weakref import WeakValueDictionary, finalize

from src.core.fcis_m6_j07_authority_switch import (
    J07AuthorityContextV1,
    is_verified_authority_context_v1,
)
from src.core.fcis_m6_j07_writer_admission_v2 import (
    J07WriterAdmissionContextV2,
    J07WriterAdmissionError,
    J07WriterAdmissionRejectCodeV2,
    J07WriterAdmissionRejectV2,
    is_verified_j07_writer_admission_context_v2,
)
from src.core.fcis_m6_writer_profile_eligibility_v1 import (
    WriterProfileEligibilityReceiptV1,
    is_verified_writer_profile_eligibility_receipt_v1,
)
from src.state.canonical import canonical_json_bytes

FCIS_M6_J07_WRITER_TOKEN_SCHEMA_V3: Final = "zenodex/fcis/m6/j07/writer-token/v3"
MAX_J07_WRITER_TOKEN_EPOCH_V3: Final = (1 << 32) - 1
MAX_J07_WRITER_TOKENS_V3: Final = 8_192

_WRITER_TOKEN_CONSTRUCTION_TOKEN_V3 = object()
_WRITER_ACCEPTED_CONSTRUCTION_TOKEN_V3 = object()
_HEX_DIGITS = frozenset("0123456789abcdef")


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


def _u32(value: object, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_J07_WRITER_TOKEN_EPOCH_V3:
        raise J07WriterAdmissionError(f"{name} must be an exact u32 integer")
    return value


def _derive(domain: str, body: Mapping[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(body)).hexdigest()


def _token_body_from_values(values: Mapping[str, object]) -> dict[str, object]:
    return {
        "schema": FCIS_M6_J07_WRITER_TOKEN_SCHEMA_V3,
        "authority_context_root": values["authority_context_root"],
        "admission_context_root": values["admission_context_root"],
        "eligibility_receipt_root": values["eligibility_receipt_root"],
        "promotion_subject_root": values["promotion_subject_root"],
        "source_schema_root": values["source_schema_root"],
        "eligibility_policy_root": values["eligibility_policy_root"],
        "eligibility_verifier_profile_root": values["eligibility_verifier_profile_root"],
        "writer_profile_root": values["writer_profile_root"],
        "authority_epoch_index": values["authority_epoch_index"],
        "authority_state_root": values["authority_state_root"],
        "expected_head_root": values["expected_head_root"],
        "expected_snapshot_root": values["expected_snapshot_root"],
        "migration_token_root": values["migration_token_root"],
    }


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class J07WriterTokenV3:
    """Verifier-owned token bound to state, policy, verifier, and eligibility."""

    authority_context_root: str
    admission_context_root: str
    eligibility_receipt_root: str
    promotion_subject_root: str
    source_schema_root: str
    eligibility_policy_root: str
    eligibility_verifier_profile_root: str
    writer_profile_root: str
    authority_epoch_index: int
    authority_state_root: str
    expected_head_root: str
    expected_snapshot_root: str
    migration_token_root: str
    token_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _WRITER_TOKEN_CONSTRUCTION_TOKEN_V3:
            raise J07WriterAdmissionError("writer-token construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        for name in (
            "authority_context_root",
            "admission_context_root",
            "eligibility_receipt_root",
            "promotion_subject_root",
            "source_schema_root",
            "eligibility_policy_root",
            "eligibility_verifier_profile_root",
            "writer_profile_root",
            "authority_state_root",
            "expected_head_root",
            "expected_snapshot_root",
            "migration_token_root",
            "token_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _u32(self.authority_epoch_index, "authority_epoch_index")
        expected = writer_token_root_v3(self)
        if self.token_root != expected:
            raise J07WriterAdmissionError("token_root does not rederive")


def writer_token_body_v3(token: J07WriterTokenV3) -> dict[str, object]:
    """Return the complete canonical body for an exact V3 token."""

    if type(token) is not J07WriterTokenV3:
        raise J07WriterAdmissionError("writer token has the wrong exact type")
    return _token_body_from_values(
        {
            name: object.__getattribute__(token, name)
            for name in (
                "authority_context_root",
                "admission_context_root",
                "eligibility_receipt_root",
                "promotion_subject_root",
                "source_schema_root",
                "eligibility_policy_root",
                "eligibility_verifier_profile_root",
                "writer_profile_root",
                "authority_epoch_index",
                "authority_state_root",
                "expected_head_root",
                "expected_snapshot_root",
                "migration_token_root",
            )
        }
    )


def writer_token_root_v3(token: J07WriterTokenV3) -> str:
    return _derive(
        "zenodex/fcis/m6/j07/writer-token/v3",
        writer_token_body_v3(token),
    )


_WRITER_TOKENS_V3: WeakValueDictionary[int, J07WriterTokenV3] = WeakValueDictionary()
_WRITER_TOKEN_SNAPSHOTS_V3: dict[
    int,
    tuple[object, tuple[object, ...]],
] = {}


def _writer_token_snapshot(value: J07WriterTokenV3) -> tuple[object, ...]:
    fields = {
        name: object.__getattribute__(value, name)
        for name in (
            "authority_context_root",
            "admission_context_root",
            "eligibility_receipt_root",
            "promotion_subject_root",
            "source_schema_root",
            "eligibility_policy_root",
            "eligibility_verifier_profile_root",
            "writer_profile_root",
            "authority_epoch_index",
            "authority_state_root",
            "expected_head_root",
            "expected_snapshot_root",
            "migration_token_root",
        )
    }
    return tuple(_token_body_from_values(fields).items()) + (value.token_root,)


def _register_writer_token_v3(value: J07WriterTokenV3) -> J07WriterTokenV3:
    if len(_WRITER_TOKENS_V3) >= MAX_J07_WRITER_TOKENS_V3:
        raise J07WriterAdmissionError("writer-token registry capacity exceeded")
    identity = id(value)
    marker = object()
    _WRITER_TOKENS_V3[identity] = value
    _WRITER_TOKEN_SNAPSHOTS_V3[identity] = (marker, _writer_token_snapshot(value))
    finalize(value, _drop_writer_token_snapshot_v3, identity, marker)
    return value


def _drop_writer_token_snapshot_v3(identity: int, marker: object) -> None:
    retained = _WRITER_TOKEN_SNAPSHOTS_V3.get(identity)
    if retained is not None and retained[0] is marker:
        _WRITER_TOKEN_SNAPSHOTS_V3.pop(identity, None)


def is_verified_j07_writer_token_v3(value: object) -> bool:
    if type(value) is not J07WriterTokenV3:
        return False
    token = value
    if _WRITER_TOKENS_V3.get(id(token)) is not token:
        return False
    try:
        token._validate_fields()
        retained = _WRITER_TOKEN_SNAPSHOTS_V3.get(id(token))
        return retained is not None and retained[1] == _writer_token_snapshot(token)
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


def _eligibility_mismatch(
    authority_context: J07AuthorityContextV1,
    admission_context: J07WriterAdmissionContextV2,
    receipt: WriterProfileEligibilityReceiptV1,
) -> tuple[str, ...] | None:
    claim = receipt.claim
    comparisons = (
        (
            "authority_context",
            admission_context.authority_context_root,
            authority_context.context_root,
        ),
        ("claim_context", claim.authority_context_root, authority_context.context_root),
        ("promotion", claim.promotion_subject_root, admission_context.promotion_subject_root),
        ("source_schema", claim.source_schema_root, admission_context.source_schema_root),
        ("policy", claim.eligibility_policy_root, admission_context.eligibility_policy_root),
        (
            "verifier",
            receipt.verifier_profile_root,
            admission_context.eligibility_verifier_profile_root,
        ),
        ("state", claim.current_state_root, authority_context.current_state_root),
        (
            "deployment",
            claim.deployment_config_root,
            authority_context.deployment_config_root,
        ),
        ("epoch", claim.authority_epoch, authority_context.epoch_index),
        ("authority", claim.authority_state_root, authority_context.authority_state_root),
        ("head", claim.expected_head_root, authority_context.current_head_root),
        ("snapshot", claim.expected_snapshot_root, authority_context.current_snapshot_root),
    )
    for name, observed, expected in comparisons:
        if observed != expected:
            return ("eligibility", name)
    return None


J07WriterTokenIssueV3: TypeAlias = J07WriterTokenV3 | J07WriterAdmissionRejectV2


def _mint_writer_token_v3(
    authority: J07AuthorityContextV1,
    admission: J07WriterAdmissionContextV2,
    receipt: WriterProfileEligibilityReceiptV1,
) -> J07WriterTokenV3:
    claim = receipt.claim
    values: dict[str, object] = {
        "authority_context_root": authority.context_root,
        "admission_context_root": admission.admission_context_root,
        "eligibility_receipt_root": receipt.receipt_root,
        "promotion_subject_root": admission.promotion_subject_root,
        "source_schema_root": admission.source_schema_root,
        "eligibility_policy_root": admission.eligibility_policy_root,
        "eligibility_verifier_profile_root": admission.eligibility_verifier_profile_root,
        "writer_profile_root": claim.writer_profile_root,
        "authority_epoch_index": authority.epoch_index,
        "authority_state_root": authority.authority_state_root,
        "expected_head_root": authority.current_head_root,
        "expected_snapshot_root": authority.current_snapshot_root,
        "migration_token_root": authority.migration_token_root,
    }
    return _register_writer_token_v3(
        J07WriterTokenV3(
            authority_context_root=authority.context_root,
            admission_context_root=admission.admission_context_root,
            eligibility_receipt_root=receipt.receipt_root,
            promotion_subject_root=admission.promotion_subject_root,
            source_schema_root=admission.source_schema_root,
            eligibility_policy_root=admission.eligibility_policy_root,
            eligibility_verifier_profile_root=admission.eligibility_verifier_profile_root,
            writer_profile_root=claim.writer_profile_root,
            authority_epoch_index=authority.epoch_index,
            authority_state_root=authority.authority_state_root,
            expected_head_root=authority.current_head_root,
            expected_snapshot_root=authority.current_snapshot_root,
            migration_token_root=authority.migration_token_root,
            token_root=_derive(
                "zenodex/fcis/m6/j07/writer-token/v3",
                _token_body_from_values(values),
            ),
            _construction_token=_WRITER_TOKEN_CONSTRUCTION_TOKEN_V3,
        )
    )


def issue_writer_token_v3(
    authority_context: object,
    admission_context: object,
    eligibility_receipt: object,
) -> J07WriterTokenIssueV3:
    """Issue only from one current context and its expected eligibility policy."""

    if not is_verified_authority_context_v1(authority_context):
        return _reject(
            J07WriterAdmissionRejectCodeV2.AUTHORITY_CONTEXT_REJECTED,
            "authority_context",
        )
    exact_authority = cast(J07AuthorityContextV1, authority_context)
    if not is_verified_j07_writer_admission_context_v2(admission_context):
        return _reject(
            J07WriterAdmissionRejectCodeV2.ADMISSION_CONTEXT_REJECTED,
            "admission_context",
        )
    exact_admission = cast(J07WriterAdmissionContextV2, admission_context)
    if not is_verified_writer_profile_eligibility_receipt_v1(eligibility_receipt):
        return _reject(
            J07WriterAdmissionRejectCodeV2.ELIGIBILITY_REJECTED,
            "eligibility",
        )
    exact_receipt = cast(WriterProfileEligibilityReceiptV1, eligibility_receipt)
    mismatch = _eligibility_mismatch(exact_authority, exact_admission, exact_receipt)
    if mismatch is not None:
        return _reject(
            J07WriterAdmissionRejectCodeV2.ELIGIBILITY_CONTEXT_MISMATCH,
            *mismatch,
        )
    claim = exact_receipt.claim
    if claim.writer_profile_root not in exact_authority.allowed_writer_roots:
        return _reject(
            J07WriterAdmissionRejectCodeV2.WRITER_PROFILE_DISABLED,
            "eligibility",
            "writer_profile",
        )
    if len(_WRITER_TOKENS_V3) >= MAX_J07_WRITER_TOKENS_V3:
        return _reject(
            J07WriterAdmissionRejectCodeV2.TOKEN_REJECTED,
            "token",
            "capacity",
        )
    try:
        return _mint_writer_token_v3(exact_authority, exact_admission, exact_receipt)
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(
            J07WriterAdmissionRejectCodeV2.TOKEN_REJECTED,
            "token",
            "construction",
        )


@final
@dataclass(frozen=True, slots=True)
class J07WriterAcceptedV3:
    """Authority-empty accepted observation of the complete V3 relation."""

    authority_context_root: str
    admission_context_root: str
    token_root: str
    eligibility_receipt_root: str
    promotion_subject_root: str
    source_schema_root: str
    eligibility_policy_root: str
    eligibility_verifier_profile_root: str
    writer_profile_root: str
    authority_epoch_index: int
    authority_state_root: str
    head_root: str
    snapshot_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _WRITER_ACCEPTED_CONSTRUCTION_TOKEN_V3:
            raise J07WriterAdmissionError("accepted decision is verifier-owned")
        for name in (
            "authority_context_root",
            "admission_context_root",
            "token_root",
            "eligibility_receipt_root",
            "promotion_subject_root",
            "source_schema_root",
            "eligibility_policy_root",
            "eligibility_verifier_profile_root",
            "writer_profile_root",
            "authority_state_root",
            "head_root",
            "snapshot_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _u32(self.authority_epoch_index, "authority_epoch_index")


J07WriterDecisionV3: TypeAlias = J07WriterAcceptedV3 | J07WriterAdmissionRejectV2


def _token_current_mismatch(
    authority_context: J07AuthorityContextV1,
    admission_context: J07WriterAdmissionContextV2,
    token: J07WriterTokenV3,
) -> str | None:
    comparisons = (
        ("authority_context", token.authority_context_root, authority_context.context_root),
        (
            "admission_context",
            token.admission_context_root,
            admission_context.admission_context_root,
        ),
        ("epoch", token.authority_epoch_index, authority_context.epoch_index),
        ("authority", token.authority_state_root, authority_context.authority_state_root),
        ("head", token.expected_head_root, authority_context.current_head_root),
        ("snapshot", token.expected_snapshot_root, authority_context.current_snapshot_root),
        ("migration", token.migration_token_root, authority_context.migration_token_root),
    )
    return next(
        (name for name, observed, expected in comparisons if observed != expected),
        None,
    )


def _token_binding_mismatch(
    admission_context: J07WriterAdmissionContextV2,
    token: J07WriterTokenV3,
    receipt: WriterProfileEligibilityReceiptV1,
) -> str | None:
    claim = receipt.claim
    comparisons = (
        ("receipt", token.eligibility_receipt_root, receipt.receipt_root),
        ("promotion", token.promotion_subject_root, admission_context.promotion_subject_root),
        ("source_schema", token.source_schema_root, admission_context.source_schema_root),
        ("policy", token.eligibility_policy_root, admission_context.eligibility_policy_root),
        (
            "verifier",
            token.eligibility_verifier_profile_root,
            admission_context.eligibility_verifier_profile_root,
        ),
        ("writer_profile", token.writer_profile_root, claim.writer_profile_root),
    )
    return next(
        (name for name, observed, expected in comparisons if observed != expected),
        None,
    )


def _accepted_writer_v3(
    authority_context: J07AuthorityContextV1,
    admission_context: J07WriterAdmissionContextV2,
    token: J07WriterTokenV3,
    receipt: WriterProfileEligibilityReceiptV1,
) -> J07WriterAcceptedV3:
    return J07WriterAcceptedV3(
        authority_context_root=authority_context.context_root,
        admission_context_root=admission_context.admission_context_root,
        token_root=token.token_root,
        eligibility_receipt_root=receipt.receipt_root,
        promotion_subject_root=admission_context.promotion_subject_root,
        source_schema_root=admission_context.source_schema_root,
        eligibility_policy_root=admission_context.eligibility_policy_root,
        eligibility_verifier_profile_root=(admission_context.eligibility_verifier_profile_root),
        writer_profile_root=token.writer_profile_root,
        authority_epoch_index=authority_context.epoch_index,
        authority_state_root=authority_context.authority_state_root,
        head_root=authority_context.current_head_root,
        snapshot_root=authority_context.current_snapshot_root,
        _construction_token=_WRITER_ACCEPTED_CONSTRUCTION_TOKEN_V3,
    )


def authorize_writer_v3(
    authority_context: object,
    admission_context: object,
    token: object,
    eligibility_receipt: object,
) -> J07WriterDecisionV3:
    """Recheck current state, policy, verifier, receipt, and token at use."""

    if not is_verified_authority_context_v1(authority_context):
        return _reject(
            J07WriterAdmissionRejectCodeV2.AUTHORITY_CONTEXT_REJECTED,
            "authority_context",
        )
    exact_authority = cast(J07AuthorityContextV1, authority_context)
    if not is_verified_j07_writer_admission_context_v2(admission_context):
        return _reject(
            J07WriterAdmissionRejectCodeV2.ADMISSION_CONTEXT_REJECTED,
            "admission_context",
        )
    exact_admission = cast(J07WriterAdmissionContextV2, admission_context)
    if not is_verified_j07_writer_token_v3(token):
        return _reject(J07WriterAdmissionRejectCodeV2.TOKEN_REJECTED, "token")
    exact_token = cast(J07WriterTokenV3, token)
    if not is_verified_writer_profile_eligibility_receipt_v1(eligibility_receipt):
        return _reject(
            J07WriterAdmissionRejectCodeV2.ELIGIBILITY_REJECTED,
            "eligibility",
        )
    exact_receipt = cast(WriterProfileEligibilityReceiptV1, eligibility_receipt)
    mismatch = _eligibility_mismatch(exact_authority, exact_admission, exact_receipt)
    if mismatch is not None:
        return _reject(
            J07WriterAdmissionRejectCodeV2.ELIGIBILITY_CONTEXT_MISMATCH,
            *mismatch,
        )
    stale_field = _token_current_mismatch(exact_authority, exact_admission, exact_token)
    if stale_field is not None:
        return _reject(J07WriterAdmissionRejectCodeV2.STALE_CONTEXT, "token", stale_field)
    binding_field = _token_binding_mismatch(exact_admission, exact_token, exact_receipt)
    if binding_field is not None:
        return _reject(
            J07WriterAdmissionRejectCodeV2.ELIGIBILITY_CONTEXT_MISMATCH,
            "token",
            binding_field,
        )
    if exact_token.writer_profile_root not in exact_authority.allowed_writer_roots:
        return _reject(
            J07WriterAdmissionRejectCodeV2.WRITER_PROFILE_DISABLED,
            "token",
            "writer_profile",
        )
    return _accepted_writer_v3(exact_authority, exact_admission, exact_token, exact_receipt)


__all__ = (
    "FCIS_M6_J07_WRITER_TOKEN_SCHEMA_V3",
    "MAX_J07_WRITER_TOKENS_V3",
    "J07WriterAcceptedV3",
    "J07WriterDecisionV3",
    "J07WriterTokenIssueV3",
    "J07WriterTokenV3",
    "authorize_writer_v3",
    "is_verified_j07_writer_token_v3",
    "issue_writer_token_v3",
    "writer_token_body_v3",
    "writer_token_root_v3",
)
