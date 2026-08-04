"""Substrate-neutral writer-profile eligibility evidence for FCIS M6.

The public claim is canonical data and grants no authority.  A selected
external verifier may mint one registered receipt after checking the exact
promotion subject, source evidence, policy, writer profile, and current J07
authority coordinates.  J07 must still revalidate the receipt against its
current context when issuing and using a writer token.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Callable, Final, Mapping, Protocol, TypeAlias, cast, final
from weakref import WeakValueDictionary

from src.state.canonical import canonical_json_bytes

WRITER_PROFILE_ELIGIBILITY_CLAIM_SCHEMA_V1: Final = (
    "zenodex/fcis/m6/writer-profile-eligibility-claim/v1"
)
WRITER_PROFILE_ELIGIBILITY_RECEIPT_SCHEMA_V1: Final = (
    "zenodex/fcis/m6/writer-profile-eligibility-receipt/v1"
)
MAX_WRITER_PROFILE_AUTHORITY_EPOCH_V1: Final = (1 << 64) - 1

_RECEIPT_CONSTRUCTION_TOKEN_V1 = object()
_HEX_DIGITS = frozenset("0123456789abcdef")


class WriterProfileEligibilityError(ValueError):
    """Raised when an eligibility value violates its closed language."""


class WriterProfileEligibilityRejectCodeV1(str, Enum):
    """Stable authority-empty eligibility rejection classes."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_CLAIM = "invalid_claim"
    EXTERNAL_VERIFIER_REJECTED = "external_verifier_rejected"
    RECEIPT_REJECTED = "receipt_rejected"


@final
@dataclass(frozen=True, slots=True)
class WriterProfileEligibilityRejectV1:
    """Typed rejection carrying no token, successor, receipt, or effect."""

    code: WriterProfileEligibilityRejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not WriterProfileEligibilityRejectCodeV1:
            raise WriterProfileEligibilityError("reject code has the wrong exact type")
        if type(self.path) is not tuple or not self.path:
            raise WriterProfileEligibilityError("reject path must be a nonempty exact tuple")
        if len(self.path) > 8 or any(type(part) is not str or not part for part in self.path):
            raise WriterProfileEligibilityError("reject path is outside its closed bound")


def _reject(
    code: WriterProfileEligibilityRejectCodeV1,
    *path: str,
) -> WriterProfileEligibilityRejectV1:
    return WriterProfileEligibilityRejectV1(code=code, path=tuple(path))


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or value != value.lower()
        or any(character not in _HEX_DIGITS for character in value)
    ):
        raise WriterProfileEligibilityError(f"{name} must be a lowercase SHA-256 digest")
    return value


def _u64(value: object, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_WRITER_PROFILE_AUTHORITY_EPOCH_V1:
        raise WriterProfileEligibilityError(f"{name} must be an exact u64 integer")
    return value


def _derive(domain: str, body: Mapping[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(body)).hexdigest()


def _claim_body_from_values(values: Mapping[str, object]) -> dict[str, object]:
    return {
        "schema": WRITER_PROFILE_ELIGIBILITY_CLAIM_SCHEMA_V1,
        "promotion_subject_root": values["promotion_subject_root"],
        "source_schema_root": values["source_schema_root"],
        "source_receipt_root": values["source_receipt_root"],
        "source_binding_root": values["source_binding_root"],
        "writer_profile_root": values["writer_profile_root"],
        "authority_context_root": values["authority_context_root"],
        "current_state_root": values["current_state_root"],
        "deployment_config_root": values["deployment_config_root"],
        "authority_epoch": values["authority_epoch"],
        "authority_state_root": values["authority_state_root"],
        "expected_head_root": values["expected_head_root"],
        "expected_snapshot_root": values["expected_snapshot_root"],
        "eligibility_policy_root": values["eligibility_policy_root"],
    }


@final
@dataclass(frozen=True, slots=True)
class WriterProfileEligibilityClaimV1:
    """Canonical untrusted claim awaiting the selected verifier."""

    promotion_subject_root: str
    source_schema_root: str
    source_receipt_root: str
    source_binding_root: str
    writer_profile_root: str
    authority_context_root: str
    current_state_root: str
    deployment_config_root: str
    authority_epoch: int
    authority_state_root: str
    expected_head_root: str
    expected_snapshot_root: str
    eligibility_policy_root: str
    claim_root: str

    def __post_init__(self) -> None:
        for name in (
            "promotion_subject_root",
            "source_schema_root",
            "source_receipt_root",
            "source_binding_root",
            "writer_profile_root",
            "authority_context_root",
            "current_state_root",
            "deployment_config_root",
            "authority_state_root",
            "expected_head_root",
            "expected_snapshot_root",
            "eligibility_policy_root",
            "claim_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _u64(self.authority_epoch, "authority_epoch")
        expected = _derive(
            "zenodex/fcis/m6/writer-profile-eligibility-claim/v1",
            _claim_body_from_values(
                {
                    name: object.__getattribute__(self, name)
                    for name in (
                        "promotion_subject_root",
                        "source_schema_root",
                        "source_receipt_root",
                        "source_binding_root",
                        "writer_profile_root",
                        "authority_context_root",
                        "current_state_root",
                        "deployment_config_root",
                        "authority_epoch",
                        "authority_state_root",
                        "expected_head_root",
                        "expected_snapshot_root",
                        "eligibility_policy_root",
                    )
                }
            ),
        )
        if self.claim_root != expected:
            raise WriterProfileEligibilityError("claim_root does not rederive")


def build_writer_profile_eligibility_claim_v1(
    *,
    promotion_subject_root: str,
    source_schema_root: str,
    source_receipt_root: str,
    source_binding_root: str,
    writer_profile_root: str,
    authority_context_root: str,
    current_state_root: str,
    deployment_config_root: str,
    authority_epoch: int,
    authority_state_root: str,
    expected_head_root: str,
    expected_snapshot_root: str,
    eligibility_policy_root: str,
) -> WriterProfileEligibilityClaimV1:
    """Build canonical data without granting eligibility authority."""

    values: dict[str, object] = {
        "promotion_subject_root": promotion_subject_root,
        "source_schema_root": source_schema_root,
        "source_receipt_root": source_receipt_root,
        "source_binding_root": source_binding_root,
        "writer_profile_root": writer_profile_root,
        "authority_context_root": authority_context_root,
        "current_state_root": current_state_root,
        "deployment_config_root": deployment_config_root,
        "authority_epoch": authority_epoch,
        "authority_state_root": authority_state_root,
        "expected_head_root": expected_head_root,
        "expected_snapshot_root": expected_snapshot_root,
        "eligibility_policy_root": eligibility_policy_root,
    }
    return WriterProfileEligibilityClaimV1(
        **values,  # type: ignore[arg-type]
        claim_root=_derive(
            "zenodex/fcis/m6/writer-profile-eligibility-claim/v1",
            _claim_body_from_values(values),
        ),
    )


class WriterProfileEligibilityVerifierAdapterV1(Protocol):
    """Shell-selected verifier for the complete source-bound claim."""

    def verify_writer_profile_eligibility(
        self,
        claim: object,
        *,
        expected_claim_root: object,
        expected_promotion_subject_root: object,
        expected_source_schema_root: object,
        expected_source_receipt_root: object,
        expected_source_binding_root: object,
        expected_writer_profile_root: object,
        expected_authority_context_root: object,
        expected_current_state_root: object,
        expected_deployment_config_root: object,
        expected_authority_epoch: object,
        expected_authority_state_root: object,
        expected_head_root: object,
        expected_snapshot_root: object,
        expected_eligibility_policy_root: object,
        expected_verifier_profile_root: object,
        expected_verification_evidence_root: object,
    ) -> object:
        """Return exact True only after independent verification."""


def _receipt_body(
    *,
    claim_root: str,
    verifier_profile_root: str,
    verification_evidence_root: str,
) -> dict[str, object]:
    return {
        "schema": WRITER_PROFILE_ELIGIBILITY_RECEIPT_SCHEMA_V1,
        "claim_root": claim_root,
        "verifier_profile_root": verifier_profile_root,
        "verification_evidence_root": verification_evidence_root,
    }


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class WriterProfileEligibilityReceiptV1:
    """Registered verifier result; J07 must recheck it at every use."""

    claim: WriterProfileEligibilityClaimV1
    verifier_profile_root: str
    verification_evidence_root: str
    receipt_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _RECEIPT_CONSTRUCTION_TOKEN_V1:
            raise TypeError("eligibility receipt requires the selected verifier")
        self._validate_fields()

    def _validate_fields(self) -> None:
        if type(self.claim) is not WriterProfileEligibilityClaimV1:
            raise TypeError("claim has the wrong exact type")
        self.claim.__post_init__()
        _digest(self.verifier_profile_root, "verifier_profile_root")
        _digest(self.verification_evidence_root, "verification_evidence_root")
        _digest(self.receipt_root, "receipt_root")
        expected = _derive(
            "zenodex/fcis/m6/writer-profile-eligibility-receipt/v1",
            _receipt_body(
                claim_root=self.claim.claim_root,
                verifier_profile_root=self.verifier_profile_root,
                verification_evidence_root=self.verification_evidence_root,
            ),
        )
        if self.receipt_root != expected:
            raise WriterProfileEligibilityError("receipt_root does not rederive")


_RECEIPTS_V1: WeakValueDictionary[int, WriterProfileEligibilityReceiptV1] = WeakValueDictionary()
_RECEIPT_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _receipt_snapshot(value: WriterProfileEligibilityReceiptV1) -> tuple[object, ...]:
    return (
        value.claim.claim_root,
        value.verifier_profile_root,
        value.verification_evidence_root,
        value.receipt_root,
    )


def is_verified_writer_profile_eligibility_receipt_v1(value: object) -> bool:
    """Revalidate construction provenance and all canonical bindings."""

    if type(value) is not WriterProfileEligibilityReceiptV1:
        return False
    receipt = value
    if _RECEIPTS_V1.get(id(receipt)) is not receipt:
        return False
    try:
        receipt._validate_fields()
        return _RECEIPT_SNAPSHOTS_V1.get(id(receipt)) == _receipt_snapshot(receipt)
    except (
        AttributeError,
        TypeError,
        ValueError,
        ArithmeticError,
        OverflowError,
        RecursionError,
    ):
        return False


WriterProfileEligibilityResultV1: TypeAlias = (
    WriterProfileEligibilityReceiptV1 | WriterProfileEligibilityRejectV1
)


def _external_verifier_accepts(
    claim: WriterProfileEligibilityClaimV1,
    *,
    verifier_profile_root: str,
    verification_evidence_root: str,
    verifier_adapter: object,
) -> bool:
    method = getattr(verifier_adapter, "verify_writer_profile_eligibility", None)
    if not callable(method):
        return False
    try:
        decision = cast(Callable[..., object], method)(
            claim,
            expected_claim_root=claim.claim_root,
            expected_promotion_subject_root=claim.promotion_subject_root,
            expected_source_schema_root=claim.source_schema_root,
            expected_source_receipt_root=claim.source_receipt_root,
            expected_source_binding_root=claim.source_binding_root,
            expected_writer_profile_root=claim.writer_profile_root,
            expected_authority_context_root=claim.authority_context_root,
            expected_current_state_root=claim.current_state_root,
            expected_deployment_config_root=claim.deployment_config_root,
            expected_authority_epoch=claim.authority_epoch,
            expected_authority_state_root=claim.authority_state_root,
            expected_head_root=claim.expected_head_root,
            expected_snapshot_root=claim.expected_snapshot_root,
            expected_eligibility_policy_root=claim.eligibility_policy_root,
            expected_verifier_profile_root=verifier_profile_root,
            expected_verification_evidence_root=verification_evidence_root,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return False
    return decision is True


def verify_writer_profile_eligibility_v1(
    *,
    claim: object,
    verifier_profile_root: object,
    verification_evidence_root: object,
    verifier_adapter: object,
) -> WriterProfileEligibilityResultV1:
    """Verify one complete claim and return a registered authority receipt."""

    if type(claim) is not WriterProfileEligibilityClaimV1:
        return _reject(WriterProfileEligibilityRejectCodeV1.WRONG_EXACT_TYPE, "claim")
    exact_claim = claim
    try:
        exact_claim.__post_init__()
        checked_verifier_root = _digest(verifier_profile_root, "verifier_profile_root")
        checked_evidence_root = _digest(
            verification_evidence_root,
            "verification_evidence_root",
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(WriterProfileEligibilityRejectCodeV1.INVALID_CLAIM, "claim")
    if not _external_verifier_accepts(
        exact_claim,
        verifier_profile_root=checked_verifier_root,
        verification_evidence_root=checked_evidence_root,
        verifier_adapter=verifier_adapter,
    ):
        return _reject(
            WriterProfileEligibilityRejectCodeV1.EXTERNAL_VERIFIER_REJECTED,
            "verifier",
        )
    body = _receipt_body(
        claim_root=exact_claim.claim_root,
        verifier_profile_root=checked_verifier_root,
        verification_evidence_root=checked_evidence_root,
    )
    try:
        receipt = WriterProfileEligibilityReceiptV1(
            claim=exact_claim,
            verifier_profile_root=checked_verifier_root,
            verification_evidence_root=checked_evidence_root,
            receipt_root=_derive(
                "zenodex/fcis/m6/writer-profile-eligibility-receipt/v1",
                body,
            ),
            _construction_token=_RECEIPT_CONSTRUCTION_TOKEN_V1,
        )
        _RECEIPTS_V1[id(receipt)] = receipt
        _RECEIPT_SNAPSHOTS_V1[id(receipt)] = _receipt_snapshot(receipt)
        return receipt
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(WriterProfileEligibilityRejectCodeV1.RECEIPT_REJECTED, "receipt")


__all__ = (
    "MAX_WRITER_PROFILE_AUTHORITY_EPOCH_V1",
    "WRITER_PROFILE_ELIGIBILITY_CLAIM_SCHEMA_V1",
    "WRITER_PROFILE_ELIGIBILITY_RECEIPT_SCHEMA_V1",
    "WriterProfileEligibilityClaimV1",
    "WriterProfileEligibilityError",
    "WriterProfileEligibilityReceiptV1",
    "WriterProfileEligibilityRejectCodeV1",
    "WriterProfileEligibilityRejectV1",
    "WriterProfileEligibilityResultV1",
    "WriterProfileEligibilityVerifierAdapterV1",
    "build_writer_profile_eligibility_claim_v1",
    "is_verified_writer_profile_eligibility_receipt_v1",
    "verify_writer_profile_eligibility_v1",
)
