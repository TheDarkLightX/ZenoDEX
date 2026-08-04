"""Tau-to-J07 refinement for substrate-neutral writer eligibility.

The adapter consumes one registered Tau profile receipt, its exact writer
binding, and the current registered J07 authority context.  It projects those
sources into the generic writer-profile eligibility claim and delegates the
final decision to a shell-selected verifier.  The result is research evidence,
not a writer token, commit capability, deployment mount, or permission to move
value.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from hashlib import sha256
from typing import Final, Mapping, TypeAlias, cast, final

from ..core.fcis_m6_j07_authority_switch import (
    FCIS_M6_J07_CONTEXT_SCHEMA_V1,
    J07AuthorityContextV1,
    is_verified_authority_context_v1,
)
from ..core.fcis_m6_writer_profile_eligibility_v1 import (
    WriterProfileEligibilityReceiptV1,
    WriterProfileEligibilityVerifierAdapterV1,
    build_writer_profile_eligibility_claim_v1,
    verify_writer_profile_eligibility_v1,
)
from ..state.canonical import canonical_json_bytes
from .fcis_m6_tau_profile_runtime_v1 import (
    TAU_PROFILE_RECEIPT_SCHEMA_V1,
    TAU_WRITER_PROFILE_BINDING_SCHEMA_V1,
    TauIntegrationProfileReceiptV1,
    TauWriterProfileBindingV1,
    is_verified_tau_integration_profile_receipt_v1,
    is_verified_tau_writer_profile_binding_v1,
)

TAU_J07_WRITER_ELIGIBILITY_ADAPTER_SCHEMA_V1: Final = (
    "zenodex/fcis/m6/tau-j07-writer-eligibility-adapter/v1"
)
_HEX_DIGITS = frozenset("0123456789abcdef")


class TauJ07WriterEligibilityError(ValueError):
    """Raised when adapter-owned data violates its closed contract."""


class TauJ07WriterEligibilityRejectCodeV1(str, Enum):
    """Stable authority-empty failure classes for the Tau refinement."""

    PROFILE_RECEIPT_REJECTED = "profile_receipt_rejected"
    PROFILE_NOT_USABLE = "profile_not_usable"
    WRITER_BINDING_REJECTED = "writer_binding_rejected"
    AUTHORITY_CONTEXT_REJECTED = "authority_context_rejected"
    SOURCE_BINDING_MISMATCH = "source_binding_mismatch"
    J07_CONTEXT_MISMATCH = "j07_context_mismatch"
    INVALID_POLICY = "invalid_policy"
    ELIGIBILITY_REJECTED = "eligibility_rejected"


@final
@dataclass(frozen=True, slots=True)
class TauJ07WriterEligibilityRejectV1:
    """Typed rejection carrying no eligibility receipt or writer token."""

    code: TauJ07WriterEligibilityRejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not TauJ07WriterEligibilityRejectCodeV1:
            raise TauJ07WriterEligibilityError("reject code has the wrong exact type")
        if type(self.path) is not tuple or not self.path:
            raise TauJ07WriterEligibilityError("reject path must be a nonempty exact tuple")
        if len(self.path) > 8 or any(type(part) is not str or not part for part in self.path):
            raise TauJ07WriterEligibilityError("reject path is outside its closed bound")


def _reject(
    code: TauJ07WriterEligibilityRejectCodeV1,
    *path: str,
) -> TauJ07WriterEligibilityRejectV1:
    return TauJ07WriterEligibilityRejectV1(code=code, path=tuple(path))


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or value != value.lower()
        or any(character not in _HEX_DIGITS for character in value)
    ):
        raise TauJ07WriterEligibilityError(f"{name} must be a lowercase SHA-256 digest")
    return value


def _derive(domain: str, body: Mapping[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(body)).hexdigest()


TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V1: Final = _derive(
    "zenodex/fcis/m6/tau-j07-writer-eligibility/source-schema/v1",
    {
        "adapter_schema": TAU_J07_WRITER_ELIGIBILITY_ADAPTER_SCHEMA_V1,
        "tau_profile_receipt_schema": TAU_PROFILE_RECEIPT_SCHEMA_V1,
        "tau_writer_binding_schema": TAU_WRITER_PROFILE_BINDING_SCHEMA_V1,
        "j07_context_schema": FCIS_M6_J07_CONTEXT_SCHEMA_V1,
    },
)


def _source_mismatch(
    receipt: TauIntegrationProfileReceiptV1,
    binding: TauWriterProfileBindingV1,
) -> tuple[str, ...] | None:
    comparisons = (
        ("profile_receipt", binding.profile_receipt_root, receipt.receipt_root),
        ("writer_profile", binding.writer_profile_root, receipt.profile.writer_profile_root),
        ("state", binding.current_state_root, receipt.context.current_state_root),
        (
            "deployment",
            binding.deployment_config_root,
            receipt.context.deployment_config_root,
        ),
        ("epoch", binding.authority_epoch, receipt.context.authority_epoch),
    )
    for name, observed, expected in comparisons:
        if observed != expected:
            return ("source", name)
    return None


def _j07_mismatch(
    binding: TauWriterProfileBindingV1,
    context: J07AuthorityContextV1,
) -> tuple[str, ...] | None:
    comparisons = (
        ("state", context.current_state_root, binding.current_state_root),
        ("deployment", context.deployment_config_root, binding.deployment_config_root),
        ("epoch", context.epoch_index, binding.authority_epoch),
        ("active_writer", context.active_profile_root, binding.writer_profile_root),
        ("target_writer", context.target_profile_root, binding.writer_profile_root),
    )
    for name, observed, expected in comparisons:
        if observed != expected:
            return ("j07_context", name)
    if binding.writer_profile_root not in context.allowed_writer_roots:
        return ("j07_context", "allowed_writer")
    return None


TauJ07WriterEligibilityResultV1: TypeAlias = (
    WriterProfileEligibilityReceiptV1 | TauJ07WriterEligibilityRejectV1
)


def verify_tau_j07_writer_profile_eligibility_v1(
    *,
    profile_receipt: object,
    writer_binding: object,
    authority_context: object,
    eligibility_policy_root: object,
    verifier_profile_root: object,
    verifier_adapter: WriterProfileEligibilityVerifierAdapterV1 | object,
) -> TauJ07WriterEligibilityResultV1:
    """Refine exact Tau evidence into one generic J07 eligibility receipt."""

    if not is_verified_tau_integration_profile_receipt_v1(profile_receipt):
        return _reject(
            TauJ07WriterEligibilityRejectCodeV1.PROFILE_RECEIPT_REJECTED,
            "profile_receipt",
        )
    receipt = cast(TauIntegrationProfileReceiptV1, profile_receipt)
    if not receipt.profile_usable:
        return _reject(
            TauJ07WriterEligibilityRejectCodeV1.PROFILE_NOT_USABLE,
            "profile_receipt",
        )
    if not is_verified_tau_writer_profile_binding_v1(writer_binding):
        return _reject(
            TauJ07WriterEligibilityRejectCodeV1.WRITER_BINDING_REJECTED,
            "writer_binding",
        )
    binding = cast(TauWriterProfileBindingV1, writer_binding)
    if not is_verified_authority_context_v1(authority_context):
        return _reject(
            TauJ07WriterEligibilityRejectCodeV1.AUTHORITY_CONTEXT_REJECTED,
            "authority_context",
        )
    context = cast(J07AuthorityContextV1, authority_context)
    source_mismatch = _source_mismatch(receipt, binding)
    if source_mismatch is not None:
        return _reject(
            TauJ07WriterEligibilityRejectCodeV1.SOURCE_BINDING_MISMATCH,
            *source_mismatch,
        )
    context_mismatch = _j07_mismatch(binding, context)
    if context_mismatch is not None:
        return _reject(
            TauJ07WriterEligibilityRejectCodeV1.J07_CONTEXT_MISMATCH,
            *context_mismatch,
        )
    try:
        policy_root = _digest(eligibility_policy_root, "eligibility_policy_root")
        selected_verifier_root = _digest(verifier_profile_root, "verifier_profile_root")
        claim = build_writer_profile_eligibility_claim_v1(
            promotion_subject_root=receipt.context.promotion_subject_root,
            source_schema_root=TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V1,
            source_receipt_root=receipt.receipt_root,
            source_binding_root=binding.binding_root,
            writer_profile_root=binding.writer_profile_root,
            authority_context_root=context.context_root,
            current_state_root=context.current_state_root,
            deployment_config_root=context.deployment_config_root,
            authority_epoch=context.epoch_index,
            authority_state_root=context.authority_state_root,
            expected_head_root=context.current_head_root,
            expected_snapshot_root=context.current_snapshot_root,
            eligibility_policy_root=policy_root,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(TauJ07WriterEligibilityRejectCodeV1.INVALID_POLICY, "policy")
    evidence_root = _derive(
        "zenodex/fcis/m6/tau-j07-writer-eligibility/evidence/v1",
        {
            "claim_root": claim.claim_root,
            "profile_receipt_root": receipt.receipt_root,
            "writer_binding_root": binding.binding_root,
            "authority_context_root": context.context_root,
            "eligibility_policy_root": policy_root,
            "verifier_profile_root": selected_verifier_root,
        },
    )
    result = verify_writer_profile_eligibility_v1(
        claim=claim,
        verifier_profile_root=selected_verifier_root,
        verification_evidence_root=evidence_root,
        verifier_adapter=verifier_adapter,
    )
    if type(result) is not WriterProfileEligibilityReceiptV1:
        return _reject(
            TauJ07WriterEligibilityRejectCodeV1.ELIGIBILITY_REJECTED,
            "eligibility",
        )
    return result


__all__ = (
    "TAU_J07_WRITER_ELIGIBILITY_ADAPTER_SCHEMA_V1",
    "TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V1",
    "TauJ07WriterEligibilityError",
    "TauJ07WriterEligibilityRejectCodeV1",
    "TauJ07WriterEligibilityRejectV1",
    "TauJ07WriterEligibilityResultV1",
    "verify_tau_j07_writer_profile_eligibility_v1",
)
