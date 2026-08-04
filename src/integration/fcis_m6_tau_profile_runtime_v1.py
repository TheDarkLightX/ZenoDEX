"""Verifier-owned runtime receipts for the M6 Tau substrate profile.

This module refines the compact Tau profile and disposition relations into
typed Python values.  External verification remains an explicit shell premise.
The receipts are research evidence and are not commit capabilities, writer
tokens, deployment mounts, or permission to move value.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Callable, Final, Mapping, Protocol, TypeAlias, cast, final
from weakref import WeakValueDictionary

from ..core.fcis_m6_tau_profile_v1 import (
    TauIntegrationObservationV1,
    TauIntegrationProfileV1,
    TauOperationClassV1,
    TauProfileValueError,
    TauSubstrateDispositionV1,
    validate_capabilities_v1,
)
from ..state.canonical import canonical_json_bytes

TAU_PROFILE_VERIFICATION_CONTEXT_SCHEMA_V1: Final = (
    "zenodex/fcis/m6/tau-profile-verification-context/v1"
)
TAU_PROFILE_VERIFICATION_EVIDENCE_SCHEMA_V1: Final = (
    "zenodex/fcis/m6/tau-profile-verification-evidence/v1"
)
TAU_PROFILE_RECEIPT_SCHEMA_V1: Final = "zenodex/fcis/m6/tau-profile-receipt/v1"
TAU_DISPOSITION_CONTEXT_SCHEMA_V1: Final = "zenodex/fcis/m6/tau-disposition-context/v1"
TAU_DISPOSITION_EVIDENCE_SCHEMA_V1: Final = "zenodex/fcis/m6/tau-disposition-evidence/v1"
TAU_DISPOSITION_DECISION_SCHEMA_V1: Final = "zenodex/fcis/m6/tau-disposition-decision/v1"
TAU_WRITER_PROFILE_BINDING_SCHEMA_V1: Final = "zenodex/fcis/m6/tau-writer-profile-binding/v1"
MAX_TAU_PROFILE_AUTHORITY_EPOCH_V1: Final = (1 << 64) - 1

_PROFILE_RECEIPT_TOKEN_V1 = object()
_DISPOSITION_DECISION_TOKEN_V1 = object()
_WRITER_BINDING_TOKEN_V1 = object()
_HEX = frozenset("0123456789abcdef")
_PROFILE_INPUT_NAMES_V1: Final = tuple(f"i{index}" for index in range(1, 14))
_DISPOSITION_INPUT_NAMES_V1: Final = tuple(f"i{index}" for index in range(1, 15))
_PROFILE_ACCEPTING_INPUTS_V1: Final = (1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1)


class TauProfileRuntimeError(ValueError):
    """Raised when an internal runtime receipt violates its closed contract."""


class TauProfileRuntimeRejectCodeV1(str, Enum):
    """Stable fail-closed outcomes for this unmounted runtime refinement."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_PROFILE = "invalid_profile"
    INVALID_CONTEXT = "invalid_context"
    INVALID_EVIDENCE = "invalid_evidence"
    CONTEXT_MISMATCH = "context_mismatch"
    EXTERNAL_VERIFIER_REJECTED = "external_verifier_rejected"
    PROFILE_RECEIPT_REJECTED = "profile_receipt_rejected"
    PROFILE_NOT_USABLE = "profile_not_usable"
    DISPOSITION_REJECTED = "disposition_rejected"
    WRITER_PROFILE_MISMATCH = "writer_profile_mismatch"
    STALE_STATE = "stale_state"
    STALE_AUTHORITY_EPOCH = "stale_authority_epoch"


@final
@dataclass(frozen=True, slots=True)
class TauProfileRuntimeRejectV1:
    """Typed rejection carrying no successor, effect, token, or receipt."""

    code: TauProfileRuntimeRejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not TauProfileRuntimeRejectCodeV1:
            raise TauProfileRuntimeError("reject code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TauProfileRuntimeError("reject path must be an exact string tuple")


def _reject(code: TauProfileRuntimeRejectCodeV1, *path: str) -> TauProfileRuntimeRejectV1:
    return TauProfileRuntimeRejectV1(code=code, path=tuple(path))


def _text(value: object, name: str, *, maximum_bytes: int = 512) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be nonempty exact text")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise TypeError(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise TauProfileRuntimeError(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise TauProfileRuntimeError(f"{name} contains a control character")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if (
        len(checked) != 64
        or checked != checked.lower()
        or any(character not in _HEX for character in checked)
    ):
        raise TypeError(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _optional_digest(value: object, name: str) -> str | None:
    if value is None:
        return None
    return _digest(value, name)


def _u64(value: object, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_TAU_PROFILE_AUTHORITY_EPOCH_V1:
        raise TypeError(f"{name} must be an exact u64 integer")
    return value


def _derive(domain: str, body: Mapping[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(body)).hexdigest()


def _profile_context_body(value: "TauProfileVerificationContextV1") -> dict[str, object]:
    return {
        "schema": TAU_PROFILE_VERIFICATION_CONTEXT_SCHEMA_V1,
        "deployment_id": value.deployment_id,
        "promotion_subject_root": value.promotion_subject_root,
        "current_state_root": value.current_state_root,
        "deployment_config_root": value.deployment_config_root,
        "authority_epoch": value.authority_epoch,
        "expected_profile_root": value.expected_profile_root,
        "expected_governance_root": value.expected_governance_root,
        "expected_rule_history_root": value.expected_rule_history_root,
        "required_capabilities": list(value.required_capabilities),
        "expected_refinement_root": value.expected_refinement_root,
        "verifier_profile_root": value.verifier_profile_root,
    }


@final
@dataclass(frozen=True, slots=True)
class TauProfileVerificationContextV1:
    """Current-state and promotion-subject expectations for profile verification."""

    deployment_id: str
    promotion_subject_root: str
    current_state_root: str
    deployment_config_root: str
    authority_epoch: int
    expected_profile_root: str
    expected_governance_root: str
    expected_rule_history_root: str
    required_capabilities: tuple[str, ...]
    expected_refinement_root: str
    verifier_profile_root: str
    context_root: str

    def __post_init__(self) -> None:
        _text(self.deployment_id, "deployment_id")
        for name in (
            "promotion_subject_root",
            "current_state_root",
            "deployment_config_root",
            "expected_profile_root",
            "expected_governance_root",
            "expected_rule_history_root",
            "expected_refinement_root",
            "verifier_profile_root",
            "context_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _u64(self.authority_epoch, "authority_epoch")
        required = validate_capabilities_v1(self.required_capabilities, "required_capabilities")
        if not required:
            raise TauProfileRuntimeError("required_capabilities must not be empty")
        if self.context_root != _derive(
            "zenodex/fcis/m6/tau-profile-verification-context/v1",
            _profile_context_body(self),
        ):
            raise TauProfileRuntimeError("context_root does not rederive")


def build_tau_profile_verification_context_v1(
    *,
    deployment_id: str,
    promotion_subject_root: str,
    current_state_root: str,
    deployment_config_root: str,
    authority_epoch: int,
    expected_profile_root: str,
    expected_governance_root: str,
    expected_rule_history_root: str,
    required_capabilities: tuple[str, ...],
    expected_refinement_root: str,
    verifier_profile_root: str,
) -> TauProfileVerificationContextV1:
    values = {
        "deployment_id": deployment_id,
        "promotion_subject_root": promotion_subject_root,
        "current_state_root": current_state_root,
        "deployment_config_root": deployment_config_root,
        "authority_epoch": authority_epoch,
        "expected_profile_root": expected_profile_root,
        "expected_governance_root": expected_governance_root,
        "expected_rule_history_root": expected_rule_history_root,
        "required_capabilities": required_capabilities,
        "expected_refinement_root": expected_refinement_root,
        "verifier_profile_root": verifier_profile_root,
    }
    body = {"schema": TAU_PROFILE_VERIFICATION_CONTEXT_SCHEMA_V1, **values}
    body["required_capabilities"] = list(required_capabilities)
    return TauProfileVerificationContextV1(
        **values,  # type: ignore[arg-type]
        context_root=_derive(
            "zenodex/fcis/m6/tau-profile-verification-context/v1",
            body,
        ),
    )


def _profile_evidence_body(value: "TauProfileVerificationEvidenceV1") -> dict[str, object]:
    return {
        "schema": TAU_PROFILE_VERIFICATION_EVIDENCE_SCHEMA_V1,
        "observation": value.observation.value,
        "observed_profile_root": value.observed_profile_root,
        "observed_governance_root": value.observed_governance_root,
        "observed_rule_history_root": value.observed_rule_history_root,
        "observed_capabilities": list(value.observed_capabilities),
        "observed_refinement_root": value.observed_refinement_root,
        "profile_proof_root": value.profile_proof_root,
        "binding_context_root": value.binding_context_root,
    }


@final
@dataclass(frozen=True, slots=True)
class TauProfileVerificationEvidenceV1:
    """Untrusted evidence carrier awaiting the selected external verifier."""

    observation: TauIntegrationObservationV1
    observed_profile_root: str
    observed_governance_root: str
    observed_rule_history_root: str
    observed_capabilities: tuple[str, ...]
    observed_refinement_root: str
    profile_proof_root: str
    binding_context_root: str
    evidence_root: str

    def __post_init__(self) -> None:
        if type(self.observation) is not TauIntegrationObservationV1:
            raise TypeError("observation has the wrong exact type")
        for name in (
            "observed_profile_root",
            "observed_governance_root",
            "observed_rule_history_root",
            "observed_refinement_root",
            "profile_proof_root",
            "binding_context_root",
            "evidence_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        validate_capabilities_v1(self.observed_capabilities, "observed_capabilities")
        if self.evidence_root != _derive(
            "zenodex/fcis/m6/tau-profile-verification-evidence/v1",
            _profile_evidence_body(self),
        ):
            raise TauProfileRuntimeError("evidence_root does not rederive")


def build_tau_profile_verification_evidence_v1(
    *,
    observation: TauIntegrationObservationV1,
    observed_profile_root: str,
    observed_governance_root: str,
    observed_rule_history_root: str,
    observed_capabilities: tuple[str, ...],
    observed_refinement_root: str,
    profile_proof_root: str,
    binding_context_root: str,
) -> TauProfileVerificationEvidenceV1:
    values = {
        "observation": observation,
        "observed_profile_root": observed_profile_root,
        "observed_governance_root": observed_governance_root,
        "observed_rule_history_root": observed_rule_history_root,
        "observed_capabilities": observed_capabilities,
        "observed_refinement_root": observed_refinement_root,
        "profile_proof_root": profile_proof_root,
        "binding_context_root": binding_context_root,
    }
    body = {
        "schema": TAU_PROFILE_VERIFICATION_EVIDENCE_SCHEMA_V1,
        **values,
        "observation": observation.value,
        "observed_capabilities": list(observed_capabilities),
    }
    return TauProfileVerificationEvidenceV1(
        **values,  # type: ignore[arg-type]
        evidence_root=_derive(
            "zenodex/fcis/m6/tau-profile-verification-evidence/v1",
            body,
        ),
    )


class TauIntegrationProfileVerifierAdapterV1(Protocol):
    """Shell-selected verifier for source, proof, and profile observation facts."""

    def verify_tau_integration_profile(
        self,
        profile: object,
        evidence: object,
        *,
        expected_context_root: object,
        expected_promotion_subject_root: object,
        expected_current_state_root: object,
        expected_deployment_config_root: object,
        expected_authority_epoch: object,
        expected_verifier_profile_root: object,
    ) -> object:
        """Return exact True only after external verification."""


def _observation_bits(observation: TauIntegrationObservationV1) -> tuple[int, ...]:
    order = tuple(TauIntegrationObservationV1)
    return tuple(1 if observation is item else 0 for item in order)


def _profile_gate_inputs(
    profile: TauIntegrationProfileV1,
    context: TauProfileVerificationContextV1,
    evidence: TauProfileVerificationEvidenceV1,
    *,
    external_verifier_accepted: bool,
) -> dict[str, int]:
    observations = _observation_bits(evidence.observation)
    required_present = set(context.required_capabilities).issubset(evidence.observed_capabilities)
    observed_profile_matches = (
        evidence.observed_profile_root == profile.profile_root == context.expected_profile_root
    )
    return {
        "i1": observations[0],
        "i2": observations[1],
        "i3": observations[2],
        "i4": observations[3],
        "i5": observations[4],
        "i6": observations[5],
        "i7": int(required_present and evidence.observed_capabilities == profile.capabilities),
        "i8": int(
            evidence.observed_refinement_root
            == profile.refinement_root
            == context.expected_refinement_root
        ),
        "i9": int(observed_profile_matches),
        "i10": int(
            evidence.observed_governance_root
            == profile.governance_root
            == context.expected_governance_root
        ),
        "i11": int(
            evidence.observed_rule_history_root
            == profile.rule_history_root
            == context.expected_rule_history_root
        ),
        "i12": int(external_verifier_accepted is True),
        "i13": int(evidence.binding_context_root == context.context_root),
    }


def _profile_gate_accepts(inputs: dict[str, int]) -> bool:
    return tuple(inputs[name] for name in _PROFILE_INPUT_NAMES_V1) == (_PROFILE_ACCEPTING_INPUTS_V1)


def _profile_receipt_body(
    *,
    profile_root: str,
    context_root: str,
    evidence_root: str,
    gate_inputs: tuple[int, ...],
) -> dict[str, object]:
    return {
        "schema": TAU_PROFILE_RECEIPT_SCHEMA_V1,
        "profile_root": profile_root,
        "context_root": context_root,
        "evidence_root": evidence_root,
        "gate_inputs": list(gate_inputs),
        "profile_usable": gate_inputs == _PROFILE_ACCEPTING_INPUTS_V1,
    }


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class TauIntegrationProfileReceiptV1:
    """Verifier-owned observation receipt; usability is always rederived."""

    profile: TauIntegrationProfileV1
    context: TauProfileVerificationContextV1
    evidence: TauProfileVerificationEvidenceV1
    gate_inputs: tuple[int, ...]
    receipt_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _PROFILE_RECEIPT_TOKEN_V1:
            raise TypeError("Tau profile receipt requires the profile verifier")
        self._validate_fields()

    def _validate_fields(self) -> None:
        if type(self.profile) is not TauIntegrationProfileV1:
            raise TypeError("profile must be exact")
        if type(self.context) is not TauProfileVerificationContextV1:
            raise TypeError("context must be exact")
        if type(self.evidence) is not TauProfileVerificationEvidenceV1:
            raise TypeError("evidence must be exact")
        self.profile.__post_init__()
        self.context.__post_init__()
        self.evidence.__post_init__()
        if type(self.gate_inputs) is not tuple or len(self.gate_inputs) != 13:
            raise TypeError("gate_inputs must be an exact 13-bit tuple")
        if any(type(item) is not int or item not in (0, 1) for item in self.gate_inputs):
            raise TypeError("gate_inputs contain a non-sbf value")
        projected = _profile_gate_inputs(
            self.profile,
            self.context,
            self.evidence,
            external_verifier_accepted=True,
        )
        expected_inputs = tuple(projected[name] for name in _PROFILE_INPUT_NAMES_V1)
        if self.gate_inputs != expected_inputs:
            raise TauProfileRuntimeError("gate_inputs do not rederive")
        _digest(self.receipt_root, "receipt_root")
        expected_root = _derive(
            "zenodex/fcis/m6/tau-profile-receipt/v1",
            _profile_receipt_body(
                profile_root=self.profile.profile_root,
                context_root=self.context.context_root,
                evidence_root=self.evidence.evidence_root,
                gate_inputs=self.gate_inputs,
            ),
        )
        if self.receipt_root != expected_root:
            raise TauProfileRuntimeError("receipt_root does not rederive")

    @property
    def profile_usable(self) -> bool:
        self._validate_fields()
        return self.gate_inputs == _PROFILE_ACCEPTING_INPUTS_V1


_PROFILE_RECEIPTS_V1: WeakValueDictionary[int, TauIntegrationProfileReceiptV1] = (
    WeakValueDictionary()
)
_PROFILE_RECEIPT_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _profile_receipt_snapshot(value: TauIntegrationProfileReceiptV1) -> tuple[object, ...]:
    return (
        value.profile.profile_root,
        value.context.context_root,
        value.evidence.evidence_root,
        value.gate_inputs,
        value.receipt_root,
    )


def _register_profile_receipt(
    value: TauIntegrationProfileReceiptV1,
) -> TauIntegrationProfileReceiptV1:
    identity = id(value)
    _PROFILE_RECEIPTS_V1[identity] = value
    _PROFILE_RECEIPT_SNAPSHOTS_V1[identity] = _profile_receipt_snapshot(value)
    return value


def is_verified_tau_integration_profile_receipt_v1(value: object) -> bool:
    """Revalidate construction provenance and every receipt binding."""

    if type(value) is not TauIntegrationProfileReceiptV1:
        return False
    receipt = value
    if _PROFILE_RECEIPTS_V1.get(id(receipt)) is not receipt:
        return False
    try:
        receipt._validate_fields()
        return _PROFILE_RECEIPT_SNAPSHOTS_V1.get(id(receipt)) == _profile_receipt_snapshot(receipt)
    except (
        AttributeError,
        TauProfileRuntimeError,
        TauProfileValueError,
        TypeError,
        ValueError,
        ArithmeticError,
        OverflowError,
    ):
        return False


TauProfileVerificationResultV1: TypeAlias = (
    TauIntegrationProfileReceiptV1 | TauProfileRuntimeRejectV1
)


def _external_profile_verifier_accepts(
    profile: TauIntegrationProfileV1,
    context: TauProfileVerificationContextV1,
    evidence: TauProfileVerificationEvidenceV1,
    verifier_adapter: object,
) -> bool:
    method = getattr(verifier_adapter, "verify_tau_integration_profile", None)
    if not callable(method):
        return False
    try:
        decision = cast(Callable[..., object], method)(
            profile,
            evidence,
            expected_context_root=context.context_root,
            expected_promotion_subject_root=context.promotion_subject_root,
            expected_current_state_root=context.current_state_root,
            expected_deployment_config_root=context.deployment_config_root,
            expected_authority_epoch=context.authority_epoch,
            expected_verifier_profile_root=context.verifier_profile_root,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return False
    return decision is True


def verify_tau_integration_profile_v1(
    *,
    profile: object,
    context: object,
    evidence: object,
    verifier_adapter: object,
) -> TauProfileVerificationResultV1:
    """Verify one exact observation and mint a source/state-bound receipt."""

    if type(profile) is not TauIntegrationProfileV1:
        return _reject(TauProfileRuntimeRejectCodeV1.WRONG_EXACT_TYPE, "profile")
    if type(context) is not TauProfileVerificationContextV1:
        return _reject(TauProfileRuntimeRejectCodeV1.WRONG_EXACT_TYPE, "context")
    if type(evidence) is not TauProfileVerificationEvidenceV1:
        return _reject(TauProfileRuntimeRejectCodeV1.WRONG_EXACT_TYPE, "evidence")
    try:
        profile.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(TauProfileRuntimeRejectCodeV1.INVALID_PROFILE, "profile")
    try:
        context.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(TauProfileRuntimeRejectCodeV1.INVALID_CONTEXT, "context")
    try:
        evidence.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(TauProfileRuntimeRejectCodeV1.INVALID_EVIDENCE, "evidence")
    if profile.profile_root != context.expected_profile_root:
        return _reject(TauProfileRuntimeRejectCodeV1.CONTEXT_MISMATCH, "profile", "root")
    if evidence.binding_context_root != context.context_root:
        return _reject(TauProfileRuntimeRejectCodeV1.CONTEXT_MISMATCH, "evidence", "context")
    inputs = _profile_gate_inputs(
        profile,
        context,
        evidence,
        external_verifier_accepted=True,
    )
    if (
        evidence.observation is TauIntegrationObservationV1.VERIFIED_COMPATIBLE
        and not _profile_gate_accepts(inputs)
    ):
        return _reject(TauProfileRuntimeRejectCodeV1.INVALID_EVIDENCE, "evidence", "profile_gate")
    external_accepted = _external_profile_verifier_accepts(
        profile, context, evidence, verifier_adapter
    )
    if not external_accepted:
        return _reject(TauProfileRuntimeRejectCodeV1.EXTERNAL_VERIFIER_REJECTED, "verifier")
    gate_inputs = tuple(inputs[name] for name in _PROFILE_INPUT_NAMES_V1)
    body = _profile_receipt_body(
        profile_root=profile.profile_root,
        context_root=context.context_root,
        evidence_root=evidence.evidence_root,
        gate_inputs=gate_inputs,
    )
    try:
        return _register_profile_receipt(
            TauIntegrationProfileReceiptV1(
                profile=profile,
                context=context,
                evidence=evidence,
                gate_inputs=gate_inputs,
                receipt_root=_derive(
                    "zenodex/fcis/m6/tau-profile-receipt/v1",
                    body,
                ),
                _construction_token=_PROFILE_RECEIPT_TOKEN_V1,
            )
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(TauProfileRuntimeRejectCodeV1.PROFILE_RECEIPT_REJECTED, "receipt")


def project_tau_profile_gate_inputs_v1(value: object) -> dict[str, int]:
    """Project only a verifier-owned receipt into the exact 13 Tau inputs."""

    if not is_verified_tau_integration_profile_receipt_v1(value):
        raise TauProfileRuntimeError("profile receipt is not verifier-owned and unchanged")
    receipt = cast(TauIntegrationProfileReceiptV1, value)
    return {f"i{index}": bit for index, bit in enumerate(receipt.gate_inputs, start=1)}


def _disposition_context_body(value: "TauDispositionContextV1") -> dict[str, object]:
    return {
        "schema": TAU_DISPOSITION_CONTEXT_SCHEMA_V1,
        "profile_receipt_root": value.profile_receipt_root,
        "profile_context_root": value.profile_context_root,
        "promotion_subject_root": value.promotion_subject_root,
        "current_state_root": value.current_state_root,
        "deployment_config_root": value.deployment_config_root,
        "authority_epoch": value.authority_epoch,
        "expected_operation_root": value.expected_operation_root,
        "last_adopted_semantics_root": value.last_adopted_semantics_root,
        "zeno_ledger_state_root": value.zeno_ledger_state_root,
        "expected_portable_certificate_root": value.expected_portable_certificate_root,
        "expected_safe_exit_single_issuer_root": value.expected_safe_exit_single_issuer_root,
        "verifier_profile_root": value.verifier_profile_root,
    }


@final
@dataclass(frozen=True, slots=True)
class TauDispositionContextV1:
    """Exact current-state expectations for one substrate choice."""

    profile_receipt_root: str
    profile_context_root: str
    promotion_subject_root: str
    current_state_root: str
    deployment_config_root: str
    authority_epoch: int
    expected_operation_root: str
    last_adopted_semantics_root: str
    zeno_ledger_state_root: str
    expected_portable_certificate_root: str | None
    expected_safe_exit_single_issuer_root: str | None
    verifier_profile_root: str
    context_root: str

    def __post_init__(self) -> None:
        for name in (
            "profile_receipt_root",
            "profile_context_root",
            "promotion_subject_root",
            "current_state_root",
            "deployment_config_root",
            "expected_operation_root",
            "last_adopted_semantics_root",
            "zeno_ledger_state_root",
            "verifier_profile_root",
            "context_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _optional_digest(
            self.expected_portable_certificate_root,
            "expected_portable_certificate_root",
        )
        _optional_digest(
            self.expected_safe_exit_single_issuer_root,
            "expected_safe_exit_single_issuer_root",
        )
        _u64(self.authority_epoch, "authority_epoch")
        if self.context_root != _derive(
            "zenodex/fcis/m6/tau-disposition-context/v1",
            _disposition_context_body(self),
        ):
            raise TauProfileRuntimeError("disposition context_root does not rederive")


def build_tau_disposition_context_v1(
    *,
    profile_receipt: object,
    expected_operation_root: str,
    last_adopted_semantics_root: str,
    zeno_ledger_state_root: str,
    expected_portable_certificate_root: str | None,
    expected_safe_exit_single_issuer_root: str | None,
    verifier_profile_root: str,
) -> TauDispositionContextV1:
    if not is_verified_tau_integration_profile_receipt_v1(profile_receipt):
        raise TauProfileRuntimeError("disposition context requires a verified profile receipt")
    receipt = cast(TauIntegrationProfileReceiptV1, profile_receipt)
    values = {
        "profile_receipt_root": receipt.receipt_root,
        "profile_context_root": receipt.context.context_root,
        "promotion_subject_root": receipt.context.promotion_subject_root,
        "current_state_root": receipt.context.current_state_root,
        "deployment_config_root": receipt.context.deployment_config_root,
        "authority_epoch": receipt.context.authority_epoch,
        "expected_operation_root": expected_operation_root,
        "last_adopted_semantics_root": last_adopted_semantics_root,
        "zeno_ledger_state_root": zeno_ledger_state_root,
        "expected_portable_certificate_root": expected_portable_certificate_root,
        "expected_safe_exit_single_issuer_root": expected_safe_exit_single_issuer_root,
        "verifier_profile_root": verifier_profile_root,
    }
    body = {"schema": TAU_DISPOSITION_CONTEXT_SCHEMA_V1, **values}
    return TauDispositionContextV1(
        **values,  # type: ignore[arg-type]
        context_root=_derive("zenodex/fcis/m6/tau-disposition-context/v1", body),
    )


def _disposition_evidence_body(value: "TauDispositionEvidenceV1") -> dict[str, object]:
    return {
        "schema": TAU_DISPOSITION_EVIDENCE_SCHEMA_V1,
        "operation_class": value.operation_class.value,
        "proposed_disposition": value.proposed_disposition.value,
        "operation_root": value.operation_root,
        "portable_certificate_root": value.portable_certificate_root,
        "safe_exit_single_issuer_root": value.safe_exit_single_issuer_root,
        "observed_last_adopted_semantics_root": value.observed_last_adopted_semantics_root,
        "observed_zeno_ledger_state_root": value.observed_zeno_ledger_state_root,
        "request_proof_root": value.request_proof_root,
        "binding_context_root": value.binding_context_root,
    }


@final
@dataclass(frozen=True, slots=True)
class TauDispositionEvidenceV1:
    """Untrusted per-operation evidence; no caller-authored usability Boolean."""

    operation_class: TauOperationClassV1
    proposed_disposition: TauSubstrateDispositionV1
    operation_root: str
    portable_certificate_root: str | None
    safe_exit_single_issuer_root: str | None
    observed_last_adopted_semantics_root: str
    observed_zeno_ledger_state_root: str
    request_proof_root: str
    binding_context_root: str
    evidence_root: str

    def __post_init__(self) -> None:
        if type(self.operation_class) is not TauOperationClassV1:
            raise TypeError("operation_class has the wrong exact type")
        if type(self.proposed_disposition) is not TauSubstrateDispositionV1:
            raise TypeError("proposed_disposition has the wrong exact type")
        for name in (
            "operation_root",
            "observed_last_adopted_semantics_root",
            "observed_zeno_ledger_state_root",
            "request_proof_root",
            "binding_context_root",
            "evidence_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _optional_digest(self.portable_certificate_root, "portable_certificate_root")
        _optional_digest(
            self.safe_exit_single_issuer_root,
            "safe_exit_single_issuer_root",
        )
        if self.evidence_root != _derive(
            "zenodex/fcis/m6/tau-disposition-evidence/v1",
            _disposition_evidence_body(self),
        ):
            raise TauProfileRuntimeError("disposition evidence_root does not rederive")


def build_tau_disposition_evidence_v1(
    *,
    operation_class: TauOperationClassV1,
    proposed_disposition: TauSubstrateDispositionV1,
    operation_root: str,
    portable_certificate_root: str | None,
    safe_exit_single_issuer_root: str | None,
    observed_last_adopted_semantics_root: str,
    observed_zeno_ledger_state_root: str,
    request_proof_root: str,
    binding_context_root: str,
) -> TauDispositionEvidenceV1:
    values = {
        "operation_class": operation_class,
        "proposed_disposition": proposed_disposition,
        "operation_root": operation_root,
        "portable_certificate_root": portable_certificate_root,
        "safe_exit_single_issuer_root": safe_exit_single_issuer_root,
        "observed_last_adopted_semantics_root": observed_last_adopted_semantics_root,
        "observed_zeno_ledger_state_root": observed_zeno_ledger_state_root,
        "request_proof_root": request_proof_root,
        "binding_context_root": binding_context_root,
    }
    body = {
        "schema": TAU_DISPOSITION_EVIDENCE_SCHEMA_V1,
        **values,
        "operation_class": operation_class.value,
        "proposed_disposition": proposed_disposition.value,
    }
    return TauDispositionEvidenceV1(
        **values,  # type: ignore[arg-type]
        evidence_root=_derive("zenodex/fcis/m6/tau-disposition-evidence/v1", body),
    )


class TauSubstrateDispositionVerifierAdapterV1(Protocol):
    """Shell-selected verifier for operation, continuity, and safe-exit facts."""

    def verify_tau_substrate_disposition(
        self,
        evidence: object,
        *,
        expected_profile_receipt_root: object,
        expected_context_root: object,
        expected_promotion_subject_root: object,
        expected_current_state_root: object,
        expected_deployment_config_root: object,
        expected_authority_epoch: object,
        expected_operation_root: object,
        expected_verifier_profile_root: object,
    ) -> object:
        """Return exact True only after external verification."""


def _class_bits(value: TauOperationClassV1) -> tuple[int, int, int]:
    return tuple(int(value is member) for member in TauOperationClassV1)  # type: ignore[return-value]


def _disposition_bits(value: TauSubstrateDispositionV1) -> tuple[int, int, int]:
    return tuple(int(value is member) for member in TauSubstrateDispositionV1)  # type: ignore[return-value]


def project_tau_substrate_disposition_inputs_v1(
    *,
    profile_receipt: object,
    context: object,
    evidence: object,
    external_verifier_accepted: object,
) -> dict[str, int]:
    """Project exact runtime values into the fourteen Tau disposition inputs."""

    if not is_verified_tau_integration_profile_receipt_v1(profile_receipt):
        raise TauProfileRuntimeError("disposition projection requires a verified profile receipt")
    if type(context) is not TauDispositionContextV1:
        raise TypeError("disposition context has the wrong exact type")
    if type(evidence) is not TauDispositionEvidenceV1:
        raise TypeError("disposition evidence has the wrong exact type")
    if type(external_verifier_accepted) is not bool:
        raise TypeError("external_verifier_accepted must be an exact Boolean")
    receipt = cast(TauIntegrationProfileReceiptV1, profile_receipt)
    context.__post_init__()
    evidence.__post_init__()
    class_bits = _class_bits(evidence.operation_class)
    disposition_bits = _disposition_bits(evidence.proposed_disposition)
    portable = (
        context.expected_portable_certificate_root is not None
        and evidence.portable_certificate_root == context.expected_portable_certificate_root
    )
    safe_exit = (
        context.expected_safe_exit_single_issuer_root is not None
        and evidence.safe_exit_single_issuer_root == context.expected_safe_exit_single_issuer_root
    )
    bound = _disposition_context_matches_receipt(receipt, context, evidence)
    return {
        "i1": int(receipt.profile_usable),
        "i2": class_bits[0],
        "i3": class_bits[1],
        "i4": class_bits[2],
        "i5": int(portable),
        "i6": int(safe_exit),
        "i7": int(
            evidence.observed_last_adopted_semantics_root == context.last_adopted_semantics_root
        ),
        "i8": int(evidence.observed_zeno_ledger_state_root == context.zeno_ledger_state_root),
        "i9": disposition_bits[0],
        "i10": disposition_bits[1],
        "i11": disposition_bits[2],
        "i12": 1,
        "i13": int(external_verifier_accepted),
        "i14": int(bound),
    }


def _disposition_gate(inputs: dict[str, int]) -> tuple[bool, bool]:
    profile_usable = inputs["i1"] == 1
    independent = inputs["i2"] == 1
    dependent = inputs["i3"] == 1
    native = inputs["i4"] == 1
    operation_exact = sum((independent, dependent, native)) == 1
    use_tau = inputs["i9"] == 1
    use_ledger = inputs["i10"] == 1
    reject_or_pend = inputs["i11"] == 1
    request_bound = inputs["i12"] == inputs["i13"] == inputs["i14"] == 1
    continuity = inputs["i7"] == inputs["i8"] == 1 and (
        independent or (dependent and inputs["i5"] == 1) or (native and inputs["i6"] == 1)
    )
    branch_valid = (
        (use_tau and not use_ledger and not reject_or_pend and profile_usable)
        or (not use_tau and use_ledger and not reject_or_pend and not profile_usable and continuity)
        or (
            not use_tau
            and not use_ledger
            and reject_or_pend
            and not profile_usable
            and not continuity
        )
    )
    valid = request_bound and operation_exact and branch_valid
    return valid, valid and (use_tau or use_ledger)


def _disposition_decision_body(
    *,
    profile_receipt_root: str,
    context_root: str,
    evidence_root: str,
    inputs: tuple[int, ...],
    authorizes_execution: bool,
) -> dict[str, object]:
    return {
        "schema": TAU_DISPOSITION_DECISION_SCHEMA_V1,
        "profile_receipt_root": profile_receipt_root,
        "context_root": context_root,
        "evidence_root": evidence_root,
        "inputs": list(inputs),
        "authorizes_execution": authorizes_execution,
    }


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class TauSubstrateDispositionDecisionV1:
    """Verifier-owned valid disposition; it is not a commit capability."""

    profile_receipt_root: str
    context_root: str
    evidence_root: str
    inputs: tuple[int, ...]
    authorizes_execution: bool
    decision_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _DISPOSITION_DECISION_TOKEN_V1:
            raise TypeError("Tau disposition decision requires the disposition verifier")
        self._validate_fields()

    def _validate_fields(self) -> None:
        for name in ("profile_receipt_root", "context_root", "evidence_root", "decision_root"):
            _digest(object.__getattribute__(self, name), name)
        if type(self.inputs) is not tuple or len(self.inputs) != 14:
            raise TypeError("inputs must be an exact 14-bit tuple")
        if any(type(item) is not int or item not in (0, 1) for item in self.inputs):
            raise TypeError("inputs contain a non-sbf value")
        if type(self.authorizes_execution) is not bool:
            raise TypeError("authorizes_execution must be an exact Boolean")
        valid, authorized = _disposition_gate(
            {f"i{index}": bit for index, bit in enumerate(self.inputs, start=1)}
        )
        if not valid or authorized is not self.authorizes_execution:
            raise TauProfileRuntimeError("decision does not rederive from the Tau relation")
        expected = _derive(
            "zenodex/fcis/m6/tau-disposition-decision/v1",
            _disposition_decision_body(
                profile_receipt_root=self.profile_receipt_root,
                context_root=self.context_root,
                evidence_root=self.evidence_root,
                inputs=self.inputs,
                authorizes_execution=self.authorizes_execution,
            ),
        )
        if self.decision_root != expected:
            raise TauProfileRuntimeError("decision_root does not rederive")


_DISPOSITION_DECISIONS_V1: WeakValueDictionary[int, TauSubstrateDispositionDecisionV1] = (
    WeakValueDictionary()
)
_DISPOSITION_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _disposition_snapshot(value: TauSubstrateDispositionDecisionV1) -> tuple[object, ...]:
    return (
        value.profile_receipt_root,
        value.context_root,
        value.evidence_root,
        value.inputs,
        value.authorizes_execution,
        value.decision_root,
    )


def is_verified_tau_substrate_disposition_v1(value: object) -> bool:
    if type(value) is not TauSubstrateDispositionDecisionV1:
        return False
    decision = value
    if _DISPOSITION_DECISIONS_V1.get(id(decision)) is not decision:
        return False
    try:
        decision._validate_fields()
        return _DISPOSITION_SNAPSHOTS_V1.get(id(decision)) == _disposition_snapshot(decision)
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


TauDispositionResultV1: TypeAlias = TauSubstrateDispositionDecisionV1 | TauProfileRuntimeRejectV1


def _external_disposition_verifier_accepts(
    evidence: TauDispositionEvidenceV1,
    context: TauDispositionContextV1,
    verifier_adapter: object,
) -> bool:
    method = getattr(verifier_adapter, "verify_tau_substrate_disposition", None)
    if not callable(method):
        return False
    try:
        decision = cast(Callable[..., object], method)(
            evidence,
            expected_profile_receipt_root=context.profile_receipt_root,
            expected_context_root=context.context_root,
            expected_promotion_subject_root=context.promotion_subject_root,
            expected_current_state_root=context.current_state_root,
            expected_deployment_config_root=context.deployment_config_root,
            expected_authority_epoch=context.authority_epoch,
            expected_operation_root=context.expected_operation_root,
            expected_verifier_profile_root=context.verifier_profile_root,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return False
    return decision is True


def _disposition_context_matches_receipt(
    receipt: TauIntegrationProfileReceiptV1,
    context: TauDispositionContextV1,
    evidence: TauDispositionEvidenceV1,
) -> bool:
    return (
        context.profile_receipt_root == receipt.receipt_root
        and context.profile_context_root == receipt.context.context_root
        and context.promotion_subject_root == receipt.context.promotion_subject_root
        and context.current_state_root == receipt.context.current_state_root
        and context.deployment_config_root == receipt.context.deployment_config_root
        and context.authority_epoch == receipt.context.authority_epoch
        and evidence.operation_root == context.expected_operation_root
        and evidence.binding_context_root == context.context_root
    )


def verify_tau_substrate_disposition_v1(
    *,
    profile_receipt: object,
    context: object,
    evidence: object,
    verifier_adapter: object,
) -> TauDispositionResultV1:
    """Verify one disposition against the exact profile observation receipt."""

    if not is_verified_tau_integration_profile_receipt_v1(profile_receipt):
        return _reject(TauProfileRuntimeRejectCodeV1.PROFILE_RECEIPT_REJECTED, "profile_receipt")
    if type(context) is not TauDispositionContextV1:
        return _reject(TauProfileRuntimeRejectCodeV1.WRONG_EXACT_TYPE, "context")
    if type(evidence) is not TauDispositionEvidenceV1:
        return _reject(TauProfileRuntimeRejectCodeV1.WRONG_EXACT_TYPE, "evidence")
    receipt = cast(TauIntegrationProfileReceiptV1, profile_receipt)
    try:
        context.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(TauProfileRuntimeRejectCodeV1.INVALID_CONTEXT, "context")
    try:
        evidence.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(TauProfileRuntimeRejectCodeV1.INVALID_EVIDENCE, "evidence")
    if not _disposition_context_matches_receipt(receipt, context, evidence):
        return _reject(TauProfileRuntimeRejectCodeV1.CONTEXT_MISMATCH, "context", "binding")
    external_accepted = _external_disposition_verifier_accepts(evidence, context, verifier_adapter)
    if not external_accepted:
        return _reject(TauProfileRuntimeRejectCodeV1.EXTERNAL_VERIFIER_REJECTED, "verifier")
    try:
        inputs = project_tau_substrate_disposition_inputs_v1(
            profile_receipt=receipt,
            context=context,
            evidence=evidence,
            external_verifier_accepted=True,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(TauProfileRuntimeRejectCodeV1.CONTEXT_MISMATCH, "binding")
    valid, authorized = _disposition_gate(inputs)
    if not valid:
        return _reject(TauProfileRuntimeRejectCodeV1.DISPOSITION_REJECTED, "disposition")
    input_tuple = tuple(inputs[name] for name in _DISPOSITION_INPUT_NAMES_V1)
    body = _disposition_decision_body(
        profile_receipt_root=receipt.receipt_root,
        context_root=context.context_root,
        evidence_root=evidence.evidence_root,
        inputs=input_tuple,
        authorizes_execution=authorized,
    )
    decision = TauSubstrateDispositionDecisionV1(
        profile_receipt_root=receipt.receipt_root,
        context_root=context.context_root,
        evidence_root=evidence.evidence_root,
        inputs=input_tuple,
        authorizes_execution=authorized,
        decision_root=_derive(
            "zenodex/fcis/m6/tau-disposition-decision/v1",
            body,
        ),
        _construction_token=_DISPOSITION_DECISION_TOKEN_V1,
    )
    _DISPOSITION_DECISIONS_V1[id(decision)] = decision
    _DISPOSITION_SNAPSHOTS_V1[id(decision)] = _disposition_snapshot(decision)
    return decision


def _writer_binding_body(
    *,
    profile_receipt_root: str,
    writer_profile_root: str,
    current_state_root: str,
    deployment_config_root: str,
    authority_epoch: int,
) -> dict[str, object]:
    return {
        "schema": TAU_WRITER_PROFILE_BINDING_SCHEMA_V1,
        "profile_receipt_root": profile_receipt_root,
        "writer_profile_root": writer_profile_root,
        "current_state_root": current_state_root,
        "deployment_config_root": deployment_config_root,
        "authority_epoch": authority_epoch,
    }


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class TauWriterProfileBindingV1:
    """Exact profile-to-writer target binding; never a J07 writer token."""

    profile_receipt_root: str
    writer_profile_root: str
    current_state_root: str
    deployment_config_root: str
    authority_epoch: int
    binding_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _WRITER_BINDING_TOKEN_V1:
            raise TypeError("Tau writer binding requires the writer-profile binder")
        self._validate_fields()

    def _validate_fields(self) -> None:
        for name in (
            "profile_receipt_root",
            "writer_profile_root",
            "current_state_root",
            "deployment_config_root",
            "binding_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _u64(self.authority_epoch, "authority_epoch")
        expected = _derive(
            "zenodex/fcis/m6/tau-writer-profile-binding/v1",
            _writer_binding_body(
                profile_receipt_root=self.profile_receipt_root,
                writer_profile_root=self.writer_profile_root,
                current_state_root=self.current_state_root,
                deployment_config_root=self.deployment_config_root,
                authority_epoch=self.authority_epoch,
            ),
        )
        if self.binding_root != expected:
            raise TauProfileRuntimeError("writer binding_root does not rederive")


_WRITER_BINDINGS_V1: WeakValueDictionary[int, TauWriterProfileBindingV1] = WeakValueDictionary()
_WRITER_BINDING_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _writer_binding_snapshot(value: TauWriterProfileBindingV1) -> tuple[object, ...]:
    return (
        value.profile_receipt_root,
        value.writer_profile_root,
        value.current_state_root,
        value.deployment_config_root,
        value.authority_epoch,
        value.binding_root,
    )


def is_verified_tau_writer_profile_binding_v1(value: object) -> bool:
    if type(value) is not TauWriterProfileBindingV1:
        return False
    binding = value
    if _WRITER_BINDINGS_V1.get(id(binding)) is not binding:
        return False
    try:
        binding._validate_fields()
        return _WRITER_BINDING_SNAPSHOTS_V1.get(id(binding)) == _writer_binding_snapshot(binding)
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


TauWriterProfileBindingResultV1: TypeAlias = TauWriterProfileBindingV1 | TauProfileRuntimeRejectV1


def bind_tau_profile_to_writer_target_v1(
    *,
    profile_receipt: object,
    expected_writer_profile_root: object,
    current_state_root: object,
    deployment_config_root: object,
    authority_epoch: object,
) -> TauWriterProfileBindingResultV1:
    """Bind a usable receipt to one exact current writer-target coordinate."""

    if not is_verified_tau_integration_profile_receipt_v1(profile_receipt):
        return _reject(TauProfileRuntimeRejectCodeV1.PROFILE_RECEIPT_REJECTED, "profile_receipt")
    receipt = cast(TauIntegrationProfileReceiptV1, profile_receipt)
    if not receipt.profile_usable:
        return _reject(TauProfileRuntimeRejectCodeV1.PROFILE_NOT_USABLE, "profile_receipt")
    try:
        writer_root = _digest(expected_writer_profile_root, "expected_writer_profile_root")
        state_root = _digest(current_state_root, "current_state_root")
        deployment_root = _digest(deployment_config_root, "deployment_config_root")
        epoch = _u64(authority_epoch, "authority_epoch")
    except (TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(TauProfileRuntimeRejectCodeV1.WRONG_EXACT_TYPE, "writer_binding")
    if writer_root != receipt.profile.writer_profile_root:
        return _reject(TauProfileRuntimeRejectCodeV1.WRITER_PROFILE_MISMATCH, "writer_profile")
    if state_root != receipt.context.current_state_root:
        return _reject(TauProfileRuntimeRejectCodeV1.STALE_STATE, "current_state_root")
    if deployment_root != receipt.context.deployment_config_root:
        return _reject(TauProfileRuntimeRejectCodeV1.CONTEXT_MISMATCH, "deployment_config_root")
    if epoch != receipt.context.authority_epoch:
        return _reject(TauProfileRuntimeRejectCodeV1.STALE_AUTHORITY_EPOCH, "authority_epoch")
    body = _writer_binding_body(
        profile_receipt_root=receipt.receipt_root,
        writer_profile_root=writer_root,
        current_state_root=state_root,
        deployment_config_root=deployment_root,
        authority_epoch=epoch,
    )
    binding = TauWriterProfileBindingV1(
        profile_receipt_root=receipt.receipt_root,
        writer_profile_root=writer_root,
        current_state_root=state_root,
        deployment_config_root=deployment_root,
        authority_epoch=epoch,
        binding_root=_derive(
            "zenodex/fcis/m6/tau-writer-profile-binding/v1",
            body,
        ),
        _construction_token=_WRITER_BINDING_TOKEN_V1,
    )
    _WRITER_BINDINGS_V1[id(binding)] = binding
    _WRITER_BINDING_SNAPSHOTS_V1[id(binding)] = _writer_binding_snapshot(binding)
    return binding


__all__ = (
    "MAX_TAU_PROFILE_AUTHORITY_EPOCH_V1",
    "TAU_DISPOSITION_CONTEXT_SCHEMA_V1",
    "TAU_DISPOSITION_DECISION_SCHEMA_V1",
    "TAU_DISPOSITION_EVIDENCE_SCHEMA_V1",
    "TAU_PROFILE_RECEIPT_SCHEMA_V1",
    "TAU_PROFILE_VERIFICATION_CONTEXT_SCHEMA_V1",
    "TAU_PROFILE_VERIFICATION_EVIDENCE_SCHEMA_V1",
    "TAU_WRITER_PROFILE_BINDING_SCHEMA_V1",
    "TauDispositionContextV1",
    "TauDispositionEvidenceV1",
    "TauDispositionResultV1",
    "TauIntegrationProfileReceiptV1",
    "TauIntegrationProfileVerifierAdapterV1",
    "TauProfileRuntimeError",
    "TauProfileRuntimeRejectCodeV1",
    "TauProfileRuntimeRejectV1",
    "TauProfileVerificationContextV1",
    "TauProfileVerificationEvidenceV1",
    "TauProfileVerificationResultV1",
    "TauSubstrateDispositionDecisionV1",
    "TauSubstrateDispositionVerifierAdapterV1",
    "TauWriterProfileBindingResultV1",
    "TauWriterProfileBindingV1",
    "bind_tau_profile_to_writer_target_v1",
    "build_tau_disposition_context_v1",
    "build_tau_disposition_evidence_v1",
    "build_tau_profile_verification_context_v1",
    "build_tau_profile_verification_evidence_v1",
    "is_verified_tau_integration_profile_receipt_v1",
    "is_verified_tau_substrate_disposition_v1",
    "is_verified_tau_writer_profile_binding_v1",
    "project_tau_profile_gate_inputs_v1",
    "project_tau_substrate_disposition_inputs_v1",
    "verify_tau_integration_profile_v1",
    "verify_tau_substrate_disposition_v1",
)
