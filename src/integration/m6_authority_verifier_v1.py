"""M6 authority adapter for the existing Tau verification port.

The current Tau retrieval/finality surface deliberately produces read-only
receipts.  Those receipts are useful evidence, yet they do not authorize an
M6 escrow credit, withdrawal acknowledgment, or migration.  This adapter
accepts an M6-aware verifier through the existing Tau state-proof port and
requires a closed, exact receipt before the core can issue its opaque
authority witness.

The module is research-only.  It contains no Tau cryptography and no
objective migration-liveness verifier.  A missing backend, a read-only
receipt, a rejected receipt, or any binding mismatch fails closed.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import islice
from typing import Mapping, Protocol

from src.core.m6_authority_evidence_v1 import (
    M6AuthorityVerificationReceiptV1,
    _issue_m6_authority_verification_receipt_v1,
)
from src.core.m6_safe_mount_types_v1 import (
    GlobalCommandKindV1,
    MigrationAuthorityProofV1,
    MigrationEvidenceKindV1,
    TauFinalityBoundDepositWitnessV1,
    WithdrawalAcknowledgmentV1,
    hash_v1,
)
from src.state.canonical import canonical_hex_fixed_allow_0x

M6_AUTHORITY_REQUEST_SCHEMA_V1 = "zenodex/m6/authority-verification-request/v1"
M6_AUTHORITY_RECEIPT_SCHEMA_V1 = "zenodex/m6/authority-verification-receipt/v1"
TAU_STATE_PROOF_REQUEST_SCHEMA_V0 = "tau_state_proof_verify"
M6_AUTHORITY_RECEIPT_HASH_DOMAIN_V1 = "m6-authority-verification-receipt-v1"


class M6AuthorityVerificationError(ValueError):
    """Base error for an M6 authority adapter refusal."""


class M6AuthorityVerifierUnavailableV1(M6AuthorityVerificationError):
    """No external verifier capable of issuing M6 authority is mounted."""


class M6AuthorityProofRejectedV1(M6AuthorityVerificationError):
    """The external verifier rejected or failed to authenticate the evidence."""


class M6AuthorityVerifierInternalFailureV1(M6AuthorityVerificationError):
    """The verifier boundary failed before returning an authority decision."""


class M6MigrationVerifierV1(Protocol):
    """Port for objective fallback/rejoin evidence verification."""

    def verify_m6_migration(self, request: Mapping[str, object]) -> Mapping[str, object]:
        """Return one exact M6 authority receipt or a rejection."""


class M6TauStateProofVerifierV1(Protocol):
    """Minimal structural port required by the M6 Tau authority adapter."""

    def verify_tau_state_proof(
        self,
        request: Mapping[str, object],
    ) -> Mapping[str, object]:
        """Return one exact M6-aware Tau authority receipt or a rejection."""


def _require_root(value: object, *, name: str, allow_zero: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    if not allow_zero and canonical == "0x" + "00" * 32:
        raise ValueError(f"{name} must be nonzero")
    return canonical


def _snapshot_receipt_mapping(
    value: object,
    *,
    name: str,
    max_items: int,
) -> dict[str, object]:
    """Own one stable observation of an untrusted verifier receipt.

    Hostile ``__iter__``, ``keys``, ``__len__``, ``__getitem__``, or
    cyclic references must not leak provider exceptions, context, or
    secret text through the authority adapter boundary.
    """

    if not isinstance(value, Mapping):
        raise M6AuthorityProofRejectedV1(f"{name} must be an object")
    try:
        keys = list(islice(iter(value), max_items + 1))
    except Exception:
        raise M6AuthorityProofRejectedV1(f"{name} could not be read") from None
    if len(keys) > max_items:
        raise M6AuthorityProofRejectedV1("M6 authority receipt binding mismatch")
    if any(type(key) is not str for key in keys):
        raise M6AuthorityProofRejectedV1(f"{name} could not be read")
    try:
        snapshot = {key: value[key] for key in keys}
    except Exception:
        raise M6AuthorityProofRejectedV1(f"{name} could not be read") from None
    if len(snapshot) != len(keys):
        raise M6AuthorityProofRejectedV1(f"{name} could not be read")
    return snapshot


def _require_receipt(
    receipt: object,
    *,
    expected: Mapping[str, object],
) -> str:
    actual = _snapshot_receipt_mapping(
        receipt,
        name="M6 authority verifier receipt",
        max_items=len(expected) + 1,
    )
    expected_body = dict(expected)
    expected_hash = hash_v1(M6_AUTHORITY_RECEIPT_HASH_DOMAIN_V1, expected_body)
    bound = {**expected_body, "receipt_hash": expected_hash}
    if any(type(key) is not str for key in actual):
        raise M6AuthorityProofRejectedV1("M6 authority receipt binding mismatch")
    if actual.get("ok") is not True:
        raise M6AuthorityProofRejectedV1("M6 authority verifier rejected the evidence")
    if len(actual) != len(bound) or set(actual) != set(bound):
        raise M6AuthorityProofRejectedV1("M6 authority receipt binding mismatch")
    for key, expected_value in bound.items():
        # The receipt ABI is deliberately primitive-only. Exact built-in types
        # prevent verifier-controlled subclasses or objects from supplying
        # hostile equality methods at this authority boundary.
        if type(expected_value) not in {str, int, bool}:  # pragma: no cover - internal contract
            raise RuntimeError("M6 authority receipt expectation is not primitive")
        actual_value = actual[key]
        if type(actual_value) is not type(expected_value) or actual_value != expected_value:
            raise M6AuthorityProofRejectedV1("M6 authority receipt binding mismatch")
    return expected_hash


def _base_request(
    *,
    kind: str,
    subject_root: str,
    pre_state_root: str,
    command_hash: str,
    evidence_root: str,
    proof: Mapping[str, object],
) -> dict[str, object]:
    return {
        "schema": M6_AUTHORITY_REQUEST_SCHEMA_V1,
        "kind": kind,
        "subject_root": _require_root(subject_root, name="M6 authority subject root"),
        "pre_state_root": _require_root(pre_state_root, name="M6 authority pre-state root"),
        "command_hash": _require_root(command_hash, name="M6 authority command hash"),
        "evidence_root": _require_root(evidence_root, name="M6 authority evidence root"),
        "proof": dict(proof),
    }


def _tau_state_proof_request(
    authority_request: Mapping[str, object],
    *,
    state_hash: str,
) -> dict[str, object]:
    """Embed an M6 request in the existing Tau state-proof verifier ABI.

    The nested ``m6_authority_request`` is mandatory for the external
    verifier to authenticate the operation.  A legacy state-proof receipt
    lacks the M6-specific receipt fields and cannot pass ``_require_receipt``.
    """

    normalized_state_hash = _require_root(state_hash, name="Tau authority state hash")
    return {
        "schema": TAU_STATE_PROOF_REQUEST_SCHEMA_V0,
        "schema_version": 1,
        "state_hash": normalized_state_hash,
        "proof": {
            "present": True,
            "state_hash": normalized_state_hash,
            "m6_authority_request": dict(authority_request),
        },
        "m6_authority_request": dict(authority_request),
    }


def _deposit_receipt_body(
    witness: TauFinalityBoundDepositWitnessV1,
    *,
    subject_root: str,
    pre_state_root: str,
    command_hash: str,
) -> dict[str, object]:
    return {
        "schema": M6_AUTHORITY_RECEIPT_SCHEMA_V1,
        "ok": True,
        "kind": GlobalCommandKindV1.TAU_ESCROW_DEPOSIT.value,
        "subject_root": subject_root,
        "pre_state_root": pre_state_root,
        "command_hash": command_hash,
        "evidence_root": witness.witness_root,
        "tau_transaction_root": witness.tau_transaction_root,
        "tau_finality_root": witness.tau_finality_root,
        "tau_profile_root": witness.tau_profile_root,
        "tau_finality_height": witness.tau_finality_height,
        "authorizes_m6_authority": True,
        "authorizes_economic_finality": False,
    }


def _ack_receipt_body(
    acknowledgment: WithdrawalAcknowledgmentV1,
    *,
    subject_root: str,
    pre_state_root: str,
    command_hash: str,
    expected_provenance_root: str,
) -> dict[str, object]:
    if acknowledgment.provenance_root != expected_provenance_root:
        raise M6AuthorityProofRejectedV1(
            "M6 acknowledgment provenance root does not match the expected withdrawal"
        )
    return {
        "schema": M6_AUTHORITY_RECEIPT_SCHEMA_V1,
        "ok": True,
        "kind": GlobalCommandKindV1.TAU_WITHDRAWAL_ACK.value,
        "subject_root": subject_root,
        "pre_state_root": pre_state_root,
        "command_hash": command_hash,
        "evidence_root": acknowledgment.acknowledgment_root,
        "provenance_root": expected_provenance_root,
        "tau_receipt_root": acknowledgment.tau_receipt_root,
        "tau_receipt_height": acknowledgment.tau_receipt_height,
        "acknowledged_state_root": acknowledgment.acknowledged_state_root,
        "authorizes_m6_authority": True,
        "authorizes_economic_finality": False,
    }


def _migration_receipt_body(
    proof: MigrationAuthorityProofV1,
    *,
    command_kind: GlobalCommandKindV1,
    subject_root: str,
    pre_state_root: str,
    command_hash: str,
    expected_source_authority_epoch: int,
    expected_compatible_profile_root: str,
) -> dict[str, object]:
    if command_kind is GlobalCommandKindV1.FALLBACK_ACTIVATE:
        expected_kind = MigrationEvidenceKindV1.FALLBACK_LIVENESS
    elif command_kind is GlobalCommandKindV1.TAU_REJOIN:
        expected_kind = MigrationEvidenceKindV1.TAU_REJOIN_CATCHUP
    else:
        raise ValueError("M6 migration command kind is unsupported")
    if proof.kind is not expected_kind:
        raise ValueError("M6 migration proof kind mismatch")
    if proof.source_authority_epoch != expected_source_authority_epoch:
        raise M6AuthorityProofRejectedV1(
            "M6 migration source authority epoch does not match the expected state"
        )
    if proof.compatible_profile_root != expected_compatible_profile_root:
        raise M6AuthorityProofRejectedV1(
            "M6 migration compatible profile does not match the expected profile"
        )
    return {
        "schema": M6_AUTHORITY_RECEIPT_SCHEMA_V1,
        "ok": True,
        "kind": command_kind.value,
        "subject_root": subject_root,
        "pre_state_root": pre_state_root,
        "command_hash": command_hash,
        "evidence_root": hash_v1("m6-migration-authority-proof-v1", proof.to_canonical()),
        "checkpoint_root": proof.checkpoint_root,
        "condition_root": proof.condition_root,
        "compatible_profile_root": expected_compatible_profile_root,
        "source_authority_epoch": expected_source_authority_epoch,
        "authorizes_m6_authority": True,
        "authorizes_economic_finality": False,
    }


@dataclass(frozen=True, slots=True)
class M6AuthorityVerifierAdapterV1:
    """Implement the core verifier port with explicit external backends.

    ``tau_state_proof_verifier`` is the existing Tau verifier ABI.  It must be
    an M6-aware implementation that understands the nested request and emits
    the exact M6 receipt contract.  The repository's current read-only Tau
    verifier receipts intentionally fail this contract.
    """

    tau_state_proof_verifier: M6TauStateProofVerifierV1 | None = None
    migration_verifier: M6MigrationVerifierV1 | None = None

    def _verify_tau_receipt(
        self,
        authority_request: Mapping[str, object],
        *,
        state_hash: str,
        expected_receipt: Mapping[str, object],
    ) -> M6AuthorityVerificationReceiptV1:
        verifier = self.tau_state_proof_verifier
        if verifier is None:
            raise M6AuthorityVerifierUnavailableV1(
                "M6 Tau authority verifier is not configured"
            )
        request = _tau_state_proof_request(authority_request, state_hash=state_hash)
        receipt: object = None
        verifier_failure: str | None = None
        try:
            receipt = verifier.verify_tau_state_proof(request)
        except M6AuthorityVerifierUnavailableV1:
            verifier_failure = "unavailable"
        except M6AuthorityVerifierInternalFailureV1:
            verifier_failure = "internal"
        except M6AuthorityProofRejectedV1:
            verifier_failure = "rejected"
        except Exception:
            verifier_failure = "internal"
        if verifier_failure == "unavailable":
            raise M6AuthorityVerifierUnavailableV1(
                "M6 Tau authority verifier is unavailable"
            )
        if verifier_failure == "internal":
            raise M6AuthorityVerifierInternalFailureV1(
                "M6 Tau authority verifier failed internally"
            )
        if verifier_failure == "rejected":
            raise M6AuthorityProofRejectedV1(
                "M6 Tau authority verifier rejected the request"
            )
        receipt_hash = _require_receipt(receipt, expected=expected_receipt)
        try:
            kind = GlobalCommandKindV1(str(expected_receipt["kind"]))
            subject_root = str(expected_receipt["subject_root"])
            pre_state_root = str(expected_receipt["pre_state_root"])
            command_hash = str(expected_receipt["command_hash"])
            evidence_root = str(expected_receipt["evidence_root"])
        except (KeyError, TypeError, ValueError) as exc:
            raise M6AuthorityProofRejectedV1(
                "M6 authority receipt body is missing typed binding fields"
            ) from exc
        return _issue_m6_authority_verification_receipt_v1(
            kind=kind,
            subject_root=subject_root,
            pre_state_root=pre_state_root,
            command_hash=command_hash,
            evidence_root=evidence_root,
            attestation_root=receipt_hash,
        )

    def verify_tau_finality_bound_deposit(
        self,
        witness: TauFinalityBoundDepositWitnessV1,
        *,
        expected_subject_root: str,
        expected_pre_state_root: str,
        expected_command_hash: str,
    ) -> M6AuthorityVerificationReceiptV1:
        expected = _deposit_receipt_body(
            witness,
            subject_root=_require_root(expected_subject_root, name="expected subject root"),
            pre_state_root=_require_root(expected_pre_state_root, name="expected pre-state root"),
            command_hash=_require_root(expected_command_hash, name="expected command hash"),
        )
        request = _base_request(
            kind=GlobalCommandKindV1.TAU_ESCROW_DEPOSIT.value,
            subject_root=str(expected["subject_root"]),
            pre_state_root=str(expected["pre_state_root"]),
            command_hash=str(expected["command_hash"]),
            evidence_root=witness.witness_root,
            proof=witness.to_canonical(),
        )
        return self._verify_tau_receipt(
            request,
            state_hash=witness.tau_finality_root,
            expected_receipt=expected,
        )

    def verify_tau_escrow_deposit(
        self,
        proof: TauFinalityBoundDepositWitnessV1,
        *,
        expected_subject_root: str,
        expected_pre_state_root: str,
        expected_command_hash: str,
    ) -> M6AuthorityVerificationReceiptV1:
        """Compatibility spelling for the finality-bound deposit port."""

        return self.verify_tau_finality_bound_deposit(
            proof,
            expected_subject_root=expected_subject_root,
            expected_pre_state_root=expected_pre_state_root,
            expected_command_hash=expected_command_hash,
        )

    def verify_tau_withdrawal_ack(
        self,
        acknowledgment: WithdrawalAcknowledgmentV1,
        *,
        expected_subject_root: str,
        expected_pre_state_root: str,
        expected_command_hash: str,
        expected_provenance_root: str,
    ) -> M6AuthorityVerificationReceiptV1:
        subject_root = _require_root(expected_subject_root, name="expected subject root")
        pre_state_root = _require_root(expected_pre_state_root, name="expected pre-state root")
        command_hash = _require_root(expected_command_hash, name="expected command hash")
        provenance_root = _require_root(expected_provenance_root, name="expected provenance root")
        expected = _ack_receipt_body(
            acknowledgment,
            subject_root=subject_root,
            pre_state_root=pre_state_root,
            command_hash=command_hash,
            expected_provenance_root=provenance_root,
        )
        request = _base_request(
            kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK.value,
            subject_root=subject_root,
            pre_state_root=pre_state_root,
            command_hash=command_hash,
            evidence_root=acknowledgment.acknowledgment_root,
            proof=acknowledgment.to_canonical(),
        )
        request["expected_provenance_root"] = provenance_root
        return self._verify_tau_receipt(
            request,
            state_hash=acknowledgment.tau_receipt_root,
            expected_receipt=expected,
        )

    def verify_migration(
        self,
        proof: MigrationAuthorityProofV1,
        *,
        expected_kind: MigrationEvidenceKindV1,
        expected_subject_root: str,
        expected_pre_state_root: str,
        expected_source_authority_epoch: int,
        expected_compatible_profile_root: str,
        expected_command_hash: str,
    ) -> M6AuthorityVerificationReceiptV1:
        verifier = self.migration_verifier
        if verifier is None:
            raise M6AuthorityVerifierUnavailableV1(
                "M6 migration authority verifier is not configured"
            )
        if not isinstance(expected_source_authority_epoch, int) or isinstance(
            expected_source_authority_epoch, bool
        ) or expected_source_authority_epoch < 0:
            raise ValueError("expected source authority epoch must be non-negative")
        if expected_kind is MigrationEvidenceKindV1.FALLBACK_LIVENESS:
            command_kind = GlobalCommandKindV1.FALLBACK_ACTIVATE
        elif expected_kind is MigrationEvidenceKindV1.TAU_REJOIN_CATCHUP:
            command_kind = GlobalCommandKindV1.TAU_REJOIN
        else:
            raise ValueError("M6 migration evidence kind is unsupported")
        subject_root = _require_root(expected_subject_root, name="expected subject root")
        pre_state_root = _require_root(expected_pre_state_root, name="expected pre-state root")
        command_hash = _require_root(expected_command_hash, name="expected command hash")
        profile_root = _require_root(
            expected_compatible_profile_root,
            name="expected compatible profile root",
            allow_zero=True,
        )
        expected = _migration_receipt_body(
            proof,
            command_kind=command_kind,
            subject_root=subject_root,
            pre_state_root=pre_state_root,
            command_hash=command_hash,
            expected_source_authority_epoch=expected_source_authority_epoch,
            expected_compatible_profile_root=profile_root,
        )
        request = _base_request(
            kind=command_kind.value,
            subject_root=subject_root,
            pre_state_root=pre_state_root,
            command_hash=command_hash,
            evidence_root=str(expected["evidence_root"]),
            proof=proof.to_canonical(),
        )
        request["expected_source_authority_epoch"] = expected_source_authority_epoch
        request["expected_compatible_profile_root"] = profile_root
        receipt: object = None
        verifier_failure: str | None = None
        try:
            receipt = verifier.verify_m6_migration(request)
        except M6AuthorityVerifierUnavailableV1:
            verifier_failure = "unavailable"
        except M6AuthorityVerifierInternalFailureV1:
            verifier_failure = "internal"
        except M6AuthorityProofRejectedV1:
            verifier_failure = "rejected"
        except Exception:
            verifier_failure = "internal"
        if verifier_failure == "unavailable":
            raise M6AuthorityVerifierUnavailableV1(
                "M6 migration authority verifier is unavailable"
            )
        if verifier_failure == "internal":
            raise M6AuthorityVerifierInternalFailureV1(
                "M6 migration authority verifier failed internally"
            )
        if verifier_failure == "rejected":
            raise M6AuthorityProofRejectedV1(
                "M6 migration authority verifier rejected the request"
            )
        receipt_hash = _require_receipt(receipt, expected=expected)
        return _issue_m6_authority_verification_receipt_v1(
            kind=command_kind,
            subject_root=subject_root,
            pre_state_root=pre_state_root,
            command_hash=command_hash,
            evidence_root=str(expected["evidence_root"]),
            attestation_root=receipt_hash,
        )


__all__ = [
    "M6_AUTHORITY_RECEIPT_HASH_DOMAIN_V1",
    "M6_AUTHORITY_RECEIPT_SCHEMA_V1",
    "M6_AUTHORITY_REQUEST_SCHEMA_V1",
    "M6AuthorityProofRejectedV1",
    "M6AuthorityVerificationError",
    "M6AuthorityVerifierAdapterV1",
    "M6AuthorityVerifierInternalFailureV1",
    "M6AuthorityVerifierUnavailableV1",
    "M6MigrationVerifierV1",
]
