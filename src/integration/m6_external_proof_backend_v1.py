"""Request-hashed shell for an injected M6 external proof verifier.

This module validates the closed M6 request and output envelopes used by the
Tau and migration adapters.  The injected verifier remains responsible for
Tau transaction inclusion, Tau finality, acknowledgment provenance, and
objective migration conditions.  No cryptographic or liveness claim is
implemented here, and the module remains research-only.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Mapping, NoReturn, Protocol

from src.core.m6_safe_mount_types_v1 import (
    GlobalCommandKindV1,
    MigrationEvidenceKindV1,
    canonical_bytes_v1,
    hash_v1,
)

from .m6_authority_verifier_v1 import (
    M6_AUTHORITY_REQUEST_SCHEMA_V1,
    TAU_STATE_PROOF_REQUEST_SCHEMA_V0,
    M6AuthorityProofRejectedV1,
    M6AuthorityVerifierUnavailableV1,
    _require_root,
)

M6_EXTERNAL_VERIFIER_REQUEST_SCHEMA_V1 = (
    "zenodex/m6/external-proof-verification-request/v1"
)
M6_EXTERNAL_VERIFIER_OUTPUT_SCHEMA_V1 = (
    "zenodex/m6/external-proof-verification-output/v1"
)
M6_EXTERNAL_VERIFIER_REQUEST_HASH_DOMAIN_V1 = (
    "m6-external-proof-verification-request-v1"
)


class M6ExternalProofVerifierPortV1(Protocol):
    """Imperative-shell port for a real external proof verifier."""

    def verify_with_output(
        self,
        payload: object,
    ) -> tuple[bool, str | None, Mapping[str, object] | None]:
        """Verify a canonical request and return its typed output envelope."""


def _reject(message: str) -> NoReturn:
    raise M6AuthorityProofRejectedV1(message)


def _require_exact_mapping(
    value: object,
    *,
    keys: frozenset[str],
    name: str,
) -> dict[str, object]:
    if not isinstance(value, Mapping):
        _reject(f"{name} must be an object")
    actual = dict(value)
    if set(actual) != keys:
        _reject(f"{name} has an unexpected field set")
    return actual


def _require_text_field(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        _reject(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_epoch(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        _reject(f"{name} must be a non-negative integer")
    return value


def _validated_root(value: object, *, name: str, allow_zero: bool = False) -> str:
    try:
        return _require_root(value, name=name, allow_zero=allow_zero)
    except (TypeError, ValueError) as exc:
        raise M6AuthorityProofRejectedV1(f"{name} is invalid: {exc}") from exc


def _canonical_mapping(value: Mapping[str, object], *, name: str) -> dict[str, object]:
    try:
        encoded = canonical_bytes_v1(value)
        decoded = json.loads(encoded.decode("utf-8"))
    except Exception as exc:
        _reject(f"{name} is not canonically encodable: {exc}")
    if not isinstance(decoded, dict):
        _reject(f"{name} must encode as an object")
    return dict(decoded)


def _authority_request_keys(kind: str) -> frozenset[str]:
    if kind == GlobalCommandKindV1.TAU_ESCROW_DEPOSIT.value:
        return frozenset(
            {
                "schema",
                "kind",
                "subject_root",
                "pre_state_root",
                "command_hash",
                "evidence_root",
                "proof",
            }
        )
    if kind == GlobalCommandKindV1.TAU_WITHDRAWAL_ACK.value:
        return frozenset(
            {
                "schema",
                "kind",
                "subject_root",
                "pre_state_root",
                "command_hash",
                "evidence_root",
                "proof",
                "expected_provenance_root",
            }
        )
    if kind in {
        GlobalCommandKindV1.FALLBACK_ACTIVATE.value,
        GlobalCommandKindV1.TAU_REJOIN.value,
    }:
        return frozenset(
            {
                "schema",
                "kind",
                "subject_root",
                "pre_state_root",
                "command_hash",
                "evidence_root",
                "proof",
                "expected_source_authority_epoch",
                "expected_compatible_profile_root",
            }
        )
    _reject("M6 authority request kind is unsupported")


def _proof_keys(kind: str) -> frozenset[str]:
    if kind == GlobalCommandKindV1.TAU_ESCROW_DEPOSIT.value:
        return frozenset(
            {
                "deposit_id",
                "tau_transaction_root",
                "tau_finality_root",
                "tau_profile_root",
                "beneficiary",
                "asset",
                "amount_atoms",
                "tau_finality_height",
            }
        )
    if kind == GlobalCommandKindV1.TAU_WITHDRAWAL_ACK.value:
        return frozenset(
            {
                "withdrawal_id",
                "provenance_root",
                "tau_receipt_root",
                "acknowledged_state_root",
                "tau_receipt_height",
            }
        )
    return frozenset(
        {
            "kind",
            "checkpoint_root",
            "compatible_profile_root",
            "condition_root",
            "source_authority_epoch",
        }
    )


def _validate_deposit_request(
    request: Mapping[str, object],
    proof: Mapping[str, object],
) -> None:
    _require_text_field(proof["deposit_id"], name="M6 deposit id")
    _require_text_field(proof["beneficiary"], name="M6 deposit beneficiary")
    _require_text_field(proof["asset"], name="M6 deposit asset")
    amount_atoms = proof["amount_atoms"]
    if not isinstance(amount_atoms, int) or isinstance(amount_atoms, bool) or amount_atoms <= 0:
        _reject("M6 deposit amount must be a positive integer")
    _require_nonnegative_epoch(proof["tau_finality_height"], name="M6 deposit finality height")
    for field_name in ("tau_transaction_root", "tau_finality_root", "tau_profile_root"):
        _validated_root(proof[field_name], name=f"M6 deposit {field_name}")
    expected_evidence_root = hash_v1("m6-tau-escrow-deposit-proof-v1", proof)
    if request["evidence_root"] != expected_evidence_root:
        _reject("M6 deposit evidence root mismatch")


def _validate_ack_request(
    request: Mapping[str, object],
    proof: Mapping[str, object],
) -> None:
    _require_text_field(proof["withdrawal_id"], name="M6 acknowledgment withdrawal id")
    for field_name in ("provenance_root", "tau_receipt_root", "acknowledged_state_root"):
        _validated_root(proof[field_name], name=f"M6 acknowledgment {field_name}")
    _require_nonnegative_epoch(proof["tau_receipt_height"], name="M6 acknowledgment receipt height")
    expected_provenance = _validated_root(
        request["expected_provenance_root"],
        name="M6 expected provenance root",
    )
    if proof["provenance_root"] != expected_provenance:
        _reject("M6 acknowledgment provenance binding mismatch")
    expected_evidence_root = hash_v1("m6-withdrawal-ack-v1", proof)
    if request["evidence_root"] != expected_evidence_root:
        _reject("M6 acknowledgment evidence root mismatch")


def _validate_migration_request(
    request: Mapping[str, object],
    proof: Mapping[str, object],
) -> None:
    kind = str(request["kind"])
    expected_kind = (
        MigrationEvidenceKindV1.FALLBACK_LIVENESS.value
        if kind == GlobalCommandKindV1.FALLBACK_ACTIVATE.value
        else MigrationEvidenceKindV1.TAU_REJOIN_CATCHUP.value
    )
    proof_kind = _require_text_field(proof["kind"], name="M6 migration proof kind")
    if proof_kind != expected_kind:
        _reject("M6 migration proof kind mismatch")
    _validated_root(proof["checkpoint_root"], name="M6 migration checkpoint root")
    _validated_root(proof["condition_root"], name="M6 migration condition root")
    proof_profile = _validated_root(
        proof["compatible_profile_root"],
        name="M6 migration proof profile root",
        allow_zero=True,
    )
    request_profile = _validated_root(
        request["expected_compatible_profile_root"],
        name="M6 expected migration profile root",
        allow_zero=True,
    )
    proof_epoch = _require_nonnegative_epoch(
        proof["source_authority_epoch"],
        name="M6 migration proof source epoch",
    )
    request_epoch = _require_nonnegative_epoch(
        request["expected_source_authority_epoch"],
        name="M6 expected source epoch",
    )
    if proof_profile != request_profile or proof_epoch != request_epoch:
        _reject("M6 migration epoch or profile binding mismatch")
    expected_evidence_root = hash_v1("m6-migration-authority-proof-v1", proof)
    if request["evidence_root"] != expected_evidence_root:
        _reject("M6 migration evidence root mismatch")


def _validate_m6_authority_request(request: object) -> dict[str, object]:
    """Validate the closed request sent to an external authority verifier."""

    if not isinstance(request, Mapping):
        _reject("M6 authority request must be an object")
    kind = _require_text_field(dict(request).get("kind"), name="M6 authority kind")
    request_obj = _require_exact_mapping(
        request,
        keys=_authority_request_keys(kind),
        name="M6 authority request",
    )
    if request_obj["schema"] != M6_AUTHORITY_REQUEST_SCHEMA_V1:
        _reject("M6 authority request schema mismatch")
    for field_name in ("subject_root", "pre_state_root", "command_hash", "evidence_root"):
        _validated_root(request_obj[field_name], name=f"M6 authority {field_name}")
    proof = _require_exact_mapping(
        request_obj["proof"],
        keys=_proof_keys(kind),
        name="M6 authority proof",
    )
    if kind == GlobalCommandKindV1.TAU_ESCROW_DEPOSIT.value:
        _validate_deposit_request(request_obj, proof)
    elif kind == GlobalCommandKindV1.TAU_WITHDRAWAL_ACK.value:
        _validate_ack_request(request_obj, proof)
    else:
        _validate_migration_request(request_obj, proof)
    return request_obj


def _validate_tau_state_proof_request(request: object) -> dict[str, object]:
    request_obj = _require_exact_mapping(
        request,
        keys=frozenset({"schema", "schema_version", "state_hash", "proof", "m6_authority_request"}),
        name="Tau M6 authority request",
    )
    if request_obj["schema"] != TAU_STATE_PROOF_REQUEST_SCHEMA_V0:
        _reject("Tau M6 authority request schema mismatch")
    if type(request_obj["schema_version"]) is not int or request_obj["schema_version"] != 1:
        _reject("Tau M6 authority request schema version mismatch")
    state_hash = _validated_root(request_obj["state_hash"], name="Tau M6 authority state hash")
    proof = _require_exact_mapping(
        request_obj["proof"],
        keys=frozenset({"present", "state_hash", "m6_authority_request"}),
        name="Tau M6 authority proof envelope",
    )
    if proof["present"] is not True or proof["state_hash"] != state_hash:
        _reject("Tau M6 authority proof envelope binding mismatch")
    authority = _validate_m6_authority_request(request_obj["m6_authority_request"])
    if proof["m6_authority_request"] != authority:
        _reject("Tau M6 authority nested request mismatch")
    return request_obj


def _external_output_or_reject(
    output: object,
    *,
    request_hash: str,
) -> dict[str, object]:
    if not isinstance(output, Mapping):
        _reject("M6 external verifier output must be an object")
    if "verifier_request_hash" not in output:
        _reject("M6 external verifier request hash is missing")
    envelope = _require_exact_mapping(
        output,
        keys=frozenset({"schema", "ok", "verifier_request_hash", "receipt"}),
        name="M6 external verifier output",
    )
    if envelope["schema"] != M6_EXTERNAL_VERIFIER_OUTPUT_SCHEMA_V1:
        _reject("M6 external verifier output schema mismatch")
    if envelope["ok"] is not True:
        _reject("M6 external verifier output is not accepted")
    if envelope["verifier_request_hash"] != request_hash:
        _reject("M6 external verifier request hash mismatch")
    receipt = envelope["receipt"]
    if not isinstance(receipt, Mapping):
        _reject("M6 external verifier receipt must be an object")
    return dict(receipt)


@dataclass(frozen=True, slots=True)
class M6ProofVerifierBackendV1:
    """Adapt a proof engine to the exact M6 Tau/migration verifier ports."""

    proof_verifier: M6ExternalProofVerifierPortV1 | None = None

    def _verify_external(
        self,
        request: Mapping[str, object],
        *,
        operation: str,
    ) -> Mapping[str, object]:
        verifier = self.proof_verifier
        if verifier is None:
            raise M6AuthorityVerifierUnavailableV1(
                "M6 external proof verifier is not configured"
            )
        canonical_request = _canonical_mapping(request, name="M6 external verifier request")
        request_identity = {"operation": operation, "request": canonical_request}
        request_hash = hash_v1(
            M6_EXTERNAL_VERIFIER_REQUEST_HASH_DOMAIN_V1,
            request_identity,
        )
        payload: dict[str, object] = {
            "schema": M6_EXTERNAL_VERIFIER_REQUEST_SCHEMA_V1,
            "operation": operation,
            "verifier_request_hash": request_hash,
            "request": canonical_request,
        }
        try:
            ok, error, output = verifier.verify_with_output(payload)
        except Exception as exc:
            raise M6AuthorityProofRejectedV1(
                f"M6 external proof verifier failed: {exc}"
            ) from exc
        if ok is not True:
            detail = error if isinstance(error, str) and error else "proof rejected"
            raise M6AuthorityProofRejectedV1(
                f"M6 external proof verifier rejected the request: {detail}"
            )
        return _external_output_or_reject(output, request_hash=request_hash)

    def verify_tau_state_proof(self, request: Mapping[str, object]) -> Mapping[str, object]:
        """Verify one M6-aware Tau request through the external proof port."""

        validated = _validate_tau_state_proof_request(request)
        return self._verify_external(validated, operation="tau_state_proof")

    def verify_m6_migration(self, request: Mapping[str, object]) -> Mapping[str, object]:
        """Verify one fallback/rejoin condition through the external proof port."""

        validated = _validate_m6_authority_request(request)
        if validated["kind"] not in {
            GlobalCommandKindV1.FALLBACK_ACTIVATE.value,
            GlobalCommandKindV1.TAU_REJOIN.value,
        }:
            _reject("M6 migration verifier received a non-migration request")
        return self._verify_external(validated, operation="migration")


__all__ = [
    "M6_EXTERNAL_VERIFIER_OUTPUT_SCHEMA_V1",
    "M6_EXTERNAL_VERIFIER_REQUEST_HASH_DOMAIN_V1",
    "M6_EXTERNAL_VERIFIER_REQUEST_SCHEMA_V1",
    "M6ExternalProofVerifierPortV1",
    "M6ProofVerifierBackendV1",
]
