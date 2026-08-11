"""Verifier boundary for M6 external and migration authority evidence.

The functional core consumes :class:`M6AuthorityEvidenceV1`, an opaque handle
whose constructor is private to this module's verifier path.  The verifier
port is deliberately explicit: this reference repository does not implement
Tau finality cryptography or objective migration-liveness proofs.
"""

from __future__ import annotations

from typing import Protocol, TypeAlias

from .m6_safe_mount_types_v1 import (
    _FINALITY_VERIFICATION_RECEIPT_TOKEN,
    _M6_VERIFIER_APPROVAL_SEAL,
    ZERO_ROOT_V1,
    AuthenticatedExecutionContextV1,
    FreshnessBoundsV1,
    GlobalCommandKindV1,
    GlobalCommandV1,
    M6AuthorityEvidenceV1,
    M6ExecutionContextClaimsV1,
    M6FinalityVerificationReceiptV1,
    MigrationAuthorityProofV1,
    MigrationEvidenceKindV1,
    OracleContextV1,
    TauFinalityBoundDepositWitnessV1,
    WithdrawalAcknowledgmentV1,
    _M6VerifierApproval,
    _require_root,
    hash_v1,
)


def _new_verifier_approval() -> _M6VerifierApproval:
    """Create the private port marker after its external check returns."""

    approval = object.__new__(_M6VerifierApproval)
    object.__setattr__(approval, "_seal", _M6_VERIFIER_APPROVAL_SEAL)
    return approval


_M6_VERIFICATION_RECEIPT_TOKEN = object()


class M6ExecutionContextVerificationReceiptV1:
    """Opaque receipt returned by the ingress verifier port.

    The receipt is intentionally separate from the core witness.  A verifier
    must return a typed result bound to the exact claims before the port can
    issue an authenticated context.  An exception or ``None`` is therefore
    never interpreted as approval.
    """

    _claims_root: str
    _verifier_registry: str
    _attestation_root: str
    _sealed: bool

    __slots__ = ("_claims_root", "_verifier_registry", "_attestation_root", "_sealed")

    def __init__(
        self,
        token: object,
        *,
        claims_root: str,
        verifier_registry: str,
        attestation_root: str,
    ) -> None:
        if token is not _M6_VERIFICATION_RECEIPT_TOKEN:
            raise TypeError("M6 execution-context receipt is verifier-created")
        _require_root(claims_root, name="M6 context receipt claims root")
        _require_root(verifier_registry, name="M6 context receipt verifier registry")
        _require_root(attestation_root, name="M6 context receipt attestation root")
        object.__setattr__(self, "_claims_root", claims_root)
        object.__setattr__(self, "_verifier_registry", verifier_registry)
        object.__setattr__(self, "_attestation_root", attestation_root)
        object.__setattr__(self, "_sealed", True)

    @property
    def claims_root(self) -> str:
        return self._claims_root

    @property
    def verifier_registry(self) -> str:
        return self._verifier_registry

    @property
    def attestation_root(self) -> str:
        return self._attestation_root

    @property
    def receipt_root(self) -> str:
        return hash_v1(
            "m6-execution-context-verification-receipt-v1",
            {
                "claims_root": self.claims_root,
                "verifier_registry": self.verifier_registry,
                "attestation_root": self.attestation_root,
            },
        )

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("M6 execution-context receipt is immutable")
        object.__setattr__(self, name, value)


class M6AuthorityVerificationReceiptV1:
    """Opaque receipt returned by an external authority verifier.

    Its binding fields are checked again by the functional authority port.
    The receipt proves that the external adapter completed its own checks; it
    does not claim Tau cryptographic or migration-liveness soundness here.
    """

    _kind: GlobalCommandKindV1
    _subject_root: str
    _pre_state_root: str
    _command_hash: str
    _evidence_root: str
    _attestation_root: str
    _sealed: bool

    __slots__ = (
        "_kind",
        "_subject_root",
        "_pre_state_root",
        "_command_hash",
        "_evidence_root",
        "_attestation_root",
        "_sealed",
    )

    def __init__(
        self,
        token: object,
        *,
        kind: GlobalCommandKindV1,
        subject_root: str,
        pre_state_root: str,
        command_hash: str,
        evidence_root: str,
        attestation_root: str,
    ) -> None:
        if token is not _M6_VERIFICATION_RECEIPT_TOKEN:
            raise TypeError("M6 authority receipt is verifier-created")
        if not isinstance(kind, GlobalCommandKindV1):
            raise TypeError("M6 authority receipt kind is not closed")
        _require_root(subject_root, name="M6 authority receipt subject root")
        _require_root(pre_state_root, name="M6 authority receipt pre-state root")
        _require_root(command_hash, name="M6 authority receipt command hash")
        _require_root(evidence_root, name="M6 authority receipt evidence root")
        _require_root(attestation_root, name="M6 authority receipt attestation root")
        object.__setattr__(self, "_kind", kind)
        object.__setattr__(self, "_subject_root", subject_root)
        object.__setattr__(self, "_pre_state_root", pre_state_root)
        object.__setattr__(self, "_command_hash", command_hash)
        object.__setattr__(self, "_evidence_root", evidence_root)
        object.__setattr__(self, "_attestation_root", attestation_root)
        object.__setattr__(self, "_sealed", True)

    @property
    def kind(self) -> GlobalCommandKindV1:
        return self._kind

    @property
    def subject_root(self) -> str:
        return self._subject_root

    @property
    def pre_state_root(self) -> str:
        return self._pre_state_root

    @property
    def command_hash(self) -> str:
        return self._command_hash

    @property
    def evidence_root(self) -> str:
        return self._evidence_root

    @property
    def attestation_root(self) -> str:
        return self._attestation_root

    @property
    def receipt_root(self) -> str:
        return hash_v1(
            "m6-authority-verification-receipt-v1",
            {
                "kind": self.kind,
                "subject_root": self.subject_root,
                "pre_state_root": self.pre_state_root,
                "command_hash": self.command_hash,
                "evidence_root": self.evidence_root,
                "attestation_root": self.attestation_root,
            },
        )

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("M6 authority receipt is immutable")
        object.__setattr__(self, name, value)


def _issue_m6_execution_context_verification_receipt_v1(
    claims: M6ExecutionContextClaimsV1,
    *,
    attestation_root: str,
) -> M6ExecutionContextVerificationReceiptV1:
    """Construct a receipt after an external verifier has checked ``claims``.

    The helper is an adapter seam for test and integration verifiers.  It does
    not perform signatures or client authentication; callers must only invoke
    it after those checks have completed.
    """

    if not isinstance(claims, M6ExecutionContextClaimsV1):
        raise TypeError("M6 context receipt claims are not typed")
    return M6ExecutionContextVerificationReceiptV1(
        _M6_VERIFICATION_RECEIPT_TOKEN,
        claims_root=claims.authentication_root,
        verifier_registry=claims.verifier_registry,
        attestation_root=attestation_root,
    )


def _issue_m6_authority_verification_receipt_v1(
    *,
    kind: GlobalCommandKindV1,
    subject_root: str,
    pre_state_root: str,
    command_hash: str,
    evidence_root: str,
    attestation_root: str,
) -> M6AuthorityVerificationReceiptV1:
    """Construct an adapter receipt after an external authority check."""

    return M6AuthorityVerificationReceiptV1(
        _M6_VERIFICATION_RECEIPT_TOKEN,
        kind=kind,
        subject_root=subject_root,
        pre_state_root=pre_state_root,
        command_hash=command_hash,
        evidence_root=evidence_root,
        attestation_root=attestation_root,
    )


def _issue_m6_finality_verification_receipt_v1(
    *,
    subject_root: str,
    candidate_parent_head: str,
    candidate_head: str,
    publication_root: str,
    expected_writer_epoch: int,
    certificate_root: str,
    attestation_root: str,
) -> M6FinalityVerificationReceiptV1:
    """Issue a finality receipt only at an external-verifier adapter seam.

    This helper intentionally performs binding and typing only.  A production
    adapter must call it after independently checking the validator registry,
    signatures, quorum, data availability, and the stated fault premise.
    """

    return M6FinalityVerificationReceiptV1(
        _FINALITY_VERIFICATION_RECEIPT_TOKEN,
        subject_root=subject_root,
        candidate_parent_head=candidate_parent_head,
        candidate_head=candidate_head,
        publication_root=publication_root,
        writer_epoch=expected_writer_epoch,
        certificate_root=certificate_root,
        attestation_root=attestation_root,
    )


class M6ExecutionContextVerifierV1(Protocol):
    """External ingress verifier required before a context enters the core."""

    def verify_execution_context(
        self,
        claims: M6ExecutionContextClaimsV1,
    ) -> M6ExecutionContextVerificationReceiptV1: ...


class M6AuthorityVerifierV1(Protocol):
    """External verifier port required before issuing M6 authority evidence."""

    def verify_tau_finality_bound_deposit(
        self,
        witness: TauFinalityBoundDepositWitnessV1,
        *,
        expected_subject_root: str,
        expected_pre_state_root: str,
        expected_command_hash: str,
    ) -> M6AuthorityVerificationReceiptV1: ...

    def verify_tau_withdrawal_ack(
        self,
        acknowledgment: WithdrawalAcknowledgmentV1,
        *,
        expected_subject_root: str,
        expected_pre_state_root: str,
        expected_command_hash: str,
        expected_provenance_root: str,
    ) -> M6AuthorityVerificationReceiptV1: ...

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
    ) -> M6AuthorityVerificationReceiptV1: ...


class LegacyM6DepositAuthorityVerifierV1(Protocol):
    """Compatibility port for pre-rename research adapters only."""

    def verify_tau_escrow_deposit(
        self,
        proof: TauFinalityBoundDepositWitnessV1,
        *,
        expected_subject_root: str,
        expected_pre_state_root: str,
        expected_command_hash: str,
    ) -> M6AuthorityVerificationReceiptV1: ...


M6DepositAuthorityVerifierV1: TypeAlias = (
    M6AuthorityVerifierV1 | LegacyM6DepositAuthorityVerifierV1
)


def verify_authenticated_execution_context_v1(
    *,
    deployment: str,
    chain_id: str,
    parent_head: str,
    epoch: int,
    sender: str,
    nonce: int,
    oracle_context: OracleContextV1,
    tau_profile: str,
    verifier_registry: str,
    freshness_bounds: FreshnessBoundsV1,
    ledger_height: int = 0,
    authority_evidence: M6AuthorityEvidenceV1 | None = None,
    verifier: M6ExecutionContextVerifierV1,
) -> AuthenticatedExecutionContextV1:
    """Issue a context only after an external ingress verifier approves it.

    This reference port checks the typed shape and binds all fields into the
    opaque witness.  Signature, session, and client-authentication semantics
    remain the verifier's explicit external obligation.
    """

    if not isinstance(oracle_context, OracleContextV1):
        raise TypeError("execution context oracle_context must be OracleContextV1")
    claims = M6ExecutionContextClaimsV1(
        deployment=deployment,
        chain_id=chain_id,
        parent_head=parent_head,
        epoch=epoch,
        sender=sender,
        nonce=nonce,
        oracle_context=oracle_context,
        tau_profile=tau_profile,
        verifier_registry=verifier_registry,
        freshness_bounds=freshness_bounds,
        ledger_height=ledger_height,
        authority_evidence=authority_evidence,
    )
    receipt = verifier.verify_execution_context(claims)
    if not isinstance(receipt, M6ExecutionContextVerificationReceiptV1):
        raise TypeError("M6 execution-context verifier did not return a typed receipt")
    if (
        receipt.claims_root != claims.authentication_root
        or receipt.verifier_registry != claims.verifier_registry
    ):
        raise ValueError("M6 execution-context verifier receipt binding mismatch")
    context = AuthenticatedExecutionContextV1._from_verifier(
        claims=claims,
        verification_approval=_new_verifier_approval(),
    )
    return context


def _require_command_kind(command: GlobalCommandV1, expected: GlobalCommandKindV1) -> None:
    if not isinstance(command, GlobalCommandV1):
        raise TypeError("M6 authority command must be GlobalCommandV1")
    if command.kind is not expected:
        raise ValueError("M6 authority evidence command kind mismatch")


def _field(command: GlobalCommandV1, key: str, expected_type: type[object]) -> object:
    value = command.payload_value(key)
    if not isinstance(value, expected_type):
        raise ValueError(f"M6 authority command field {key} has the wrong type")
    return value


def _bind_roots(subject_root: str, pre_state_root: str) -> None:
    _require_root(subject_root, name="M6 authority subject root")
    _require_root(pre_state_root, name="M6 authority pre-state root")


def _require_authority_receipt(
    receipt: object,
    *,
    kind: GlobalCommandKindV1,
    subject_root: str,
    pre_state_root: str,
    command_hash: str,
    evidence_root: str,
) -> M6AuthorityVerificationReceiptV1:
    if not isinstance(receipt, M6AuthorityVerificationReceiptV1):
        raise TypeError("M6 authority verifier did not return a typed receipt")
    if (
        receipt.kind is not kind
        or receipt.subject_root != subject_root
        or receipt.pre_state_root != pre_state_root
        or receipt.command_hash != command_hash
        or receipt.evidence_root != evidence_root
    ):
        raise ValueError("M6 authority verifier receipt binding mismatch")
    return receipt


def verify_tau_finality_bound_deposit_evidence_v1(
    command: GlobalCommandV1,
    witness: TauFinalityBoundDepositWitnessV1,
    *,
    subject_root: str,
    pre_state_root: str,
    tau_profile_root: str,
    verifier: M6DepositAuthorityVerifierV1,
) -> M6AuthorityEvidenceV1:
    """Issue M6 evidence from one finality-bound external deposit witness.

    The witness is a single transfer fact.  It cannot describe aggregate Tau
    balances or serve as a legal-custody assertion.  Compatibility verifiers
    using the legacy method name are supported only at this research boundary.
    """

    _require_command_kind(command, GlobalCommandKindV1.TAU_ESCROW_DEPOSIT)
    if not isinstance(witness, TauFinalityBoundDepositWitnessV1):
        raise TypeError(
            "Tau finality-bound deposit witness must be TauFinalityBoundDepositWitnessV1"
        )
    _bind_roots(subject_root, pre_state_root)
    _require_root(tau_profile_root, name="M6 authority Tau profile root")
    expected = {
        "deposit_id": command.payload_value("deposit_id"),
        "asset": command.payload_value("asset"),
        "amount_atoms": command.payload_value("amount_atoms"),
        "tau_transaction_root": command.payload_value("tau_transaction_root"),
        "tau_finality_root": command.payload_value("tau_finality_root"),
        "tau_profile_root": command.payload_value("tau_profile_root"),
        "tau_finality_height": command.payload_value("tau_finality_height", 0),
    }
    actual = {
        "deposit_id": witness.deposit_id,
        "asset": witness.asset,
        "amount_atoms": witness.amount_atoms,
        "tau_transaction_root": witness.tau_transaction_root,
        "tau_finality_root": witness.tau_finality_root,
        "tau_profile_root": witness.tau_profile_root,
        "tau_finality_height": witness.tau_finality_height,
    }
    if witness.beneficiary != command.sender or actual != expected:
        raise ValueError("Tau finality-bound deposit witness is not bound to the command")
    if witness.tau_profile_root != tau_profile_root:
        raise ValueError("Tau finality-bound deposit witness profile does not match the subject")
    verify_witness = getattr(verifier, "verify_tau_finality_bound_deposit", None)
    if not callable(verify_witness):
        # Existing research fixtures retain this spelling during the API
        # migration.  The typed witness and every binding above remain the
        # same; a mounted adapter must implement the new port method.
        verify_witness = getattr(verifier, "verify_tau_escrow_deposit", None)
    if not callable(verify_witness):
        raise TypeError("M6 authority verifier lacks the finality-bound deposit method")
    receipt = verify_witness(
        witness,
        expected_subject_root=subject_root,
        expected_pre_state_root=pre_state_root,
        expected_command_hash=command.command_hash,
    )
    _require_authority_receipt(
        receipt,
        kind=GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        subject_root=subject_root,
        pre_state_root=pre_state_root,
        command_hash=command.command_hash,
        evidence_root=witness.witness_root,
    )
    return M6AuthorityEvidenceV1(
        _new_verifier_approval(),
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        subject_root,
        pre_state_root,
        command.command_hash,
        witness,
    )


def verify_tau_escrow_deposit_evidence_v1(
    command: GlobalCommandV1,
    proof: TauFinalityBoundDepositWitnessV1,
    *,
    subject_root: str,
    pre_state_root: str,
    tau_profile_root: str,
    verifier: M6DepositAuthorityVerifierV1,
) -> M6AuthorityEvidenceV1:
    """Compatibility spelling for finality-bound deposit verification."""

    return verify_tau_finality_bound_deposit_evidence_v1(
        command,
        proof,
        subject_root=subject_root,
        pre_state_root=pre_state_root,
        tau_profile_root=tau_profile_root,
        verifier=verifier,
    )


def verify_tau_withdrawal_ack_evidence_v1(
    command: GlobalCommandV1,
    acknowledgment: WithdrawalAcknowledgmentV1,
    *,
    subject_root: str,
    pre_state_root: str,
    expected_provenance_root: str,
    verifier: M6AuthorityVerifierV1,
) -> M6AuthorityEvidenceV1:
    """Verify and issue an acknowledgment witness bound to one withdrawal."""

    _require_command_kind(command, GlobalCommandKindV1.TAU_WITHDRAWAL_ACK)
    if not isinstance(acknowledgment, WithdrawalAcknowledgmentV1):
        raise TypeError("Tau acknowledgment must be WithdrawalAcknowledgmentV1")
    _bind_roots(subject_root, pre_state_root)
    _require_root(expected_provenance_root, name="expected withdrawal provenance root")
    expected = {
        "withdrawal_id": command.payload_value("withdrawal_id"),
        "ack_root": command.payload_value("ack_root"),
        "tau_receipt_root": command.payload_value("tau_receipt_root"),
        "tau_receipt_height": command.payload_value("tau_receipt_height", 0),
    }
    actual = {
        "withdrawal_id": acknowledgment.withdrawal_id,
        "ack_root": acknowledgment.acknowledged_state_root,
        "tau_receipt_root": acknowledgment.tau_receipt_root,
        "tau_receipt_height": acknowledgment.tau_receipt_height,
    }
    if actual != expected or acknowledgment.provenance_root != expected_provenance_root:
        raise ValueError("Tau acknowledgment is not bound to the withdrawal")
    receipt = verifier.verify_tau_withdrawal_ack(
        acknowledgment,
        expected_subject_root=subject_root,
        expected_pre_state_root=pre_state_root,
        expected_command_hash=command.command_hash,
        expected_provenance_root=expected_provenance_root,
    )
    _require_authority_receipt(
        receipt,
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        subject_root=subject_root,
        pre_state_root=pre_state_root,
        command_hash=command.command_hash,
        evidence_root=acknowledgment.acknowledgment_root,
    )
    return M6AuthorityEvidenceV1(
        _new_verifier_approval(),
        GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        subject_root,
        pre_state_root,
        command.command_hash,
        acknowledgment,
    )


def verify_migration_evidence_v1(
    command: GlobalCommandV1,
    proof: MigrationAuthorityProofV1,
    *,
    subject_root: str,
    pre_state_root: str,
    source_authority_epoch: int,
    tau_profile_root: str,
    verifier: M6AuthorityVerifierV1,
) -> M6AuthorityEvidenceV1:
    """Verify and issue a fallback or Tau-rejoin witness.

    ``condition_root`` is intentionally opaque.  The external verifier must
    establish the objective liveness, forced-inclusion, catch-up, quiescence,
    and profile-compatibility conditions represented by that commitment.
    """

    if command.kind is GlobalCommandKindV1.FALLBACK_ACTIVATE:
        expected_kind = MigrationEvidenceKindV1.FALLBACK_LIVENESS
        expected_profile = ZERO_ROOT_V1
    elif command.kind is GlobalCommandKindV1.TAU_REJOIN:
        expected_kind = MigrationEvidenceKindV1.TAU_REJOIN_CATCHUP
        expected_profile = tau_profile_root
    else:
        raise ValueError("migration evidence command kind mismatch")
    if not isinstance(proof, MigrationAuthorityProofV1):
        raise TypeError("migration proof must be MigrationAuthorityProofV1")
    _bind_roots(subject_root, pre_state_root)
    _require_root(tau_profile_root, name="M6 migration Tau profile root")
    checkpoint = _field(command, "checkpoint_root", str)
    if (
        proof.kind is not expected_kind
        or proof.checkpoint_root != checkpoint
        or proof.compatible_profile_root != expected_profile
        or proof.source_authority_epoch != source_authority_epoch
    ):
        raise ValueError("migration proof is not bound to the command and source state")
    receipt = verifier.verify_migration(
        proof,
        expected_kind=expected_kind,
        expected_subject_root=subject_root,
        expected_pre_state_root=pre_state_root,
        expected_source_authority_epoch=source_authority_epoch,
        expected_compatible_profile_root=expected_profile,
        expected_command_hash=command.command_hash,
    )
    _require_authority_receipt(
        receipt,
        kind=command.kind,
        subject_root=subject_root,
        pre_state_root=pre_state_root,
        command_hash=command.command_hash,
        evidence_root=hash_v1("m6-migration-authority-proof-v1", proof.to_canonical()),
    )
    return M6AuthorityEvidenceV1(
        _new_verifier_approval(),
        command.kind,
        subject_root,
        pre_state_root,
        command.command_hash,
        proof,
    )


__all__ = [
    "M6AuthorityVerificationReceiptV1",
    "M6ExecutionContextVerifierV1",
    "M6ExecutionContextVerificationReceiptV1",
    "M6AuthorityVerifierV1",
    "LegacyM6DepositAuthorityVerifierV1",
    "M6DepositAuthorityVerifierV1",
    "verify_authenticated_execution_context_v1",
    "verify_tau_finality_bound_deposit_evidence_v1",
    "verify_tau_escrow_deposit_evidence_v1",
    "verify_tau_withdrawal_ack_evidence_v1",
    "verify_migration_evidence_v1",
]
