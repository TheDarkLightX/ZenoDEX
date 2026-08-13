"""Adversarial contract tests for the M6 authority verifier adapter."""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field
from typing import Mapping

import pytest

from src.core.m6_authority_evidence_v1 import (
    verify_migration_evidence_v1,
    verify_tau_escrow_deposit_evidence_v1,
    verify_tau_finality_bound_deposit_evidence_v1,
    verify_tau_withdrawal_ack_evidence_v1,
)
from src.core.m6_safe_mount_types_v1 import (
    GlobalCommandKindV1,
    GlobalCommandV1,
    MigrationAuthorityProofV1,
    MigrationEvidenceKindV1,
    TauEscrowDepositProofV1,
    TauFinalityBoundDepositWitnessV1,
    WithdrawalAcknowledgmentV1,
    hash_v1,
)
from src.integration.m6_authority_verifier_v1 import (
    M6_AUTHORITY_RECEIPT_HASH_DOMAIN_V1,
    M6_AUTHORITY_RECEIPT_SCHEMA_V1,
    M6_AUTHORITY_REQUEST_SCHEMA_V1,
    M6AuthorityProofRejectedV1,
    M6AuthorityVerifierAdapterV1,
    M6AuthorityVerifierInternalFailureV1,
    M6AuthorityVerifierUnavailableV1,
)
from src.integration.m6_external_proof_backend_v1 import (
    M6_EXTERNAL_VERIFIER_OUTPUT_SCHEMA_V1,
    M6_EXTERNAL_VERIFIER_REQUEST_HASH_DOMAIN_V1,
    M6_EXTERNAL_VERIFIER_REQUEST_SCHEMA_V1,
    M6ProofVerifierBackendV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _deposit() -> TauEscrowDepositProofV1:
    return TauEscrowDepositProofV1(
        deposit_id="deposit-1",
        tau_transaction_root=_root(11),
        tau_finality_root=_root(12),
        tau_profile_root=_root(13),
        beneficiary="alice",
        asset="A",
        amount_atoms=7,
    )


def test_given_finality_bound_deposit_witness_when_m6_authority_is_requested_then_a_mapping_cannot_become_backing_evidence() -> None:
    # Arrange: one exact, Tau-finalized deposit fact and an M6-aware verifier.
    witness = TauFinalityBoundDepositWitnessV1(
        deposit_id="deposit-1",
        tau_transaction_root=_root(11),
        tau_finality_root=_root(12),
        tau_profile_root=_root(13),
        beneficiary="alice",
        asset="A",
        amount_atoms=7,
    )
    command = _deposit_command()
    backend = _M6AwareTauVerifier()
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    # Act: the typed value reaches the authority boundary.
    evidence = verify_tau_finality_bound_deposit_evidence_v1(
        command,
        witness,
        subject_root=_root(31),
        pre_state_root=_root(32),
        tau_profile_root=witness.tau_profile_root,
        verifier=adapter,
    )

    # Assert: the renamed witness preserves the legacy commitment ABI, while
    # a caller-authored balance mapping cannot reach the external verifier.
    assert TauEscrowDepositProofV1 is TauFinalityBoundDepositWitnessV1
    assert evidence.payload is witness
    assert witness.witness_root == witness.proof_root
    with pytest.raises(TypeError, match="Tau finality-bound deposit witness"):
        verify_tau_finality_bound_deposit_evidence_v1(
            command,
            {"chain_balances": {"alice": 1}},  # type: ignore[arg-type]
            subject_root=_root(31),
            pre_state_root=_root(32),
            tau_profile_root=witness.tau_profile_root,
            verifier=adapter,
        )
    assert len(backend.requests) == 1


def _deposit_receipt_from_request(request: Mapping[str, object]) -> dict[str, object]:
    authority = request["m6_authority_request"]
    assert isinstance(authority, Mapping)
    proof = authority["proof"]
    assert isinstance(proof, Mapping)
    body: dict[str, object] = {
        "schema": M6_AUTHORITY_RECEIPT_SCHEMA_V1,
        "ok": True,
        "kind": authority["kind"],
        "subject_root": authority["subject_root"],
        "pre_state_root": authority["pre_state_root"],
        "command_hash": authority["command_hash"],
        "evidence_root": hash_v1("m6-tau-escrow-deposit-proof-v1", proof),
        "tau_transaction_root": proof["tau_transaction_root"],
        "tau_finality_root": proof["tau_finality_root"],
        "tau_profile_root": proof["tau_profile_root"],
        "tau_finality_height": proof["tau_finality_height"],
        "authorizes_m6_authority": True,
        "authorizes_economic_finality": False,
    }
    return {
        **body,
        "receipt_hash": hash_v1(M6_AUTHORITY_RECEIPT_HASH_DOMAIN_V1, body),
    }


def _ack_receipt_from_request(request: Mapping[str, object]) -> dict[str, object]:
    authority = request["m6_authority_request"]
    assert isinstance(authority, Mapping)
    proof = authority["proof"]
    assert isinstance(proof, Mapping)
    body: dict[str, object] = {
        "schema": M6_AUTHORITY_RECEIPT_SCHEMA_V1,
        "ok": True,
        "kind": authority["kind"],
        "subject_root": authority["subject_root"],
        "pre_state_root": authority["pre_state_root"],
        "command_hash": authority["command_hash"],
        "evidence_root": hash_v1("m6-withdrawal-ack-v1", proof),
        "provenance_root": authority["expected_provenance_root"],
        "tau_receipt_root": proof["tau_receipt_root"],
        "tau_receipt_height": proof["tau_receipt_height"],
        "acknowledged_state_root": proof["acknowledged_state_root"],
        "authorizes_m6_authority": True,
        "authorizes_economic_finality": False,
    }
    return {
        **body,
        "receipt_hash": hash_v1(M6_AUTHORITY_RECEIPT_HASH_DOMAIN_V1, body),
    }


@dataclass
class _M6AwareTauVerifier:
    receipt_mutator: object | None = None
    requests: list[Mapping[str, object]] = field(default_factory=list)

    def verify_tau_state_proof(self, request: Mapping[str, object]) -> Mapping[str, object]:
        self.requests.append(request)
        authority = request["m6_authority_request"]
        assert isinstance(authority, Mapping)
        receipt = (
            _deposit_receipt_from_request(request)
            if authority["kind"] == GlobalCommandKindV1.TAU_ESCROW_DEPOSIT.value
            else _ack_receipt_from_request(request)
        )
        if callable(self.receipt_mutator):
            mutated = self.receipt_mutator(dict(receipt))
            assert isinstance(mutated, Mapping)
            return dict(mutated)
        return receipt


@dataclass
class _ReadOnlyTauVerifier:
    requests: list[Mapping[str, object]] = field(default_factory=list)

    def verify_tau_state_proof(self, request: Mapping[str, object]) -> Mapping[str, object]:
        self.requests.append(request)
        return {
            "schema": "zenodex.tau.state_proof_verification_receipt.v0",
            "ok": True,
            "state_hash": request["state_hash"],
            "authorizes_settlement": False,
        }


@dataclass
class _M6AwareMigrationVerifier:
    requests: list[Mapping[str, object]] = field(default_factory=list)

    def verify_m6_migration(self, request: Mapping[str, object]) -> Mapping[str, object]:
        self.requests.append(request)
        authority = request["proof"]
        assert isinstance(authority, Mapping)
        body: dict[str, object] = {
            "schema": M6_AUTHORITY_RECEIPT_SCHEMA_V1,
            "ok": True,
            "kind": request["kind"],
            "subject_root": request["subject_root"],
            "pre_state_root": request["pre_state_root"],
            "command_hash": request["command_hash"],
            "evidence_root": hash_v1("m6-migration-authority-proof-v1", authority),
            "checkpoint_root": authority["checkpoint_root"],
            "condition_root": authority["condition_root"],
            "compatible_profile_root": request["expected_compatible_profile_root"],
            "source_authority_epoch": request["expected_source_authority_epoch"],
            "authorizes_m6_authority": True,
            "authorizes_economic_finality": False,
        }
        return {
            **body,
            "receipt_hash": hash_v1(M6_AUTHORITY_RECEIPT_HASH_DOMAIN_V1, body),
        }


def _migration_receipt_from_request(request: Mapping[str, object]) -> dict[str, object]:
    proof = request["proof"]
    assert isinstance(proof, Mapping)
    body: dict[str, object] = {
        "schema": M6_AUTHORITY_RECEIPT_SCHEMA_V1,
        "ok": True,
        "kind": request["kind"],
        "subject_root": request["subject_root"],
        "pre_state_root": request["pre_state_root"],
        "command_hash": request["command_hash"],
        "evidence_root": hash_v1("m6-migration-authority-proof-v1", proof),
        "checkpoint_root": proof["checkpoint_root"],
        "condition_root": proof["condition_root"],
        "compatible_profile_root": request["expected_compatible_profile_root"],
        "source_authority_epoch": request["expected_source_authority_epoch"],
        "authorizes_m6_authority": True,
        "authorizes_economic_finality": False,
    }
    return {
        **body,
        "receipt_hash": hash_v1(M6_AUTHORITY_RECEIPT_HASH_DOMAIN_V1, body),
    }


@dataclass
class _ExternalProofVerifier:
    output_mutator: object | None = None
    accept: bool = True
    payloads: list[Mapping[str, object]] = field(default_factory=list)

    def verify_with_output(
        self,
        payload: object,
    ) -> tuple[bool, str | None, Mapping[str, object] | None]:
        assert isinstance(payload, Mapping)
        self.payloads.append(payload)
        if not self.accept:
            return False, "external proof rejected", None
        request = payload["request"]
        assert isinstance(request, Mapping)
        if request.get("schema") == "tau_state_proof_verify":
            authority = request["m6_authority_request"]
            assert isinstance(authority, Mapping)
        else:
            authority = request
        kind = authority["kind"]
        if kind == GlobalCommandKindV1.TAU_ESCROW_DEPOSIT.value:
            receipt = _deposit_receipt_from_request(request)
        elif kind == GlobalCommandKindV1.TAU_WITHDRAWAL_ACK.value:
            receipt = _ack_receipt_from_request(request)
        else:
            receipt = _migration_receipt_from_request(authority)
        envelope: dict[str, object] = {
            "schema": M6_EXTERNAL_VERIFIER_OUTPUT_SCHEMA_V1,
            "ok": True,
            "verifier_request_hash": payload["verifier_request_hash"],
            "receipt": receipt,
        }
        if callable(self.output_mutator):
            mutated = self.output_mutator(dict(envelope))
            assert isinstance(mutated, Mapping)
            return True, None, dict(mutated)
        return True, None, envelope


class _SingleSnapshotMapping(Mapping[str, object]):
    """Adversarial mapping whose key stream is valid exactly once."""

    def __init__(self, values: Mapping[str, object]) -> None:
        self._values = dict(values)
        self.iterations = 0

    def __getitem__(self, key: str) -> object:
        return self._values[key]

    def __iter__(self) -> Iterator[str]:
        self.iterations += 1
        if self.iterations > 1:
            raise RuntimeError("mapping was observed more than once")
        return iter(self._values)

    def __len__(self) -> int:
        return len(self._values)


class _ChangingSnapshotMapping(Mapping[str, object]):
    """Adversarial mapping that changes after its first key observation."""

    def __init__(
        self,
        first: Mapping[str, object],
        second: Mapping[str, object],
    ) -> None:
        self._versions = (dict(first), dict(second))
        self.iterations = 0

    @property
    def _current(self) -> Mapping[str, object]:
        return self._versions[min(max(self.iterations - 1, 0), 1)]

    def __getitem__(self, key: str) -> object:
        return self._current[key]

    def __iter__(self) -> Iterator[str]:
        self.iterations += 1
        return iter(self._current)

    def __len__(self) -> int:
        return len(self._current)


def _deposit_command() -> GlobalCommandV1:
    proof = _deposit()
    return GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        command_id=_root(21),
        sender="alice",
        nonce=1,
        payload={
            "deposit_id": proof.deposit_id,
            "asset": proof.asset,
            "amount_atoms": proof.amount_atoms,
            "tau_transaction_root": proof.tau_transaction_root,
            "tau_finality_root": proof.tau_finality_root,
            "tau_profile_root": proof.tau_profile_root,
        },
    )


def _ack_command() -> GlobalCommandV1:
    return GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        command_id=_root(22),
        sender="alice",
        nonce=2,
        payload={
            "withdrawal_id": "withdrawal-1",
            "ack_root": _root(23),
            "tau_receipt_root": _root(24),
        },
    )


def test_given_no_backend_when_tau_authority_is_requested_then_it_fails_closed() -> None:
    # Arrange: the default adapter has no external authority implementation.
    adapter = M6AuthorityVerifierAdapterV1()

    # Act / Assert: no caller-authored roots can manufacture a witness.
    with pytest.raises(M6AuthorityVerifierUnavailableV1, match="not configured"):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )


def test_given_zero_or_one_subject_root_when_authority_is_requested_then_boundary_is_explicit() -> None:
    # Arrange: adjacent BVE inputs around the nonzero-root guard.
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=_M6AwareTauVerifier())

    # Act / Assert: zero is inadmissible, while the one-atom neighbor reaches
    # the external verifier contract.
    with pytest.raises(ValueError, match="subject root must be nonzero"):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(0),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )
    adapter.verify_tau_escrow_deposit(
        _deposit(),
        expected_subject_root=_root(1),
        expected_pre_state_root=_root(32),
        expected_command_hash=_root(33),
    )


def test_given_read_only_tau_receipt_when_m6_credit_is_requested_then_it_is_rejected() -> None:
    # Arrange: current Tau infrastructure reports read-only finality evidence.
    backend = _ReadOnlyTauVerifier()
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    # Act / Assert: a read-only receipt cannot issue M6 authority.
    with pytest.raises(M6AuthorityProofRejectedV1, match="binding mismatch"):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )
    assert len(backend.requests) == 1
    request = backend.requests[0]
    assert request["schema"] == "tau_state_proof_verify"
    authority_request = request["m6_authority_request"]
    assert isinstance(authority_request, Mapping)
    assert authority_request["schema"] == M6_AUTHORITY_REQUEST_SCHEMA_V1


def test_given_m6_aware_tau_receipt_when_bindings_match_then_core_can_issue_opaque_evidence() -> None:
    # Arrange: the external verifier returns the exact closed M6 receipt.
    backend = _M6AwareTauVerifier()
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)
    command = _deposit_command()
    proof = _deposit()

    # Act: the core performs command binding, then delegates external authority.
    evidence = verify_tau_escrow_deposit_evidence_v1(
        command,
        proof,
        subject_root=_root(31),
        pre_state_root=_root(32),
        tau_profile_root=proof.tau_profile_root,
        verifier=adapter,
    )

    # Assert: only the opaque core witness crosses into consensus state.
    assert evidence.command_hash == command.command_hash
    assert evidence.subject_root == _root(31)
    assert evidence.pre_state_root == _root(32)
    assert evidence.payload == proof
    assert backend.requests[0]["state_hash"] == proof.tau_finality_root


def test_given_m6_aware_ack_receipt_when_provenance_matches_then_core_can_issue_evidence() -> None:
    # Arrange: an acknowledgment is bound to the pending withdrawal provenance.
    backend = _M6AwareTauVerifier()
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)
    command = _ack_command()
    acknowledgment = WithdrawalAcknowledgmentV1(
        withdrawal_id="withdrawal-1",
        provenance_root=_root(25),
        tau_receipt_root=_root(24),
        acknowledged_state_root=_root(23),
    )

    # Act: the core delegates the exact acknowledgment to the Tau adapter.
    evidence = verify_tau_withdrawal_ack_evidence_v1(
        command,
        acknowledgment,
        subject_root=_root(31),
        pre_state_root=_root(32),
        expected_provenance_root=_root(25),
        verifier=adapter,
    )

    # Assert: the Tau receipt root is used as the external state-proof anchor.
    assert evidence.payload == acknowledgment
    assert backend.requests[0]["state_hash"] == acknowledgment.tau_receipt_root


def test_given_crossed_or_finality_authorizing_receipt_when_verified_then_it_rejects() -> None:
    def mutate(receipt: Mapping[str, object]) -> Mapping[str, object]:
        body = dict(receipt)
        body["pre_state_root"] = _root(999)
        body["authorizes_economic_finality"] = True
        body_without_hash = {key: value for key, value in body.items() if key != "receipt_hash"}
        body["receipt_hash"] = hash_v1(M6_AUTHORITY_RECEIPT_HASH_DOMAIN_V1, body_without_hash)
        return body

    # Arrange: the backend attempts a crossed binding and upgrades Tau evidence
    # into economic finality in the same receipt.
    adapter = M6AuthorityVerifierAdapterV1(
        tau_state_proof_verifier=_M6AwareTauVerifier(receipt_mutator=mutate)
    )

    # Act / Assert: both mutations are below the exact-receipt acceptance gate.
    with pytest.raises(M6AuthorityProofRejectedV1, match="binding mismatch"):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )


def test_given_migration_backend_when_fallback_condition_is_bound_then_core_can_issue_evidence() -> None:
    # Arrange: the migration backend is a test-only stand-in for the missing
    # objective liveness/catch-up proof implementation.
    backend = _M6AwareMigrationVerifier()
    adapter = M6AuthorityVerifierAdapterV1(migration_verifier=backend)
    command = GlobalCommandV1(
        kind=GlobalCommandKindV1.FALLBACK_ACTIVATE,
        command_id=_root(41),
        sender="operator",
        nonce=1,
        payload={"checkpoint_root": _root(42)},
    )
    proof = MigrationAuthorityProofV1(
        kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
        checkpoint_root=_root(42),
        compatible_profile_root=_root(0),
        condition_root=_root(43),
        source_authority_epoch=2,
    )

    # Act: issue the witness only after the adapter validates the exact receipt.
    evidence = verify_migration_evidence_v1(
        command,
        proof,
        subject_root=_root(31),
        pre_state_root=_root(32),
        source_authority_epoch=2,
        tau_profile_root=_root(44),
        verifier=adapter,
    )

    # Assert: the request preserves migration kind, epoch, and profile binding.
    assert evidence.payload == proof
    request = backend.requests[0]
    assert request["kind"] == GlobalCommandKindV1.FALLBACK_ACTIVATE.value
    assert request["expected_source_authority_epoch"] == 2
    assert request["expected_compatible_profile_root"] == _root(0)


def test_given_crossed_migration_epoch_or_profile_when_adapter_is_called_then_it_rejects() -> None:
    # Arrange: the proof is valid only for source epoch 2 and the fallback
    # profile marker zero.
    adapter = M6AuthorityVerifierAdapterV1(migration_verifier=_M6AwareMigrationVerifier())
    proof = MigrationAuthorityProofV1(
        kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
        checkpoint_root=_root(42),
        compatible_profile_root=_root(0),
        condition_root=_root(43),
        source_authority_epoch=2,
    )

    # Act / Assert: the adapter retains the boundary even without the core
    # command-binding helper around it.
    with pytest.raises(M6AuthorityProofRejectedV1, match="epoch"):
        adapter.verify_migration(
            proof,
            expected_kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_source_authority_epoch=3,
            expected_compatible_profile_root=_root(0),
            expected_command_hash=_root(41),
        )
    with pytest.raises(M6AuthorityProofRejectedV1, match="profile"):
        adapter.verify_migration(
            proof,
            expected_kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_source_authority_epoch=2,
            expected_compatible_profile_root=_root(44),
            expected_command_hash=_root(41),
        )


def test_given_request_hashed_external_backend_when_receipt_matches_then_it_issues_evidence() -> None:
    # Arrange: the shell receives a verifier implementation through a narrow
    # port; it has no authority to construct the core witness itself.
    external = _ExternalProofVerifier()
    backend = M6ProofVerifierBackendV1(proof_verifier=external)
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)
    command = _deposit_command()
    proof = _deposit()

    # Act: the core binds the command and the external shell checks the exact
    # request/receipt envelope before the opaque witness is issued.
    evidence = verify_tau_escrow_deposit_evidence_v1(
        command,
        proof,
        subject_root=_root(31),
        pre_state_root=_root(32),
        tau_profile_root=proof.tau_profile_root,
        verifier=adapter,
    )

    # Assert: request identity is canonical and independently hashed.
    assert evidence.payload == proof
    payload = external.payloads[0]
    assert payload["schema"] == M6_EXTERNAL_VERIFIER_REQUEST_SCHEMA_V1
    assert payload["operation"] == "tau_state_proof"
    request = payload["request"]
    assert isinstance(request, Mapping)
    assert payload["verifier_request_hash"] == hash_v1(
        M6_EXTERNAL_VERIFIER_REQUEST_HASH_DOMAIN_V1,
        {"operation": payload["operation"], "request": request},
    )


def test_given_external_backend_without_request_binding_when_called_then_it_rejects() -> None:
    def remove_request_binding(envelope: Mapping[str, object]) -> Mapping[str, object]:
        return {key: value for key, value in envelope.items() if key != "verifier_request_hash"}

    # Arrange: a successful cryptographic result without the exact request
    # binding is an invalid authority result.
    external = _ExternalProofVerifier(output_mutator=remove_request_binding)
    backend = M6ProofVerifierBackendV1(proof_verifier=external)
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    # Act / Assert: no M6 witness crosses the missing-binding boundary.
    with pytest.raises(M6AuthorityProofRejectedV1) as caught:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    assert str(caught.value) == "M6 Tau authority verifier rejected the request"


def test_given_external_backend_with_an_unknown_output_field_when_called_then_it_rejects() -> None:
    def add_unknown_field(envelope: Mapping[str, object]) -> Mapping[str, object]:
        return {**envelope, "unexpected": True}

    # Arrange: a verifier response with an extension field is not the frozen
    # receipt ABI accepted by the M6 shell.
    external = _ExternalProofVerifier(output_mutator=add_unknown_field)
    backend = M6ProofVerifierBackendV1(proof_verifier=external)
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    # Act / Assert: unknown output fields cannot smuggle new authority data.
    with pytest.raises(M6AuthorityProofRejectedV1) as caught:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    assert str(caught.value) == "M6 Tau authority verifier rejected the request"


def test_given_boolean_schema_version_neighbor_when_backend_is_called_then_it_rejects() -> None:
    # Arrange: Python's bool/int equality must not blur the version boundary.
    proof = _deposit()
    authority_request: dict[str, object] = {
        "schema": M6_AUTHORITY_REQUEST_SCHEMA_V1,
        "kind": GlobalCommandKindV1.TAU_ESCROW_DEPOSIT.value,
        "subject_root": _root(31),
        "pre_state_root": _root(32),
        "command_hash": _root(33),
        "evidence_root": proof.proof_root,
        "proof": proof.to_canonical(),
    }
    request = {
        "schema": "tau_state_proof_verify",
        "schema_version": True,
        "state_hash": proof.tau_finality_root,
        "proof": {
            "present": True,
            "state_hash": proof.tau_finality_root,
            "m6_authority_request": authority_request,
        },
        "m6_authority_request": authority_request,
    }
    backend = M6ProofVerifierBackendV1(proof_verifier=_ExternalProofVerifier())

    # Act / Assert: the adjacent bool value is rejected before external I/O.
    with pytest.raises(M6AuthorityProofRejectedV1, match="schema version"):
        backend.verify_tau_state_proof(request)


def test_given_external_backend_rejecting_the_proof_when_called_then_it_fails_closed() -> None:
    # Arrange: the external proof engine is unavailable or rejects the proof.
    external = _ExternalProofVerifier(accept=False)
    backend = M6ProofVerifierBackendV1(proof_verifier=external)
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    # Act / Assert: the adapter never turns a failed external result into
    # authority evidence.
    with pytest.raises(M6AuthorityProofRejectedV1) as caught:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    assert str(caught.value) == "M6 Tau authority verifier rejected the request"
    assert "external proof rejected" not in str(caught.value)


def test_given_external_backend_bug_when_called_then_internal_failure_is_not_proof_rejection() -> None:
    class RaisingExternalVerifier:
        def verify_with_output(
            self,
            _payload: object,
        ) -> tuple[bool, str | None, Mapping[str, object] | None]:
            raise RuntimeError("private proof-provider token")

    backend = M6ProofVerifierBackendV1(proof_verifier=RaisingExternalVerifier())
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    with pytest.raises(M6AuthorityVerifierInternalFailureV1) as caught:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    assert str(caught.value) == "M6 Tau authority verifier failed internally"
    assert "token" not in str(caught.value)
    assert caught.value.__cause__ is None
    assert caught.value.__context__ is None


def test_given_external_backend_timeout_when_called_then_unavailable_is_retryable_class() -> None:
    class TimedOutExternalVerifier:
        def verify_with_output(
            self,
            _payload: object,
        ) -> tuple[bool, str | None, Mapping[str, object] | None]:
            raise TimeoutError("private verifier endpoint")

    backend = M6ProofVerifierBackendV1(proof_verifier=TimedOutExternalVerifier())
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    with pytest.raises(M6AuthorityVerifierUnavailableV1) as caught:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    assert str(caught.value) == "M6 Tau authority verifier is unavailable"
    assert "endpoint" not in str(caught.value)
    assert caught.value.__cause__ is None
    assert caught.value.__context__ is None


def test_given_stateful_mapping_when_validated_then_authority_request_is_snapshotted_once() -> None:
    proof = MigrationAuthorityProofV1(
        kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
        checkpoint_root=_root(42),
        compatible_profile_root=_root(0),
        condition_root=_root(43),
        source_authority_epoch=2,
    ).to_canonical()
    request = _SingleSnapshotMapping(
        {
            "schema": M6_AUTHORITY_REQUEST_SCHEMA_V1,
            "kind": GlobalCommandKindV1.FALLBACK_ACTIVATE.value,
            "subject_root": _root(31),
            "pre_state_root": _root(32),
            "command_hash": _root(41),
            "evidence_root": hash_v1("m6-migration-authority-proof-v1", proof),
            "proof": proof,
            "expected_source_authority_epoch": 2,
            "expected_compatible_profile_root": _root(0),
        }
    )
    external = _ExternalProofVerifier()
    backend = M6ProofVerifierBackendV1(proof_verifier=external)

    receipt = backend.verify_m6_migration(request)

    assert receipt["kind"] == GlobalCommandKindV1.FALLBACK_ACTIVATE.value
    assert request.iterations == 1
    assert len(external.payloads) == 1


def test_given_stateful_nested_proof_when_validated_then_forwarded_proof_is_the_owned_snapshot(
) -> None:
    first = MigrationAuthorityProofV1(
        kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
        checkpoint_root=_root(42),
        compatible_profile_root=_root(0),
        condition_root=_root(43),
        source_authority_epoch=2,
    ).to_canonical()
    second = {**first, "checkpoint_root": _root(99)}
    proof = _ChangingSnapshotMapping(first, second)
    request = {
        "schema": M6_AUTHORITY_REQUEST_SCHEMA_V1,
        "kind": GlobalCommandKindV1.FALLBACK_ACTIVATE.value,
        "subject_root": _root(31),
        "pre_state_root": _root(32),
        "command_hash": _root(41),
        "evidence_root": hash_v1("m6-migration-authority-proof-v1", first),
        "proof": proof,
        "expected_source_authority_epoch": 2,
        "expected_compatible_profile_root": _root(0),
    }
    external = _ExternalProofVerifier(accept=False)
    backend = M6ProofVerifierBackendV1(proof_verifier=external)

    with pytest.raises(M6AuthorityProofRejectedV1):
        backend.verify_m6_migration(request)

    forwarded = external.payloads[0]["request"]
    assert isinstance(forwarded, Mapping)
    assert proof.iterations == 1
    assert forwarded["proof"] == first
    assert forwarded["evidence_root"] == hash_v1(
        "m6-migration-authority-proof-v1",
        forwarded["proof"],
    )


def test_given_stateful_tau_authority_aliases_when_validated_then_both_forwarded_views_are_owned(
) -> None:
    deposit = _deposit()
    first: dict[str, object] = {
        "schema": M6_AUTHORITY_REQUEST_SCHEMA_V1,
        "kind": GlobalCommandKindV1.TAU_ESCROW_DEPOSIT.value,
        "subject_root": _root(31),
        "pre_state_root": _root(32),
        "command_hash": _root(33),
        "evidence_root": deposit.proof_root,
        "proof": deposit.to_canonical(),
    }
    second = {**first, "command_hash": _root(99)}
    top_authority = _ChangingSnapshotMapping(first, second)
    envelope_authority = _ChangingSnapshotMapping(first, second)
    request = {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": deposit.tau_finality_root,
        "proof": {
            "present": True,
            "state_hash": deposit.tau_finality_root,
            "m6_authority_request": envelope_authority,
        },
        "m6_authority_request": top_authority,
    }
    external = _ExternalProofVerifier(accept=False)
    backend = M6ProofVerifierBackendV1(proof_verifier=external)

    with pytest.raises(M6AuthorityProofRejectedV1):
        backend.verify_tau_state_proof(request)

    forwarded = external.payloads[0]["request"]
    assert isinstance(forwarded, Mapping)
    forwarded_proof = forwarded["proof"]
    assert isinstance(forwarded_proof, Mapping)
    assert top_authority.iterations == 1
    assert envelope_authority.iterations == 1
    assert forwarded["m6_authority_request"] == first
    assert forwarded_proof["m6_authority_request"] == first


def test_given_request_hashed_migration_backend_when_epoch_and_profile_match_then_it_issues_evidence() -> None:
    # Arrange: fallback uses the same request-hashed external verifier port.
    external = _ExternalProofVerifier()
    backend = M6ProofVerifierBackendV1(proof_verifier=external)
    adapter = M6AuthorityVerifierAdapterV1(migration_verifier=backend)
    command = GlobalCommandV1(
        kind=GlobalCommandKindV1.FALLBACK_ACTIVATE,
        command_id=_root(41),
        sender="operator",
        nonce=1,
        payload={"checkpoint_root": _root(42)},
    )
    proof = MigrationAuthorityProofV1(
        kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
        checkpoint_root=_root(42),
        compatible_profile_root=_root(0),
        condition_root=_root(43),
        source_authority_epoch=2,
    )

    # Act: migration evidence crosses only after exact external verification.
    evidence = verify_migration_evidence_v1(
        command,
        proof,
        subject_root=_root(31),
        pre_state_root=_root(32),
        source_authority_epoch=2,
        tau_profile_root=_root(44),
        verifier=adapter,
    )

    # Assert: the migration request remains bound to the exact source epoch.
    assert evidence.payload == proof
    payload = external.payloads[0]
    assert payload["operation"] == "migration"
    request = payload["request"]
    assert isinstance(request, Mapping)
    assert request["expected_source_authority_epoch"] == 2
    assert request["expected_compatible_profile_root"] == _root(0)


def test_given_valid_max_root_and_overflow_neighbor_when_backend_is_called_then_bve_is_explicit() -> None:
    # Arrange: BVE probes the maximum valid 256-bit root and its first invalid
    # neighbor, in addition to the zero/one boundary above.
    external = _ExternalProofVerifier()
    adapter = M6AuthorityVerifierAdapterV1(
        tau_state_proof_verifier=M6ProofVerifierBackendV1(proof_verifier=external)
    )

    # Act / Assert: the maximum root reaches the verifier, while overflow is
    # rejected before any external call.
    adapter.verify_tau_escrow_deposit(
        _deposit(),
        expected_subject_root=_root((1 << 256) - 1),
        expected_pre_state_root=_root(32),
        expected_command_hash=_root(33),
    )
    with pytest.raises(ValueError):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root="0x1" + "00" * 32,
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )


# ── Hostile receipt-mapping probes (Sol review Issue #4) ────────────────────


class _HostileIterMapping(Mapping[str, object]):
    """Mapping whose __iter__ raises with secret-bearing exception text."""

    def __init__(self, values: Mapping[str, object]) -> None:
        self._values = dict(values)

    def __getitem__(self, key: str) -> object:
        return self._values[key]

    def __iter__(self) -> Iterator[str]:
        raise RuntimeError("SENSITIVE_BACKEND_DETAIL_ITER")

    def __len__(self) -> int:
        return len(self._values)


class _HostileKeysMapping(Mapping[str, object]):
    """Mapping whose keys() raises when observed."""

    def __init__(self, values: Mapping[str, object]) -> None:
        self._values = dict(values)

    def __getitem__(self, key: str) -> object:
        return self._values[key]

    def __iter__(self) -> Iterator[str]:
        return iter(self._values)

    def __len__(self) -> int:
        return len(self._values)

    def keys(self) -> object:
        raise RuntimeError("SENSITIVE_BACKEND_DETAIL_KEYS")


class _HostileGetItemMapping(Mapping[str, object]):
    """Mapping whose __getitem__ raises for one key."""

    def __init__(self, values: Mapping[str, object], failing_key: str) -> None:
        self._values = dict(values)
        self._failing_key = failing_key

    def __getitem__(self, key: str) -> object:
        if key == self._failing_key:
            raise RuntimeError("SENSITIVE_BACKEND_DETAIL_GETITEM")
        return self._values[key]

    def __iter__(self) -> Iterator[str]:
        return iter(self._values)

    def __len__(self) -> int:
        return len(self._values)


class _CyclicReceiptMapping(Mapping[str, object]):
    """Mapping that contains a self-reference cycle."""

    def __init__(self) -> None:
        self._data: dict[str, object] = {"ok": True, "schema": "test"}
        self._data["self"] = self

    def __getitem__(self, key: str) -> object:
        return self._data[key]

    def __iter__(self) -> Iterator[str]:
        return iter(self._data)

    def __len__(self) -> int:
        return len(self._data)


class _HostileLenMapping(Mapping[str, object]):
    """Mapping whose __len__ raises."""

    def __init__(self, values: Mapping[str, object]) -> None:
        self._values = dict(values)

    def __getitem__(self, key: str) -> object:
        return self._values[key]

    def __iter__(self) -> Iterator[str]:
        return iter(self._values)

    def __len__(self) -> int:
        raise RuntimeError("SENSITIVE_BACKEND_DETAIL_LEN")


class _AlwaysEqualReceiptValue:
    """Attacker value that makes ordinary mapping equality accept a forgery."""

    def __eq__(self, _other: object) -> bool:
        return True


class _ExplodingReceiptValue:
    """Attacker value whose comparison tries to cross the verifier boundary."""

    def __eq__(self, _other: object) -> bool:
        raise RuntimeError("SENSITIVE_BACKEND_DETAIL_EQ")


class _ExplodingReceiptKey:
    """Attacker key colliding with ``ok`` must be rejected before lookup."""

    def __init__(self, collision: str = "ok") -> None:
        self._collision = collision

    def __hash__(self) -> int:
        return hash(self._collision)

    def __eq__(self, _other: object) -> bool:
        raise RuntimeError("SENSITIVE_BACKEND_DETAIL_KEY_EQ")


@pytest.mark.parametrize("field", ["schema", "verifier_request_hash"])
@pytest.mark.parametrize(
    "hostile_value",
    [_AlwaysEqualReceiptValue(), _ExplodingReceiptValue()],
    ids=["always-equal", "exploding-equality"],
)
def test_given_hostile_external_envelope_value_when_checked_then_it_cannot_forge_binding(
    field: str,
    hostile_value: object,
) -> None:
    """External envelope bindings require exact built-in strings."""

    def forge_envelope(envelope: Mapping[str, object]) -> Mapping[str, object]:
        return {**envelope, field: hostile_value}

    external = _ExternalProofVerifier(output_mutator=forge_envelope)
    adapter = M6AuthorityVerifierAdapterV1(
        tau_state_proof_verifier=M6ProofVerifierBackendV1(proof_verifier=external)
    )

    with pytest.raises(M6AuthorityProofRejectedV1) as exc_info:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    assert "SENSITIVE" not in str(exc_info.value)


def test_given_hostile_external_envelope_key_when_checked_then_no_lookup_hook_runs() -> None:
    """Closed string field names are established before request-hash lookup."""

    def forge_key(envelope: Mapping[str, object]) -> Mapping[object, object]:
        return {
            (
                _ExplodingReceiptKey("verifier_request_hash")
                if key == "verifier_request_hash"
                else key
            ): value
            for key, value in envelope.items()
        }

    external = _ExternalProofVerifier(output_mutator=forge_key)
    adapter = M6AuthorityVerifierAdapterV1(
        tau_state_proof_verifier=M6ProofVerifierBackendV1(proof_verifier=external)
    )

    with pytest.raises(M6AuthorityProofRejectedV1) as exc_info:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    assert "SENSITIVE" not in str(exc_info.value)


@pytest.mark.parametrize(
    "hostile_label,hostile_mapping,expected_error",
    [
        ("hostile-iter", lambda: _HostileIterMapping({"ok": True}), M6AuthorityVerifierInternalFailureV1),
        ("hostile-keys", lambda: _HostileKeysMapping({"ok": True}), M6AuthorityVerifierInternalFailureV1),
        ("hostile-getitem", lambda: _HostileGetItemMapping({"ok": True}, "ok"), M6AuthorityVerifierInternalFailureV1),
        ("hostile-len", lambda: _HostileLenMapping({"ok": True}), M6AuthorityProofRejectedV1),
        ("cyclic", lambda: _CyclicReceiptMapping(), M6AuthorityProofRejectedV1),
    ],
)
def test_given_hostile_receipt_mapping_when_observed_then_typed_rejection_without_secret_leakage(
    hostile_label: str,
    hostile_mapping: object,
    expected_error: type,
) -> None:
    """RIPR: Reach receipt conversion with every hostile dunder; Infect with
    secret-bearing exceptions; Propagate through Tau and migration adapter
    methods; Reveal only a stable typed rejection with no cause, context, or
    provider text.

    Hostile ``__iter__``, ``keys``, ``__len__``, and ``__getitem__`` are
    caught at the backend boundary by the existing ``dict()`` call in
    ``_M6AwareTauVerifier.verify_tau_state_proof`` and converted to
    ``M6AuthorityVerifierInternalFailureV1``.  The cyclic mapping reaches
    ``_require_receipt`` where ``_snapshot_receipt_mapping`` owns a stable
    observation and the binding-mismatch check rejects the extra field.
    """

    hostile = hostile_mapping() if callable(hostile_mapping) else hostile_mapping
    backend = _M6AwareTauVerifier()
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    def hostile_receipt(_request: object) -> Mapping[str, object]:
        assert isinstance(hostile, Mapping)
        return hostile

    backend.receipt_mutator = hostile_receipt  # type: ignore[assignment]

    with pytest.raises(expected_error) as exc_info:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    message = str(exc_info.value)
    assert "SENSITIVE" not in message


def test_given_hostile_migration_receipt_when_observed_then_typed_rejection_without_secret_leakage() -> None:
    """The migration adapter path is independently protected."""

    hostile = _HostileIterMapping({"ok": True, "schema": M6_AUTHORITY_RECEIPT_SCHEMA_V1})
    migration_backend = _M6AwareMigrationVerifier()
    adapter = M6AuthorityVerifierAdapterV1(migration_verifier=migration_backend)

    # Override the backend to return the hostile mapping.
    original_verify = migration_backend.verify_m6_migration

    def hostile_verify(request: Mapping[str, object]) -> Mapping[str, object]:
        original_verify(request)  # consume request normally
        return hostile

    migration_backend.verify_m6_migration = hostile_verify  # type: ignore[method-assign]

    proof = MigrationAuthorityProofV1(
        kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
        checkpoint_root=_root(42),
        compatible_profile_root=_root(0),
        condition_root=_root(43),
        source_authority_epoch=2,
    )

    with pytest.raises(M6AuthorityProofRejectedV1) as exc_info:
        adapter.verify_migration(
            proof,
            expected_kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_source_authority_epoch=2,
            expected_compatible_profile_root=_root(0),
            expected_command_hash=_root(33),
        )

    message = str(exc_info.value)
    assert "SENSITIVE" not in message


def test_given_non_mapping_receipt_when_observed_then_typed_rejection() -> None:
    """BVA: non-mapping receipt is caught at the backend boundary and converted
    to a stable typed internal-failure rejection."""

    backend = _M6AwareTauVerifier()
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    def non_mapping_receipt(_request: object) -> object:
        return ["not", "a", "mapping"]

    backend.receipt_mutator = non_mapping_receipt  # type: ignore[assignment]

    with pytest.raises(M6AuthorityVerifierInternalFailureV1):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )


@pytest.mark.parametrize(
    "hostile_value",
    [_AlwaysEqualReceiptValue(), _ExplodingReceiptValue()],
    ids=["always-equal", "exploding-equality"],
)
def test_given_hostile_receipt_values_when_compared_then_no_authority_is_issued(
    hostile_value: object,
) -> None:
    """RIPR: exact keys with hostile values must not exploit Python equality."""

    backend = _M6AwareTauVerifier()
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    def forge_values(receipt: Mapping[str, object]) -> Mapping[str, object]:
        return {
            key: (True if key == "ok" else hostile_value)
            for key in receipt
        }

    backend.receipt_mutator = forge_values

    with pytest.raises(M6AuthorityProofRejectedV1) as exc_info:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    assert "SENSITIVE" not in str(exc_info.value)


def test_given_hostile_receipt_key_when_validated_then_no_lookup_hook_runs() -> None:
    """Field-name validation precedes any receipt lookup or equality hook."""

    backend = _M6AwareTauVerifier()
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    def forge_key(receipt: Mapping[str, object]) -> Mapping[object, object]:
        return {
            (_ExplodingReceiptKey() if key == "ok" else key): value
            for key, value in receipt.items()
        }

    backend.receipt_mutator = forge_key

    with pytest.raises(M6AuthorityProofRejectedV1) as exc_info:
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    assert "SENSITIVE" not in str(exc_info.value)


def test_given_empty_or_extra_field_receipt_when_verified_then_rejected() -> None:
    """BVA: empty and extra-field receipts are rejected with a typed error."""

    backend = _M6AwareTauVerifier()
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    # Empty receipt: ok is missing, so rejected-the-evidence.
    backend.receipt_mutator = lambda r: {}
    with pytest.raises(M6AuthorityProofRejectedV1, match="rejected the evidence"):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )

    # Extra-field receipt: binding mismatch.
    backend.receipt_mutator = lambda r: {**dict(r), "secret_field": "leaked"}
    with pytest.raises(M6AuthorityProofRejectedV1, match="binding mismatch"):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )
