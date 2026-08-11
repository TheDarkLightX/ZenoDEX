"""Adversarial contract tests for the M6 authority verifier adapter."""

from __future__ import annotations

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
    with pytest.raises(M6AuthorityProofRejectedV1, match="request hash"):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )


def test_given_external_backend_with_an_unknown_output_field_when_called_then_it_rejects() -> None:
    def add_unknown_field(envelope: Mapping[str, object]) -> Mapping[str, object]:
        return {**envelope, "unexpected": True}

    # Arrange: a verifier response with an extension field is not the frozen
    # receipt ABI accepted by the M6 shell.
    external = _ExternalProofVerifier(output_mutator=add_unknown_field)
    backend = M6ProofVerifierBackendV1(proof_verifier=external)
    adapter = M6AuthorityVerifierAdapterV1(tau_state_proof_verifier=backend)

    # Act / Assert: unknown output fields cannot smuggle new authority data.
    with pytest.raises(M6AuthorityProofRejectedV1, match="field set"):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )


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
    with pytest.raises(M6AuthorityProofRejectedV1, match="external proof rejected"):
        adapter.verify_tau_escrow_deposit(
            _deposit(),
            expected_subject_root=_root(31),
            expected_pre_state_root=_root(32),
            expected_command_hash=_root(33),
        )


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
