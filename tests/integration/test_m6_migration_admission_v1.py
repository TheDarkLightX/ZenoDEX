"""BDD/AAA evidence for the research-only M6-R11 admission shell."""

from __future__ import annotations

import json
from collections.abc import Iterator
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Mapping, cast

import pytest

import src.integration.m6_migration_admission_v1 as admission_module
from src.core.m6_migration_lifecycle_v1 import (
    M6MigrationPhaseV1,
    M6MigrationPlanV1,
    M6MigrationRejectCodeV1,
    M6MigrationStateV1,
    M6MigrationStepKindV1,
    M6MigrationStepV1,
)
from src.core.m6_safe_mount_types_v1 import ZERO_ROOT_V1, canonical_bytes_v1, hash_v1
from src.integration.m6_migration_admission_v1 import (
    M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V1,
    M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V2,
    M6MigrationAdmissionResultV1,
    M6MigrationAdmissionStatusV1,
    M6MigrationDurableCorruptionError,
    M6MigrationDurableStoreV1,
    M6MigrationExternalHeadAnchorV1,
    M6MigrationWriterAdmissionResultV1,
    M6MigrationWriterAdmissionStatusV1,
    M6MigrationWriterAuthorizationV1,
    M6MigrationWriterConsumerV1,
    _decode_state,
    authorize_m6_migration_writer_v1,
)
from src.integration.m6_migration_authority_v1 import (
    M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
    M6_MIGRATION_AUTHORITY_PROOF_SCHEMA_V1,
    M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_BYTES_V1,
    M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_DEPTH_V1,
    M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_ITEMS_V1,
    M6MigrationAuthorityProofRejectedV1,
    M6MigrationAuthorityVerifierV1,
    M6MigrationWriterMembershipProofV1,
    M6MigrationWriterMembershipVerifierV1,
    migration_authority_payload_hash_v1,
)
from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import (
    build_signer_registry_v0,
    verify_signature_quorum_v0,
)
from src.state.canonical import canonical_hex_fixed_allow_0x

_M6_TEST_PRIVATE_KEY = "0x" + "11" * 32
_M6_TEST_PRIVATE_KEY_2 = "0x" + "22" * 32


def _root(number: int) -> str:
    return canonical_hex_fixed_allow_0x(f"0x{number:064x}", nbytes=32, name="test root")


@dataclass
class _StructuralMigrationBackend:
    registry: Mapping[str, object] | None = None

    def verify_m6_migration_step(self, request: Mapping[str, object]) -> Mapping[str, object]:
        body = {
            "schema": request["receipt_schema"],
            "ok": True,
            "plan_root": request["plan_root"],
            "step_root": request["step_root"],
            "source_subject_root": request["source_subject_root"],
            "target_subject_root": request["target_subject_root"],
            "source_state_root": request["source_state_root"],
            "target_state_root": request["target_state_root"],
            "source_writer_epoch": request["source_writer_epoch"],
            "target_writer_epoch": request["target_writer_epoch"],
            "allowed_writer_set_root": request["allowed_writer_set_root"],
            "authority_registry_root": request["authority_registry_root"],
            "rollback_state_root": request["rollback_state_root"],
            "evidence_root": request["evidence_root"],
            "kind": request["kind"],
            "branch_root": request["branch_root"],
            "pre_state_root": request["pre_state_root"],
            "pre_phase": request["pre_phase"],
        }
        registry = self.registry or _m6_test_registry()
        payload_hash = migration_authority_payload_hash_v1(body)
        envelope = build_bls_signed_artifact_envelope_v0(
            payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id="migration-validator-0",
            key_id="migration-key-0",
            private_key_hex=_M6_TEST_PRIVATE_KEY,
        )
        quorum_report = verify_signature_quorum_v0(
            registry=registry,
            payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            envelopes=[envelope],
        )
        authority_proof = {
            "schema": M6_MIGRATION_AUTHORITY_PROOF_SCHEMA_V1,
            "payload_kind": M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
            "payload_hash": payload_hash,
            "registry_hash": registry["registry_hash"],
            "envelopes": [envelope],
            "quorum_report": quorum_report,
        }
        receipt_body = {**body, "authority_proof": authority_proof}
        return {
            **receipt_body,
            "receipt_hash": hash_v1("m6-migration-authority-receipt-v1", receipt_body),
        }

    def verify_m6_migration_writer_membership(
        self,
        request: Mapping[str, object],
    ) -> Mapping[str, object]:
        body = {
            "schema": request["receipt_schema"],
            "ok": True,
            "plan_root": request["plan_root"],
            "authority_registry_root": request["authority_registry_root"],
            "allowed_writer_set_root": request["allowed_writer_set_root"],
            "writer_subject_root": request["writer_subject_root"],
            "writer_epoch": request["writer_epoch"],
            "state_root": request["state_root"],
            "phase": request["phase"],
            "branch_root": request["branch_root"],
            "membership_proof_root": request["membership_proof_root"],
        }
        registry = self.registry or _m6_test_registry()
        payload_hash = migration_authority_payload_hash_v1(body)
        envelope = build_bls_signed_artifact_envelope_v0(
            payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id="migration-validator-0",
            key_id="migration-key-0",
            private_key_hex=_M6_TEST_PRIVATE_KEY,
        )
        authority_proof = {
            "schema": M6_MIGRATION_AUTHORITY_PROOF_SCHEMA_V1,
            "payload_kind": M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
            "payload_hash": payload_hash,
            "registry_hash": registry["registry_hash"],
            "envelopes": [envelope],
            "quorum_report": verify_signature_quorum_v0(
                registry=registry,
                payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
                payload_hash=payload_hash,
                envelopes=[envelope],
            ),
        }
        receipt_body = {**body, "authority_proof": authority_proof}
        return {
            **receipt_body,
            "receipt_hash": hash_v1("m6-migration-authority-receipt-v1", receipt_body),
        }


@dataclass
class _ReceiptMutationMembershipBackend(_StructuralMigrationBackend):
    """Deliberately substitute one receipt coordinate for authority tests."""

    mutation_field: str = ""
    mutation_value: object = None

    def verify_m6_migration_writer_membership(
        self,
        request: Mapping[str, object],
    ) -> Mapping[str, object]:
        receipt = dict(super().verify_m6_migration_writer_membership(request))
        receipt[self.mutation_field] = self.mutation_value
        return receipt


@dataclass
class _SignedPayloadMutationMembershipBackend(_StructuralMigrationBackend):
    """Mutate the nested signed payload while retaining the old receipt root."""

    def verify_m6_migration_writer_membership(
        self,
        request: Mapping[str, object],
    ) -> Mapping[str, object]:
        receipt = dict(super().verify_m6_migration_writer_membership(request))
        proof = dict(cast(Mapping[str, object], receipt["authority_proof"]))
        proof["payload_hash"] = _root(98)
        receipt["authority_proof"] = proof
        return receipt


class _ChangingMapping(Mapping[str, object]):
    """Expose one value on the first observation and another thereafter."""

    def __init__(
        self,
        first: Mapping[str, object],
        second: Mapping[str, object],
    ) -> None:
        self.first = dict(first)
        self.second = dict(second)
        self.iterations = 0
        self._current = self.first

    def __getitem__(self, key: str) -> object:
        return self._current[key]

    def __iter__(self) -> Iterator[str]:
        self.iterations += 1
        self._current = self.first if self.iterations == 1 else self.second
        return iter(self._current)

    def __len__(self) -> int:
        return len(self._current)

    def __eq__(self, other: object) -> bool:
        return self._current == other


def _changing_nested_authority_proof(
    receipt: Mapping[str, object],
) -> tuple[dict[str, object], _ChangingMapping]:
    first_proof = dict(cast(Mapping[str, object], receipt["authority_proof"]))
    forged_proof = {**first_proof, "quorum_report": {"forged": True}}
    changing_proof = _ChangingMapping(first_proof, forged_proof)
    body = {
        key: value
        for key, value in receipt.items()
        if key not in {"authority_proof", "receipt_hash"}
    }
    forged_body = {**body, "authority_proof": forged_proof}
    return (
        {
            **body,
            "authority_proof": changing_proof,
            "receipt_hash": hash_v1(
                "m6-migration-authority-receipt-v1",
                forged_body,
            ),
        },
        changing_proof,
    )


@dataclass
class _ChangingReceiptBackend(_StructuralMigrationBackend):
    nested: bool = False
    migration_mapping: _ChangingMapping | None = None
    membership_mapping: _ChangingMapping | None = None

    def _changing_receipt(
        self,
        receipt: Mapping[str, object],
    ) -> tuple[Mapping[str, object], _ChangingMapping]:
        first = dict(receipt)
        if self.nested:
            return _changing_nested_authority_proof(first)
        changing = _ChangingMapping(
            first,
            {**first, "receipt_hash": _root(99)},
        )
        return changing, changing

    def verify_m6_migration_step(
        self,
        request: Mapping[str, object],
    ) -> Mapping[str, object]:
        receipt, observed = self._changing_receipt(
            super().verify_m6_migration_step(request)
        )
        self.migration_mapping = observed
        return receipt

    def verify_m6_migration_writer_membership(
        self,
        request: Mapping[str, object],
    ) -> Mapping[str, object]:
        receipt, observed = self._changing_receipt(
            super().verify_m6_migration_writer_membership(request)
        )
        self.membership_mapping = observed
        return receipt


def _m6_test_registry() -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="m6-migration-test-registry",
        payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
        threshold=1,
        signers=[
            {
                "signer_id": "migration-validator-0",
                "key_id": "migration-key-0",
                "public_key": bls_public_key_hex_from_private_key_v0(_M6_TEST_PRIVATE_KEY),
                "weight": 1,
                "status": "active",
            }
        ],
    )


def _m6_two_signer_registry() -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="m6-migration-two-signer-test-registry",
        payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
        threshold=2,
        signers=[
            {
                "signer_id": "migration-validator-0",
                "key_id": "migration-key-0",
                "public_key": bls_public_key_hex_from_private_key_v0(_M6_TEST_PRIVATE_KEY),
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "migration-validator-1",
                "key_id": "migration-key-1",
                "public_key": bls_public_key_hex_from_private_key_v0(_M6_TEST_PRIVATE_KEY_2),
                "weight": 1,
                "status": "active",
            },
        ],
    )


@dataclass
class _NonCanonicalOrderMigrationBackend:
    registry: Mapping[str, object]

    def verify_m6_migration_step(self, request: Mapping[str, object]) -> Mapping[str, object]:
        body = {
            "schema": request["receipt_schema"],
            "ok": True,
            "plan_root": request["plan_root"],
            "step_root": request["step_root"],
            "source_subject_root": request["source_subject_root"],
            "target_subject_root": request["target_subject_root"],
            "source_state_root": request["source_state_root"],
            "target_state_root": request["target_state_root"],
            "source_writer_epoch": request["source_writer_epoch"],
            "target_writer_epoch": request["target_writer_epoch"],
            "allowed_writer_set_root": request["allowed_writer_set_root"],
            "authority_registry_root": request["authority_registry_root"],
            "rollback_state_root": request["rollback_state_root"],
            "evidence_root": request["evidence_root"],
            "kind": request["kind"],
            "branch_root": request["branch_root"],
            "pre_state_root": request["pre_state_root"],
            "pre_phase": request["pre_phase"],
        }
        payload_hash = migration_authority_payload_hash_v1(body)
        envelopes = [
            build_bls_signed_artifact_envelope_v0(
                payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
                payload_hash=payload_hash,
                signer_id="migration-validator-1",
                key_id="migration-key-1",
                private_key_hex=_M6_TEST_PRIVATE_KEY_2,
            ),
            build_bls_signed_artifact_envelope_v0(
                payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
                payload_hash=payload_hash,
                signer_id="migration-validator-0",
                key_id="migration-key-0",
                private_key_hex=_M6_TEST_PRIVATE_KEY,
            ),
        ]
        authority_proof = {
            "schema": M6_MIGRATION_AUTHORITY_PROOF_SCHEMA_V1,
            "payload_kind": M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
            "payload_hash": payload_hash,
            "registry_hash": self.registry["registry_hash"],
            "envelopes": envelopes,
            "quorum_report": verify_signature_quorum_v0(
                registry=self.registry,
                payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
                payload_hash=payload_hash,
                envelopes=envelopes,
            ),
        }
        receipt_body = {**body, "authority_proof": authority_proof}
        return {
            **receipt_body,
            "receipt_hash": hash_v1("m6-migration-authority-receipt-v1", receipt_body),
        }


def _foreign_registry() -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="m6-migration-foreign-registry",
        payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
        threshold=1,
        signers=[
            {
                "signer_id": "migration-validator-0",
                "key_id": "migration-key-0",
                "public_key": bls_public_key_hex_from_private_key_v0(_M6_TEST_PRIVATE_KEY),
                "weight": 1,
                "status": "active",
            }
        ],
    )


def _plan() -> M6MigrationPlanV1:
    return M6MigrationPlanV1(
        source_subject_root=_root(1),
        target_subject_root=_root(2),
        source_state_root=_root(3),
        target_state_root=_root(4),
        source_writer_epoch=7,
        target_writer_epoch=8,
        allowed_writer_set_root=_root(5),
        authority_registry_root=cast(str, _m6_test_registry()["registry_hash"]),
        rollback_state_root=_root(3),
    )


def _step(
    plan: M6MigrationPlanV1,
    kind: M6MigrationStepKindV1,
    evidence_number: int,
) -> M6MigrationStepV1:
    return M6MigrationStepV1(
        kind=kind,
        source_subject_root=plan.source_subject_root,
        target_subject_root=plan.target_subject_root,
        source_state_root=plan.source_state_root,
        target_state_root=plan.target_state_root,
        source_writer_epoch=plan.source_writer_epoch,
        target_writer_epoch=plan.target_writer_epoch,
        allowed_writer_set_root=plan.allowed_writer_set_root,
        rollback_state_root=plan.rollback_state_root,
        evidence_root=_root(evidence_number),
        rollback=kind is M6MigrationStepKindV1.ROLLBACK,
    )


def _verified(
    plan: M6MigrationPlanV1,
    kind: M6MigrationStepKindV1,
    evidence_number: int,
    *,
    state: M6MigrationStateV1 | None = None,
):
    active_state = state or M6MigrationStateV1.initial(plan)
    return M6MigrationAuthorityVerifierV1(
        _StructuralMigrationBackend(),
        signer_registry=_m6_test_registry(),
    ).verify_step_with_receipt(
        plan,
        _step(plan, kind, evidence_number),
        active_state.branch_root,
        pre_state_root=active_state.state_root,
        pre_phase=active_state.phase,
    )


def _verifier() -> M6MigrationAuthorityVerifierV1:
    return M6MigrationAuthorityVerifierV1(
        _StructuralMigrationBackend(),
        signer_registry=_m6_test_registry(),
    )


def _writer_membership_verifier() -> M6MigrationWriterMembershipVerifierV1:
    return M6MigrationWriterMembershipVerifierV1(
        _StructuralMigrationBackend(),
        signer_registry=_m6_test_registry(),
    )


def _writer_membership_proof(plan: M6MigrationPlanV1) -> dict[str, object]:
    return {
        "leaf": plan.target_subject_root,
        "set_root": plan.allowed_writer_set_root,
        "epoch": plan.target_writer_epoch,
    }


def _store(
    tmp_path: Path,
    initial: M6MigrationStateV1,
    *,
    require_external_anchor: bool = False,
    external_anchor: M6MigrationExternalHeadAnchorV1 | None = None,
) -> M6MigrationDurableStoreV1:
    return M6MigrationDurableStoreV1(
        tmp_path / "migration",
        initial_state=initial,
        authority_verifier=_verifier(),
        require_external_anchor=require_external_anchor,
        external_anchor=external_anchor,
    )


def _durable_snapshot(
    store: M6MigrationDurableStoreV1,
    anchor: M6MigrationExternalHeadAnchorV1,
) -> tuple[object, ...]:
    """Observe every durable value changed by the anchored commit port."""

    reopened = store.reopen()
    return (reopened.state, reopened.committed_steps, reopened.head_root, anchor.read())


def test_given_initial_state_when_store_reopens_then_canonical_state_is_reconstructed(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)

    store = _store(tmp_path, initial)
    reopened = store.reopen()

    assert reopened.state == initial
    assert reopened.committed_steps == ()


def test_given_pinned_store_when_root_path_is_replaced_then_original_store_fails_closed(
    tmp_path: Path,
) -> None:
    """RIPR/BVA: a live store cannot be redirected to a replacement root."""

    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    original_root = tmp_path / "migration"
    moved_root = tmp_path / "migration-original"

    original_root.rename(moved_root)
    replacement = M6MigrationDurableStoreV1(
        original_root,
        initial_state=initial,
        authority_verifier=_verifier(),
    )

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="root changed after initialization",
    ):
        store.reopen()
    assert replacement.reopen().state == initial


def test_given_custom_genesis_branch_when_store_reopens_then_branch_is_preserved(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan, branch_root=_root(99))

    store = _store(tmp_path, initial)

    assert store.reopen().state == initial


def test_given_advanced_state_without_history_when_store_is_created_then_bootstrap_rejects(
    tmp_path: Path,
) -> None:
    plan = _plan()
    advanced = replace(
        M6MigrationStateV1.initial(plan),
        phase=M6MigrationPhaseV1.SHADOW_REPLAY,
        replay_root=_root(11),
    )

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="genesis state with empty history",
    ):
        _store(tmp_path, advanced)


def test_given_authenticated_step_when_expected_head_matches_then_one_phase_commits_and_survives_restart(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    verified = _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11)

    result = store.admit(initial.state_root, verified)
    reopened = M6MigrationDurableStoreV1(
        tmp_path / "migration", authority_verifier=_verifier()
    ).reopen()

    assert result.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert result.state.phase is M6MigrationPhaseV1.SHADOW_REPLAY
    assert reopened.state == result.state
    assert len(reopened.committed_steps) == 1
    assert reopened.committed_steps[0].step_root == verified.verified_step.step.step_root
    assert result.head_root == reopened.head_root


def test_given_external_anchor_when_commit_succeeds_then_result_and_anchor_bind_new_head(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    anchor = M6MigrationExternalHeadAnchorV1(tmp_path / "external-anchor.json")
    store = _store(
        tmp_path,
        initial,
        require_external_anchor=True,
        external_anchor=anchor,
    )
    genesis_head_root = anchor.read()

    result = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )

    assert result.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert result.head_root is not None
    assert anchor.read() == result.head_root
    assert store.reopen(expected_head_root=result.head_root).state == result.state

    retry = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    assert retry.status is M6MigrationAdmissionStatusV1.ALREADY_COMMITTED
    assert retry.head_root == result.head_root
    assert anchor.read() == result.head_root

    with pytest.raises(TypeError, match="requires an admission result"):
        anchor.compare_and_set(genesis_head_root, _root(999), store=store)  # type: ignore[arg-type]


def test_given_ordered_anchor_history_when_retry_and_stale_submission_occur_then_model_and_durable_tail_agree(
    tmp_path: Path,
) -> None:
    """Stateful model: anchored commits form one exact, retry-safe head chain."""

    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    anchor = M6MigrationExternalHeadAnchorV1(tmp_path / "external-anchor.json")
    store = _store(
        tmp_path,
        initial,
        require_external_anchor=True,
        external_anchor=anchor,
    )

    model_state = initial
    model_head = anchor.read()
    model_step_roots: list[str] = []
    model_pre_head_roots: list[str] = []
    last_pre_state = initial
    last_evidence = None

    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
    ):
        evidence = _verified(plan, kind, evidence_number, state=model_state)
        result = store.admit(model_state.state_root, evidence)

        assert result.status is M6MigrationAdmissionStatusV1.COMMITTED
        assert result.pre_state_root == model_state.state_root
        assert result.pre_head_root == model_head
        assert result.head_root == anchor.read()

        last_pre_state = model_state
        last_evidence = evidence
        model_pre_head_roots.append(model_head)
        model_step_roots.append(evidence.verified_step.step.step_root)
        model_head = result.head_root  # type: ignore[assignment]
        model_state = result.state

        reopened = store.reopen()
        assert tuple(step.step_root for step in reopened.committed_steps) == tuple(
            model_step_roots
        )
        assert tuple(step.pre_head_root for step in reopened.committed_steps) == tuple(
            model_pre_head_roots
        )
        assert reopened.state == model_state
        assert reopened.head_root == model_head

    assert last_evidence is not None
    before_retry = _durable_snapshot(store, anchor)
    retry = store.admit(last_pre_state.state_root, last_evidence)
    assert retry.status is M6MigrationAdmissionStatusV1.ALREADY_COMMITTED
    assert _durable_snapshot(store, anchor) == before_retry

    stale_evidence = _verified(
        plan,
        M6MigrationStepKindV1.AUTHORITY_SWITCH,
        14,
        state=model_state,
    )
    before_stale = _durable_snapshot(store, anchor)
    stale = store.admit(last_pre_state.state_root, stale_evidence)
    assert stale.status is M6MigrationAdmissionStatusV1.STALE_STATE
    assert stale.reason == "expected migration state root is stale"
    assert _durable_snapshot(store, anchor) == before_stale

    resumed = store.admit(model_state.state_root, stale_evidence)
    assert resumed.status is M6MigrationAdmissionStatusV1.COMMITTED


def test_given_configured_anchor_when_foreign_anchor_is_supplied_then_admission_rejects_before_commit(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    trusted = M6MigrationExternalHeadAnchorV1(tmp_path / "trusted-anchor.json")
    store = _store(
        tmp_path,
        initial,
        require_external_anchor=True,
        external_anchor=trusted,
    )
    rogue = M6MigrationExternalHeadAnchorV1(tmp_path / "rogue-anchor.json")
    rogue.initialize(trusted.read())

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="configured external anchor",
    ):
        store.admit_with_external_anchor(
            initial.state_root,
            _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
            external_anchor=rogue,
        )

    assert trusted.read() == rogue.read()
    assert store.reopen().state == initial


def test_given_anchor_and_lost_install_response_when_step_was_installed_then_recovery_advances_anchor(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    anchor = M6MigrationExternalHeadAnchorV1(tmp_path / "external-anchor.json")
    store = _store(
        tmp_path,
        initial,
        require_external_anchor=True,
        external_anchor=anchor,
    )
    real_write_head = admission_module._write_head

    def write_then_report_indeterminate(
        path: Path,
        state: M6MigrationStateV1,
        committed_steps: tuple[object, ...],
    ) -> None:
        real_write_head(path, state, committed_steps)  # type: ignore[arg-type]
        raise M6MigrationDurableCorruptionError("simulated lost install response")

    monkeypatch.setattr(admission_module, "_write_head", write_then_report_indeterminate)

    result = store.admit_with_external_anchor(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        external_anchor=anchor,
    )

    assert result.status is M6MigrationAdmissionStatusV1.ALREADY_COMMITTED
    assert result.head_root is not None
    assert anchor.read() == result.head_root
    assert result.state.phase is M6MigrationPhaseV1.SHADOW_REPLAY


def test_given_anchor_when_unanchored_descendant_exists_then_ancestor_recovery_fails_closed(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    anchor = M6MigrationExternalHeadAnchorV1(tmp_path / "external-anchor.json")
    store = _store(
        tmp_path,
        initial,
        require_external_anchor=True,
        external_anchor=anchor,
    )
    genesis_head_root = anchor.read()

    first_evidence = _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11)
    first = store._admit_unanchored(  # type: ignore[attr-defined]
        initial.state_root,
        first_evidence,
        expected_head_root=genesis_head_root,
    )
    assert first.status is M6MigrationAdmissionStatusV1.COMMITTED
    second_evidence = _verified(
        plan,
        M6MigrationStepKindV1.DUAL_CHECK,
        12,
        state=first.state,
    )
    second = store._admit_unanchored(  # type: ignore[attr-defined]
        first.state.state_root,
        second_evidence,
        expected_head_root=first.head_root,
    )
    assert second.status is M6MigrationAdmissionStatusV1.COMMITTED

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="HEAD tail",
    ):
        store.admit_with_external_anchor(
            initial.state_root,
            first_evidence,
            external_anchor=anchor,
    )

    assert anchor.read() == genesis_head_root
    local_head = admission_module._read_head(  # type: ignore[attr-defined]
        tmp_path / "migration" / "HEAD.json",
        authority_verifier=_verifier(),
    )
    assert local_head.head_root == second.head_root
    assert local_head.state == second.state


def test_given_committed_history_when_fresh_process_reopens_offline_then_persisted_bls_receipts_are_reverified(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    committed = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    assert committed.status is M6MigrationAdmissionStatusV1.COMMITTED

    offline_verifier = M6MigrationAuthorityVerifierV1(
        None,
        signer_registry=_m6_test_registry(),
    )
    reopened = M6MigrationDurableStoreV1(
        tmp_path / "migration",
        authority_verifier=offline_verifier,
    ).reopen()

    assert reopened.state == committed.state
    assert len(reopened.committed_steps) == 1


def test_given_valid_older_head_when_external_anchor_is_newer_then_fresh_reopen_rejects_stale_generation(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    head_path = tmp_path / "migration" / "HEAD.json"
    genesis_bytes = head_path.read_bytes()
    committed = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    assert committed.status is M6MigrationAdmissionStatusV1.COMMITTED
    latest_head_root = store.reopen().head_root

    head_path.write_bytes(genesis_bytes)

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="stale relative to external anchor",
        ):
            M6MigrationDurableStoreV1(
                tmp_path / "migration",
                authority_verifier=_verifier(),
                expected_head_root=latest_head_root,
            )


def test_given_safe_anchor_profile_when_external_head_root_is_omitted_then_reopen_and_admit_fail_closed(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial, require_external_anchor=True)

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="external migration HEAD anchor is required",
    ):
        store.reopen()
    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="configured external anchor is required",
    ):
        store.admit(
            initial.state_root,
            _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        )

    caller_anchor = M6MigrationExternalHeadAnchorV1(tmp_path / "caller-anchor.json")
    caller_anchor.initialize(_root(77))
    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="configured external anchor is required",
    ):
        store.admit_with_external_anchor(
            initial.state_root,
            _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
            external_anchor=caller_anchor,
        )


def test_given_noncanonical_quorum_envelope_order_when_authenticated_then_verification_rejects(
) -> None:
    registry = _m6_two_signer_registry()
    plan = replace(_plan(), authority_registry_root=cast(str, registry["registry_hash"]))
    verifier = M6MigrationAuthorityVerifierV1(
        _NonCanonicalOrderMigrationBackend(registry),
        signer_registry=registry,
    )

    with pytest.raises(
        M6MigrationAuthorityProofRejectedV1,
        match="envelope order is not canonical",
    ):
        verifier.verify_step_with_receipt(
            plan,
            _step(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
            M6MigrationStateV1.initial(plan).branch_root,
            pre_state_root=M6MigrationStateV1.initial(plan).state_root,
            pre_phase=M6MigrationStateV1.initial(plan).phase,
        )


def test_given_migration_backend_exception_when_verifying_then_private_detail_is_not_disclosed(
) -> None:
    class RaisingMigrationBackend:
        def verify_m6_migration_step(
            self,
            _request: Mapping[str, object],
        ) -> Mapping[str, object]:
            raise RuntimeError("private migration-provider token")

    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationAuthorityVerifierV1(
        RaisingMigrationBackend(),
        signer_registry=_m6_test_registry(),
    )

    with pytest.raises(M6MigrationAuthorityProofRejectedV1) as caught:
        verifier.verify_step_with_receipt(
            plan,
            _step(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
            state.branch_root,
            pre_state_root=state.state_root,
            pre_phase=state.phase,
        )

    assert str(caught.value) == "migration authority backend failed"
    assert "token" not in str(caught.value)
    assert caught.value.__cause__ is None
    assert caught.value.__context__ is None


def test_given_typed_migration_backend_error_when_verifying_then_private_detail_is_not_disclosed(
) -> None:
    class RejectingMigrationBackend:
        def verify_m6_migration_step(
            self,
            _request: Mapping[str, object],
        ) -> Mapping[str, object]:
            raise M6MigrationAuthorityProofRejectedV1(
                "private migration-provider credential"
            )

    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationAuthorityVerifierV1(
        RejectingMigrationBackend(),
        signer_registry=_m6_test_registry(),
    )

    with pytest.raises(M6MigrationAuthorityProofRejectedV1) as caught:
        verifier.verify_step_with_receipt(
            plan,
            _step(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
            state.branch_root,
            pre_state_root=state.state_root,
            pre_phase=state.phase,
        )

    assert str(caught.value) == "migration authority backend rejected the request"
    assert "credential" not in str(caught.value)
    assert caught.value.__cause__ is None
    assert caught.value.__context__ is None


def test_given_changing_migration_receipt_when_verified_then_one_owned_observation_is_retained(
) -> None:
    backend = _ChangingReceiptBackend()
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationAuthorityVerifierV1(
        backend,
        signer_registry=_m6_test_registry(),
    )

    admission = verifier.verify_step_with_receipt(
        plan,
        _step(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        state.branch_root,
        pre_state_root=state.state_root,
        pre_phase=state.phase,
    )

    observed = backend.migration_mapping
    assert observed is not None
    assert observed.iterations == 1
    assert admission.receipt.receipt_root == observed.first["receipt_hash"]


def test_given_changing_nested_migration_proof_when_verified_then_receipt_rejects(
) -> None:
    backend = _ChangingReceiptBackend(nested=True)
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationAuthorityVerifierV1(
        backend,
        signer_registry=_m6_test_registry(),
    )

    with pytest.raises(
        M6MigrationAuthorityProofRejectedV1,
        match="receipt binding mismatch",
    ):
        verifier.verify_step_with_receipt(
            plan,
            _step(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
            state.branch_root,
            pre_state_root=state.state_root,
            pre_phase=state.phase,
        )

    observed = backend.migration_mapping
    assert observed is not None
    assert observed.iterations == 1


def test_given_authentic_receipt_from_foreign_registry_when_plan_registry_is_pinned_then_verification_rejects() -> None:
    plan = _plan()
    foreign = _foreign_registry()
    verifier = M6MigrationAuthorityVerifierV1(
        _StructuralMigrationBackend(registry=foreign),
        signer_registry=foreign,
    )

    with pytest.raises(
        M6MigrationAuthorityProofRejectedV1,
        match="different plan registry",
    ):
        verifier.verify_step_with_receipt(
            plan,
            _step(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
            M6MigrationStateV1.initial(plan).branch_root,
            pre_state_root=M6MigrationStateV1.initial(plan).state_root,
            pre_phase=M6MigrationStateV1.initial(plan).phase,
        )


def test_given_empty_head_when_reopen_uses_foreign_verifier_registry_then_it_fails_closed(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    _store(tmp_path, initial)
    foreign = _foreign_registry()
    foreign_verifier = M6MigrationAuthorityVerifierV1(
        _StructuralMigrationBackend(registry=foreign),
        signer_registry=foreign,
    )

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="not bound to the durable plan",
    ):
        M6MigrationDurableStoreV1(
            tmp_path / "migration",
            authority_verifier=foreign_verifier,
        ).reopen()


def test_given_committed_history_when_fresh_process_lacks_verifier_then_reopen_fails_closed(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    committed = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )

    assert committed.status is M6MigrationAdmissionStatusV1.COMMITTED
    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="authenticated migration verifier is required",
    ):
        M6MigrationDurableStoreV1(tmp_path / "migration")


def test_given_rehashed_public_receipt_when_signature_is_stale_then_reopen_rejects(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    committed = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    assert committed.status is M6MigrationAdmissionStatusV1.COMMITTED

    head_path = tmp_path / "migration" / "HEAD.json"
    raw = json.loads(head_path.read_text(encoding="utf-8"))
    receipt_record = raw["committed_steps"][0]["authority_receipt"]
    receipt = json.loads(receipt_record["canonical_json"])
    receipt["evidence_root"] = _root(99)
    receipt_body = {
        key: value for key, value in receipt.items() if key != "receipt_hash"
    }
    receipt["receipt_hash"] = hash_v1(
        "m6-migration-authority-receipt-v1", receipt_body
    )
    receipt_record["receipt_root"] = receipt["receipt_hash"]
    raw["committed_steps"][0]["receipt_root"] = receipt["receipt_hash"]
    receipt_record["canonical_json"] = canonical_bytes_v1(receipt).decode("utf-8")
    head_body = {
        key: raw[key]
        for key in ("schema", "state_root", "state", "committed_steps")
    }
    raw["head_root"] = hash_v1(M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V2, head_body)
    head_path.write_bytes(canonical_bytes_v1(raw))

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="migration authority receipt verification failed",
    ):
        store.reopen()


def test_given_lost_commit_response_when_identical_step_retries_then_admission_is_idempotent(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    verified = _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11)
    first = store.admit(initial.state_root, verified)

    retry = M6MigrationDurableStoreV1(
        tmp_path / "migration", authority_verifier=_verifier()
    ).admit(
        initial.state_root,
        verified,
    )

    assert first.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert retry.status is M6MigrationAdmissionStatusV1.ALREADY_COMMITTED
    assert retry.state == first.state
    assert len(store.reopen().committed_steps) == 1


def test_given_forward_descendant_when_ancestor_step_retries_then_active_branch_is_idempotent(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    shadow = _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11)
    first = store.admit(initial.state_root, shadow)
    assert first.status is M6MigrationAdmissionStatusV1.COMMITTED
    dual = store.admit(
        first.state.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.DUAL_CHECK,
            12,
            state=first.state,
        ),
    )
    retry = store.admit(initial.state_root, shadow)

    assert dual.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert retry.status is M6MigrationAdmissionStatusV1.ALREADY_COMMITTED
    assert retry.state == dual.state


def test_given_rollback_branch_when_old_step_retries_then_existing_branch_commit_is_rejected(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    shadow = _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11)
    first = store.admit(initial.state_root, shadow)
    assert first.status is M6MigrationAdmissionStatusV1.COMMITTED

    rollback = store.admit(
        first.state.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.ROLLBACK,
            17,
            state=first.state,
        ),
    )
    retry = store.admit(initial.state_root, shadow)

    assert rollback.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert rollback.state != initial
    assert rollback.state.branch_root != first.state.branch_root
    assert retry.status is M6MigrationAdmissionStatusV1.REJECTED
    assert retry.state == rollback.state
    assert retry.reason == "migration step is already committed on this branch"


def test_given_rollback_branch_when_step_is_reauthenticated_for_new_branch_then_it_can_commit(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    first = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    rollback = store.admit(
        first.state.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.ROLLBACK,
            17,
            state=first.state,
        ),
    )
    reauthenticated = _verifier().verify_step_with_receipt(
        plan,
        _step(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        rollback.state.branch_root,
        pre_state_root=rollback.state.state_root,
        pre_phase=rollback.state.phase,
    )

    retry = store.admit(rollback.state.state_root, reauthenticated)
    reopened = store.reopen()

    assert retry.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert retry.state.phase is M6MigrationPhaseV1.SHADOW_REPLAY
    assert len(reopened.committed_steps) == 3
    assert reopened.committed_steps[0].step_root == reopened.committed_steps[2].step_root
    assert reopened.committed_steps[0].branch_root != reopened.committed_steps[2].branch_root


def test_given_uncommitted_old_branch_witness_when_rollback_repeats_state_root_then_it_is_rejected(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    stale_witness = _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 99)
    first = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    assert first.status is M6MigrationAdmissionStatusV1.COMMITTED
    rollback = store.admit(
        first.state.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.ROLLBACK,
            17,
            state=first.state,
        ),
    )
    rejected = store.admit(rollback.state.state_root, stale_witness)

    assert rollback.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert rejected.status is M6MigrationAdmissionStatusV1.REJECTED
    assert rejected.reason == "migration verifier branch does not match the current state"
    assert store.reopen().state == rollback.state


def test_given_stale_expected_head_when_step_arrives_then_state_and_history_remain_unchanged(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    first = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    before = store.reopen()

    stale = store.admit(
        initial.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.DUAL_CHECK,
            12,
            state=first.state,
        ),
    )
    after = store.reopen()

    assert first.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert stale.status is M6MigrationAdmissionStatusV1.STALE_STATE
    assert after == before


def test_given_rollback_receipt_bound_to_shadow_when_consumed_at_dual_then_it_is_rejected(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    shadow = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    rollback_authorized_at_shadow = _verified(
        plan,
        M6MigrationStepKindV1.ROLLBACK,
        17,
        state=shadow.state,
    )
    dual = store.admit(
        shadow.state.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.DUAL_CHECK,
            12,
            state=shadow.state,
        ),
    )

    rejected = store.admit(dual.state.state_root, rollback_authorized_at_shadow)

    assert shadow.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert dual.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert rejected.status is M6MigrationAdmissionStatusV1.REJECTED
    assert rejected.reason is not None
    assert "migration authority receipt rejected" in rejected.reason
    assert store.reopen().state == dual.state


def test_given_authenticated_phase_invalid_step_when_admission_runs_then_core_reject_code_is_closed_and_state_is_unchanged(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)

    result = store.admit(
        initial.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.DUAL_CHECK,
            12,
            state=initial,
        ),
    )

    assert result.status is M6MigrationAdmissionStatusV1.REJECTED
    assert result.core_reject_code is M6MigrationRejectCodeV1.PHASE_MISMATCH
    assert result.pre_state_root == result.post_state_root == initial.state_root
    assert result.state == initial
    assert store.reopen().committed_steps == ()


def test_given_post_switch_failure_when_fail_stop_commits_then_reopen_quarantines_writers_and_rejects_progress(
    tmp_path: Path,
) -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, state)
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
    ):
        result = store.admit(
            state.state_root,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert result.status is M6MigrationAdmissionStatusV1.COMMITTED
        state = result.state

    failed = store.admit(
        state.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.POST_SWITCH_FAIL_STOP,
            99,
            state=state,
        ),
    )
    reopened = store.reopen()

    assert failed.status is M6MigrationAdmissionStatusV1.COMMITTED
    assert reopened.state.phase is M6MigrationPhaseV1.POST_SWITCH_FAILED
    assert reopened.state.legacy_writes_enabled is False
    assert reopened.state.target_writes_enabled is False
    assert authorize_m6_migration_writer_v1(
        reopened.state,
        writer_subject_root=plan.target_subject_root,
        writer_epoch=plan.target_writer_epoch,
        allowed_writer_set_root=plan.allowed_writer_set_root,
    ).status is M6MigrationWriterAdmissionStatusV1.REJECTED

    progress = store.admit(
        reopened.state.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.LEGACY_DISABLE,
            100,
            state=reopened.state,
        ),
    )
    assert progress.status is M6MigrationAdmissionStatusV1.REJECTED
    assert progress.core_reject_code is M6MigrationRejectCodeV1.PHASE_MISMATCH
    assert store.reopen().state == reopened.state


def test_given_raw_step_when_admission_runs_then_no_authority_is_created(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)

    rejected = store.admit(
        initial.state_root,
        _step(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )

    assert rejected.status is M6MigrationAdmissionStatusV1.REJECTED
    assert store.reopen().state == initial
    assert store.reopen().committed_steps == ()


def test_given_noncanonical_head_when_reopen_runs_then_fixed_point_check_rejects(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    head_path = tmp_path / "migration" / "HEAD.json"
    raw = json.loads(head_path.read_text(encoding="utf-8"))
    replay_root = raw["state"]["replay_root"]
    raw["state"]["replay_root"] = f" {replay_root}"
    body = {
        key: raw[key]
        for key in ("schema", "state_root", "state", "committed_steps")
    }
    raw["head_root"] = hash_v1(M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V2, body)
    head_path.write_bytes(canonical_bytes_v1(raw))

    with pytest.raises(M6MigrationDurableCorruptionError, match="canonical"):
        store.reopen()


def test_given_prechange_v1_state_layout_when_reopen_runs_then_explicit_state_migration_is_required(
    tmp_path: Path,
) -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    raw_state = state.to_canonical()
    raw_state["schema"] = "zenodex/m6-migration-state/v1"
    raw_state.pop("post_switch_failure_root")

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="schema v1 is obsolete",
    ):
        _decode_state(raw_state)


def test_given_prechange_v1_admission_head_when_reopen_runs_then_explicit_admission_migration_is_required(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    head_path = tmp_path / "migration" / "HEAD.json"
    raw = json.loads(head_path.read_text(encoding="utf-8"))
    raw["schema"] = "zenodex/m6-migration-admission/v1"
    body = {
        key: raw[key]
        for key in ("schema", "state_root", "state", "committed_steps")
    }
    raw["head_root"] = hash_v1(M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V1, body)
    head_path.write_bytes(canonical_bytes_v1(raw))

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="admission schema v1 is obsolete",
    ):
        store.reopen()


def test_given_rehashed_but_semantically_tampered_history_when_reopen_runs_then_replay_rejects(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    committed = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    assert committed.status is M6MigrationAdmissionStatusV1.COMMITTED
    head_path = tmp_path / "migration" / "HEAD.json"
    raw = json.loads(head_path.read_text(encoding="utf-8"))
    raw["committed_steps"][0]["post_state_root"] = _root(99)
    body = {
        key: raw[key]
        for key in ("schema", "state_root", "state", "committed_steps")
    }
    raw["head_root"] = hash_v1(M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V2, body)
    head_path.write_bytes(canonical_bytes_v1(raw))

    with pytest.raises(M6MigrationDurableCorruptionError, match="post-state mismatch"):
        store.reopen()


def test_given_two_step_history_when_pre_head_root_is_rehashed_then_replay_rejects(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    first = store.admit(
        initial.state_root,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )
    assert first.status is M6MigrationAdmissionStatusV1.COMMITTED
    second = store.admit(
        first.state.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.DUAL_CHECK,
            12,
            state=first.state,
        ),
    )
    assert second.status is M6MigrationAdmissionStatusV1.COMMITTED
    head_path = tmp_path / "migration" / "HEAD.json"
    raw = json.loads(head_path.read_text(encoding="utf-8"))
    raw["committed_steps"][1]["pre_head_root"] = _root(99)
    body = {
        key: raw[key]
        for key in ("schema", "state_root", "state", "committed_steps")
    }
    raw["head_root"] = hash_v1(M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V2, body)
    head_path.write_bytes(canonical_bytes_v1(raw))

    with pytest.raises(
        M6MigrationDurableCorruptionError,
        match="pre-HEAD history is not chained",
    ):
        store.reopen()


def test_given_zero_expected_root_when_admission_runs_then_state_is_unchanged(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)

    rejected = store.admit(
        ZERO_ROOT_V1,
        _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11),
    )

    assert rejected.status is M6MigrationAdmissionStatusV1.REJECTED
    assert store.reopen().state == initial


def test_given_terminal_switch_when_writer_is_checked_then_legacy_is_permanently_denied(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    state = initial
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
        (M6MigrationStepKindV1.POST_SWITCH_VALIDATION, 15),
        (M6MigrationStepKindV1.LEGACY_DISABLE, 16),
    ):
        result = store.admit(
            state.state_root,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert result.status is M6MigrationAdmissionStatusV1.COMMITTED
        state = result.state

    legacy = authorize_m6_migration_writer_v1(
        state,
        writer_subject_root=plan.source_subject_root,
        writer_epoch=plan.source_writer_epoch,
        allowed_writer_set_root=plan.allowed_writer_set_root,
    )
    target = authorize_m6_migration_writer_v1(
        state,
        writer_subject_root=plan.target_subject_root,
        writer_epoch=plan.target_writer_epoch,
        allowed_writer_set_root=plan.allowed_writer_set_root,
        membership_verifier=_writer_membership_verifier(),
        membership_proof=_writer_membership_proof(plan),
    )

    assert legacy.status is M6MigrationWriterAdmissionStatusV1.REJECTED
    assert target.status is M6MigrationWriterAdmissionStatusV1.ALLOWED
    assert target.membership_receipt_root is not None
    assert target.authorization is not None
    assert target.authorization.state_root == state.state_root


def test_given_active_profile_match_without_membership_receipt_then_writer_is_rejected(
    tmp_path: Path,
) -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, state)
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
        (M6MigrationStepKindV1.POST_SWITCH_VALIDATION, 15),
        (M6MigrationStepKindV1.LEGACY_DISABLE, 16),
    ):
        result = store.admit(
            state.state_root,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert result.status is M6MigrationAdmissionStatusV1.COMMITTED
        state = result.state

    denied = authorize_m6_migration_writer_v1(
        state,
        writer_subject_root=plan.target_subject_root,
        writer_epoch=plan.target_writer_epoch,
        allowed_writer_set_root=plan.allowed_writer_set_root,
    )

    assert denied.status is M6MigrationWriterAdmissionStatusV1.REJECTED
    assert denied.reason == "authenticated writer membership proof is required"


def test_given_stale_writer_authorization_when_consumer_runs_then_no_migration_commit_occurs(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    state = initial
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
    ):
        result = store.admit(
            state.state_root,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert result.status is M6MigrationAdmissionStatusV1.COMMITTED
        state = result.state

    stale = authorize_m6_migration_writer_v1(
        state,
        writer_subject_root=plan.target_subject_root,
        writer_epoch=plan.target_writer_epoch,
        allowed_writer_set_root=plan.allowed_writer_set_root,
        membership_verifier=_writer_membership_verifier(),
        membership_proof=_writer_membership_proof(plan),
    )
    assert stale.status is M6MigrationWriterAdmissionStatusV1.ALLOWED

    advanced = store.admit(
        state.state_root,
        _verified(
            plan,
            M6MigrationStepKindV1.POST_SWITCH_VALIDATION,
            15,
            state=state,
        ),
    )
    assert advanced.status is M6MigrationAdmissionStatusV1.COMMITTED

    consumer = M6MigrationWriterConsumerV1(store, _writer_membership_verifier())
    result = consumer.admit_from_authorization(
        stale,
        membership_proof=_writer_membership_proof(plan),
        expected_state_root=advanced.state.state_root,
        verified_step=_verified(
            plan,
            M6MigrationStepKindV1.LEGACY_DISABLE,
            16,
            state=advanced.state,
        ),
    )

    assert result.writer_admission.status is M6MigrationWriterAdmissionStatusV1.REJECTED
    assert result.writer_admission.reason == "writer authorization is stale"
    assert result.migration_admission is None
    assert store.reopen().state == advanced.state

    root_mismatch = consumer.admit(
        writer_subject_root=plan.target_subject_root,
        writer_epoch=plan.target_writer_epoch,
        membership_proof=_writer_membership_proof(plan),
        expected_state_root=state.state_root,
        verified_step=_verified(
            plan,
            M6MigrationStepKindV1.LEGACY_DISABLE,
            16,
            state=advanced.state,
        ),
    )
    assert root_mismatch.writer_admission.status is M6MigrationWriterAdmissionStatusV1.REJECTED
    assert root_mismatch.writer_admission.reason == "writer authorization is stale at commit root"
    assert root_mismatch.migration_admission is None
    assert store.reopen().state == advanced.state


def test_given_directly_constructed_writer_authorization_when_consumer_rechecks_then_it_is_rejected(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    state = initial
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
        (M6MigrationStepKindV1.POST_SWITCH_VALIDATION, 15),
    ):
        result = store.admit(
            state.state_root,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert result.status is M6MigrationAdmissionStatusV1.COMMITTED
        state = result.state

    forged_authorization = M6MigrationWriterAuthorizationV1(
        admission_module._M6_MIGRATION_WRITER_AUTHORIZATION_TOKEN,  # type: ignore[attr-defined]
        plan_root=plan.plan_root,
        state_root=state.state_root,
        active_subject_root=state.active_subject_root,
        active_writer_epoch=state.active_writer_epoch,
        allowed_writer_set_root=plan.allowed_writer_set_root,
        membership_receipt_root=_root(99),
    )
    forged = M6MigrationWriterAdmissionResultV1(
        M6MigrationWriterAdmissionStatusV1.ALLOWED,
        state.active_subject_root,
        state.active_writer_epoch,
        membership_receipt_root=_root(99),
        authorization=forged_authorization,
    )
    consumer = M6MigrationWriterConsumerV1(store, _writer_membership_verifier())
    result = consumer.admit_from_authorization(
        forged,
        membership_proof=_writer_membership_proof(plan),
        expected_state_root=state.state_root,
        verified_step=_verified(
            plan,
            M6MigrationStepKindV1.LEGACY_DISABLE,
            16,
            state=state,
        ),
    )

    assert result.writer_admission.status is M6MigrationWriterAdmissionStatusV1.REJECTED
    assert result.writer_admission.reason == "writer authorization is not verifier-derived"
    assert result.migration_admission is None
    assert store.reopen().state == state


def test_given_membership_proof_with_non_string_key_when_snapshot_is_created_then_it_is_rejected() -> None:
    with pytest.raises(TypeError, match="mapping keys must be strings"):
        M6MigrationWriterMembershipProofV1.from_mapping({1: "member"})


def test_given_membership_proof_when_caller_mutates_input_then_owned_snapshot_is_stable() -> None:
    raw_proof = {"path": {"leaf": "member"}}
    proof = M6MigrationWriterMembershipProofV1.from_mapping(raw_proof)
    raw_proof["path"]["leaf"] = "tampered"

    assert proof.to_mapping() == {"path": {"leaf": "member"}}


def test_given_cyclic_membership_proof_when_snapshot_is_created_then_it_is_rejected() -> None:
    cyclic_proof: dict[str, object] = {}
    cyclic_proof["self"] = cyclic_proof

    with pytest.raises(ValueError, match="contains a cycle"):
        M6MigrationWriterMembershipProofV1.from_mapping(cyclic_proof)


def test_given_membership_proof_above_item_bound_when_snapshot_is_created_then_it_is_rejected() -> None:
    oversized_proof = {
        f"item-{index}": True
        for index in range(M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_ITEMS_V1 + 1)
    }

    with pytest.raises(ValueError, match="item limit"):
        M6MigrationWriterMembershipProofV1.from_mapping(oversized_proof)


def test_given_membership_proof_at_item_bound_when_snapshot_is_created_then_it_is_accepted() -> None:
    exact_proof = {
        f"item-{index}": True
        for index in range(M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_ITEMS_V1)
    }

    snapshot = M6MigrationWriterMembershipProofV1.from_mapping(exact_proof)

    assert len(snapshot.to_mapping()) == M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_ITEMS_V1


def test_given_membership_proof_at_size_bound_when_snapshot_is_created_then_it_is_accepted() -> None:
    empty_size = len(canonical_bytes_v1({"blob": ""}))
    exact_proof = {
        "blob": "x" * (M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_BYTES_V1 - empty_size)
    }
    encoded = canonical_bytes_v1(exact_proof)

    assert len(encoded) == M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_BYTES_V1
    snapshot = M6MigrationWriterMembershipProofV1.from_mapping(exact_proof)
    assert len(snapshot.canonical_json) == M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_BYTES_V1


def test_given_membership_proof_above_size_bound_when_snapshot_is_created_then_it_is_rejected() -> None:
    empty_size = len(canonical_bytes_v1({"blob": ""}))
    oversized_proof = {
        "blob": "x"
        * (M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_BYTES_V1 - empty_size + 1)
    }

    with pytest.raises(ValueError, match="size limit"):
        M6MigrationWriterMembershipProofV1.from_mapping(oversized_proof)


def test_given_membership_proof_at_depth_bound_when_snapshot_is_created_then_it_is_accepted() -> None:
    value: object = True
    for _ in range(M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_DEPTH_V1):
        value = {"x": value}

    snapshot = M6MigrationWriterMembershipProofV1.from_mapping({"proof": value})

    assert snapshot.to_mapping()["proof"] is not None


def test_given_membership_proof_above_depth_bound_when_snapshot_is_created_then_it_is_rejected() -> None:
    value: object = True
    for _ in range(M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_DEPTH_V1 + 1):
        value = {"x": value}

    with pytest.raises(ValueError, match="nesting limit"):
        M6MigrationWriterMembershipProofV1.from_mapping({"proof": value})


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("plan_root", _root(91)),
        ("authority_registry_root", _root(92)),
        ("writer_subject_root", _root(93)),
        ("writer_epoch", 999),
        ("state_root", _root(94)),
        ("phase", M6MigrationPhaseV1.SHADOW_REPLAY.value),
        ("branch_root", _root(95)),
        ("membership_proof_root", _root(96)),
    ),
)
def test_given_membership_receipt_with_one_coordinate_substituted_then_verifier_rejects(
    field: str,
    value: object,
) -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationWriterMembershipVerifierV1(
        _ReceiptMutationMembershipBackend(
            mutation_field=field,
            mutation_value=value,
        ),
        signer_registry=_m6_test_registry(),
    )

    with pytest.raises(
        M6MigrationAuthorityProofRejectedV1,
        match="receipt binding mismatch",
    ):
        verifier.verify_writer_membership(
            state,
            writer_subject_root=plan.source_subject_root,
            writer_epoch=plan.source_writer_epoch,
            membership_proof={"member": True},
        )


def test_given_membership_receipt_with_mutated_signed_payload_then_verifier_rejects() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationWriterMembershipVerifierV1(
        _SignedPayloadMutationMembershipBackend(),
        signer_registry=_m6_test_registry(),
    )

    with pytest.raises(
        M6MigrationAuthorityProofRejectedV1,
        match="payload binding mismatch",
    ):
        verifier.verify_writer_membership(
            state,
            writer_subject_root=plan.source_subject_root,
            writer_epoch=plan.source_writer_epoch,
            membership_proof={"member": True},
        )


def test_given_membership_backend_exception_when_verifying_then_private_detail_is_not_disclosed(
) -> None:
    class RaisingMembershipBackend:
        def verify_m6_migration_writer_membership(
            self,
            _request: Mapping[str, object],
        ) -> Mapping[str, object]:
            raise RuntimeError("private writer-provider credential")

    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationWriterMembershipVerifierV1(
        RaisingMembershipBackend(),
        signer_registry=_m6_test_registry(),
    )

    with pytest.raises(M6MigrationAuthorityProofRejectedV1) as caught:
        verifier.verify_writer_membership(
            state,
            writer_subject_root=plan.source_subject_root,
            writer_epoch=plan.source_writer_epoch,
            membership_proof={"member": True},
        )

    assert str(caught.value) == "migration writer membership backend failed"
    assert "credential" not in str(caught.value)
    assert caught.value.__cause__ is None
    assert caught.value.__context__ is None


def test_given_typed_membership_backend_error_when_verifying_then_private_detail_is_not_disclosed(
) -> None:
    class RejectingMembershipBackend:
        def verify_m6_migration_writer_membership(
            self,
            _request: Mapping[str, object],
        ) -> Mapping[str, object]:
            raise M6MigrationAuthorityProofRejectedV1(
                "private writer-provider credential"
            )

    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationWriterMembershipVerifierV1(
        RejectingMembershipBackend(),
        signer_registry=_m6_test_registry(),
    )

    with pytest.raises(M6MigrationAuthorityProofRejectedV1) as caught:
        verifier.verify_writer_membership(
            state,
            writer_subject_root=plan.source_subject_root,
            writer_epoch=plan.source_writer_epoch,
            membership_proof={"member": True},
        )

    assert (
        str(caught.value)
        == "migration writer membership backend rejected the request"
    )
    assert "credential" not in str(caught.value)
    assert caught.value.__cause__ is None
    assert caught.value.__context__ is None


def test_given_changing_membership_receipt_when_verified_then_one_owned_observation_is_retained(
) -> None:
    backend = _ChangingReceiptBackend()
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationWriterMembershipVerifierV1(
        backend,
        signer_registry=_m6_test_registry(),
    )

    receipt = verifier.verify_writer_membership(
        state,
        writer_subject_root=plan.source_subject_root,
        writer_epoch=plan.source_writer_epoch,
        membership_proof={"member": True},
    )

    observed = backend.membership_mapping
    assert observed is not None
    assert observed.iterations == 1
    assert receipt.receipt_root == observed.first["receipt_hash"]


def test_given_changing_nested_membership_proof_when_verified_then_receipt_rejects(
) -> None:
    backend = _ChangingReceiptBackend(nested=True)
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    verifier = M6MigrationWriterMembershipVerifierV1(
        backend,
        signer_registry=_m6_test_registry(),
    )

    with pytest.raises(
        M6MigrationAuthorityProofRejectedV1,
        match="receipt binding mismatch",
    ):
        verifier.verify_writer_membership(
            state,
            writer_subject_root=plan.source_subject_root,
            writer_epoch=plan.source_writer_epoch,
            membership_proof={"member": True},
        )

    observed = backend.membership_mapping
    assert observed is not None
    assert observed.iterations == 1


def test_given_duck_typed_membership_verifier_when_writer_is_authorized_then_it_is_rejected() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)

    class DuckVerifier:
        authenticated = True

        def verify_writer_membership(self, *args: object, **kwargs: object) -> object:
            raise AssertionError("duck verifier must not be called")

    denied = authorize_m6_migration_writer_v1(
        state,
        writer_subject_root=plan.source_subject_root,
        writer_epoch=plan.source_writer_epoch,
        allowed_writer_set_root=plan.allowed_writer_set_root,
        membership_verifier=DuckVerifier(),  # type: ignore[arg-type]
        membership_proof={"member": True},
    )

    assert denied.status is M6MigrationWriterAdmissionStatusV1.REJECTED
    assert denied.reason == "authenticated writer membership proof is required"


def test_given_allowed_writer_result_without_receipt_when_constructed_then_it_is_rejected() -> None:
    plan = _plan()

    with pytest.raises(ValueError, match="requires a membership receipt"):
        M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.ALLOWED,
            plan.source_subject_root,
            plan.source_writer_epoch,
        )


def test_given_allowed_writer_result_with_unverified_receipt_when_constructed_then_it_is_rejected() -> None:
    plan = _plan()

    with pytest.raises(ValueError, match="verifier-created authorization"):
        M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.ALLOWED,
            plan.source_subject_root,
            plan.source_writer_epoch,
            membership_receipt_root=_root(99),
        )


def test_given_committed_result_without_step_identity_when_constructed_then_it_is_rejected() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)

    with pytest.raises(ValueError, match="requires a step root"):
        M6MigrationAdmissionResultV1(
            M6MigrationAdmissionStatusV1.COMMITTED,
            state,
            state.state_root,
            state.state_root,
            head_root=_root(99),
        )


def test_given_terminal_switch_when_writer_set_root_is_wrong_then_writer_is_denied(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    store = _store(tmp_path, initial)
    state = initial
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
        (M6MigrationStepKindV1.POST_SWITCH_VALIDATION, 15),
        (M6MigrationStepKindV1.LEGACY_DISABLE, 16),
    ):
        result = store.admit(
            state.state_root,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert result.status is M6MigrationAdmissionStatusV1.COMMITTED
        state = result.state

    denied = authorize_m6_migration_writer_v1(
        state,
        writer_subject_root=plan.target_subject_root,
        writer_epoch=plan.target_writer_epoch,
        allowed_writer_set_root=_root(99),
    )

    assert denied.status is M6MigrationWriterAdmissionStatusV1.REJECTED


def test_given_symlinked_lock_when_store_initializes_then_open_is_rejected(
    tmp_path: Path,
) -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    root = tmp_path / "migration"
    root.mkdir()
    (root / ".m6-migration.lock").symlink_to(tmp_path / "outside.lock")

    with pytest.raises(M6MigrationDurableCorruptionError, match="lock"):
        M6MigrationDurableStoreV1(root, initial_state=initial, authority_verifier=_verifier())
