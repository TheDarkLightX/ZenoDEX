from __future__ import annotations

from dataclasses import dataclass, replace
from types import MappingProxyType
from typing import Mapping, cast

import pytest

import src.core.m6_migration_lifecycle_v1 as m6_lifecycle
from src.core.m6_migration_lifecycle_v1 import (
    M6_MIGRATION_LIFECYCLE_SCHEMA_V1,
    M6_MIGRATION_MAX_WRITER_EPOCH_V1,
    M6MigrationAcceptedV1,
    M6MigrationPhaseV1,
    M6MigrationPlanV1,
    M6MigrationRejectCodeV1,
    M6MigrationRejectedV1,
    M6MigrationStateV1,
    M6MigrationStepKindV1,
    M6MigrationStepV1,
    M6MigrationStructuralReplayV1,
    step_m6_migration_replay_v1,
    step_m6_migration_v1,
)
from src.core.m6_safe_mount_types_v1 import hash_v1
from src.integration.m6_migration_authority_v1 import (
    M6_MIGRATION_AUTHORITY_REQUEST_SCHEMA_V1,
    M6MigrationAuthorityVerifierV1,
)
from src.state.canonical import canonical_hex_fixed_allow_0x


def _root(number: int) -> str:
    return canonical_hex_fixed_allow_0x(f"0x{number:064x}", nbytes=32, name="test root")


@dataclass
class _StructuralMigrationBackend:
    calls: list[Mapping[str, object]]
    reject: bool = False

    def verify_m6_migration_step(self, request: Mapping[str, object]) -> Mapping[str, object]:
        self.calls.append(request)
        if self.reject:
            return {"ok": False}
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
        return {
            **body,
            "receipt_hash": hash_v1("m6-migration-authority-receipt-v1", body),
        }


def _plan() -> M6MigrationPlanV1:
    return M6MigrationPlanV1(
        source_subject_root=_root(1),
        target_subject_root=_root(2),
        source_state_root=_root(3),
        target_state_root=_root(4),
        source_writer_epoch=7,
        target_writer_epoch=8,
        allowed_writer_set_root=_root(5),
        authority_registry_root=_root(6),
        rollback_state_root=_root(3),
    )


def _step(
    plan: M6MigrationPlanV1,
    kind: M6MigrationStepKindV1,
    evidence_number: int,
    *,
    rollback: bool = False,
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
        rollback=rollback,
    )


def _verified(
    plan: M6MigrationPlanV1,
    kind: M6MigrationStepKindV1,
    evidence_number: int,
    *,
    rollback: bool = False,
    backend: _StructuralMigrationBackend | None = None,
    state: M6MigrationStateV1 | None = None,
) -> M6MigrationStructuralReplayV1:
    active_backend = backend or _StructuralMigrationBackend([])
    active_state = state or M6MigrationStateV1.initial(plan)
    step = _step(plan, kind, evidence_number, rollback=rollback)
    return cast(
        M6MigrationStructuralReplayV1,
        M6MigrationAuthorityVerifierV1(active_backend).verify_step(
            plan,
            step,
            active_state.branch_root,
            pre_state_root=active_state.state_root,
            pre_phase=active_state.phase,
        ),
    )


def test_given_legacy_when_seven_structural_replay_steps_arrive_then_lifecycle_reaches_legacy_disabled() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    sequence = (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
        (M6MigrationStepKindV1.POST_SWITCH_VALIDATION, 15),
        (M6MigrationStepKindV1.LEGACY_DISABLE, 16),
    )

    for kind, evidence_number in sequence:
        result = step_m6_migration_replay_v1(
            state,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert isinstance(result, M6MigrationAcceptedV1)
        state = result.post_state

    assert state.phase is M6MigrationPhaseV1.LEGACY_DISABLED
    assert state.active_subject_root == plan.target_subject_root
    assert state.active_state_root == plan.target_state_root
    assert state.active_writer_epoch == plan.target_writer_epoch
    assert state.legacy_writes_enabled is False
    assert state.target_writes_enabled is True


def test_given_authority_request_when_backend_receives_it_then_request_and_receipt_schemas_stay_distinct() -> None:
    plan = _plan()
    backend = _StructuralMigrationBackend([])

    _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11, backend=backend)

    assert backend.calls[0]["schema"] == M6_MIGRATION_AUTHORITY_REQUEST_SCHEMA_V1
    assert backend.calls[0]["receipt_schema"] == M6_MIGRATION_LIFECYCLE_SCHEMA_V1


def test_given_raw_caller_step_when_submitted_then_core_rejects_non_verified_authority() -> None:
    plan = _plan()
    raw = _step(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11)

    with pytest.raises(TypeError, match="authenticated"):
        step_m6_migration_v1(M6MigrationStateV1.initial(plan), raw)  # type: ignore[arg-type]


def test_given_structural_replay_witness_when_authoritative_core_runs_then_it_is_rejected() -> None:
    plan = _plan()
    witness = _verified(plan, M6MigrationStepKindV1.SHADOW_REPLAY, 11)

    with pytest.raises(TypeError, match="authenticated"):
        step_m6_migration_v1(
            M6MigrationStateV1.initial(plan),
            witness,  # type: ignore[arg-type]
        )


def test_given_legacy_when_dual_check_skips_shadow_then_reject_is_noop() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    result = step_m6_migration_replay_v1(
        state,
        _verified(plan, M6MigrationStepKindV1.DUAL_CHECK, 12),
    )

    assert isinstance(result, M6MigrationRejectedV1)
    assert result.code is M6MigrationRejectCodeV1.PHASE_MISMATCH
    assert result.pre_state_root == state.state_root
    assert result.post_state_root == state.state_root


def test_given_legacy_when_future_phase_evidence_is_present_then_state_construction_rejects() -> None:
    plan = _plan()

    with pytest.raises(ValueError, match="future evidence"):
        replace(M6MigrationStateV1.initial(plan), replay_root=_root(11))


def test_given_two_future_evidence_roots_then_rejection_precedence_is_stable() -> None:
    plan = _plan()

    with pytest.raises(ValueError, match="future evidence replay_root"):
        replace(
            M6MigrationStateV1.initial(plan),
            replay_root=_root(11),
            dual_check_root=_root(12),
        )


def test_given_distinct_rollback_root_then_v1_plan_construction_rejects() -> None:
    with pytest.raises(ValueError, match="rollback state root"):
        M6MigrationPlanV1(
            source_subject_root=_root(1),
            target_subject_root=_root(2),
            source_state_root=_root(3),
            target_state_root=_root(4),
            source_writer_epoch=7,
            target_writer_epoch=8,
            allowed_writer_set_root=_root(5),
            authority_registry_root=_root(6),
            rollback_state_root=_root(6),
        )


def test_given_writer_epoch_boundary_then_u64_max_is_valid_and_overflow_is_rejected() -> None:
    at_max = replace(
        _plan(),
        source_writer_epoch=M6_MIGRATION_MAX_WRITER_EPOCH_V1 - 1,
        target_writer_epoch=M6_MIGRATION_MAX_WRITER_EPOCH_V1,
    )
    assert at_max.target_writer_epoch == M6_MIGRATION_MAX_WRITER_EPOCH_V1

    with pytest.raises(ValueError, match="u64 writer epoch bound"):
        replace(
            _plan(),
            source_writer_epoch=M6_MIGRATION_MAX_WRITER_EPOCH_V1,
            target_writer_epoch=M6_MIGRATION_MAX_WRITER_EPOCH_V1 + 1,
        )


def test_given_replay_witness_authorized_for_one_state_then_later_consumption_is_a_noop() -> None:
    plan = _plan()
    initial = M6MigrationStateV1.initial(plan)
    witness = _verified(
        plan,
        M6MigrationStepKindV1.SHADOW_REPLAY,
        11,
        state=initial,
    )
    accepted = step_m6_migration_replay_v1(initial, witness)
    assert isinstance(accepted, M6MigrationAcceptedV1)

    replayed_again = step_m6_migration_replay_v1(accepted.post_state, witness)

    assert isinstance(replayed_again, M6MigrationRejectedV1)
    assert replayed_again.code is M6MigrationRejectCodeV1.CONTEXT_BINDING_MISMATCH
    assert replayed_again.pre_state_root == accepted.post_state.state_root
    assert replayed_again.post_state_root == accepted.post_state.state_root


def test_given_crossed_plan_binding_when_verified_step_arrives_then_reject_is_noop() -> None:
    plan = _plan()
    crossed = M6MigrationStepV1(
        kind=M6MigrationStepKindV1.SHADOW_REPLAY,
        source_subject_root=plan.source_subject_root,
        target_subject_root=_root(99),
        source_state_root=plan.source_state_root,
        target_state_root=plan.target_state_root,
        source_writer_epoch=plan.source_writer_epoch,
        target_writer_epoch=plan.target_writer_epoch,
        allowed_writer_set_root=plan.allowed_writer_set_root,
        rollback_state_root=plan.rollback_state_root,
        evidence_root=_root(11),
        rollback=False,
    )
    verified = cast(
        M6MigrationStructuralReplayV1,
        M6MigrationAuthorityVerifierV1(_StructuralMigrationBackend([])).verify_step(
            plan,
            crossed,
            M6MigrationStateV1.initial(plan).branch_root,
            pre_state_root=M6MigrationStateV1.initial(plan).state_root,
            pre_phase=M6MigrationStateV1.initial(plan).phase,
        ),
    )
    state = M6MigrationStateV1.initial(plan)

    result = step_m6_migration_replay_v1(state, verified)

    assert isinstance(result, M6MigrationRejectedV1)
    assert result.code is M6MigrationRejectCodeV1.PLAN_BINDING_MISMATCH
    assert result.pre_state_root == state.state_root
    assert result.post_state_root == state.state_root


def test_given_quiesced_when_rollback_arrives_then_source_authority_is_restored() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
    ):
        accepted = step_m6_migration_replay_v1(
            state,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert isinstance(accepted, M6MigrationAcceptedV1)
        state = accepted.post_state

    result = step_m6_migration_replay_v1(
        state,
        _verified(
            plan,
            M6MigrationStepKindV1.ROLLBACK,
            17,
            rollback=True,
            state=state,
        ),
    )

    assert isinstance(result, M6MigrationAcceptedV1)
    assert result.post_state.phase is M6MigrationPhaseV1.LEGACY
    assert result.post_state.active_subject_root == plan.source_subject_root
    assert result.post_state.active_state_root == plan.source_state_root
    assert result.post_state.active_writer_epoch == plan.source_writer_epoch
    assert result.post_state.legacy_writes_enabled is True
    assert result.post_state.target_writes_enabled is False
    assert result.post_state != M6MigrationStateV1.initial(plan)
    assert result.post_state.branch_root != state.branch_root


def test_given_legacy_disabled_when_rollback_arrives_then_old_writer_cannot_return() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
        (M6MigrationStepKindV1.POST_SWITCH_VALIDATION, 15),
        (M6MigrationStepKindV1.LEGACY_DISABLE, 16),
    ):
        accepted = step_m6_migration_replay_v1(
            state,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert isinstance(accepted, M6MigrationAcceptedV1)
        state = accepted.post_state

    result = step_m6_migration_replay_v1(
        state,
        _verified(
            plan,
            M6MigrationStepKindV1.ROLLBACK,
            17,
            rollback=True,
            state=state,
        ),
    )

    assert isinstance(result, M6MigrationRejectedV1)
    assert result.code is M6MigrationRejectCodeV1.LEGACY_ALREADY_DISABLED
    assert result.pre_state_root == state.state_root


def test_given_target_authority_switched_when_rollback_arrives_then_recovery_is_forbidden() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
    ):
        accepted = step_m6_migration_replay_v1(
            state,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert isinstance(accepted, M6MigrationAcceptedV1)
        state = accepted.post_state

    result = step_m6_migration_replay_v1(
        state,
        _verified(
            plan,
            M6MigrationStepKindV1.ROLLBACK,
            17,
            rollback=True,
            state=state,
        ),
    )

    assert isinstance(result, M6MigrationRejectedV1)
    assert result.code is M6MigrationRejectCodeV1.ROLLBACK_FORBIDDEN
    assert result.pre_state_root == result.post_state_root == state.state_root


def test_given_authority_switch_when_post_switch_validation_fails_then_fail_stop_disables_all_writers() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
    ):
        accepted = step_m6_migration_replay_v1(
            state,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert isinstance(accepted, M6MigrationAcceptedV1)
        state = accepted.post_state

    failed = step_m6_migration_replay_v1(
        state,
        _verified(
            plan,
            M6MigrationStepKindV1.POST_SWITCH_FAIL_STOP,
            99,
            state=state,
        ),
    )

    assert isinstance(failed, M6MigrationAcceptedV1)
    assert failed.post_state.phase is M6MigrationPhaseV1.POST_SWITCH_FAILED
    assert failed.post_state.post_switch_failure_root == _root(99)
    assert failed.post_state.legacy_writes_enabled is False
    assert failed.post_state.target_writes_enabled is False

    terminal_retry = step_m6_migration_replay_v1(
        failed.post_state,
        _verified(
            plan,
            M6MigrationStepKindV1.LEGACY_DISABLE,
            100,
            state=failed.post_state,
        ),
    )
    assert isinstance(terminal_retry, M6MigrationRejectedV1)
    assert terminal_retry.code is M6MigrationRejectCodeV1.PHASE_MISMATCH
    assert terminal_retry.pre_state_root == terminal_retry.post_state_root

    rollback_retry = step_m6_migration_replay_v1(
        failed.post_state,
        _verified(
            plan,
            M6MigrationStepKindV1.ROLLBACK,
            101,
            rollback=True,
            state=failed.post_state,
        ),
    )
    assert isinstance(rollback_retry, M6MigrationRejectedV1)
    assert rollback_retry.code is M6MigrationRejectCodeV1.ROLLBACK_FORBIDDEN
    assert rollback_retry.pre_state_root == rollback_retry.post_state_root


def test_given_post_switch_validation_when_fail_stop_arrives_then_quarantine_preserves_validation() -> None:
    plan = _plan()
    state = M6MigrationStateV1.initial(plan)
    for kind, evidence_number in (
        (M6MigrationStepKindV1.SHADOW_REPLAY, 11),
        (M6MigrationStepKindV1.DUAL_CHECK, 12),
        (M6MigrationStepKindV1.QUIESCE, 13),
        (M6MigrationStepKindV1.AUTHORITY_SWITCH, 14),
        (M6MigrationStepKindV1.POST_SWITCH_VALIDATION, 15),
    ):
        accepted = step_m6_migration_replay_v1(
            state,
            _verified(plan, kind, evidence_number, state=state),
        )
        assert isinstance(accepted, M6MigrationAcceptedV1)
        state = accepted.post_state

    failed = step_m6_migration_replay_v1(
        state,
        _verified(
            plan,
            M6MigrationStepKindV1.POST_SWITCH_FAIL_STOP,
            99,
            state=state,
        ),
    )

    assert isinstance(failed, M6MigrationAcceptedV1)
    assert failed.post_state.phase is M6MigrationPhaseV1.POST_SWITCH_FAILED
    assert failed.post_state.post_switch_validation_root == _root(15)
    assert failed.post_state.post_switch_failure_root == _root(99)
    assert failed.post_state.legacy_writes_enabled is False
    assert failed.post_state.target_writes_enabled is False


def test_migration_phase_table_is_immutable_and_rebinding_safe(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Architecture/BVA: the core captures its closed lifecycle policy."""

    expected = {
        M6MigrationPhaseV1.LEGACY: (
            M6MigrationStepKindV1.SHADOW_REPLAY,
            M6MigrationPhaseV1.SHADOW_REPLAY,
        ),
        M6MigrationPhaseV1.SHADOW_REPLAY: (
            M6MigrationStepKindV1.DUAL_CHECK,
            M6MigrationPhaseV1.DUAL_CHECK,
        ),
        M6MigrationPhaseV1.DUAL_CHECK: (
            M6MigrationStepKindV1.QUIESCE,
            M6MigrationPhaseV1.QUIESCED,
        ),
        M6MigrationPhaseV1.QUIESCED: (
            M6MigrationStepKindV1.AUTHORITY_SWITCH,
            M6MigrationPhaseV1.AUTHORITY_SWITCH,
        ),
        M6MigrationPhaseV1.AUTHORITY_SWITCH: (
            M6MigrationStepKindV1.POST_SWITCH_VALIDATION,
            M6MigrationPhaseV1.POST_SWITCH_VALIDATION,
        ),
        M6MigrationPhaseV1.POST_SWITCH_VALIDATION: (
            M6MigrationStepKindV1.LEGACY_DISABLE,
            M6MigrationPhaseV1.LEGACY_DISABLED,
        ),
    }
    assert isinstance(m6_lifecycle._NEXT_PHASE, MappingProxyType)
    assert dict(m6_lifecycle._NEXT_PHASE) == expected
    for phase in M6MigrationPhaseV1:
        assert m6_lifecycle._next_phase_v1(phase) == expected.get(phase)

    with pytest.raises(TypeError):
        m6_lifecycle._NEXT_PHASE[M6MigrationPhaseV1.LEGACY] = expected[M6MigrationPhaseV1.LEGACY]  # type: ignore[index]
    initial = M6MigrationStateV1.initial(_plan())
    witness = _verified(_plan(), M6MigrationStepKindV1.SHADOW_REPLAY, 11, state=initial)
    monkeypatch.setattr(m6_lifecycle, "_NEXT_PHASE", {})
    assert m6_lifecycle._next_phase_v1(M6MigrationPhaseV1.LEGACY) == expected[
        M6MigrationPhaseV1.LEGACY
    ]
    monkeypatch.setattr(
        m6_lifecycle,
        "_next_phase_v1",
        lambda _phase: (M6MigrationStepKindV1.ROLLBACK, M6MigrationPhaseV1.LEGACY),
    )
    accepted = step_m6_migration_replay_v1(initial, witness)
    assert isinstance(accepted, M6MigrationAcceptedV1)
    assert accepted.post_state.phase is M6MigrationPhaseV1.SHADOW_REPLAY
