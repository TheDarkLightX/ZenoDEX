"""Typed, research-only M6 migration and authority-switch transition core.

The existing M6 fallback/rejoin phase records Tau liveness.  This module models
the separate deployment migration lifecycle required by M6-R11:

    LEGACY -> SHADOW_REPLAY -> DUAL_CHECK -> QUIESCED
      -> AUTHORITY_SWITCH -> POST_SWITCH_VALIDATION -> LEGACY_DISABLED
                             or POST_SWITCH_FAILED (terminal)

The transition is pure.  It accepts only an opaque verifier-created step,
returns a new immutable state or a typed no-op rejection, and never disables a
writer or publishes economic state itself.  Those effects remain shell and
deployment obligations.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from types import MappingProxyType
from typing import Callable, Final, Mapping, TypeAlias

from .m6_safe_mount_types_v1 import (
    ZERO_ROOT_V1,
    _require_nonnegative_int,
    _require_root,
    hash_v1,
)

M6_MIGRATION_LIFECYCLE_SCHEMA_V1: Final = "zenodex/m6-migration-lifecycle/v1"
M6_MIGRATION_STATE_SCHEMA_V1: Final = "zenodex/m6-migration-state/v1"
M6_MIGRATION_STATE_SCHEMA_V2: Final = "zenodex/m6-migration-state/v2"
M6_MIGRATION_STATE_ROOT_DOMAIN_V2: Final = "m6-migration-state-v2"
M6_MIGRATION_RECEIPT_DOMAIN_V1: Final = "m6-migration-authority-receipt-v1"
M6_MIGRATION_BRANCH_DOMAIN_V1: Final = "m6-migration-branch-v1"
M6_MIGRATION_MAX_WRITER_EPOCH_V1: Final = (1 << 64) - 1


def _require_writer_epoch(value: object, *, name: str) -> int:
    epoch = _require_nonnegative_int(value, name=name)
    if epoch > M6_MIGRATION_MAX_WRITER_EPOCH_V1:
        raise ValueError(
            f"{name} exceeds the u64 writer epoch bound "
            f"({M6_MIGRATION_MAX_WRITER_EPOCH_V1})"
        )
    return epoch


class M6MigrationPhaseV1(str, Enum):
    LEGACY = "legacy"
    SHADOW_REPLAY = "shadow_replay"
    DUAL_CHECK = "dual_check"
    QUIESCED = "quiesced"
    AUTHORITY_SWITCH = "authority_switch"
    POST_SWITCH_VALIDATION = "post_switch_validation"
    POST_SWITCH_FAILED = "post_switch_failed"
    LEGACY_DISABLED = "legacy_disabled"


class M6MigrationStepKindV1(str, Enum):
    SHADOW_REPLAY = "shadow_replay"
    DUAL_CHECK = "dual_check"
    QUIESCE = "quiesce"
    AUTHORITY_SWITCH = "authority_switch"
    POST_SWITCH_VALIDATION = "post_switch_validation"
    POST_SWITCH_FAIL_STOP = "post_switch_fail_stop"
    LEGACY_DISABLE = "legacy_disable"
    ROLLBACK = "rollback"


class M6MigrationRejectCodeV1(str, Enum):
    INVALID_STATE = "invalid_state"
    INVALID_STEP = "invalid_step"
    PHASE_MISMATCH = "phase_mismatch"
    PLAN_BINDING_MISMATCH = "plan_binding_mismatch"
    BRANCH_BINDING_MISMATCH = "branch_binding_mismatch"
    CONTEXT_BINDING_MISMATCH = "context_binding_mismatch"
    EVIDENCE_BINDING_MISMATCH = "evidence_binding_mismatch"
    LEGACY_ALREADY_DISABLED = "legacy_already_disabled"
    ROLLBACK_FORBIDDEN = "rollback_forbidden"


@dataclass(frozen=True, slots=True)
class M6MigrationPlanV1:
    """Immutable roots and epochs that define one authority-switch attempt.

    M6-R11 v1 only supports rollback to the exact source snapshot.  A
    rollback destination with different state semantics requires a new schema
    and a separate recovery proof; accepting a second, currently-unused root
    here would make the rollback contract ambiguous.
    """

    source_subject_root: str
    target_subject_root: str
    source_state_root: str
    target_state_root: str
    source_writer_epoch: int
    target_writer_epoch: int
    allowed_writer_set_root: str
    authority_registry_root: str
    rollback_state_root: str

    def __post_init__(self) -> None:
        for field_name in (
            "source_subject_root",
            "target_subject_root",
            "source_state_root",
            "target_state_root",
            "allowed_writer_set_root",
            "authority_registry_root",
            "rollback_state_root",
        ):
            _require_root(getattr(self, field_name), name=f"migration plan {field_name}")
        _require_writer_epoch(self.source_writer_epoch, name="migration source writer epoch")
        _require_writer_epoch(self.target_writer_epoch, name="migration target writer epoch")
        if self.source_subject_root == self.target_subject_root:
            raise ValueError("migration plan source and target subjects must differ")
        if self.target_writer_epoch <= self.source_writer_epoch:
            raise ValueError("migration target writer epoch must advance")
        if self.rollback_state_root != self.source_state_root:
            raise ValueError(
                "migration v1 rollback state root must equal the source state root"
            )

    @property
    def plan_root(self) -> str:
        return hash_v1("m6-migration-plan-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": M6_MIGRATION_LIFECYCLE_SCHEMA_V1,
            "source_subject_root": self.source_subject_root,
            "target_subject_root": self.target_subject_root,
            "source_state_root": self.source_state_root,
            "target_state_root": self.target_state_root,
            "source_writer_epoch": self.source_writer_epoch,
            "target_writer_epoch": self.target_writer_epoch,
            "allowed_writer_set_root": self.allowed_writer_set_root,
            "authority_registry_root": self.authority_registry_root,
            "rollback_state_root": self.rollback_state_root,
        }


@dataclass(frozen=True, slots=True)
class M6MigrationStepV1:
    """Caller-visible migration claim; it is not accepted as authority."""

    kind: M6MigrationStepKindV1
    source_subject_root: str
    target_subject_root: str
    source_state_root: str
    target_state_root: str
    source_writer_epoch: int
    target_writer_epoch: int
    allowed_writer_set_root: str
    rollback_state_root: str
    evidence_root: str
    rollback: bool

    def __post_init__(self) -> None:
        if not isinstance(self.kind, M6MigrationStepKindV1):
            raise TypeError("migration step kind is not closed")
        for field_name in (
            "source_subject_root",
            "target_subject_root",
            "source_state_root",
            "target_state_root",
            "allowed_writer_set_root",
            "rollback_state_root",
            "evidence_root",
        ):
            _require_root(getattr(self, field_name), name=f"migration step {field_name}")
        _require_writer_epoch(self.source_writer_epoch, name="migration step source writer epoch")
        _require_writer_epoch(self.target_writer_epoch, name="migration step target writer epoch")
        if type(self.rollback) is not bool:
            raise TypeError("migration step rollback must be bool")
        if self.rollback != (self.kind is M6MigrationStepKindV1.ROLLBACK):
            raise ValueError("migration step rollback flag does not match its kind")

    @property
    def step_root(self) -> str:
        return hash_v1("m6-migration-step-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": M6_MIGRATION_LIFECYCLE_SCHEMA_V1,
            "kind": self.kind,
            "source_subject_root": self.source_subject_root,
            "target_subject_root": self.target_subject_root,
            "source_state_root": self.source_state_root,
            "target_state_root": self.target_state_root,
            "source_writer_epoch": self.source_writer_epoch,
            "target_writer_epoch": self.target_writer_epoch,
            "allowed_writer_set_root": self.allowed_writer_set_root,
            "rollback_state_root": self.rollback_state_root,
            "evidence_root": self.evidence_root,
            "rollback": self.rollback,
        }


_M6_MIGRATION_VERIFIED_TOKEN = object()
_M6_MIGRATION_REPLAY_TOKEN = object()


class VerifiedM6MigrationStepV1:
    """Opaque verifier-owned wrapper for one migration step."""

    __slots__ = (
        "_step",
        "_receipt_root",
        "_branch_root",
        "_pre_state_root",
        "_pre_phase",
        "_sealed",
    )
    _step: M6MigrationStepV1
    _receipt_root: str
    _branch_root: str
    _pre_state_root: str
    _pre_phase: M6MigrationPhaseV1
    _sealed: bool

    def __init__(
        self,
        token: object,
        step: M6MigrationStepV1,
        receipt_root: str,
        branch_root: str,
        pre_state_root: str,
        pre_phase: M6MigrationPhaseV1,
    ) -> None:
        if token is not _M6_MIGRATION_VERIFIED_TOKEN:
            raise TypeError("VerifiedM6MigrationStepV1 is verifier-created")
        if not isinstance(step, M6MigrationStepV1):
            raise TypeError("verified migration step payload is invalid")
        _require_root(receipt_root, name="migration verifier receipt root")
        _require_root(branch_root, name="migration verifier branch root")
        _require_root(pre_state_root, name="migration verifier pre-state root")
        if not isinstance(pre_phase, M6MigrationPhaseV1):
            raise TypeError("migration verifier pre-phase is not closed")
        object.__setattr__(self, "_step", step)
        object.__setattr__(self, "_receipt_root", receipt_root)
        object.__setattr__(self, "_branch_root", branch_root)
        object.__setattr__(self, "_pre_state_root", pre_state_root)
        object.__setattr__(self, "_pre_phase", pre_phase)
        object.__setattr__(self, "_sealed", True)

    @property
    def step(self) -> M6MigrationStepV1:
        return self._step

    @property
    def receipt_root(self) -> str:
        return self._receipt_root

    @property
    def branch_root(self) -> str:
        return self._branch_root

    @property
    def pre_state_root(self) -> str:
        return self._pre_state_root

    @property
    def pre_phase(self) -> M6MigrationPhaseV1:
        return self._pre_phase

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": M6_MIGRATION_LIFECYCLE_SCHEMA_V1,
            "step": self._step,
            "receipt_root": self._receipt_root,
            "branch_root": self._branch_root,
            "pre_state_root": self._pre_state_root,
            "pre_phase": self._pre_phase,
        }

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("verified migration step is immutable")
        object.__setattr__(self, name, value)

    def __repr__(self) -> str:
        return f"VerifiedM6MigrationStepV1(step_root={self.step.step_root!r})"


class M6MigrationStructuralReplayV1:
    """Opaque verifier-created witness for structural replay only.

    This type deliberately remains distinct from ``VerifiedM6MigrationStepV1``.
    A structural backend can support deterministic replay and differential
    testing, while the authoritative transition requires the authenticated
    witness created by the BLS-backed verifier path.
    """

    __slots__ = (
        "_step",
        "_receipt_root",
        "_branch_root",
        "_pre_state_root",
        "_pre_phase",
        "_sealed",
    )
    _step: M6MigrationStepV1
    _receipt_root: str
    _branch_root: str
    _pre_state_root: str
    _pre_phase: M6MigrationPhaseV1
    _sealed: bool

    def __init__(
        self,
        token: object,
        step: M6MigrationStepV1,
        receipt_root: str,
        branch_root: str,
        pre_state_root: str,
        pre_phase: M6MigrationPhaseV1,
    ) -> None:
        if token is not _M6_MIGRATION_REPLAY_TOKEN:
            raise TypeError("M6MigrationStructuralReplayV1 is verifier-created")
        if not isinstance(step, M6MigrationStepV1):
            raise TypeError("structural replay step payload is invalid")
        _require_root(receipt_root, name="migration replay receipt root")
        _require_root(branch_root, name="migration replay branch root")
        _require_root(pre_state_root, name="migration replay pre-state root")
        if not isinstance(pre_phase, M6MigrationPhaseV1):
            raise TypeError("migration replay pre-phase is not closed")
        object.__setattr__(self, "_step", step)
        object.__setattr__(self, "_receipt_root", receipt_root)
        object.__setattr__(self, "_branch_root", branch_root)
        object.__setattr__(self, "_pre_state_root", pre_state_root)
        object.__setattr__(self, "_pre_phase", pre_phase)
        object.__setattr__(self, "_sealed", True)

    @property
    def step(self) -> M6MigrationStepV1:
        return self._step

    @property
    def receipt_root(self) -> str:
        return self._receipt_root

    @property
    def branch_root(self) -> str:
        return self._branch_root

    @property
    def pre_state_root(self) -> str:
        return self._pre_state_root

    @property
    def pre_phase(self) -> M6MigrationPhaseV1:
        return self._pre_phase

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": M6_MIGRATION_LIFECYCLE_SCHEMA_V1,
            "step": self._step,
            "receipt_root": self._receipt_root,
            "branch_root": self._branch_root,
            "pre_state_root": self._pre_state_root,
            "pre_phase": self._pre_phase,
        }

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("structural replay witness is immutable")
        object.__setattr__(self, name, value)

    def __repr__(self) -> str:
        return f"M6MigrationStructuralReplayV1(step_root={self.step.step_root!r})"


@dataclass(frozen=True, slots=True)
class M6MigrationStateV1:
    plan: M6MigrationPlanV1
    phase: M6MigrationPhaseV1
    replay_root: str
    dual_check_root: str
    quiescence_root: str
    switch_root: str
    post_switch_validation_root: str
    post_switch_failure_root: str
    legacy_disable_root: str
    active_subject_root: str
    active_state_root: str
    active_writer_epoch: int
    branch_root: str
    legacy_writes_enabled: bool
    target_writes_enabled: bool

    def __post_init__(self) -> None:
        if not isinstance(self.plan, M6MigrationPlanV1):
            raise TypeError("migration state plan is invalid")
        if not isinstance(self.phase, M6MigrationPhaseV1):
            raise TypeError("migration state phase is not closed")
        for field_name in (
            "replay_root",
            "dual_check_root",
            "quiescence_root",
            "switch_root",
            "post_switch_validation_root",
            "post_switch_failure_root",
            "legacy_disable_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"migration state {field_name}",
                allow_zero=True,
            )
        _require_root(self.active_subject_root, name="migration active subject root")
        _require_root(self.active_state_root, name="migration active state root")
        _require_writer_epoch(self.active_writer_epoch, name="migration active writer epoch")
        _require_root(self.branch_root, name="migration branch root")
        if type(self.legacy_writes_enabled) is not bool:
            raise TypeError("migration legacy write flag must be bool")
        if type(self.target_writes_enabled) is not bool:
            raise TypeError("migration target write flag must be bool")
        if self.legacy_writes_enabled and self.target_writes_enabled:
            raise ValueError("migration cannot enable legacy and target writers together")
        source_phases = {
            M6MigrationPhaseV1.LEGACY,
            M6MigrationPhaseV1.SHADOW_REPLAY,
            M6MigrationPhaseV1.DUAL_CHECK,
            M6MigrationPhaseV1.QUIESCED,
        }
        if self.phase in source_phases:
            if (
                self.active_subject_root != self.plan.source_subject_root
                or self.active_state_root != self.plan.source_state_root
                or self.active_writer_epoch != self.plan.source_writer_epoch
            ):
                raise ValueError("source migration phase has target authority active")
            if self.phase is M6MigrationPhaseV1.QUIESCED:
                if (
                    self.quiescence_root == ZERO_ROOT_V1
                    or self.legacy_writes_enabled
                    or self.target_writes_enabled
                ):
                    raise ValueError("quiesced migration state must disable writers and bind quiescence")
            elif not self.legacy_writes_enabled or self.target_writes_enabled:
                raise ValueError("pre-switch migration state has invalid writer flags")
        elif self.phase is M6MigrationPhaseV1.POST_SWITCH_FAILED:
            if (
                self.active_subject_root != self.plan.target_subject_root
                or self.active_state_root != self.plan.target_state_root
                or self.active_writer_epoch != self.plan.target_writer_epoch
            ):
                raise ValueError("failed post-switch migration has source authority active")
            if self.legacy_writes_enabled or self.target_writes_enabled:
                raise ValueError("failed post-switch migration must disable all writers")
        else:
            if (
                self.active_subject_root != self.plan.target_subject_root
                or self.active_state_root != self.plan.target_state_root
                or self.active_writer_epoch != self.plan.target_writer_epoch
            ):
                raise ValueError("post-switch migration phase has source authority active")
            if self.legacy_writes_enabled or not self.target_writes_enabled:
                raise ValueError("post-switch migration state has invalid writer flags")
        required_roots = {
            M6MigrationPhaseV1.SHADOW_REPLAY: ("replay_root",),
            M6MigrationPhaseV1.DUAL_CHECK: ("replay_root", "dual_check_root"),
            M6MigrationPhaseV1.QUIESCED: (
                "replay_root",
                "dual_check_root",
                "quiescence_root",
            ),
            M6MigrationPhaseV1.AUTHORITY_SWITCH: (
                "replay_root",
                "dual_check_root",
                "quiescence_root",
                "switch_root",
            ),
            M6MigrationPhaseV1.POST_SWITCH_VALIDATION: (
                "replay_root",
                "dual_check_root",
                "quiescence_root",
                "switch_root",
                "post_switch_validation_root",
            ),
            M6MigrationPhaseV1.POST_SWITCH_FAILED: (
                "replay_root",
                "dual_check_root",
                "quiescence_root",
                "switch_root",
                "post_switch_failure_root",
            ),
            M6MigrationPhaseV1.LEGACY_DISABLED: (
                "replay_root",
                "dual_check_root",
                "quiescence_root",
                "switch_root",
                "post_switch_validation_root",
                "legacy_disable_root",
            ),
        }
        required_fields = required_roots.get(self.phase, ())
        evidence_fields = (
            "replay_root",
            "dual_check_root",
            "quiescence_root",
            "switch_root",
            "post_switch_validation_root",
            "post_switch_failure_root",
            "legacy_disable_root",
        )
        optional_fields = (
            ("post_switch_validation_root",)
            if self.phase is M6MigrationPhaseV1.POST_SWITCH_FAILED
            else ()
        )
        for field_name in evidence_fields:
            value = getattr(self, field_name)
            if field_name in required_fields and value == ZERO_ROOT_V1:
                raise ValueError(f"migration phase requires {field_name}")
            if field_name in optional_fields:
                continue
            if field_name not in required_fields and value != ZERO_ROOT_V1:
                raise ValueError(f"migration phase cannot bind future evidence {field_name}")

    @classmethod
    def initial(
        cls,
        plan: M6MigrationPlanV1,
        *,
        branch_root: str | None = None,
    ) -> "M6MigrationStateV1":
        if not isinstance(plan, M6MigrationPlanV1):
            raise TypeError("migration initial plan is invalid")
        if branch_root is None:
            branch_root = hash_v1(
                M6_MIGRATION_BRANCH_DOMAIN_V1,
                {"plan_root": plan.plan_root, "generation": 0},
            )
        _require_root(branch_root, name="migration initial branch root")
        return cls(
            plan=plan,
            phase=M6MigrationPhaseV1.LEGACY,
            replay_root=ZERO_ROOT_V1,
            dual_check_root=ZERO_ROOT_V1,
            quiescence_root=ZERO_ROOT_V1,
            switch_root=ZERO_ROOT_V1,
            post_switch_validation_root=ZERO_ROOT_V1,
            post_switch_failure_root=ZERO_ROOT_V1,
            legacy_disable_root=ZERO_ROOT_V1,
            active_subject_root=plan.source_subject_root,
            active_state_root=plan.source_state_root,
            active_writer_epoch=plan.source_writer_epoch,
            branch_root=branch_root,
            legacy_writes_enabled=True,
            target_writes_enabled=False,
        )

    @property
    def state_root(self) -> str:
        return hash_v1(M6_MIGRATION_STATE_ROOT_DOMAIN_V2, self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": M6_MIGRATION_STATE_SCHEMA_V2,
            "plan": self.plan,
            "phase": self.phase,
            "replay_root": self.replay_root,
            "dual_check_root": self.dual_check_root,
            "quiescence_root": self.quiescence_root,
            "switch_root": self.switch_root,
            "post_switch_validation_root": self.post_switch_validation_root,
            "post_switch_failure_root": self.post_switch_failure_root,
            "legacy_disable_root": self.legacy_disable_root,
            "active_subject_root": self.active_subject_root,
            "active_state_root": self.active_state_root,
            "active_writer_epoch": self.active_writer_epoch,
            "branch_root": self.branch_root,
            "legacy_writes_enabled": self.legacy_writes_enabled,
            "target_writes_enabled": self.target_writes_enabled,
        }


@dataclass(frozen=True, slots=True)
class M6MigrationAcceptedV1:
    post_state: M6MigrationStateV1
    step_root: str

    def __post_init__(self) -> None:
        if not isinstance(self.post_state, M6MigrationStateV1):
            raise TypeError("migration accepted post-state is invalid")
        _require_root(self.step_root, name="migration accepted step root")


@dataclass(frozen=True, slots=True)
class M6MigrationRejectedV1:
    code: M6MigrationRejectCodeV1
    pre_state_root: str
    post_state_root: str
    reason: str

    def __post_init__(self) -> None:
        if not isinstance(self.code, M6MigrationRejectCodeV1):
            raise TypeError("migration reject code is not closed")
        _require_root(self.pre_state_root, name="migration rejected pre-state root")
        _require_root(self.post_state_root, name="migration rejected post-state root")
        if self.pre_state_root != self.post_state_root:
            raise ValueError("migration rejection changed the state root")
        if not isinstance(self.reason, str) or not self.reason:
            raise ValueError("migration rejection reason must be non-empty")


M6MigrationResultV1: TypeAlias = M6MigrationAcceptedV1 | M6MigrationRejectedV1


_NEXT_PHASE: Final[Mapping[M6MigrationPhaseV1, tuple[M6MigrationStepKindV1, M6MigrationPhaseV1]]] = MappingProxyType(
    {
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
)


def _next_phase_v1(
    phase: M6MigrationPhaseV1,
    _table: Mapping[M6MigrationPhaseV1, tuple[M6MigrationStepKindV1, M6MigrationPhaseV1]] = _NEXT_PHASE,
) -> tuple[M6MigrationStepKindV1, M6MigrationPhaseV1] | None:
    """Read the frozen lifecycle table captured at function definition."""

    return _table.get(phase)


def _reject(
    state: M6MigrationStateV1,
    code: M6MigrationRejectCodeV1,
    reason: str,
) -> M6MigrationRejectedV1:
    root = state.state_root
    return M6MigrationRejectedV1(code, root, root, reason)


def _plan_binding_reason(
    plan: M6MigrationPlanV1,
    step: M6MigrationStepV1,
) -> str | None:
    bindings = (
        (step.source_subject_root, plan.source_subject_root, "source subject"),
        (step.target_subject_root, plan.target_subject_root, "target subject"),
        (step.source_state_root, plan.source_state_root, "source state"),
        (step.target_state_root, plan.target_state_root, "target state"),
        (step.source_writer_epoch, plan.source_writer_epoch, "source writer epoch"),
        (step.target_writer_epoch, plan.target_writer_epoch, "target writer epoch"),
        (step.allowed_writer_set_root, plan.allowed_writer_set_root, "allowed writer set"),
        (step.rollback_state_root, plan.rollback_state_root, "rollback state"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            return f"migration {label} binding mismatch"
    return None


def _context_binding_reason(
    state: M6MigrationStateV1,
    *,
    pre_state_root: str,
    pre_phase: M6MigrationPhaseV1,
) -> str | None:
    if pre_state_root != state.state_root:
        return "migration witness pre-state root does not match the current state"
    if pre_phase is not state.phase:
        return "migration witness pre-phase does not match the current state"
    return None


def _apply_m6_migration_step_v1(
    state: M6MigrationStateV1,
    step: M6MigrationStepV1,
    _phase_transition: Callable[
        [M6MigrationPhaseV1],
        tuple[M6MigrationStepKindV1, M6MigrationPhaseV1] | None,
    ] = _next_phase_v1,
) -> M6MigrationResultV1:
    """Apply the shared structural transition after its boundary checks."""

    binding_reason = _plan_binding_reason(state.plan, step)
    if binding_reason is not None:
        return _reject(
            state,
            M6MigrationRejectCodeV1.PLAN_BINDING_MISMATCH,
            binding_reason,
        )
    if step.evidence_root == ZERO_ROOT_V1:
        return _reject(
            state,
            M6MigrationRejectCodeV1.EVIDENCE_BINDING_MISMATCH,
            "migration evidence root is zero",
        )
    if step.kind is M6MigrationStepKindV1.ROLLBACK:
        if state.phase is M6MigrationPhaseV1.LEGACY_DISABLED:
            return _reject(
                state,
                M6MigrationRejectCodeV1.LEGACY_ALREADY_DISABLED,
                "legacy rollback is forbidden after legacy disable",
            )
        if state.phase is M6MigrationPhaseV1.LEGACY:
            return _reject(
                state,
                M6MigrationRejectCodeV1.ROLLBACK_FORBIDDEN,
                "legacy state has no migration to roll back",
            )
        if state.phase in (
            M6MigrationPhaseV1.AUTHORITY_SWITCH,
            M6MigrationPhaseV1.POST_SWITCH_VALIDATION,
            M6MigrationPhaseV1.POST_SWITCH_FAILED,
        ):
            return _reject(
                state,
                M6MigrationRejectCodeV1.ROLLBACK_FORBIDDEN,
                "rollback is forbidden after authority switch or fail-stop",
            )
        return M6MigrationAcceptedV1(
            post_state=M6MigrationStateV1.initial(
                state.plan,
                branch_root=hash_v1(
                    M6_MIGRATION_BRANCH_DOMAIN_V1,
                    {
                        "parent_branch_root": state.branch_root,
                        "rollback_step_root": step.step_root,
                    },
                ),
            ),
            step_root=step.step_root,
        )
    if step.kind is M6MigrationStepKindV1.POST_SWITCH_FAIL_STOP:
        if state.phase not in (
            M6MigrationPhaseV1.AUTHORITY_SWITCH,
            M6MigrationPhaseV1.POST_SWITCH_VALIDATION,
        ):
            return _reject(
                state,
                M6MigrationRejectCodeV1.PHASE_MISMATCH,
                "post-switch fail-stop is only valid after authority switch",
            )
        return M6MigrationAcceptedV1(
            post_state=replace(
                state,
                phase=M6MigrationPhaseV1.POST_SWITCH_FAILED,
                post_switch_failure_root=step.evidence_root,
                active_subject_root=state.plan.target_subject_root,
                active_state_root=state.plan.target_state_root,
                active_writer_epoch=state.plan.target_writer_epoch,
                legacy_writes_enabled=False,
                target_writes_enabled=False,
            ),
            step_root=step.step_root,
        )
    expected = _phase_transition(state.phase)
    if expected is None or step.kind is not expected[0]:
        return _reject(
            state,
            M6MigrationRejectCodeV1.PHASE_MISMATCH,
            f"step {step.kind.value} is not valid in phase {state.phase.value}",
        )
    next_phase = expected[1]
    if step.kind is M6MigrationStepKindV1.SHADOW_REPLAY:
        post_state = replace(
            state,
            phase=next_phase,
            replay_root=step.evidence_root,
        )
    elif step.kind is M6MigrationStepKindV1.DUAL_CHECK:
        post_state = replace(
            state,
            phase=next_phase,
            dual_check_root=step.evidence_root,
        )
    elif step.kind is M6MigrationStepKindV1.QUIESCE:
        post_state = replace(
            state,
            phase=next_phase,
            quiescence_root=step.evidence_root,
            legacy_writes_enabled=False,
            target_writes_enabled=False,
        )
    elif step.kind is M6MigrationStepKindV1.AUTHORITY_SWITCH:
        post_state = replace(
            state,
            phase=next_phase,
            switch_root=step.evidence_root,
            active_subject_root=state.plan.target_subject_root,
            active_state_root=state.plan.target_state_root,
            active_writer_epoch=state.plan.target_writer_epoch,
            legacy_writes_enabled=False,
            target_writes_enabled=True,
        )
    elif step.kind is M6MigrationStepKindV1.POST_SWITCH_VALIDATION:
        post_state = replace(
            state,
            phase=next_phase,
            post_switch_validation_root=step.evidence_root,
            active_subject_root=state.plan.target_subject_root,
            active_state_root=state.plan.target_state_root,
            active_writer_epoch=state.plan.target_writer_epoch,
            legacy_writes_enabled=False,
            target_writes_enabled=True,
        )
    elif step.kind is M6MigrationStepKindV1.LEGACY_DISABLE:
        post_state = replace(
            state,
            phase=next_phase,
            legacy_disable_root=step.evidence_root,
            active_subject_root=state.plan.target_subject_root,
            active_state_root=state.plan.target_state_root,
            active_writer_epoch=state.plan.target_writer_epoch,
            legacy_writes_enabled=False,
            target_writes_enabled=True,
        )
    return M6MigrationAcceptedV1(post_state=post_state, step_root=step.step_root)


def replay_m6_migration_step_v1(
    state: M6MigrationStateV1,
    step: M6MigrationStepV1,
) -> M6MigrationResultV1:
    """Replay one persisted step for structural history validation only.

    This function never creates verifier authority.  Admission uses it after
    loading a step and its persisted verifier receipt, so reopen can reject a
    rehashed or phase-inconsistent history.  Cryptographic receipt validity
    remains a verifier obligation and is deliberately not inferred here.
    """

    if not isinstance(state, M6MigrationStateV1):
        raise TypeError("migration state is invalid")
    if not isinstance(step, M6MigrationStepV1):
        raise TypeError("migration history step is invalid")
    return _apply_m6_migration_step_v1(state, step)


def step_m6_migration_replay_v1(
    state: M6MigrationStateV1,
    replay_witness: M6MigrationStructuralReplayV1,
) -> M6MigrationResultV1:
    """Apply a structural replay witness in the research/differential lane."""

    if not isinstance(state, M6MigrationStateV1):
        raise TypeError("migration state is invalid")
    if not isinstance(replay_witness, M6MigrationStructuralReplayV1):
        raise TypeError(
            "migration replay transition requires a structural replay witness"
        )
    receipt_root = replay_witness.receipt_root
    branch_root = replay_witness.branch_root
    step = replay_witness.step
    try:
        _require_root(receipt_root, name="migration replay receipt root")
        _require_root(branch_root, name="migration replay branch root")
    except (TypeError, ValueError) as exc:
        raise TypeError("structural replay witness receipt is invalid") from exc
    if branch_root != state.branch_root:
        return _reject(
            state,
            M6MigrationRejectCodeV1.BRANCH_BINDING_MISMATCH,
            "migration replay witness branch does not match the current state",
        )
    context_reason = _context_binding_reason(
        state,
        pre_state_root=replay_witness.pre_state_root,
        pre_phase=replay_witness.pre_phase,
    )
    if context_reason is not None:
        return _reject(
            state,
            M6MigrationRejectCodeV1.CONTEXT_BINDING_MISMATCH,
            context_reason,
        )
    return _apply_m6_migration_step_v1(state, step)


def step_m6_migration_v1(
    state: M6MigrationStateV1,
    verified_step: VerifiedM6MigrationStepV1,
) -> M6MigrationResultV1:
    """Apply one verifier-authenticated migration step or return a typed no-op reject."""

    if not isinstance(state, M6MigrationStateV1):
        raise TypeError("migration state is invalid")
    if not isinstance(verified_step, VerifiedM6MigrationStepV1):
        raise TypeError(
            "migration transition requires a BLS-authenticated migration step"
        )
    try:
        receipt_root = verified_step.receipt_root
        branch_root = verified_step.branch_root
        step = verified_step.step
    except AttributeError as exc:
        raise TypeError("verified migration step is incomplete") from exc
    try:
        _require_root(receipt_root, name="migration verifier receipt root")
        _require_root(branch_root, name="migration verifier branch root")
    except (TypeError, ValueError) as exc:
        raise TypeError("verified migration step receipt is invalid") from exc
    if not isinstance(step, M6MigrationStepV1):
        raise TypeError("verified migration step payload is invalid")
    if branch_root != state.branch_root:
        return _reject(
            state,
            M6MigrationRejectCodeV1.BRANCH_BINDING_MISMATCH,
            "migration verifier branch does not match the current state",
        )
    context_reason = _context_binding_reason(
        state,
        pre_state_root=verified_step.pre_state_root,
        pre_phase=verified_step.pre_phase,
    )
    if context_reason is not None:
        return _reject(
            state,
            M6MigrationRejectCodeV1.CONTEXT_BINDING_MISMATCH,
            context_reason,
        )
    return _apply_m6_migration_step_v1(state, step)


__all__ = [
    "M6_MIGRATION_LIFECYCLE_SCHEMA_V1",
    "M6_MIGRATION_STATE_SCHEMA_V1",
    "M6_MIGRATION_STATE_SCHEMA_V2",
    "M6_MIGRATION_STATE_ROOT_DOMAIN_V2",
    "M6_MIGRATION_RECEIPT_DOMAIN_V1",
    "M6_MIGRATION_BRANCH_DOMAIN_V1",
    "M6_MIGRATION_MAX_WRITER_EPOCH_V1",
    "M6MigrationPhaseV1",
    "M6MigrationStepKindV1",
    "M6MigrationRejectCodeV1",
    "M6MigrationPlanV1",
    "M6MigrationStepV1",
    "VerifiedM6MigrationStepV1",
    "M6MigrationStructuralReplayV1",
    "M6MigrationStateV1",
    "M6MigrationAcceptedV1",
    "M6MigrationRejectedV1",
    "M6MigrationResultV1",
    "replay_m6_migration_step_v1",
    "step_m6_migration_replay_v1",
    "step_m6_migration_v1",
]
