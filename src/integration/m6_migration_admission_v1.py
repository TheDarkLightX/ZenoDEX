"""Research-only durable admission shell for M6-R11.

The migration lifecycle itself is a pure transition over immutable typed values.
This module supplies the imperative boundary around that core:

* one canonical ``HEAD.json`` contains the complete migration state and step
  history;
* an inter-process lock protects the read/compare/transition/install sequence;
* the expected state root is a real compare-and-swap guard;
* a committed step root is idempotent across process restart; and
* reopen validates canonical bytes, the complete history chain, and the state
  root before any later admission.

The shell does not stop processes, publish economic state, or create verifier
authority.  ``M6MigrationWriterConsumerV1`` is the research-only writer
adapter: it reauthorizes against the reopened state and then calls the same
durable admission port.
"""

from __future__ import annotations

import fcntl
import json
import os
import tempfile
from contextlib import contextmanager
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Iterator

from ..core.m6_migration_lifecycle_v1 import (
    M6_MIGRATION_LIFECYCLE_SCHEMA_V1,
    M6_MIGRATION_MAX_WRITER_EPOCH_V1,
    M6_MIGRATION_STATE_SCHEMA_V1,
    M6_MIGRATION_STATE_SCHEMA_V2,
    M6MigrationAcceptedV1,
    M6MigrationPhaseV1,
    M6MigrationPlanV1,
    M6MigrationRejectCodeV1,
    M6MigrationStateV1,
    M6MigrationStepKindV1,
    M6MigrationStepV1,
    replay_m6_migration_step_v1,
    step_m6_migration_v1,
)
from ..core.m6_safe_mount_types_v1 import (
    ZERO_ROOT_V1,
    _require_root,
    canonical_bytes_v1,
    hash_v1,
)
from ..state.canonical import canonical_hex_fixed_allow_0x
from .m6_migration_authority_v1 import (
    M6MigrationAuthorityProofRejectedV1,
    M6MigrationAuthorityReceiptV1,
    M6MigrationAuthorityVerifierUnavailableV1,
    M6MigrationAuthorityVerifierV1,
    M6MigrationVerifiedAdmissionV1,
    M6MigrationWriterMembershipProofV1,
    M6MigrationWriterMembershipVerifierV1,
)

M6_MIGRATION_ADMISSION_SCHEMA_V1 = "zenodex/m6-migration-admission/v1"
M6_MIGRATION_ADMISSION_SCHEMA_V2 = "zenodex/m6-migration-admission/v2"
M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V1 = "m6-migration-admission-head-v1"
M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V2 = "m6-migration-admission-head-v2"
M6_MIGRATION_HEAD_FILE_V1 = "HEAD.json"
M6_MIGRATION_LOCK_FILE_V1 = ".m6-migration.lock"
M6_MIGRATION_EXTERNAL_ANCHOR_SCHEMA_V1 = "zenodex/m6-migration-external-anchor/v1"
M6_MIGRATION_EXTERNAL_ANCHOR_DOMAIN_V1 = "m6-migration-external-anchor-v1"
M6_MIGRATION_MAX_HEAD_BYTES_V1 = 4 * 1024 * 1024
M6_MIGRATION_MAX_EXTERNAL_ANCHOR_BYTES_V1 = 4096
M6_MIGRATION_MAX_HISTORY_STEPS_V1 = 4096


class M6MigrationDurableCorruptionError(RuntimeError):
    """The migration head cannot be reconstructed without ambiguity."""


class M6MigrationAdmissionStatusV1(str, Enum):
    COMMITTED = "committed"
    ALREADY_COMMITTED = "already_committed"
    STALE_STATE = "stale_state"
    REJECTED = "rejected"


class M6MigrationWriterAdmissionStatusV1(str, Enum):
    ALLOWED = "allowed"
    REJECTED = "rejected"


_M6_MIGRATION_WRITER_AUTHORIZATION_TOKEN = object()


class M6MigrationWriterAuthorizationV1:
    """Verifier-created capability for one exact migration writer snapshot."""

    __slots__ = (
        "_plan_root",
        "_state_root",
        "_active_subject_root",
        "_active_writer_epoch",
        "_allowed_writer_set_root",
        "_membership_receipt_root",
        "_sealed",
    )
    _plan_root: str
    _state_root: str
    _active_subject_root: str
    _active_writer_epoch: int
    _allowed_writer_set_root: str
    _membership_receipt_root: str
    _sealed: bool

    def __init__(
        self,
        token: object,
        *,
        plan_root: str,
        state_root: str,
        active_subject_root: str,
        active_writer_epoch: int,
        allowed_writer_set_root: str,
        membership_receipt_root: str,
    ) -> None:
        if token is not _M6_MIGRATION_WRITER_AUTHORIZATION_TOKEN:
            raise TypeError("migration writer authorization is verifier-created")
        _require_root(plan_root, name="migration writer authorization plan root")
        _require_root(state_root, name="migration writer authorization state root")
        _require_root(
            active_subject_root,
            name="migration writer authorization subject root",
        )
        _require_root(
            allowed_writer_set_root,
            name="migration writer authorization writer set root",
        )
        _require_root(
            membership_receipt_root,
            name="migration writer authorization receipt root",
        )
        if (
            type(active_writer_epoch) is not int
            or active_writer_epoch < 0
            or active_writer_epoch > M6_MIGRATION_MAX_WRITER_EPOCH_V1
        ):
            raise ValueError("migration writer authorization epoch must be a u64")
        object.__setattr__(self, "_plan_root", plan_root)
        object.__setattr__(self, "_state_root", state_root)
        object.__setattr__(self, "_active_subject_root", active_subject_root)
        object.__setattr__(self, "_active_writer_epoch", active_writer_epoch)
        object.__setattr__(self, "_allowed_writer_set_root", allowed_writer_set_root)
        object.__setattr__(self, "_membership_receipt_root", membership_receipt_root)
        object.__setattr__(self, "_sealed", True)

    @property
    def plan_root(self) -> str:
        return self._plan_root

    @property
    def state_root(self) -> str:
        return self._state_root

    @property
    def active_subject_root(self) -> str:
        return self._active_subject_root

    @property
    def active_writer_epoch(self) -> int:
        return self._active_writer_epoch

    @property
    def allowed_writer_set_root(self) -> str:
        return self._allowed_writer_set_root

    @property
    def membership_receipt_root(self) -> str:
        return self._membership_receipt_root

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("migration writer authorization is immutable")
        object.__setattr__(self, name, value)

    def __repr__(self) -> str:
        return (
            "M6MigrationWriterAuthorizationV1("
            f"state_root={self.state_root!r}, subject_root={self.active_subject_root!r})"
        )


@dataclass(frozen=True, slots=True)
class M6MigrationCommittedStepV1:
    """Durable replay and idempotency record for one accepted transition."""

    step: M6MigrationStepV1
    receipt_root: str
    authority_receipt: M6MigrationAuthorityReceiptV1
    branch_root: str
    pre_head_root: str
    pre_state_root: str
    post_state_root: str

    def __post_init__(self) -> None:
        if not isinstance(self.step, M6MigrationStepV1):
            raise TypeError("committed migration step is invalid")
        _require_root(self.receipt_root, name="committed migration receipt root")
        if not isinstance(self.authority_receipt, M6MigrationAuthorityReceiptV1):
            raise TypeError("committed migration authority receipt is invalid")
        if self.authority_receipt.receipt_root != self.receipt_root:
            raise ValueError("committed migration receipt is not bound to authority evidence")
        _require_root(self.branch_root, name="committed migration branch root")
        _require_root(self.pre_head_root, name="committed migration pre-HEAD root")
        _require_root(self.pre_state_root, name="committed migration pre-state root")
        _require_root(self.post_state_root, name="committed migration post-state root")

    @property
    def step_root(self) -> str:
        return self.step.step_root

    @property
    def identity(self) -> tuple[str, str]:
        """Return the branch-scoped idempotency identity for this commit."""

        return self.step_root, self.branch_root

    def to_canonical(self) -> dict[str, object]:
        return {
            "step": self.step,
            "receipt_root": self.receipt_root,
            "authority_receipt": self.authority_receipt,
            "branch_root": self.branch_root,
            "pre_head_root": self.pre_head_root,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
        }


@dataclass(frozen=True, slots=True)
class M6MigrationDurableReopenV1:
    state: M6MigrationStateV1
    committed_steps: tuple[M6MigrationCommittedStepV1, ...]
    head_root: str

    def __post_init__(self) -> None:
        if not isinstance(self.state, M6MigrationStateV1):
            raise TypeError("migration reopened state is invalid")
        if not isinstance(self.committed_steps, tuple):
            raise TypeError("migration reopened history is invalid")
        _require_root(self.head_root, name="migration reopened HEAD root")


@dataclass(frozen=True, slots=True)
class M6MigrationDurableRecoveryV1:
    """A committed step recovered after an indeterminate admission result."""

    reopened: M6MigrationDurableReopenV1
    committed_step: M6MigrationCommittedStepV1

    def __post_init__(self) -> None:
        if not isinstance(self.reopened, M6MigrationDurableReopenV1):
            raise TypeError("migration recovery reopen is invalid")
        if not isinstance(self.committed_step, M6MigrationCommittedStepV1):
            raise TypeError("migration recovery committed step is invalid")


@dataclass(frozen=True, slots=True)
class M6MigrationAdmissionResultV1:
    status: M6MigrationAdmissionStatusV1
    state: M6MigrationStateV1
    pre_state_root: str
    post_state_root: str
    step_root: str | None = None
    reason: str | None = None
    core_reject_code: M6MigrationRejectCodeV1 | None = None
    head_root: str | None = None
    pre_head_root: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.status, M6MigrationAdmissionStatusV1):
            raise TypeError("migration admission status is not closed")
        if not isinstance(self.state, M6MigrationStateV1):
            raise TypeError("migration admission state is invalid")
        _require_root(self.pre_state_root, name="migration admission pre-state root")
        _require_root(self.post_state_root, name="migration admission post-state root")
        if self.post_state_root != self.state.state_root:
            raise ValueError("migration admission post-state root is not state-bound")
        if self.step_root is not None:
            _require_root(self.step_root, name="migration admission step root")
        if self.head_root is not None:
            _require_root(self.head_root, name="migration admission HEAD root")
        if self.pre_head_root is not None:
            _require_root(self.pre_head_root, name="migration admission pre-HEAD root")
        if self.status in (
            M6MigrationAdmissionStatusV1.COMMITTED,
            M6MigrationAdmissionStatusV1.ALREADY_COMMITTED,
        ) and self.head_root is None:
            raise ValueError("committed migration admission requires a HEAD root")
        if self.status in (
            M6MigrationAdmissionStatusV1.COMMITTED,
            M6MigrationAdmissionStatusV1.ALREADY_COMMITTED,
        ) and self.step_root is None:
            raise ValueError("committed migration admission requires a step root")
        if self.status in (
            M6MigrationAdmissionStatusV1.COMMITTED,
            M6MigrationAdmissionStatusV1.ALREADY_COMMITTED,
        ) and self.pre_head_root is None:
            raise ValueError("committed migration admission requires a pre-HEAD root")
        if self.reason is not None and (not isinstance(self.reason, str) or not self.reason):
            raise ValueError("migration admission reason must be non-empty when present")
        if self.core_reject_code is not None and not isinstance(
            self.core_reject_code, M6MigrationRejectCodeV1
        ):
            raise TypeError("migration core reject code is not closed")


@dataclass(frozen=True, slots=True)
class M6MigrationWriterAdmissionResultV1:
    status: M6MigrationWriterAdmissionStatusV1
    active_subject_root: str
    active_writer_epoch: int
    reason: str | None = None
    membership_receipt_root: str | None = None
    authorization: M6MigrationWriterAuthorizationV1 | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.status, M6MigrationWriterAdmissionStatusV1):
            raise TypeError("migration writer admission status is not closed")
        _require_root(self.active_subject_root, name="active migration subject root")
        if (
            type(self.active_writer_epoch) is not int
            or self.active_writer_epoch < 0
            or self.active_writer_epoch > M6_MIGRATION_MAX_WRITER_EPOCH_V1
        ):
            raise ValueError("active migration writer epoch must be a u64")
        if self.reason is not None and (not isinstance(self.reason, str) or not self.reason):
            raise ValueError("migration writer admission reason must be non-empty when present")
        if self.status is M6MigrationWriterAdmissionStatusV1.ALLOWED:
            if self.membership_receipt_root is None:
                raise ValueError("allowed migration writer admission requires a membership receipt")
            if not isinstance(self.authorization, M6MigrationWriterAuthorizationV1):
                raise ValueError(
                    "allowed migration writer admission requires verifier-created authorization"
                )
            if self.reason is not None:
                raise ValueError("allowed migration writer admission cannot carry a rejection reason")
            if (
                self.authorization.active_subject_root != self.active_subject_root
                or self.authorization.active_writer_epoch != self.active_writer_epoch
                or self.authorization.membership_receipt_root
                != self.membership_receipt_root
            ):
                raise ValueError("migration writer authorization is not result-bound")
        elif self.membership_receipt_root is not None or self.authorization is not None:
            raise ValueError("rejected migration writer admission cannot carry authorization")
        if self.membership_receipt_root is not None:
            _require_root(
                self.membership_receipt_root,
                name="migration writer membership receipt root",
            )


def _canonical_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a root string")
    try:
        canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    except (TypeError, ValueError) as exc:
        raise ValueError(str(exc)) from exc
    if value != canonical or canonical == ZERO_ROOT_V1:
        raise ValueError(f"{name} must be a non-zero canonical root")
    return canonical


def _canonical_state_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a root string")
    try:
        canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    except (TypeError, ValueError) as exc:
        raise ValueError(str(exc)) from exc
    if value != canonical:
        raise ValueError(f"{name} is not canonical")
    return canonical


def _object(value: object, *, name: str, keys: set[str]) -> dict[str, object]:
    if not isinstance(value, dict):
        raise M6MigrationDurableCorruptionError(f"{name} must be an object")
    if set(value) != keys:
        raise M6MigrationDurableCorruptionError(f"{name} keys mismatch")
    return value


def _text(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise M6MigrationDurableCorruptionError(f"{name} must be a non-empty string")
    return value


def _nonnegative_int(value: object, *, name: str) -> int:
    if (
        type(value) is not int
        or value < 0
        or value > M6_MIGRATION_MAX_WRITER_EPOCH_V1
    ):
        raise M6MigrationDurableCorruptionError(f"{name} must be a u64")
    return value


def _bool(value: object, *, name: str) -> bool:
    if type(value) is not bool:
        raise M6MigrationDurableCorruptionError(f"{name} must be bool")
    return value


def _reject_json_constant(value: str) -> object:
    raise ValueError(f"JSON constant is forbidden: {value}")


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _decode_plan(raw: object) -> M6MigrationPlanV1:
    obj = _object(
        raw,
        name="migration plan",
        keys={
            "schema",
            "source_subject_root",
            "target_subject_root",
            "source_state_root",
            "target_state_root",
            "source_writer_epoch",
            "target_writer_epoch",
            "allowed_writer_set_root",
            "authority_registry_root",
            "rollback_state_root",
        },
    )
    if obj["schema"] != M6_MIGRATION_LIFECYCLE_SCHEMA_V1:
        raise M6MigrationDurableCorruptionError("migration plan schema mismatch")
    try:
        return M6MigrationPlanV1(
            source_subject_root=_canonical_root(
                obj["source_subject_root"], name="migration source subject root"
            ),
            target_subject_root=_canonical_root(
                obj["target_subject_root"], name="migration target subject root"
            ),
            source_state_root=_canonical_root(
                obj["source_state_root"], name="migration source state root"
            ),
            target_state_root=_canonical_root(
                obj["target_state_root"], name="migration target state root"
            ),
            source_writer_epoch=_nonnegative_int(
                obj["source_writer_epoch"], name="migration source writer epoch"
            ),
            target_writer_epoch=_nonnegative_int(
                obj["target_writer_epoch"], name="migration target writer epoch"
            ),
            allowed_writer_set_root=_canonical_root(
                obj["allowed_writer_set_root"], name="migration allowed writer set root"
            ),
            authority_registry_root=_canonical_root(
                obj["authority_registry_root"], name="migration authority registry root"
            ),
            rollback_state_root=_canonical_root(
                obj["rollback_state_root"], name="migration rollback state root"
            ),
        )
    except (TypeError, ValueError) as exc:
        raise M6MigrationDurableCorruptionError(f"invalid migration plan: {exc}") from exc


def _decode_state(raw: object) -> M6MigrationStateV1:
    if not isinstance(raw, dict):
        raise M6MigrationDurableCorruptionError("migration state must be an object")
    raw_schema = raw.get("schema")
    if raw_schema == M6_MIGRATION_STATE_SCHEMA_V1:
        raise M6MigrationDurableCorruptionError(
            "migration state schema v1 is obsolete; rebuild the research head with state schema v2"
        )
    if raw_schema != M6_MIGRATION_STATE_SCHEMA_V2:
        raise M6MigrationDurableCorruptionError("migration state schema mismatch")
    obj = _object(
        raw,
        name="migration state",
        keys={
            "schema",
            "plan",
            "phase",
            "replay_root",
            "dual_check_root",
            "quiescence_root",
            "switch_root",
            "post_switch_validation_root",
            "post_switch_failure_root",
            "legacy_disable_root",
            "active_subject_root",
            "active_state_root",
            "active_writer_epoch",
            "branch_root",
            "legacy_writes_enabled",
            "target_writes_enabled",
        },
    )
    try:
        return M6MigrationStateV1(
            plan=_decode_plan(obj["plan"]),
            phase=M6MigrationPhaseV1(_text(obj["phase"], name="migration phase")),
            replay_root=_canonical_state_root(
                _text(obj["replay_root"], name="migration replay root"),
                name="migration replay root",
            ),
            dual_check_root=_canonical_state_root(
                _text(obj["dual_check_root"], name="migration dual-check root"),
                name="migration dual-check root",
            ),
            quiescence_root=_canonical_state_root(
                _text(obj["quiescence_root"], name="migration quiescence root"),
                name="migration quiescence root",
            ),
            switch_root=_canonical_state_root(
                _text(obj["switch_root"], name="migration switch root"),
                name="migration switch root",
            ),
            post_switch_validation_root=_canonical_state_root(
                _text(
                    obj["post_switch_validation_root"],
                    name="migration post-switch validation root",
                ),
                name="migration post-switch validation root",
            ),
            post_switch_failure_root=_canonical_state_root(
                _text(
                    obj["post_switch_failure_root"],
                    name="migration post-switch failure root",
                ),
                name="migration post-switch failure root",
            ),
            legacy_disable_root=_canonical_state_root(
                _text(obj["legacy_disable_root"], name="migration legacy-disable root"),
                name="migration legacy-disable root",
            ),
            active_subject_root=_canonical_root(
                obj["active_subject_root"], name="migration active subject root"
            ),
            active_state_root=_canonical_root(
                obj["active_state_root"], name="migration active state root"
            ),
            active_writer_epoch=_nonnegative_int(
                obj["active_writer_epoch"], name="migration active writer epoch"
            ),
            branch_root=_canonical_root(obj["branch_root"], name="migration branch root"),
            legacy_writes_enabled=_bool(
                obj["legacy_writes_enabled"], name="migration legacy writer flag"
            ),
            target_writes_enabled=_bool(
                obj["target_writes_enabled"], name="migration target writer flag"
            ),
        )
    except (TypeError, ValueError) as exc:
        raise M6MigrationDurableCorruptionError(f"invalid migration state: {exc}") from exc


def _decode_step(raw: object, *, index: int) -> M6MigrationStepV1:
    obj = _object(
        raw,
        name=f"migration step {index}",
        keys={
            "schema",
            "kind",
            "source_subject_root",
            "target_subject_root",
            "source_state_root",
            "target_state_root",
            "source_writer_epoch",
            "target_writer_epoch",
            "allowed_writer_set_root",
            "rollback_state_root",
            "evidence_root",
            "rollback",
        },
    )
    if obj["schema"] != M6_MIGRATION_LIFECYCLE_SCHEMA_V1:
        raise M6MigrationDurableCorruptionError(
            f"migration step {index} schema mismatch"
        )
    try:
        return M6MigrationStepV1(
            kind=M6MigrationStepKindV1(
                _text(obj["kind"], name=f"migration step {index} kind")
            ),
            source_subject_root=_canonical_root(
                obj["source_subject_root"],
                name=f"migration step {index} source subject root",
            ),
            target_subject_root=_canonical_root(
                obj["target_subject_root"],
                name=f"migration step {index} target subject root",
            ),
            source_state_root=_canonical_root(
                obj["source_state_root"],
                name=f"migration step {index} source state root",
            ),
            target_state_root=_canonical_root(
                obj["target_state_root"],
                name=f"migration step {index} target state root",
            ),
            source_writer_epoch=_nonnegative_int(
                obj["source_writer_epoch"],
                name=f"migration step {index} source writer epoch",
            ),
            target_writer_epoch=_nonnegative_int(
                obj["target_writer_epoch"],
                name=f"migration step {index} target writer epoch",
            ),
            allowed_writer_set_root=_canonical_root(
                obj["allowed_writer_set_root"],
                name=f"migration step {index} allowed writer set root",
            ),
            rollback_state_root=_canonical_root(
                obj["rollback_state_root"],
                name=f"migration step {index} rollback state root",
            ),
            evidence_root=_canonical_root(
                obj["evidence_root"],
                name=f"migration step {index} evidence root",
            ),
            rollback=_bool(obj["rollback"], name=f"migration step {index} rollback"),
        )
    except (TypeError, ValueError) as exc:
        raise M6MigrationDurableCorruptionError(
            f"invalid migration step {index}: {exc}"
        ) from exc


def _decode_committed_step(raw: object, *, index: int) -> M6MigrationCommittedStepV1:
    obj = _object(
        raw,
        name=f"committed migration step {index}",
        keys={
            "step",
            "receipt_root",
            "authority_receipt",
            "branch_root",
            "pre_head_root",
            "pre_state_root",
            "post_state_root",
        },
    )
    try:
        return M6MigrationCommittedStepV1(
            step=_decode_step(obj["step"], index=index),
            receipt_root=_canonical_root(
                obj["receipt_root"], name="committed migration receipt root"
            ),
            authority_receipt=M6MigrationAuthorityReceiptV1.from_canonical(
                obj["authority_receipt"]
            ),
            branch_root=_canonical_root(
                obj["branch_root"], name="committed migration branch root"
            ),
            pre_head_root=_canonical_root(
                obj["pre_head_root"], name="committed migration pre-HEAD root"
            ),
            pre_state_root=_canonical_root(
                obj["pre_state_root"], name="committed pre-state root"
            ),
            post_state_root=_canonical_root(
                obj["post_state_root"], name="committed post-state root"
            ),
        )
    except (TypeError, ValueError) as exc:
        raise M6MigrationDurableCorruptionError(
            f"invalid committed migration step {index}: {exc}"
        ) from exc


def _validate_history(
    state: M6MigrationStateV1,
    committed_steps: tuple[M6MigrationCommittedStepV1, ...],
    authority_verifier: M6MigrationAuthorityVerifierV1 | None,
) -> None:
    if len(committed_steps) > M6_MIGRATION_MAX_HISTORY_STEPS_V1:
        raise M6MigrationDurableCorruptionError("migration step history exceeds size bound")
    if len({step.identity for step in committed_steps}) != len(committed_steps):
        raise M6MigrationDurableCorruptionError("migration step history contains duplicates")
    if committed_steps and (
        authority_verifier is None or not authority_verifier.authenticated
    ):
        raise M6MigrationDurableCorruptionError(
            "authenticated migration verifier is required to reopen committed history"
        )
    if authority_verifier is not None and authority_verifier.authenticated:
        try:
            authority_verifier.validate_plan_binding(state.plan)
        except (
            TypeError,
            ValueError,
            M6MigrationAuthorityVerifierUnavailableV1,
            M6MigrationAuthorityProofRejectedV1,
        ) as exc:
            raise M6MigrationDurableCorruptionError(
                f"migration authority verifier is not bound to the durable plan: {exc}"
            ) from exc
    initial_branch_root = (
        committed_steps[0].branch_root if committed_steps else state.branch_root
    )
    replay_state = M6MigrationStateV1.initial(
        state.plan,
        branch_root=initial_branch_root,
    )
    replay_steps: tuple[M6MigrationCommittedStepV1, ...] = ()
    for index, step in enumerate(committed_steps):
        expected_pre_head_root = _head_document(replay_state, replay_steps)["head_root"]
        if step.pre_head_root != expected_pre_head_root:
            raise M6MigrationDurableCorruptionError(
                f"migration pre-HEAD history is not chained at index {index}"
            )
        if step.pre_state_root != replay_state.state_root:
            raise M6MigrationDurableCorruptionError(
                f"migration step history is not chained at index {index}"
            )
        if step.branch_root != replay_state.branch_root:
            raise M6MigrationDurableCorruptionError(
                f"migration branch history is not chained at index {index}"
            )
        if authority_verifier is None:
            raise M6MigrationDurableCorruptionError(
                "authenticated migration verifier disappeared during history replay"
            )
        try:
            reverified = authority_verifier.reverify_step(
                state.plan,
                step.step,
                step.branch_root,
                step.authority_receipt,
                pre_state_root=replay_state.state_root,
                pre_phase=replay_state.phase,
            )
        except (TypeError, ValueError, M6MigrationAuthorityProofRejectedV1) as exc:
            raise M6MigrationDurableCorruptionError(
                f"migration authority receipt verification failed at index {index}: {exc}"
            ) from exc
        if reverified.receipt_root != step.receipt_root:
            raise M6MigrationDurableCorruptionError(
                f"migration receipt root mismatch at index {index}"
            )
        replayed = replay_m6_migration_step_v1(replay_state, step.step)
        if not isinstance(replayed, M6MigrationAcceptedV1):
            raise M6MigrationDurableCorruptionError(
                f"migration step history contains a rejected step at index {index}"
            )
        if replayed.step_root != step.step_root:
            raise M6MigrationDurableCorruptionError(
                f"migration step root mismatch at index {index}"
            )
        if replayed.post_state.state_root != step.post_state_root:
            raise M6MigrationDurableCorruptionError(
                f"migration post-state mismatch at index {index}"
            )
        replay_state = replayed.post_state
        replay_steps = (*replay_steps, step)
    if state.state_root != replay_state.state_root:
        raise M6MigrationDurableCorruptionError("migration head does not match step history")


def _head_body(
    state: M6MigrationStateV1,
    committed_steps: tuple[M6MigrationCommittedStepV1, ...],
) -> dict[str, object]:
    return {
        "schema": M6_MIGRATION_ADMISSION_SCHEMA_V2,
        "state_root": state.state_root,
        "state": state,
        "committed_steps": committed_steps,
    }


def _head_document(
    state: M6MigrationStateV1,
    committed_steps: tuple[M6MigrationCommittedStepV1, ...],
) -> dict[str, object]:
    body = _head_body(state, committed_steps)
    return {**body, "head_root": hash_v1(M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V2, body)}


def _read_head(
    path: Path,
    *,
    authority_verifier: M6MigrationAuthorityVerifierV1 | None = None,
    expected_head_root: object | None = None,
) -> M6MigrationDurableReopenV1:
    if path.is_symlink() or not path.is_file():
        raise M6MigrationDurableCorruptionError("migration HEAD is not a regular file")
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(path, os.O_RDONLY | nofollow)
    except OSError as exc:
        raise M6MigrationDurableCorruptionError(f"cannot open migration HEAD: {exc}") from exc
    try:
        size = os.fstat(fd).st_size
        if size > M6_MIGRATION_MAX_HEAD_BYTES_V1:
            raise M6MigrationDurableCorruptionError("migration HEAD exceeds size bound")
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            data = handle.read(M6_MIGRATION_MAX_HEAD_BYTES_V1 + 1)
    except OSError as exc:
        raise M6MigrationDurableCorruptionError(f"cannot read migration HEAD: {exc}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
    if len(data) > M6_MIGRATION_MAX_HEAD_BYTES_V1:
        raise M6MigrationDurableCorruptionError("migration HEAD exceeds size bound")
    try:
        raw = json.loads(
            data.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
            parse_float=lambda _value: (_ for _ in ()).throw(ValueError("floats are forbidden")),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, TypeError, ValueError) as exc:
        raise M6MigrationDurableCorruptionError(f"invalid migration HEAD JSON: {exc}") from exc
    if not isinstance(raw, dict) or canonical_bytes_v1(raw) != data:
        raise M6MigrationDurableCorruptionError("migration HEAD is not canonical JSON")
    obj = _object(
        raw,
        name="migration HEAD",
        keys={"schema", "state_root", "state", "committed_steps", "head_root"},
    )
    if obj["schema"] == M6_MIGRATION_ADMISSION_SCHEMA_V1:
        raise M6MigrationDurableCorruptionError(
            "migration admission schema v1 is obsolete; rebuild the research head with schema v2"
        )
    if obj["schema"] != M6_MIGRATION_ADMISSION_SCHEMA_V2:
        raise M6MigrationDurableCorruptionError("migration HEAD schema mismatch")
    state = _decode_state(obj["state"])
    try:
        state_root = _canonical_root(obj["state_root"], name="migration HEAD state root")
        head_root = _canonical_root(obj["head_root"], name="migration HEAD root")
    except ValueError as exc:
        raise M6MigrationDurableCorruptionError(str(exc)) from exc
    if state_root != state.state_root:
        raise M6MigrationDurableCorruptionError("migration HEAD state root mismatch")
    body = {key: obj[key] for key in ("schema", "state_root", "state", "committed_steps")}
    if head_root != hash_v1(M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V2, body):
        raise M6MigrationDurableCorruptionError("migration HEAD hash mismatch")
    if expected_head_root is not None:
        try:
            normalized_expected_head = _canonical_root(
                expected_head_root,
                name="expected migration HEAD root",
            )
        except ValueError as exc:
            raise M6MigrationDurableCorruptionError(str(exc)) from exc
        if head_root != normalized_expected_head:
            raise M6MigrationDurableCorruptionError(
                "migration HEAD is stale relative to external anchor"
            )
    raw_steps = obj["committed_steps"]
    if not isinstance(raw_steps, list):
        raise M6MigrationDurableCorruptionError("migration committed steps must be a list")
    if len(raw_steps) > M6_MIGRATION_MAX_HISTORY_STEPS_V1:
        raise M6MigrationDurableCorruptionError("migration step history exceeds size bound")
    committed_steps = tuple(
        _decode_committed_step(item, index=index) for index, item in enumerate(raw_steps)
    )
    _validate_history(state, committed_steps, authority_verifier)
    return M6MigrationDurableReopenV1(
        state=state,
        committed_steps=committed_steps,
        head_root=head_root,
    )


def _fsync_directory(path: Path) -> None:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    try:
        fd = os.open(path, flags)
    except OSError as exc:
        raise M6MigrationDurableCorruptionError(
            f"cannot open migration directory for fsync: {exc}"
        ) from exc
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _write_head(path: Path, state: M6MigrationStateV1, committed_steps: tuple[M6MigrationCommittedStepV1, ...]) -> None:
    document = _head_document(state, committed_steps)
    data = canonical_bytes_v1(document)
    if len(data) > M6_MIGRATION_MAX_HEAD_BYTES_V1:
        raise M6MigrationDurableCorruptionError("migration HEAD exceeds size bound")
    if path.is_symlink():
        raise M6MigrationDurableCorruptionError("migration HEAD must not be a symlink")
    fd, temp_name = tempfile.mkstemp(prefix=".m6-migration-head.", suffix=".tmp", dir=path.parent)
    temp_path = Path(temp_name)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_path, path)
        _fsync_directory(path.parent)
    except OSError as exc:
        raise M6MigrationDurableCorruptionError(f"cannot install migration HEAD: {exc}") from exc
    finally:
        if temp_path.exists() or temp_path.is_symlink():
            temp_path.unlink()


def _external_anchor_document(head_root: str) -> dict[str, object]:
    normalized = _canonical_root(head_root, name="migration external anchor HEAD root")
    body = {
        "schema": M6_MIGRATION_EXTERNAL_ANCHOR_SCHEMA_V1,
        "head_root": normalized,
    }
    return {
        **body,
        "anchor_root": hash_v1(M6_MIGRATION_EXTERNAL_ANCHOR_DOMAIN_V1, body),
    }


def _read_external_anchor(path: Path) -> str:
    if path.is_symlink() or not path.is_file():
        raise M6MigrationDurableCorruptionError(
            "migration external anchor is not a regular file"
        )
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(path, os.O_RDONLY | nofollow)
    except OSError as exc:
        raise M6MigrationDurableCorruptionError(
            f"cannot open migration external anchor: {exc}"
        ) from exc
    try:
        if os.fstat(fd).st_size > M6_MIGRATION_MAX_EXTERNAL_ANCHOR_BYTES_V1:
            raise M6MigrationDurableCorruptionError(
                "migration external anchor exceeds size bound"
            )
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            data = handle.read(M6_MIGRATION_MAX_EXTERNAL_ANCHOR_BYTES_V1 + 1)
    except OSError as exc:
        raise M6MigrationDurableCorruptionError(
            f"cannot read migration external anchor: {exc}"
        ) from exc
    finally:
        if fd >= 0:
            os.close(fd)
    if len(data) > M6_MIGRATION_MAX_EXTERNAL_ANCHOR_BYTES_V1:
        raise M6MigrationDurableCorruptionError(
            "migration external anchor exceeds size bound"
        )
    try:
        raw = json.loads(
            data.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
            parse_float=lambda _value: (_ for _ in ()).throw(
                ValueError("floats are forbidden")
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, TypeError, ValueError) as exc:
        raise M6MigrationDurableCorruptionError(
            f"invalid migration external anchor JSON: {exc}"
        ) from exc
    if not isinstance(raw, dict) or canonical_bytes_v1(raw) != data:
        raise M6MigrationDurableCorruptionError(
            "migration external anchor is not canonical JSON"
        )
    obj = _object(
        raw,
        name="migration external anchor",
        keys={"schema", "head_root", "anchor_root"},
    )
    if obj["schema"] != M6_MIGRATION_EXTERNAL_ANCHOR_SCHEMA_V1:
        raise M6MigrationDurableCorruptionError(
            "migration external anchor schema mismatch"
        )
    try:
        head_root = _canonical_root(
            obj["head_root"], name="migration external anchor HEAD root"
        )
        anchor_root = _canonical_root(
            obj["anchor_root"], name="migration external anchor root"
        )
    except ValueError as exc:
        raise M6MigrationDurableCorruptionError(str(exc)) from exc
    body = {"schema": obj["schema"], "head_root": obj["head_root"]}
    if anchor_root != hash_v1(M6_MIGRATION_EXTERNAL_ANCHOR_DOMAIN_V1, body):
        raise M6MigrationDurableCorruptionError(
            "migration external anchor hash mismatch"
        )
    return head_root


def _write_external_anchor(path: Path, head_root: str) -> None:
    document = _external_anchor_document(head_root)
    data = canonical_bytes_v1(document)
    if len(data) > M6_MIGRATION_MAX_EXTERNAL_ANCHOR_BYTES_V1:
        raise M6MigrationDurableCorruptionError(
            "migration external anchor exceeds size bound"
        )
    if path.is_symlink():
        raise M6MigrationDurableCorruptionError(
            "migration external anchor must not be a symlink"
        )
    fd, temp_name = tempfile.mkstemp(
        prefix=".m6-migration-anchor.",
        suffix=".tmp",
        dir=path.parent,
    )
    temp_path = Path(temp_name)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_path, path)
        _fsync_directory(path.parent)
    except OSError as exc:
        raise M6MigrationDurableCorruptionError(
            f"cannot install migration external anchor: {exc}"
        ) from exc
    finally:
        if temp_path.exists() or temp_path.is_symlink():
            temp_path.unlink()


@contextmanager
def _exclusive_lock(path: Path) -> Iterator[None]:
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | nofollow, 0o600)
    except OSError as exc:
        raise M6MigrationDurableCorruptionError(f"cannot open migration lock: {exc}") from exc
    try:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX)
        except OSError as exc:
            raise M6MigrationDurableCorruptionError(f"cannot lock migration store: {exc}") from exc
        yield
    finally:
        try:
            fcntl.flock(fd, fcntl.LOCK_UN)
        finally:
            os.close(fd)


class M6MigrationExternalHeadAnchorV1:
    """A separate fsynced root with compare-and-set semantics."""

    def __init__(self, path: str | os.PathLike[str]) -> None:
        if not isinstance(path, (str, os.PathLike)):
            raise TypeError("migration external anchor path must be path-like")
        self._path = Path(path)
        if self._path.is_symlink():
            raise M6MigrationDurableCorruptionError(
                "migration external anchor path must not be a symlink"
            )
        self._path.parent.mkdir(parents=True, exist_ok=True)
        self._lock = self._path.with_name(f".{self._path.name}.lock")

    @property
    def path(self) -> Path:
        return self._path

    def initialize(self, head_root: object) -> str:
        normalized = _canonical_root(
            head_root, name="migration external anchor HEAD root"
        )
        with _exclusive_lock(self._lock):
            if self._path.exists() or self._path.is_symlink():
                current = _read_external_anchor(self._path)
                if current != normalized:
                    raise M6MigrationDurableCorruptionError(
                        "migration external anchor is already bound to another HEAD"
                    )
                return current
            _write_external_anchor(self._path, normalized)
            return normalized

    def read(self) -> str:
        return _read_external_anchor(self._path)

    def compare_and_set(
        self,
        expected_head_root: object,
        new_result: object,
        *,
        store: "M6MigrationDurableStoreV1",
    ) -> bool:
        if not isinstance(new_result, M6MigrationAdmissionResultV1):
            raise TypeError("migration external anchor requires an admission result")
        if new_result.status not in (
            M6MigrationAdmissionStatusV1.COMMITTED,
            M6MigrationAdmissionStatusV1.ALREADY_COMMITTED,
        ):
            raise ValueError("migration external anchor requires a committed result")
        if not isinstance(store, M6MigrationDurableStoreV1):
            raise TypeError("migration external anchor store is invalid")
        store._assert_root_binding()
        if new_result.head_root is None or new_result.step_root is None:
            raise ValueError("migration external anchor result is incomplete")
        if new_result.pre_head_root is None:
            raise ValueError("migration external anchor result lacks a pre-HEAD root")
        expected = _canonical_root(
            expected_head_root, name="expected migration external anchor HEAD root"
        )
        new = _canonical_root(
            new_result.head_root, name="new migration external anchor HEAD root"
        )
        with _exclusive_lock(store._lock):
            validated = _read_head(
                store._head,
                authority_verifier=store._authority_verifier,
                expected_head_root=new,
            )
            if (
                validated.state != new_result.state
                or new_result.step_root
                not in {step.step_root for step in validated.committed_steps}
            ):
                raise M6MigrationDurableCorruptionError(
                    "migration external anchor result is not bound to the durable HEAD"
                )
            tail = validated.committed_steps[-1] if validated.committed_steps else None
            if new != expected and (
                tail is None
                or new_result.pre_head_root != expected
                or tail.pre_head_root != expected
                or tail.step_root != new_result.step_root
                or tail.pre_state_root != new_result.pre_state_root
                or tail.post_state_root != new_result.post_state_root
            ):
                raise M6MigrationDurableCorruptionError(
                    "migration external anchor result is not the exact next durable HEAD"
                )
            with _exclusive_lock(self._lock):
                current = _read_external_anchor(self._path)
                if current != expected:
                    return False
                if new == expected:
                    return True
                _write_external_anchor(self._path, new)
                return True


def _result(
    status: M6MigrationAdmissionStatusV1,
    state: M6MigrationStateV1,
    *,
    pre_state_root: str,
    step_root: str | None,
    reason: str | None = None,
    core_reject_code: M6MigrationRejectCodeV1 | None = None,
    head_root: str | None = None,
    pre_head_root: str | None = None,
) -> M6MigrationAdmissionResultV1:
    return M6MigrationAdmissionResultV1(
        status=status,
        state=state,
        pre_state_root=pre_state_root,
        post_state_root=state.state_root,
        step_root=step_root,
        reason=reason,
        core_reject_code=core_reject_code,
        head_root=head_root,
        pre_head_root=pre_head_root,
    )


class M6MigrationDurableStoreV1:
    """Filesystem-backed, fail-closed admission for one migration plan.

    ``require_external_anchor`` with a configured
    ``M6MigrationExternalHeadAnchorV1`` is the safe deployment profile.  The
    anchor is read and advanced by the admission wrapper, including
    indeterminate-commit recovery.  The research default remains permissive
    so existing local fixtures can reconstruct an unanchored history; those
    fixtures do not provide anti-rollback evidence.
    """

    def __init__(
        self,
        root: str | os.PathLike[str],
        *,
        initial_state: M6MigrationStateV1 | None = None,
        authority_verifier: M6MigrationAuthorityVerifierV1 | None = None,
        expected_head_root: object | None = None,
        require_external_anchor: bool = False,
        external_anchor: M6MigrationExternalHeadAnchorV1 | None = None,
    ) -> None:
        if not isinstance(root, (str, os.PathLike)):
            raise TypeError("migration store root must be path-like")
        if initial_state is not None and not isinstance(initial_state, M6MigrationStateV1):
            raise TypeError("migration initial state is invalid")
        if authority_verifier is not None and not isinstance(
            authority_verifier, M6MigrationAuthorityVerifierV1
        ):
            raise TypeError("migration authority verifier is invalid")
        if type(require_external_anchor) is not bool:
            raise TypeError("migration external-anchor profile must be bool")
        if external_anchor is not None and not isinstance(
            external_anchor, M6MigrationExternalHeadAnchorV1
        ):
            raise TypeError("migration external anchor is invalid")
        self._authority_verifier = authority_verifier
        self._require_external_anchor = require_external_anchor
        self._external_anchor = external_anchor
        self._root = Path(root)
        if self._root.is_symlink() or (self._root.exists() and not self._root.is_dir()):
            raise M6MigrationDurableCorruptionError("migration store root is not a directory")
        self._root.mkdir(parents=True, exist_ok=True)
        root_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
        try:
            self._root_fd = os.open(self._root, root_flags)
            self._root_stat = os.fstat(self._root_fd)
            current_root_stat = os.stat(self._root, follow_symlinks=False)
        except OSError as exc:
            raise M6MigrationDurableCorruptionError(
                f"cannot pin migration store root: {exc}"
            ) from exc
        if not os.path.samestat(self._root_stat, current_root_stat):
            os.close(self._root_fd)
            raise M6MigrationDurableCorruptionError(
                "migration store root changed during initialization"
            )
        self._bound_root = Path(f"/proc/self/fd/{self._root_fd}")
        self._head = self._bound_root / M6_MIGRATION_HEAD_FILE_V1
        self._lock = self._bound_root / M6_MIGRATION_LOCK_FILE_V1
        if self._head.exists() or self._head.is_symlink():
            current = self.reopen(expected_head_root=expected_head_root)
            if initial_state is not None and current.state != initial_state:
                raise ValueError("migration initial state conflicts with durable head")
        elif initial_state is not None:
            if expected_head_root is not None:
                raise M6MigrationDurableCorruptionError(
                    "cannot anchor a new migration store before HEAD exists"
                )
            if initial_state != M6MigrationStateV1.initial(
                initial_state.plan,
                branch_root=initial_state.branch_root,
            ):
                raise M6MigrationDurableCorruptionError(
                    "new migration store requires a genesis state with empty history"
                )
            if self._authority_verifier is not None and self._authority_verifier.authenticated:
                try:
                    self._authority_verifier.validate_plan_binding(initial_state.plan)
                except (
                    TypeError,
                    ValueError,
                    M6MigrationAuthorityVerifierUnavailableV1,
                    M6MigrationAuthorityProofRejectedV1,
                ) as exc:
                    raise M6MigrationDurableCorruptionError(
                        f"migration authority verifier is not bound to the initial plan: {exc}"
                    ) from exc
            with _exclusive_lock(self._lock):
                self._assert_root_binding()
                if self._head.exists() or self._head.is_symlink():
                    current = _read_head(
                        self._head,
                        authority_verifier=self._authority_verifier,
                        expected_head_root=expected_head_root,
                    )
                    if current.state != initial_state:
                        raise ValueError("migration initial state conflicts with durable head")
                else:
                    _write_head(self._head, initial_state, ())
                    if self._external_anchor is not None:
                        genesis = _read_head(
                            self._head,
                            authority_verifier=self._authority_verifier,
                        )
                        self._external_anchor.initialize(genesis.head_root)
        else:
            raise M6MigrationDurableCorruptionError("migration head is missing")

    def _assert_root_binding(self) -> None:
        """Reject a pathname replacement instead of following a new root."""

        try:
            current_root_stat = os.stat(self._root, follow_symlinks=False)
        except OSError as exc:
            raise M6MigrationDurableCorruptionError(
                f"cannot revalidate migration store root: {exc}"
            ) from exc
        if not os.path.samestat(self._root_stat, current_root_stat):
            raise M6MigrationDurableCorruptionError(
                "migration store root changed after initialization"
            )
        try:
            pinned_root_stat = os.fstat(self._root_fd)
        except OSError as exc:
            raise M6MigrationDurableCorruptionError(
                f"cannot restat pinned migration store root: {exc}"
            ) from exc
        if not os.path.samestat(self._root_stat, pinned_root_stat):
            raise M6MigrationDurableCorruptionError(
                "pinned migration store root changed unexpectedly"
            )

    def __del__(self) -> None:
        root_fd = getattr(self, "_root_fd", -1)
        if isinstance(root_fd, int) and root_fd >= 0:
            try:
                os.close(root_fd)
            except OSError:
                pass

    @property
    def root(self) -> Path:
        return self._root

    def reopen(
        self,
        *,
        expected_head_root: object | None = None,
    ) -> M6MigrationDurableReopenV1:
        self._assert_root_binding()
        if self._external_anchor is not None:
            anchor_root = self._external_anchor.read()
            if expected_head_root is None:
                expected_head_root = anchor_root
            elif _canonical_root(
                expected_head_root,
                name="expected migration HEAD root",
            ) != anchor_root:
                raise M6MigrationDurableCorruptionError(
                    "expected migration HEAD root disagrees with the external anchor"
                )
        if self._require_external_anchor and expected_head_root is None:
            raise M6MigrationDurableCorruptionError(
                "external migration HEAD anchor is required"
            )
        return _read_head(
            self._head,
            authority_verifier=self._authority_verifier,
            expected_head_root=expected_head_root,
        )

    def admit(
        self,
        expected_state_root: object,
        verified_step: object,
        *,
        expected_head_root: object | None = None,
    ) -> M6MigrationAdmissionResultV1:
        """Admit through the configured external-anchor profile when present."""

        if self._external_anchor is not None:
            return self.admit_with_external_anchor(
                expected_state_root,
                verified_step,
                external_anchor=self._external_anchor,
                expected_head_root=expected_head_root,
            )
        if self._require_external_anchor and self._external_anchor is None:
            raise M6MigrationDurableCorruptionError(
                "configured external anchor is required for safe admission"
            )
        return self._admit_unanchored(
            expected_state_root,
            verified_step,
            expected_head_root=expected_head_root,
        )

    def _admit_unanchored(
        self,
        expected_state_root: object,
        verified_step: object,
        *,
        expected_head_root: object | None = None,
    ) -> M6MigrationAdmissionResultV1:
        """Install one step under the local HEAD lock.

        This is an internal phase of the anchored adapter.  Callers use
        ``admit`` so an external anchor cannot be bypassed accidentally.
        """

        self._assert_root_binding()
        with _exclusive_lock(self._lock):
            self._assert_root_binding()
            current = _read_head(
                self._head,
                authority_verifier=self._authority_verifier,
                expected_head_root=expected_head_root,
            )
            state = current.state
            if not isinstance(expected_state_root, str):
                return _result(
                    M6MigrationAdmissionStatusV1.REJECTED,
                    state,
                    pre_state_root=state.state_root,
                    step_root=None,
                    reason="expected state root must be a string",
                )
            try:
                normalized_expected = _canonical_root(
                    expected_state_root, name="expected migration state root"
                )
            except ValueError as exc:
                return _result(
                    M6MigrationAdmissionStatusV1.REJECTED,
                    state,
                    pre_state_root=state.state_root,
                    step_root=None,
                    reason=str(exc),
                )
            if not isinstance(verified_step, M6MigrationVerifiedAdmissionV1):
                return _result(
                    M6MigrationAdmissionStatusV1.REJECTED,
                    state,
                    pre_state_root=state.state_root,
                    step_root=None,
                    reason="migration admission requires a verifier-created step and receipt",
                )
            if self._authority_verifier is None or not self._authority_verifier.authenticated:
                return _result(
                    M6MigrationAdmissionStatusV1.REJECTED,
                    state,
                    pre_state_root=state.state_root,
                    step_root=None,
                    reason="migration admission requires an authenticated verifier",
                )
            evidence = verified_step
            step_root = evidence.verified_step.step.step_root
            identity = (step_root, evidence.verified_step.branch_root)
            for index, committed in enumerate(current.committed_steps):
                if committed.identity == identity:
                    if (
                        normalized_expected == committed.pre_state_root
                        and not any(
                            later.step.kind is M6MigrationStepKindV1.ROLLBACK
                            for later in current.committed_steps[index + 1 :]
                        )
                    ):
                        try:
                            checked_step = self._authority_verifier.reverify_step(
                                state.plan,
                                evidence.verified_step.step,
                                evidence.verified_step.branch_root,
                                evidence.receipt,
                                pre_state_root=committed.pre_state_root,
                                pre_phase=evidence.verified_step.pre_phase,
                            )
                        except (
                            TypeError,
                            ValueError,
                            M6MigrationAuthorityProofRejectedV1,
                        ) as exc:
                            return _result(
                                M6MigrationAdmissionStatusV1.REJECTED,
                                state,
                                pre_state_root=state.state_root,
                                step_root=step_root,
                                reason=f"migration authority receipt rejected: {exc}",
                            )
                        if (
                            checked_step.step != evidence.verified_step.step
                            or checked_step.branch_root != evidence.verified_step.branch_root
                            or checked_step.receipt_root != evidence.verified_step.receipt_root
                            or checked_step.receipt_root != committed.receipt_root
                            or checked_step.pre_state_root != evidence.verified_step.pre_state_root
                            or checked_step.pre_phase is not evidence.verified_step.pre_phase
                        ):
                            return _result(
                                M6MigrationAdmissionStatusV1.REJECTED,
                                state,
                                pre_state_root=state.state_root,
                                step_root=step_root,
                                reason="migration verifier replay does not match the committed witness",
                            )
                        return _result(
                            M6MigrationAdmissionStatusV1.ALREADY_COMMITTED,
                            state,
                            pre_state_root=committed.pre_state_root,
                            step_root=step_root,
                            head_root=current.head_root,
                            pre_head_root=committed.pre_head_root,
                        )
                    return _result(
                        M6MigrationAdmissionStatusV1.REJECTED,
                        state,
                        pre_state_root=state.state_root,
                        step_root=step_root,
                        reason="migration step is already committed on this branch",
                    )
            if evidence.verified_step.branch_root != state.branch_root:
                return _result(
                    M6MigrationAdmissionStatusV1.REJECTED,
                    state,
                    pre_state_root=state.state_root,
                    step_root=step_root,
                    reason="migration verifier branch does not match the current state",
                )
            try:
                checked_step = self._authority_verifier.reverify_step(
                    state.plan,
                    evidence.verified_step.step,
                    evidence.verified_step.branch_root,
                    evidence.receipt,
                    pre_state_root=state.state_root,
                    pre_phase=state.phase,
                )
            except (TypeError, ValueError, M6MigrationAuthorityProofRejectedV1) as exc:
                return _result(
                    M6MigrationAdmissionStatusV1.REJECTED,
                    state,
                    pre_state_root=state.state_root,
                    step_root=step_root,
                    reason=f"migration authority receipt rejected: {exc}",
                )
            if (
                checked_step.step != evidence.verified_step.step
                or checked_step.branch_root != evidence.verified_step.branch_root
                or checked_step.receipt_root != evidence.verified_step.receipt_root
                or checked_step.pre_state_root != evidence.verified_step.pre_state_root
                or checked_step.pre_phase is not evidence.verified_step.pre_phase
            ):
                return _result(
                    M6MigrationAdmissionStatusV1.REJECTED,
                    state,
                    pre_state_root=state.state_root,
                    step_root=step_root,
                    reason="migration verifier replay does not match the admission witness",
                )
            if normalized_expected != state.state_root:
                return _result(
                    M6MigrationAdmissionStatusV1.STALE_STATE,
                    state,
                    pre_state_root=state.state_root,
                    step_root=step_root,
                    reason="expected migration state root is stale",
                )
            transition = step_m6_migration_v1(state, evidence.verified_step)
            if not isinstance(transition, M6MigrationAcceptedV1):
                return _result(
                    M6MigrationAdmissionStatusV1.REJECTED,
                    state,
                    pre_state_root=state.state_root,
                    step_root=step_root,
                    reason=transition.reason,
                    core_reject_code=transition.code,
                )
            committed_step = M6MigrationCommittedStepV1(
                step=evidence.verified_step.step,
                receipt_root=evidence.verified_step.receipt_root,
                authority_receipt=evidence.receipt,
                branch_root=evidence.verified_step.branch_root,
                pre_head_root=current.head_root,
                pre_state_root=state.state_root,
                post_state_root=transition.post_state.state_root,
            )
            committed_steps = (*current.committed_steps, committed_step)
            _write_head(self._head, transition.post_state, committed_steps)
            reopened = _read_head(
                self._head,
                authority_verifier=self._authority_verifier,
            )
            if reopened.state != transition.post_state:
                raise M6MigrationDurableCorruptionError(
                    "migration HEAD changed during admission installation"
                )
            return _result(
                M6MigrationAdmissionStatusV1.COMMITTED,
                reopened.state,
                pre_state_root=state.state_root,
                step_root=step_root,
                head_root=reopened.head_root,
                pre_head_root=current.head_root,
            )

    def recover_indeterminate_commit(
        self,
        expected_head_root: object,
        step_root: object,
    ) -> M6MigrationDurableRecoveryV1:
        """Recover a step after the local install returned an indeterminate error.

        The step root and its committed pre-state root must identify the exact
        transition that was expected at the externally anchored HEAD.  The
        method validates the complete current history before returning the
        newer HEAD so the caller can advance its external anchor.
        """

        expected = _canonical_root(
            expected_head_root, name="expected migration recovery HEAD root"
        )
        expected_step = _canonical_root(
            step_root, name="expected migration recovery step root"
        )
        self._assert_root_binding()
        with _exclusive_lock(self._lock):
            self._assert_root_binding()
            current = _read_head(
                self._head,
                authority_verifier=self._authority_verifier,
            )
            matches = tuple(
                committed
                for committed in current.committed_steps
                if committed.step_root == expected_step
                and committed.pre_head_root == expected
            )
            if (
                len(matches) != 1
                or not current.committed_steps
                or current.committed_steps[-1] is not matches[0]
            ):
                raise M6MigrationDurableCorruptionError(
                    "indeterminate migration commit is not the durable HEAD tail"
                )
            return M6MigrationDurableRecoveryV1(current, matches[0])

    def admit_with_external_anchor(
        self,
        expected_state_root: object,
        verified_step: object,
        *,
        external_anchor: M6MigrationExternalHeadAnchorV1,
        expected_head_root: object | None = None,
    ) -> M6MigrationAdmissionResultV1:
        """Admit and advance an external anchor with indeterminate recovery."""

        self._assert_root_binding()
        if not isinstance(external_anchor, M6MigrationExternalHeadAnchorV1):
            raise TypeError("migration external anchor is invalid")
        if self._require_external_anchor and self._external_anchor is None:
            raise M6MigrationDurableCorruptionError(
                "configured external anchor is required for safe admission"
            )
        if self._external_anchor is not None and external_anchor is not self._external_anchor:
            raise M6MigrationDurableCorruptionError(
                "migration admission anchor is not the configured external anchor"
            )
        anchored_head_root = external_anchor.read()
        if expected_head_root is not None and _canonical_root(
            expected_head_root,
            name="expected migration external anchor HEAD root",
        ) != anchored_head_root:
            raise M6MigrationDurableCorruptionError(
                "expected migration HEAD root disagrees with the external anchor"
            )
        expected_head_root = anchored_head_root
        if not isinstance(verified_step, M6MigrationVerifiedAdmissionV1):
            return self._admit_unanchored(
                expected_state_root,
                verified_step,
                expected_head_root=expected_head_root,
            )
        step_root = verified_step.verified_step.step.step_root
        try:
            result = self._admit_unanchored(
                expected_state_root,
                verified_step,
                expected_head_root=expected_head_root,
            )
        except M6MigrationDurableCorruptionError as original_error:
            try:
                recovery = self.recover_indeterminate_commit(
                    expected_head_root,
                    step_root,
                )
            except M6MigrationDurableCorruptionError as recovery_error:
                raise recovery_error from original_error
            recovered = _result(
                M6MigrationAdmissionStatusV1.ALREADY_COMMITTED,
                recovery.reopened.state,
                pre_state_root=recovery.committed_step.pre_state_root,
                step_root=recovery.committed_step.step_root,
                head_root=recovery.reopened.head_root,
                pre_head_root=recovery.committed_step.pre_head_root,
            )
            result = recovered
        if result.head_root is not None and result.status in (
            M6MigrationAdmissionStatusV1.COMMITTED,
            M6MigrationAdmissionStatusV1.ALREADY_COMMITTED,
        ):
            if not external_anchor.compare_and_set(
                expected_head_root,
                result,
                store=self,
            ):
                if external_anchor.read() != result.head_root:
                    raise M6MigrationDurableCorruptionError(
                        "migration external anchor changed during admission recovery"
                    )
        return result


@dataclass(frozen=True, slots=True)
class M6MigrationWriterCommitResultV1:
    """The writer gate result paired with the one migration commit result."""

    writer_admission: M6MigrationWriterAdmissionResultV1
    migration_admission: M6MigrationAdmissionResultV1 | None

    def __post_init__(self) -> None:
        if not isinstance(
            self.writer_admission,
            M6MigrationWriterAdmissionResultV1,
        ):
            raise TypeError("migration writer commit admission is invalid")
        if (
            self.writer_admission.status is M6MigrationWriterAdmissionStatusV1.REJECTED
            and self.migration_admission is not None
        ):
            raise ValueError("rejected migration writer cannot carry a commit result")
        if (
            self.writer_admission.status is M6MigrationWriterAdmissionStatusV1.ALLOWED
            and not isinstance(self.migration_admission, M6MigrationAdmissionResultV1)
        ):
            raise ValueError("allowed migration writer requires a commit result")


class M6MigrationWriterConsumerV1:
    """Reauthorize a writer against the current HEAD before one atomic admit.

    The consumer accepts identity and proof inputs.  It does not accept a
    caller-authored authorization object as authority.  The supplied
    ``M6MigrationWriterAdmissionResultV1`` compatibility method is checked for
    freshness, then the membership verifier is run again from the current
    durable state before the store's compare-and-swap admission.
    """

    def __init__(
        self,
        store: M6MigrationDurableStoreV1,
        membership_verifier: M6MigrationWriterMembershipVerifierV1,
    ) -> None:
        if not isinstance(store, M6MigrationDurableStoreV1):
            raise TypeError("migration writer consumer store is invalid")
        if type(membership_verifier) is not M6MigrationWriterMembershipVerifierV1:
            raise TypeError("migration writer consumer verifier is invalid")
        self._store = store
        self._membership_verifier = membership_verifier

    @staticmethod
    def _rejected(
        state: M6MigrationStateV1,
        reason: str,
    ) -> M6MigrationWriterCommitResultV1:
        return M6MigrationWriterCommitResultV1(
            writer_admission=M6MigrationWriterAdmissionResultV1(
                M6MigrationWriterAdmissionStatusV1.REJECTED,
                state.active_subject_root,
                state.active_writer_epoch,
                reason=reason,
            ),
            migration_admission=None,
        )

    def _authorize_current(
        self,
        *,
        writer_subject_root: object,
        writer_epoch: object,
        membership_proof: object,
    ) -> tuple[M6MigrationDurableReopenV1, M6MigrationWriterAdmissionResultV1]:
        current = self._store.reopen()
        writer_admission = authorize_m6_migration_writer_v1(
            current.state,
            writer_subject_root=writer_subject_root,
            writer_epoch=writer_epoch,
            allowed_writer_set_root=current.state.plan.allowed_writer_set_root,
            membership_verifier=self._membership_verifier,
            membership_proof=membership_proof,
        )
        return current, writer_admission

    def admit(
        self,
        *,
        writer_subject_root: object,
        writer_epoch: object,
        membership_proof: object,
        expected_state_root: object,
        verified_step: object,
    ) -> M6MigrationWriterCommitResultV1:
        """Authorize from current state, then use the store commit port once."""

        current, writer_admission = self._authorize_current(
            writer_subject_root=writer_subject_root,
            writer_epoch=writer_epoch,
            membership_proof=membership_proof,
        )
        if writer_admission.status is M6MigrationWriterAdmissionStatusV1.REJECTED:
            return M6MigrationWriterCommitResultV1(writer_admission, None)
        try:
            expected = _canonical_root(
                expected_state_root,
                name="expected migration writer commit state root",
            )
        except ValueError:
            return self._rejected(current.state, "writer authorization is stale at commit root")
        if expected != current.state.state_root:
            return self._rejected(current.state, "writer authorization is stale at commit root")
        migration_admission = self._store.admit(
            expected_state_root,
            verified_step,
        )
        return M6MigrationWriterCommitResultV1(
            writer_admission,
            migration_admission,
        )

    def admit_from_authorization(
        self,
        writer_admission: object,
        *,
        membership_proof: object,
        expected_state_root: object,
        verified_step: object,
    ) -> M6MigrationWriterCommitResultV1:
        """Recheck a legacy authorization claim instead of trusting it."""

        current = self._store.reopen()
        if not isinstance(writer_admission, M6MigrationWriterAdmissionResultV1):
            return self._rejected(current.state, "writer admission is not a typed result")
        if writer_admission.status is not M6MigrationWriterAdmissionStatusV1.ALLOWED:
            return self._rejected(current.state, "writer admission is not allowed")
        authorization = writer_admission.authorization
        if authorization is None or authorization.state_root != current.state.state_root:
            return self._rejected(current.state, "writer authorization is stale")
        try:
            expected = _canonical_root(
                expected_state_root,
                name="expected migration writer commit state root",
            )
        except ValueError:
            return self._rejected(current.state, "writer authorization is stale at commit root")
        if expected != current.state.state_root:
            return self._rejected(current.state, "writer authorization is stale at commit root")
        rechecked = authorize_m6_migration_writer_v1(
            current.state,
            writer_subject_root=authorization.active_subject_root,
            writer_epoch=authorization.active_writer_epoch,
            allowed_writer_set_root=current.state.plan.allowed_writer_set_root,
            membership_verifier=self._membership_verifier,
            membership_proof=membership_proof,
        )
        if (
            rechecked.status
            is M6MigrationWriterAdmissionStatusV1.ALLOWED
            and (
                writer_admission.membership_receipt_root
                != rechecked.membership_receipt_root
                or authorization.membership_receipt_root
                != rechecked.membership_receipt_root
            )
        ):
            return self._rejected(
                current.state,
                "writer authorization is not verifier-derived",
            )
        if rechecked.status is M6MigrationWriterAdmissionStatusV1.REJECTED:
            return M6MigrationWriterCommitResultV1(rechecked, None)
        migration_admission = self._store.admit(
            expected_state_root,
            verified_step,
        )
        return M6MigrationWriterCommitResultV1(rechecked, migration_admission)


def authorize_m6_migration_writer_v1(
    state: M6MigrationStateV1,
    *,
    writer_subject_root: object,
    writer_epoch: object,
    allowed_writer_set_root: object,
    membership_verifier: M6MigrationWriterMembershipVerifierV1 | None = None,
    membership_proof: object | None = None,
) -> M6MigrationWriterAdmissionResultV1:
    """Authorize a writer only after an authenticated membership receipt.

    Epoch, subject, and writer-set checks are necessary profile checks.  The
    external membership verifier is also required; a profile match alone is
    never an ``ALLOWED`` result.
    """

    if not isinstance(state, M6MigrationStateV1):
        raise TypeError("migration writer state is invalid")
    if not isinstance(writer_subject_root, str):
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason="writer subject root must be a string",
        )
    if (
        type(writer_epoch) is not int
        or writer_epoch < 0
        or writer_epoch > M6_MIGRATION_MAX_WRITER_EPOCH_V1
    ):
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason="writer epoch must be a u64",
        )
    if not isinstance(allowed_writer_set_root, str):
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason="allowed writer set root must be a string",
        )
    try:
        writer_set_root = _canonical_root(
            allowed_writer_set_root,
            name="allowed writer set root",
        )
    except ValueError as exc:
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason=str(exc),
        )
    if writer_set_root != state.plan.allowed_writer_set_root:
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason="allowed writer set root is not bound to the migration plan",
        )
    try:
        subject = _canonical_root(writer_subject_root, name="writer subject root")
    except ValueError as exc:
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason=str(exc),
        )
    if subject != state.active_subject_root or writer_epoch != state.active_writer_epoch:
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason="writer subject or epoch is not the active authority",
        )
    if state.legacy_writes_enabled == state.target_writes_enabled:
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason="migration writer flags are not exclusive",
        )
    if not isinstance(membership_verifier, M6MigrationWriterMembershipVerifierV1):
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason="authenticated writer membership proof is required",
        )
    if type(membership_verifier) is not M6MigrationWriterMembershipVerifierV1:
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason="authenticated writer membership proof is required",
        )
    if not membership_verifier.authenticated:
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason="authenticated writer membership proof is required",
        )
    try:
        owned_membership_proof = M6MigrationWriterMembershipProofV1.from_value(
            membership_proof
        )
    except (TypeError, ValueError) as exc:
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason=str(exc),
        )
    try:
        membership_receipt = membership_verifier.verify_writer_membership(
            state,
            writer_subject_root=subject,
            writer_epoch=writer_epoch,
            membership_proof=owned_membership_proof,
        )
    except (
        TypeError,
        ValueError,
        M6MigrationAuthorityVerifierUnavailableV1,
        M6MigrationAuthorityProofRejectedV1,
    ) as exc:
        return M6MigrationWriterAdmissionResultV1(
            M6MigrationWriterAdmissionStatusV1.REJECTED,
            state.active_subject_root,
            state.active_writer_epoch,
            reason=f"writer membership proof rejected: {exc}",
        )
    return M6MigrationWriterAdmissionResultV1(
        M6MigrationWriterAdmissionStatusV1.ALLOWED,
        state.active_subject_root,
        state.active_writer_epoch,
        membership_receipt_root=membership_receipt.receipt_root,
        authorization=M6MigrationWriterAuthorizationV1(
            _M6_MIGRATION_WRITER_AUTHORIZATION_TOKEN,
            plan_root=state.plan.plan_root,
            state_root=state.state_root,
            active_subject_root=state.active_subject_root,
            active_writer_epoch=state.active_writer_epoch,
            allowed_writer_set_root=state.plan.allowed_writer_set_root,
            membership_receipt_root=membership_receipt.receipt_root,
        ),
    )


__all__ = [
    "M6_MIGRATION_ADMISSION_SCHEMA_V1",
    "M6_MIGRATION_ADMISSION_SCHEMA_V2",
    "M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V1",
    "M6_MIGRATION_ADMISSION_HEAD_DOMAIN_V2",
    "M6_MIGRATION_HEAD_FILE_V1",
    "M6_MIGRATION_EXTERNAL_ANCHOR_SCHEMA_V1",
    "M6_MIGRATION_EXTERNAL_ANCHOR_DOMAIN_V1",
    "M6MigrationDurableCorruptionError",
    "M6MigrationAdmissionStatusV1",
    "M6MigrationWriterAdmissionStatusV1",
    "M6MigrationWriterAuthorizationV1",
    "M6MigrationCommittedStepV1",
    "M6MigrationDurableReopenV1",
    "M6MigrationDurableRecoveryV1",
    "M6MigrationAdmissionResultV1",
    "M6MigrationWriterAdmissionResultV1",
    "M6MigrationWriterCommitResultV1",
    "M6MigrationWriterConsumerV1",
    "M6MigrationExternalHeadAnchorV1",
    "M6MigrationDurableStoreV1",
    "authorize_m6_migration_writer_v1",
]
