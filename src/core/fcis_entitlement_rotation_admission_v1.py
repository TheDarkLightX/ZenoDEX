"""Typed unmounted C06 rotation and migration admission checks."""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, final

from ..state.canonical import hex_to_bytes_fixed
from .fcis_entitlement_key_v1 import _require_bounded_text_v1
from .fcis_entitlement_migration_values_v1 import EntitlementStateV1
from .fcis_entitlement_transport_v1 import (
    C04TransportRejectV1,
    transport_srgd_to_agqe_v1,
)


class C06RotationCodeV1(Enum):
    """Fail-closed rejection classes for ordinary rotation checks."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_SNAPSHOT = "invalid_snapshot"
    KEY_CHANGED = "key_changed"
    REPRESENTATION_CHANGED = "representation_changed"
    HISTORY_CHANGED = "history_changed"


class C06AuthorityCodeV1(Enum):
    """Fail-closed rejection classes for deployment-bound migration checks."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_CONTEXT = "invalid_context"
    DEPLOYMENT_MISMATCH = "deployment_mismatch"
    SOURCE_EPOCH_MISMATCH = "source_epoch_mismatch"
    CURRENT_STATE_MISMATCH = "current_state_mismatch"
    TRANSPORT_REJECT = "transport_reject"


@final
@dataclass(frozen=True, slots=True)
class C06RotationRejectV1:
    """Typed rejection for an ordinary rotation history check."""

    code: C06RotationCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not C06RotationCodeV1:
            raise TypeError("C06 rotation reject code must be exact")
        if type(self.path) is not tuple or any(
            type(part) is not str for part in self.path
        ):
            raise TypeError("C06 rotation reject path must be an exact tuple")


@final
@dataclass(frozen=True, slots=True)
class C06AuthorityRejectV1:
    """Typed rejection for deployment-bound migration admission."""

    code: C06AuthorityCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not C06AuthorityCodeV1:
            raise TypeError("C06 authority reject code must be exact")
        if type(self.path) is not tuple or any(
            type(part) is not str for part in self.path
        ):
            raise TypeError("C06 authority reject path must be an exact tuple")


@final
@dataclass(frozen=True, slots=True)
class C06OperationalConfigurationV1:
    """Rotation-only configuration excluded from the C02 entitlement key."""

    policy_weights: tuple[int, int, int]
    destinations: tuple[str, str, str]
    custody_account: str

    def __post_init__(self) -> None:
        if type(self.policy_weights) is not tuple or len(self.policy_weights) != 3:
            raise TypeError("C06 policy weights must be an exact three-tuple")
        for weight in self.policy_weights:
            if type(weight) is not int or weight < 0:
                raise ValueError("C06 policy weights must be nonnegative integers")
        if type(self.destinations) is not tuple or len(self.destinations) != 3:
            raise TypeError("C06 destinations must be an exact three-tuple")
        for index, destination in enumerate(self.destinations):
            _require_bounded_text_v1(f"C06 destination[{index}]", destination)
        _require_bounded_text_v1("C06 custody account", self.custody_account)


@final
@dataclass(frozen=True, slots=True)
class C06RotationSnapshotV1:
    """A state plus ordinary configuration at one rotation boundary."""

    state: EntitlementStateV1
    configuration: C06OperationalConfigurationV1

    def __post_init__(self) -> None:
        if type(self.state) is not EntitlementStateV1:
            raise TypeError("C06 snapshot state must be exact")
        if type(self.configuration) is not C06OperationalConfigurationV1:
            raise TypeError("C06 snapshot configuration must be exact")
        self.state.__post_init__()
        self.configuration.__post_init__()


@final
@dataclass(frozen=True, slots=True)
class C06AuthorityContextV1:
    """Current-state context used by the unmounted authority comparison."""

    deployment_id: str
    authority_epoch_root: str
    state: EntitlementStateV1

    def __post_init__(self) -> None:
        _require_bounded_text_v1("C06 deployment ID", self.deployment_id)
        if type(self.authority_epoch_root) is not str:
            raise TypeError("C06 authority epoch root must be an exact string")
        hex_to_bytes_fixed(
            self.authority_epoch_root,
            nbytes=32,
            name="C06 authority epoch root",
        )
        if type(self.state) is not EntitlementStateV1:
            raise TypeError("C06 authority state must be exact")
        self.state.__post_init__()


@final
@dataclass(frozen=True, slots=True)
class C06MigrationAcceptedV1:
    """A check result, not a production authority witness."""

    deployment_id: str
    source_state_root: str
    target_state_root: str
    source_authority_epoch_root: str
    target_authority_epoch_root: str

    def __post_init__(self) -> None:
        _require_bounded_text_v1("C06 accepted deployment ID", self.deployment_id)
        for name, value in (
            ("C06 source state root", self.source_state_root),
            ("C06 target state root", self.target_state_root),
            (
                "C06 source authority epoch root",
                self.source_authority_epoch_root,
            ),
            (
                "C06 target authority epoch root",
                self.target_authority_epoch_root,
            ),
        ):
            if type(value) is not str:
                raise TypeError(f"{name} must be an exact string")
            hex_to_bytes_fixed(value, nbytes=32, name=name)


C06RotationCheckResultV1: TypeAlias = C06RotationRejectV1 | None
C06AuthorityCheckResultV1: TypeAlias = (
    C06MigrationAcceptedV1 | C06AuthorityRejectV1
)


def _rotation_reject(
    code: C06RotationCodeV1,
    *path: str,
) -> C06RotationRejectV1:
    return C06RotationRejectV1(code, path)


def _authority_reject(
    code: C06AuthorityCodeV1,
    *path: str,
) -> C06AuthorityRejectV1:
    return C06AuthorityRejectV1(code, path)


def _validated_snapshot(
    value: object,
) -> C06RotationSnapshotV1 | C06RotationRejectV1:
    if type(value) is not C06RotationSnapshotV1:
        return _rotation_reject(C06RotationCodeV1.WRONG_EXACT_TYPE, "snapshot")
    snapshot = value
    try:
        snapshot.__post_init__()
    except (TypeError, ValueError):
        return _rotation_reject(C06RotationCodeV1.INVALID_SNAPSHOT, "snapshot")
    return snapshot


def check_rotation_preserves_history_v1(
    before: object,
    after: object,
) -> C06RotationCheckResultV1:
    """Accept ordinary policy/destination/custody rotation only on exact history."""

    before_result = _validated_snapshot(before)
    if type(before_result) is C06RotationRejectV1:
        return before_result
    after_result = _validated_snapshot(after)
    if type(after_result) is C06RotationRejectV1:
        return after_result
    before_snapshot = before_result
    after_snapshot = after_result
    if before_snapshot.state.key != after_snapshot.state.key:
        return _rotation_reject(C06RotationCodeV1.KEY_CHANGED, "after", "state", "key")
    if (
        before_snapshot.state.representation_id
        != after_snapshot.state.representation_id
    ):
        return _rotation_reject(
            C06RotationCodeV1.REPRESENTATION_CHANGED,
            "after",
            "state",
            "representation_id",
        )
    if before_snapshot.state.entries != after_snapshot.state.entries:
        return _rotation_reject(
            C06RotationCodeV1.HISTORY_CHANGED,
            "after",
            "state",
            "entries",
        )
    return None


def _validated_context(
    value: object,
    path: str,
) -> C06AuthorityContextV1 | C06AuthorityRejectV1:
    if type(value) is not C06AuthorityContextV1:
        return _authority_reject(C06AuthorityCodeV1.WRONG_EXACT_TYPE, path)
    context = value
    try:
        context.__post_init__()
    except (TypeError, ValueError):
        return _authority_reject(C06AuthorityCodeV1.INVALID_CONTEXT, path)
    return context


def check_representation_migration_authority_v1(
    current_context: object,
    source_context: object,
    target_context: object,
) -> C06AuthorityCheckResultV1:
    """Check deployment/current-state binding before applying C04 transport.

    The returned accepted value is an unmounted check result. It is deliberately
    not an authority constructor and does not authorize a runtime transition.
    """

    current_result = _validated_context(current_context, "current_context")
    if type(current_result) is C06AuthorityRejectV1:
        return current_result
    source_result = _validated_context(source_context, "source_context")
    if type(source_result) is C06AuthorityRejectV1:
        return source_result
    target_result = _validated_context(target_context, "target_context")
    if type(target_result) is C06AuthorityRejectV1:
        return target_result
    current = current_result
    source = source_result
    target = target_result
    if source.deployment_id != current.deployment_id:
        return _authority_reject(
            C06AuthorityCodeV1.DEPLOYMENT_MISMATCH,
            "source_context",
            "deployment_id",
        )
    if target.deployment_id != current.deployment_id:
        return _authority_reject(
            C06AuthorityCodeV1.DEPLOYMENT_MISMATCH,
            "target_context",
            "deployment_id",
        )
    if source.authority_epoch_root != current.authority_epoch_root:
        return _authority_reject(
            C06AuthorityCodeV1.SOURCE_EPOCH_MISMATCH,
            "source_context",
            "authority_epoch_root",
        )
    if source.state != current.state:
        return _authority_reject(
            C06AuthorityCodeV1.CURRENT_STATE_MISMATCH,
            "source_context",
            "state",
        )
    transport_result = transport_srgd_to_agqe_v1(
        source.state,
        expected_target=target.state,
    )
    if type(transport_result) is C04TransportRejectV1:
        return _authority_reject(
            C06AuthorityCodeV1.TRANSPORT_REJECT,
            "target_context",
            transport_result.code.value,
        )
    return C06MigrationAcceptedV1(
        current.deployment_id,
        source.state.state_root,
        target.state.state_root,
        source.authority_epoch_root,
        target.authority_epoch_root,
    )


__all__: Final[tuple[str, ...]] = (
    "C06AuthorityCheckResultV1",
    "C06AuthorityCodeV1",
    "C06AuthorityContextV1",
    "C06AuthorityRejectV1",
    "C06MigrationAcceptedV1",
    "C06OperationalConfigurationV1",
    "C06RotationCheckResultV1",
    "C06RotationCodeV1",
    "C06RotationRejectV1",
    "C06RotationSnapshotV1",
    "check_representation_migration_authority_v1",
    "check_rotation_preserves_history_v1",
)
