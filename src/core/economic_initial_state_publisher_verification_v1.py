"""Pure genesis and migration preparation for the publisher shell.

Core owns every admission, snapshot, kind, predecessor and journal decision
and returns one exact detached subject that retains the complete owned
admission.  Receipt execution against the publisher's selected verifier lives
in ``src.integration.economic_initial_state_publisher_verification_v1``; no
function here takes or calls a verifier.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from .economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateKindV1,
    EconomicInitialStateSourceManifestV1,
    snapshot_economic_initial_state_source_manifest_v1,
)
from .economic_initial_state_v1 import (
    EconomicInitialStateAdmissionV1,
    EconomicInitialStateCertificateV1,
    _OwnedEconomicInitialStateAdmissionV1,
    _snapshot_economic_initial_state_admission_v1,
    _validate_owned_economic_initial_state_admission_v1,
    _VerifiedEconomicInitialStateV1,
)
from .global_economic_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    canonical_global_bytes_v1,
)

_PREPARED_ECONOMIC_INITIAL_STATE_TOKEN = object()


@dataclass(frozen=True, slots=True)
class _PreparedEconomicInitialStateFieldsV1:
    """Complete owned admission plus the exact journal it validates to."""

    owned: _OwnedEconomicInitialStateAdmissionV1
    expected_journal_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.owned) is not _OwnedEconomicInitialStateAdmissionV1:
            raise TypeError("prepared initial state admission type is not closed")
        if type(self.expected_journal_bytes) is not bytes:
            raise TypeError("prepared initial state journal must be exact bytes")


def _snapshot_owned_economic_initial_state_admission_v1(
    owned: _OwnedEconomicInitialStateAdmissionV1,
) -> _OwnedEconomicInitialStateAdmissionV1:
    """Return a detached copy of one complete owned admission."""

    if type(owned) is not _OwnedEconomicInitialStateAdmissionV1:
        raise TypeError("prepared initial state admission type is not closed")
    if type(owned.certificate) is not EconomicInitialStateCertificateV1:
        raise TypeError("prepared initial state certificate type is not closed")
    if type(owned.receipt_bytes) is not bytes or not owned.receipt_bytes:
        raise TypeError("prepared initial state receipt must be nonempty exact bytes")
    if owned.predecessor_state is not None and type(
        owned.predecessor_state
    ) is not GlobalEconomicStateV1:
        raise TypeError("prepared initial state predecessor type is not closed")
    return _OwnedEconomicInitialStateAdmissionV1(
        profile=snapshot_economic_profile_v1(owned.profile),
        policy_registry=snapshot_economic_policy_registry_v1(owned.policy_registry),
        state=_snapshot_state_v1(owned.state),
        predecessor_state=(
            None
            if owned.predecessor_state is None
            else _snapshot_state_v1(owned.predecessor_state)
        ),
        source_manifest=snapshot_economic_initial_state_source_manifest_v1(
            owned.source_manifest
        ),
        certificate=replace(owned.certificate),
        receipt_bytes=owned.receipt_bytes,
    )


class _PreparedEconomicInitialStateV1:
    """Exact detached genesis or migration subject awaiting receipt execution.

    Construction requires the core-private token, detaches the complete owned
    admission (profile, policy registry, state, predecessor, source manifest,
    certificate and receipt) and regenerates the exact journal by rerunning
    the full pure admission validation on that copy.  Plain data with no
    publication capability: the shell executes exactly the receipt, image and
    journal exposed here and finishes only this subject.
    """

    __slots__ = ("_fields", "_preparation_marker")
    _fields: _PreparedEconomicInitialStateFieldsV1

    def __init__(
        self,
        token: object,
        fields: _PreparedEconomicInitialStateFieldsV1,
    ) -> None:
        if token is not _PREPARED_ECONOMIC_INITIAL_STATE_TOKEN:
            raise TypeError("_PreparedEconomicInitialStateV1 is preparer-constructed")
        if type(fields) is not _PreparedEconomicInitialStateFieldsV1:
            raise TypeError("prepared initial state fields type is not closed")
        owned = _snapshot_owned_economic_initial_state_admission_v1(fields.owned)
        journal_bytes = _validate_owned_economic_initial_state_admission_v1(owned)
        if journal_bytes != fields.expected_journal_bytes:
            raise ValueError("prepared initial state journal mismatch")
        object.__setattr__(
            self,
            "_fields",
            _PreparedEconomicInitialStateFieldsV1(
                owned=owned,
                expected_journal_bytes=journal_bytes,
            ),
        )
        object.__setattr__(
            self,
            "_preparation_marker",
            _PREPARED_ECONOMIC_INITIAL_STATE_TOKEN,
        )

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("_PreparedEconomicInitialStateV1 is immutable")

    @property
    def kind(self) -> EconomicInitialStateKindV1:
        return self._fields.owned.certificate.kind

    @property
    def profile(self) -> EconomicProfileSnapshotV1:
        return snapshot_economic_profile_v1(self._fields.owned.profile)

    @property
    def policy_registry(self) -> EconomicPolicyRegistryV1:
        return snapshot_economic_policy_registry_v1(self._fields.owned.policy_registry)

    @property
    def state(self) -> GlobalEconomicStateV1:
        return _snapshot_state_v1(self._fields.owned.state)

    @property
    def predecessor_state(self) -> GlobalEconomicStateV1 | None:
        predecessor = self._fields.owned.predecessor_state
        return None if predecessor is None else _snapshot_state_v1(predecessor)

    @property
    def source_manifest(self) -> EconomicInitialStateSourceManifestV1:
        return snapshot_economic_initial_state_source_manifest_v1(
            self._fields.owned.source_manifest
        )

    @property
    def certificate(self) -> EconomicInitialStateCertificateV1:
        return replace(self._fields.owned.certificate)

    @property
    def certificate_root(self) -> str:
        return self._fields.owned.certificate.certificate_root

    @property
    def receipt_bytes(self) -> bytes:
        return self._fields.owned.receipt_bytes

    @property
    def expected_image_id(self) -> str:
        return self._fields.owned.profile.root_image_id

    @property
    def expected_journal_bytes(self) -> bytes:
        return self._fields.expected_journal_bytes

    @property
    def owned_admission(self) -> _OwnedEconomicInitialStateAdmissionV1:
        return _snapshot_owned_economic_initial_state_admission_v1(self._fields.owned)


def _require_prepared_economic_initial_state_v1(
    prepared: _PreparedEconomicInitialStateV1,
) -> _PreparedEconomicInitialStateFieldsV1:
    """Admit only an exact, preparer-constructed subject and return its fields."""

    if type(prepared) is not _PreparedEconomicInitialStateV1:
        raise TypeError("prepared initial state type is not closed")
    try:
        marker = object.__getattribute__(prepared, "_preparation_marker")
        fields = object.__getattribute__(prepared, "_fields")
    except AttributeError:
        raise TypeError("prepared initial state is not preparer-constructed") from None
    if marker is not _PREPARED_ECONOMIC_INITIAL_STATE_TOKEN:
        raise TypeError("prepared initial state is not preparer-constructed")
    if type(fields) is not _PreparedEconomicInitialStateFieldsV1:
        raise TypeError("prepared initial state fields type is not closed")
    return fields


def _snapshot_prepared_economic_initial_state_v1(
    prepared: _PreparedEconomicInitialStateV1,
) -> _PreparedEconomicInitialStateV1:
    """Detach and fully revalidate one exact prepared initial-state subject."""

    return _PreparedEconomicInitialStateV1(
        _PREPARED_ECONOMIC_INITIAL_STATE_TOKEN,
        _require_prepared_economic_initial_state_v1(prepared),
    )


def _prepare_economic_initial_state_for_publisher_v1(
    admission: EconomicInitialStateAdmissionV1,
) -> _PreparedEconomicInitialStateV1:
    """Prepare genesis before a publisher-owned head can be constructed."""

    owned = _snapshot_economic_initial_state_admission_v1(admission)
    if owned.certificate.kind is not EconomicInitialStateKindV1.GENESIS:
        raise ValueError("commit port construction requires a genesis admission")
    return _prepare_owned_economic_initial_state_v1(owned)


def _prepare_economic_migration_for_publisher_v1(
    admission: EconomicInitialStateAdmissionV1,
    expected_predecessor_state: GlobalEconomicStateV1,
) -> _PreparedEconomicInitialStateV1:
    """Prepare migration against the exact publisher-owned predecessor."""

    if type(expected_predecessor_state) is not GlobalEconomicStateV1:
        raise TypeError("migration expected predecessor state type is not closed")
    owned = _snapshot_economic_initial_state_admission_v1(admission)
    if owned.certificate.kind is not EconomicInitialStateKindV1.MIGRATION:
        raise ValueError("migration activation requires a migration admission")
    expected_predecessor = _snapshot_state_v1(expected_predecessor_state)
    if owned.predecessor_state is None:
        raise ValueError("migration initial state requires a predecessor state")
    if canonical_global_bytes_v1(
        owned.predecessor_state
    ) != canonical_global_bytes_v1(expected_predecessor):
        raise ValueError(
            "migration predecessor does not match the publisher-owned source head"
        )
    return _prepare_owned_economic_initial_state_v1(owned)


def _prepare_owned_economic_initial_state_v1(
    owned: _OwnedEconomicInitialStateAdmissionV1,
) -> _PreparedEconomicInitialStateV1:
    """Validate an owned admission and fix its exact execution subject."""

    journal_bytes = _validate_owned_economic_initial_state_admission_v1(owned)
    return _PreparedEconomicInitialStateV1(
        _PREPARED_ECONOMIC_INITIAL_STATE_TOKEN,
        _PreparedEconomicInitialStateFieldsV1(
            owned=owned,
            expected_journal_bytes=journal_bytes,
        ),
    )


def _finish_prepared_economic_initial_state_v1(
    prepared: _PreparedEconomicInitialStateV1,
) -> _VerifiedEconomicInitialStateV1:
    """Project exactly one prepared subject into the publisher's verified head."""

    owned = _require_prepared_economic_initial_state_v1(prepared).owned
    return _VerifiedEconomicInitialStateV1(
        profile=snapshot_economic_profile_v1(owned.profile),
        state=_snapshot_state_v1(owned.state),
        certificate_root=owned.certificate.certificate_root,
    )
