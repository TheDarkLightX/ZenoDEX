"""Narrow receipt ports minted only by the measured isolated verifier-set factory.

The handles own one profile snapshot and fix each port's role and release.
They carry no caller-supplied backend or mutable authority fields. Their private
mount accessor rechecks the publisher's current coordinates. Python interpreter
integrity, source authorization, publication and deployment mediation remain
separate obligations; these ports provide cryptographic verification only.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from functools import partial
from threading import Lock
from typing import NoReturn, Protocol, SupportsIndex
from weakref import WeakKeyDictionary

from ..core.economic_receipt_verifier_deployment_v1 import BoundEconomicReceiptVerifierV1
from ..core.economic_receipt_verifier_evidence_v1 import EconomicReceiptVerifierEvidenceManifestV1
from ..core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierRegistryV1,
    EconomicReceiptVerifierSelectionPurposeV1,
)
from ..core.global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from ..core.global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    _require_root,
)
from ..core.lane_composition_receipt_verification_v1 import (
    _VERIFIED_LANE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1,
    PreparedLaneCompositionReceiptV1,
    VerifiedLaneCompositionReceiptExecutionV1,
    snapshot_prepared_lane_composition_receipt_v1,
)
from ..core.lane_module_receipt_verification_v1 import (
    _VERIFIED_LANE_MODULE_RECEIPT_EXECUTION_TOKEN_V1,
    PreparedLaneModuleReceiptV1,
    VerifiedLaneModuleReceiptExecutionV1,
    snapshot_prepared_lane_module_receipt_v1,
)
from ..core.route_composition_receipt_verification_v1 import (
    _VERIFIED_ROUTE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1,
    PreparedRouteCompositionReceiptV1,
    VerifiedRouteCompositionReceiptExecutionV1,
    snapshot_prepared_route_composition_receipt_v1,
)
from .isolated_economic_verifier_set_v1 import (
    IsolatedVerifierArtifactV1,
    bind_isolated_economic_verifier_set_v1,
)


class _ReceiptCallV1(Protocol):
    def __call__(
        self, receipt_bytes: bytes, *, expected_image_id: str, expected_journal_bytes: bytes
    ) -> object: ...


@dataclass(frozen=True, slots=True)
class _ProfileAuthorityV1:
    profile: EconomicProfileSnapshotV1
    verifier: BoundEconomicReceiptVerifierV1


class _ReceiptRoleV1(Enum):
    ROOT = "root"
    MODULE = "module"
    COORDINATOR = "coordinator"
    ROUTE = "route"


@dataclass(frozen=True, slots=True)
class _ReceiptPortAuthorityV1:
    call: _ReceiptCallV1
    profile: _ProfileAuthorityV1
    role: _ReceiptRoleV1
    release_id: str
    lane_id: LaneIdV1 | None


class _OpaqueHandleV1:
    __slots__ = ("__weakref__",)

    def __new__(cls, *args: object, **kwargs: object) -> _OpaqueHandleV1:
        raise TypeError("isolated receipt handles require the measured factory")

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("isolated receipt handles are immutable")

    def __reduce_ex__(self, protocol: SupportsIndex) -> NoReturn:
        raise TypeError("isolated receipt handles cannot be copied or serialized")


class IsolatedReceiptPortV1(_OpaqueHandleV1):
    """One factory-minted role implementing existing succinct verifier protocols."""

    __slots__ = ()

    def verify_succinct_receipt(
        self, receipt_bytes: bytes, *, expected_image_id: str, expected_journal_bytes: bytes
    ) -> None:
        authority = _port_authority(self)
        authority.call(
            receipt_bytes,
            expected_image_id=expected_image_id,
            expected_journal_bytes=expected_journal_bytes,
        )

    @property
    def verifier_binding_root(self) -> str:
        return _port_authority(self).profile.verifier.binding_root

    def verify_prepared_module_receipt_v1(
        self, prepared: PreparedLaneModuleReceiptV1
    ) -> VerifiedLaneModuleReceiptExecutionV1:
        """Execute an exact module request under the retained measured role.

        Evidence is issued after successful execution and unchanged port and
        verifier identity. The result grants no publication or finality right.
        """
        if type(prepared) is not PreparedLaneModuleReceiptV1:
            raise TypeError("isolated module receipt request must be exactly prepared")
        owned = snapshot_prepared_lane_module_receipt_v1(prepared)
        authority = _port_authority(self)
        _require_module_subject(authority, owned)
        binding_root = authority.profile.verifier.binding_root
        baseline = _port_identity(authority)
        call = authority.call
        result = call(
            owned.receipt_bytes,
            expected_image_id=owned.expected_image_id,
            expected_journal_bytes=owned.expected_journal_bytes,
        )
        retained = _port_authority(self)
        if (
            retained.call is not call
            or _port_identity(retained) != baseline
            or retained.profile.verifier.binding_root != binding_root
        ):
            raise ValueError("isolated module receipt authority changed during verification")
        if result is not None:
            raise ValueError("isolated module receipt backend violated success contract")
        return VerifiedLaneModuleReceiptExecutionV1(
            _VERIFIED_LANE_MODULE_RECEIPT_EXECUTION_TOKEN_V1, owned, binding_root
        )

    def verify_prepared_coordinator_receipt_v1(
        self, prepared: PreparedLaneCompositionReceiptV1
    ) -> VerifiedLaneCompositionReceiptExecutionV1:
        """Execute an exact coordinator request under the retained measured role.

        Evidence is issued after successful execution and unchanged port and
        verifier identity. The result grants no route, epoch or finality right.
        """
        if type(prepared) is not PreparedLaneCompositionReceiptV1:
            raise TypeError("isolated coordinator receipt request must be exactly prepared")
        owned = snapshot_prepared_lane_composition_receipt_v1(prepared)
        authority = _port_authority(self)
        _require_coordinator_subject(authority, owned)
        binding_root = _execute_retained_request_v1(
            self,
            authority,
            receipt_bytes=owned.receipt_bytes,
            expected_image_id=owned.expected_image_id,
            expected_journal_bytes=owned.expected_journal_bytes,
            label="coordinator",
        )
        return VerifiedLaneCompositionReceiptExecutionV1(
            _VERIFIED_LANE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1, owned, binding_root
        )

    def verify_prepared_route_receipt_v1(
        self, prepared: PreparedRouteCompositionReceiptV1
    ) -> VerifiedRouteCompositionReceiptExecutionV1:
        """Execute an exact route request under the retained measured role.

        Evidence is issued after successful execution and unchanged port and
        verifier identity. The result grants no epoch, commit or finality right.
        """
        if type(prepared) is not PreparedRouteCompositionReceiptV1:
            raise TypeError("isolated route receipt request must be exactly prepared")
        owned = snapshot_prepared_route_composition_receipt_v1(prepared)
        authority = _port_authority(self)
        _require_route_subject(authority, owned)
        binding_root = _execute_retained_request_v1(
            self,
            authority,
            receipt_bytes=owned.receipt_bytes,
            expected_image_id=owned.expected_image_id,
            expected_journal_bytes=owned.expected_journal_bytes,
            label="route",
        )
        return VerifiedRouteCompositionReceiptExecutionV1(
            _VERIFIED_ROUTE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1, owned, binding_root
        )


class IsolatedProfileReceiptPortsV1(_OpaqueHandleV1):
    """A single measured profile's root, module, coordinator and route ports."""

    __slots__ = ()

    def root_port(self) -> IsolatedReceiptPortV1:
        authority = _authority(self)
        return _mint_port(_ReceiptPortAuthorityV1(
            authority.verifier.verify_succinct_receipt, authority,
            _ReceiptRoleV1.ROOT, authority.profile.root_image_id, None,
        ))

    def module_port(self, lane_id: LaneIdV1) -> IsolatedReceiptPortV1:
        authority = _authority(self)
        _require_lane(lane_id)
        release = authority.profile.lane_registry.release_for(lane_id)
        _require_accepting_release(release)
        return _mint_port(_ReceiptPortAuthorityV1(
            partial(
                authority.verifier.verify_profile_lane_receipt,
                profile=authority.profile,
                lane_id=lane_id,
                expected_module_release_id=release.release_id,
            ),
            authority, _ReceiptRoleV1.MODULE, release.release_id, lane_id,
        ))

    def coordinator_port(self, lane_id: LaneIdV1) -> IsolatedReceiptPortV1:
        authority = _authority(self)
        _require_lane(lane_id)
        release = authority.profile.lane_coordinator_registry.release_for(lane_id)
        _require_accepting_release(release)
        return _mint_port(_ReceiptPortAuthorityV1(
            partial(
                authority.verifier.verify_profile_lane_coordinator_receipt,
                profile=authority.profile,
                lane_id=lane_id,
                expected_coordinator_release_id=release.coordinator_release_id,
            ),
            authority, _ReceiptRoleV1.COORDINATOR, release.coordinator_release_id, lane_id,
        ))

    def route_port(self, route_release_id: str) -> IsolatedReceiptPortV1:
        authority = _authority(self)
        if type(route_release_id) is not str:
            raise TypeError("isolated route release id must be an exact string")
        _require_root(route_release_id, name="isolated route release id")
        for release in authority.profile.route_registry.routes:
            if release.route_release_id == route_release_id:
                _require_accepting_release(release)
                return _mint_port(_ReceiptPortAuthorityV1(
                    partial(
                        authority.verifier.verify_profile_route_receipt,
                        profile=authority.profile,
                        expected_route_release_id=release.route_release_id,
                    ),
                    authority, _ReceiptRoleV1.ROUTE, release.route_release_id, None,
                ))
        raise ValueError("isolated route release is outside the profile")


_LOCK = Lock()
_AUTHORITIES: WeakKeyDictionary[IsolatedProfileReceiptPortsV1, _ProfileAuthorityV1] = (
    WeakKeyDictionary()
)
_CALLS: WeakKeyDictionary[IsolatedReceiptPortV1, _ReceiptPortAuthorityV1] = WeakKeyDictionary()


def _authority(ports: IsolatedProfileReceiptPortsV1) -> _ProfileAuthorityV1:
    if type(ports) is not IsolatedProfileReceiptPortsV1:
        raise TypeError("isolated profile ports must be the exact factory type")
    with _LOCK:
        authority = _AUTHORITIES.get(ports)
    if authority is None:
        raise ValueError("isolated profile ports were not factory-minted")
    return authority


def _port_authority(port: IsolatedReceiptPortV1) -> _ReceiptPortAuthorityV1:
    if type(port) is not IsolatedReceiptPortV1:
        raise TypeError("isolated receipt port must be the exact factory type")
    with _LOCK:
        authority = _CALLS.get(port)
    if authority is None:
        raise ValueError("isolated receipt port was not factory-minted")
    return authority


def _port_identity(authority: _ReceiptPortAuthorityV1) -> tuple[object, ...]:
    return (
        authority.profile.verifier, authority.profile.profile.profile_id,
        authority.role, authority.release_id, authority.lane_id,
    )


def _require_module_subject(
    authority: _ReceiptPortAuthorityV1, prepared: PreparedLaneModuleReceiptV1
) -> None:
    if (
        authority.role is not _ReceiptRoleV1.MODULE
        or authority.profile.profile.profile_id != prepared.profile_root
        or authority.lane_id is not prepared.lane_id
        or authority.release_id != prepared.module_release_id
    ):
        raise ValueError("isolated module receipt subject is outside the port")


def _require_coordinator_subject(
    authority: _ReceiptPortAuthorityV1, prepared: PreparedLaneCompositionReceiptV1
) -> None:
    if (
        authority.role is not _ReceiptRoleV1.COORDINATOR
        or authority.profile.profile.profile_id != prepared.profile_root
        or authority.lane_id is not prepared.lane_id
        or authority.release_id != prepared.coordinator_release_id
    ):
        raise ValueError("isolated coordinator receipt subject is outside the port")


def _require_route_subject(
    authority: _ReceiptPortAuthorityV1, prepared: PreparedRouteCompositionReceiptV1
) -> None:
    if (
        authority.role is not _ReceiptRoleV1.ROUTE
        or authority.profile.profile.profile_id != prepared.profile_root
        or authority.lane_id is not None
        or authority.release_id != prepared.route_release_id
    ):
        raise ValueError("isolated route receipt subject is outside the port")


def _execute_retained_request_v1(
    port: IsolatedReceiptPortV1,
    authority: _ReceiptPortAuthorityV1,
    *,
    receipt_bytes: bytes,
    expected_image_id: str,
    expected_journal_bytes: bytes,
    label: str,
) -> str:
    """Run one owned request and return the verifier binding root retained across I/O.

    The callable, role, release, lane, profile and verifier identity observed
    before the call must be the ones observed after it, and the backend must
    honor its exact None success contract, or no execution evidence is issued.
    """
    binding_root = authority.profile.verifier.binding_root
    baseline = _port_identity(authority)
    call = authority.call
    result = call(
        receipt_bytes,
        expected_image_id=expected_image_id,
        expected_journal_bytes=expected_journal_bytes,
    )
    retained = _port_authority(port)
    if (
        retained.call is not call
        or _port_identity(retained) != baseline
        or retained.profile.verifier.binding_root != binding_root
    ):
        raise ValueError(f"isolated {label} receipt authority changed during verification")
    if result is not None:
        raise ValueError(f"isolated {label} receipt backend violated success contract")
    return binding_root


def _mint_port(authority: _ReceiptPortAuthorityV1) -> IsolatedReceiptPortV1:
    port = object.__new__(IsolatedReceiptPortV1)
    with _LOCK:
        _CALLS[port] = authority
    return port


def _require_lane(lane_id: LaneIdV1) -> None:
    if type(lane_id) is not LaneIdV1:
        raise TypeError("isolated lane selector must be the exact lane enum")


def _require_accepting_release(
    release: LaneModuleReleaseV1 | LaneCoordinatorReleaseV1 | RouteReleaseV1,
) -> None:
    # Selection fails early; the core bound verifier repeats this authorization.
    if release.status is not ReleaseStatusV1.ACTIVE_NEW or not release.accepts_new_objects:
        raise ValueError("isolated port requires an accepting release")


def _bound_isolated_profile_receipt_verifier_v1(
    ports: IsolatedProfileReceiptPortsV1,
    *,
    profile: EconomicProfileSnapshotV1,
    verifier_registry_root: str,
    deployment_root: str,
) -> BoundEconomicReceiptVerifierV1:
    """Mount only a minted measured set under the publisher's exact coordinates."""
    authority = _authority(ports)
    current = snapshot_economic_profile_v1(profile)
    if current.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("isolated publisher mount requires an ACTIVE profile")
    if current.verifier_registry_root != verifier_registry_root:
        raise ValueError("isolated publisher verifier registry binding mismatch")
    authority.verifier.require_binding(
        verifier_registry_root=verifier_registry_root,
        deployment_root=deployment_root,
        profile_root=current.profile_id,
        root_image_id=current.root_image_id,
        selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION,
    )
    return authority.verifier


def bind_isolated_profile_receipt_ports_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    verifier_registry: EconomicReceiptVerifierRegistryV1,
    evidence_manifest: EconomicReceiptVerifierEvidenceManifestV1,
    artifacts: tuple[IsolatedVerifierArtifactV1, ...],
    deployment_root: str,
    timeout_ms: int,
) -> IsolatedProfileReceiptPortsV1:
    """Acquire measured endpoints and return opaque ports without caller backends."""
    owned_profile = snapshot_economic_profile_v1(profile)
    verifier = bind_isolated_economic_verifier_set_v1(
        profile=owned_profile,
        verifier_registry=verifier_registry,
        evidence_manifest=evidence_manifest,
        artifacts=artifacts,
        deployment_root=deployment_root,
        timeout_ms=timeout_ms,
    )
    ports = object.__new__(IsolatedProfileReceiptPortsV1)
    with _LOCK:
        _AUTHORITIES[ports] = _ProfileAuthorityV1(owned_profile, verifier)
    return ports
