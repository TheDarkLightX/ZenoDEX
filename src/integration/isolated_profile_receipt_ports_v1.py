"""Narrow receipt ports minted only by the measured isolated verifier-set factory.

The handles own one profile snapshot and fix each port's role and release.
They carry no caller-supplied backend or mutable authority fields. Their private
mount accessor rechecks the publisher's current coordinates. Python interpreter
integrity, source authorization, publication and deployment mediation remain
separate obligations; these ports provide cryptographic verification only.
"""

from __future__ import annotations

from dataclasses import dataclass
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
from .isolated_economic_verifier_set_v1 import (
    IsolatedVerifierArtifactV1,
    bind_isolated_economic_verifier_set_v1,
)


class _ReceiptCallV1(Protocol):
    def __call__(
        self, receipt_bytes: bytes, *, expected_image_id: str, expected_journal_bytes: bytes
    ) -> None: ...


@dataclass(frozen=True, slots=True)
class _ProfileAuthorityV1:
    profile: EconomicProfileSnapshotV1
    verifier: BoundEconomicReceiptVerifierV1


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
        if type(self) is not IsolatedReceiptPortV1:
            raise TypeError("isolated receipt port must be the exact factory type")
        with _LOCK:
            call = _CALLS.get(self)
        if call is None:
            raise ValueError("isolated receipt port was not factory-minted")
        call(
            receipt_bytes,
            expected_image_id=expected_image_id,
            expected_journal_bytes=expected_journal_bytes,
        )


class IsolatedProfileReceiptPortsV1(_OpaqueHandleV1):
    """A single measured profile's root, module, coordinator and route ports."""

    __slots__ = ()

    def root_port(self) -> IsolatedReceiptPortV1:
        return _mint_port(_authority(self).verifier.verify_succinct_receipt)

    def module_port(self, lane_id: LaneIdV1) -> IsolatedReceiptPortV1:
        authority = _authority(self)
        _require_lane(lane_id)
        release = authority.profile.lane_registry.release_for(lane_id)
        _require_accepting_release(release)
        return _mint_port(
            partial(
                authority.verifier.verify_profile_lane_receipt,
                profile=authority.profile,
                lane_id=lane_id,
                expected_module_release_id=release.release_id,
            )
        )

    def coordinator_port(self, lane_id: LaneIdV1) -> IsolatedReceiptPortV1:
        authority = _authority(self)
        _require_lane(lane_id)
        release = authority.profile.lane_coordinator_registry.release_for(lane_id)
        _require_accepting_release(release)
        return _mint_port(
            partial(
                authority.verifier.verify_profile_lane_coordinator_receipt,
                profile=authority.profile,
                lane_id=lane_id,
                expected_coordinator_release_id=release.coordinator_release_id,
            )
        )

    def route_port(self, route_release_id: str) -> IsolatedReceiptPortV1:
        authority = _authority(self)
        if type(route_release_id) is not str:
            raise TypeError("isolated route release id must be an exact string")
        _require_root(route_release_id, name="isolated route release id")
        for release in authority.profile.route_registry.routes:
            if release.route_release_id == route_release_id:
                _require_accepting_release(release)
                return _mint_port(
                    partial(
                        authority.verifier.verify_profile_route_receipt,
                        profile=authority.profile,
                        expected_route_release_id=release.route_release_id,
                    )
                )
        raise ValueError("isolated route release is outside the profile")


_LOCK = Lock()
_AUTHORITIES: WeakKeyDictionary[IsolatedProfileReceiptPortsV1, _ProfileAuthorityV1] = (
    WeakKeyDictionary()
)
_CALLS: WeakKeyDictionary[IsolatedReceiptPortV1, _ReceiptCallV1] = WeakKeyDictionary()


def _authority(ports: IsolatedProfileReceiptPortsV1) -> _ProfileAuthorityV1:
    if type(ports) is not IsolatedProfileReceiptPortsV1:
        raise TypeError("isolated profile ports must be the exact factory type")
    with _LOCK:
        authority = _AUTHORITIES.get(ports)
    if authority is None:
        raise ValueError("isolated profile ports were not factory-minted")
    return authority


def _mint_port(call: _ReceiptCallV1) -> IsolatedReceiptPortV1:
    port = object.__new__(IsolatedReceiptPortV1)
    with _LOCK:
        _CALLS[port] = call
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
