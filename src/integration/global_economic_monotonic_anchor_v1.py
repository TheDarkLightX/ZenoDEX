"""Release-bound port for an independently durable monotonic checkpoint.

The port authenticates no source by itself.  It binds one measured shadow
backend whose deployment contract must provide authenticated current reads and
linearizable compare-and-set.  Local files, including a second fsynced file in
the same backup domain, do not satisfy that external assumption.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import Enum
from threading import Lock
from typing import Callable, Final, cast
from weakref import WeakKeyDictionary

from ..core.global_economic_authority_head_v1 import GlobalEconomicAuthorityHeadV1
from ..core.global_economic_monotonic_anchor_v1 import (
    GlobalEconomicMonotonicAnchorV1,
    decode_global_economic_monotonic_anchor_v1,
    require_global_economic_epoch_anchor_successor_v1,
)
from ..core.global_settlement_types_v1 import (
    _require_root,
    _require_token,
    hash_global_v1,
)
from .global_economic_durable_epoch_v1 import DurableEconomicPublicationHeadV1

_BOUND_ANCHOR_BACKEND_MINT_V1 = object()
_MAX_MEASURED_ANCHOR_BACKEND_BYTES_V1: Final = 16 * 1024 * 1024


class GlobalEconomicMonotonicAnchorBackendStatusV1(str, Enum):
    """Production selection is deliberately absent from this research slice."""

    SHADOW = "SHADOW"


class GlobalEconomicMonotonicAnchorBackendEvidenceStatusV1(str, Enum):
    SPECIFIED = "SPECIFIED"
    IMPLEMENTED = "IMPLEMENTED"
    TESTED = "TESTED"
    SOURCE_PINNED = "SOURCE_PINNED"
    TOOLCHAIN_PINNED = "TOOLCHAIN_PINNED"
    AUTHENTICATED_SOURCE_REQUIRED = "AUTHENTICATED_SOURCE_REQUIRED"
    MONOTONIC_CURRENT_READ_REQUIRED = "MONOTONIC_CURRENT_READ_REQUIRED"
    LINEARIZABLE_CAS_REQUIRED = "LINEARIZABLE_CAS_REQUIRED"


class GlobalEconomicMonotonicAnchorUnavailableV1(RuntimeError):
    """The external current-anchor service could not answer."""


class GlobalEconomicMonotonicAnchorProtocolViolationV1(RuntimeError):
    """The selected backend violated its exact typed protocol."""


def global_economic_monotonic_anchor_backend_protocol_root_v1() -> str:
    return hash_global_v1(
        "global-economic-monotonic-anchor-backend-protocol-v1",
        {
            "read": "read_current_anchor(namespace_root)->canonical_bytes",
            "cas": (
                "compare_and_set_anchor(namespace_root,expected_root,"
                "successor_bytes)->exact_bool"
            ),
            "currentness": "external_authenticated_monotonic_source",
        },
    )


def global_economic_monotonic_anchor_backend_implementation_root_v1(
    artifact_bytes: bytes,
) -> str:
    if type(artifact_bytes) is not bytes:
        raise TypeError("monotonic anchor backend artifact must be exact bytes")
    if not 1 <= len(artifact_bytes) <= _MAX_MEASURED_ANCHOR_BACKEND_BYTES_V1:
        raise ValueError("monotonic anchor backend artifact is outside the byte bound")
    digest = hashlib.sha256()
    digest.update(b"ZenoDEX-GlobalEconomicMonotonicAnchorBackend-V1\x00")
    digest.update(len(artifact_bytes).to_bytes(8, "big"))
    digest.update(artifact_bytes)
    return "0x" + digest.hexdigest()


@dataclass(frozen=True, slots=True)
class GlobalEconomicMonotonicAnchorBackendReleaseV1:
    release_id: str
    semantic_version: str
    implementation_root: str
    specification_root: str
    source_root: str
    toolchain_root: str
    evidence_manifest_root: str
    backend_protocol_root: str
    status: GlobalEconomicMonotonicAnchorBackendStatusV1
    evidence_statuses: tuple[
        GlobalEconomicMonotonicAnchorBackendEvidenceStatusV1, ...
    ]

    def __post_init__(self) -> None:
        _require_root(self.release_id, name="monotonic anchor backend release id")
        if type(self.semantic_version) is not str:
            raise TypeError("monotonic anchor backend semantic version must be exact str")
        _require_token(
            self.semantic_version,
            name="monotonic anchor backend semantic version",
        )
        for field_name in (
            "implementation_root",
            "specification_root",
            "source_root",
            "toolchain_root",
            "evidence_manifest_root",
            "backend_protocol_root",
        ):
            value = getattr(self, field_name)
            if type(value) is not str:
                raise TypeError(f"monotonic anchor backend {field_name} must be exact str")
            _require_root(value, name=f"monotonic anchor backend {field_name}")
        if type(self.status) is not GlobalEconomicMonotonicAnchorBackendStatusV1:
            raise TypeError("monotonic anchor backend status is not closed")
        if type(self.evidence_statuses) is not tuple or self.evidence_statuses != tuple(
            GlobalEconomicMonotonicAnchorBackendEvidenceStatusV1
        ):
            raise ValueError("shadow monotonic anchor backend evidence set is incomplete")
        if self.release_id != self.derived_release_id:
            raise ValueError("monotonic anchor backend release id is not content-derived")

    @classmethod
    def build(
        cls,
        *,
        semantic_version: str,
        implementation_root: str,
        specification_root: str,
        source_root: str,
        toolchain_root: str,
        evidence_manifest_root: str,
        backend_protocol_root: str,
        status: GlobalEconomicMonotonicAnchorBackendStatusV1,
        evidence_statuses: tuple[
            GlobalEconomicMonotonicAnchorBackendEvidenceStatusV1, ...
        ],
    ) -> GlobalEconomicMonotonicAnchorBackendReleaseV1:
        body = cls._content_body(
            implementation_root=implementation_root,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            evidence_manifest_root=evidence_manifest_root,
            backend_protocol_root=backend_protocol_root,
        )
        return cls(
            release_id=hash_global_v1(
                "global-economic-monotonic-anchor-backend-release-v1",
                body,
            ),
            semantic_version=semantic_version,
            implementation_root=implementation_root,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            evidence_manifest_root=evidence_manifest_root,
            backend_protocol_root=backend_protocol_root,
            status=status,
            evidence_statuses=evidence_statuses,
        )

    @staticmethod
    def _content_body(**values: object) -> dict[str, object]:
        return {"schema": "global-economic-monotonic-anchor-backend-release-v1", **values}

    @property
    def derived_release_id(self) -> str:
        return hash_global_v1(
            "global-economic-monotonic-anchor-backend-release-v1",
            self._content_body(
                implementation_root=self.implementation_root,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                evidence_manifest_root=self.evidence_manifest_root,
                backend_protocol_root=self.backend_protocol_root,
            ),
        )


_ReadAnchorCallV1 = Callable[[str], object]
_CompareAndSetAnchorCallV1 = Callable[[str, str, bytes], object]


@dataclass(frozen=True, slots=True)
class _BoundAnchorBackendAuthorityV1:
    release: GlobalEconomicMonotonicAnchorBackendReleaseV1
    anchor_namespace_root: str
    chain_id: str
    deployment_root: str
    backend: object
    read_call: _ReadAnchorCallV1
    compare_and_set_call: _CompareAndSetAnchorCallV1


class BoundGlobalEconomicMonotonicAnchorBackendV1:
    """Opaque same-process handle for one measured shadow backend."""

    __slots__ = ("__weakref__",)

    def __init__(
        self,
        mint: object,
        authority: _BoundAnchorBackendAuthorityV1,
    ) -> None:
        if mint is not _BOUND_ANCHOR_BACKEND_MINT_V1:
            raise TypeError("monotonic anchor backend is factory-constructed")
        _register_bound_anchor_backend_v1(self, authority)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("monotonic anchor backend binding is immutable")

    @property
    def release_id(self) -> str:
        return _bound_anchor_backend_authority_v1(self).release.release_id

    @property
    def binding_root(self) -> str:
        authority = _bound_anchor_backend_authority_v1(self)
        return hash_global_v1(
            "global-economic-monotonic-anchor-backend-binding-v1",
            {
                "release_id": authority.release.release_id,
                "implementation_root": authority.release.implementation_root,
                "evidence_manifest_root": authority.release.evidence_manifest_root,
                "backend_protocol_root": authority.release.backend_protocol_root,
                "anchor_namespace_root": authority.anchor_namespace_root,
                "chain_id": authority.chain_id,
                "deployment_root": authority.deployment_root,
                "selection_purpose": "RESEARCH_SHADOW",
            },
        )

    def _read_current_for_publisher_v1(self) -> GlobalEconomicMonotonicAnchorV1:
        authority = _bound_anchor_backend_authority_v1(self)
        try:
            raw = authority.read_call(authority.anchor_namespace_root)
        except Exception as exc:
            raise GlobalEconomicMonotonicAnchorUnavailableV1(
                "external monotonic anchor read failed"
            ) from exc
        if type(raw) is not bytes:
            raise GlobalEconomicMonotonicAnchorProtocolViolationV1(
                "external monotonic anchor read must return exact bytes"
            )
        try:
            anchor = decode_global_economic_monotonic_anchor_v1(raw)
        except (TypeError, ValueError) as exc:
            raise GlobalEconomicMonotonicAnchorProtocolViolationV1(
                "external monotonic anchor bytes are invalid"
            ) from exc
        bindings = (
            (anchor.anchor_namespace_root, authority.anchor_namespace_root),
            (anchor.chain_id, authority.chain_id),
            (anchor.deployment_root, authority.deployment_root),
        )
        if any(actual != expected for actual, expected in bindings):
            raise GlobalEconomicMonotonicAnchorProtocolViolationV1(
                "external monotonic anchor deployment binding mismatch"
            )
        return anchor

    def _compare_and_set_for_publisher_v1(
        self,
        expected: GlobalEconomicMonotonicAnchorV1,
        successor: GlobalEconomicMonotonicAnchorV1,
    ) -> bool:
        authority = _bound_anchor_backend_authority_v1(self)
        require_global_economic_epoch_anchor_successor_v1(expected, successor)
        for anchor in (expected, successor):
            if (
                anchor.anchor_namespace_root != authority.anchor_namespace_root
                or anchor.chain_id != authority.chain_id
                or anchor.deployment_root != authority.deployment_root
            ):
                raise ValueError("monotonic anchor CAS deployment binding mismatch")
        try:
            result = authority.compare_and_set_call(
                authority.anchor_namespace_root,
                expected.anchor_root,
                successor.canonical_bytes,
            )
        except Exception as exc:
            raise GlobalEconomicMonotonicAnchorUnavailableV1(
                "external monotonic anchor compare-and-set failed"
            ) from exc
        if type(result) is not bool:
            raise GlobalEconomicMonotonicAnchorProtocolViolationV1(
                "external monotonic anchor CAS must return exact bool"
            )
        if not result:
            return False
        if self._read_current_for_publisher_v1() != successor:
            raise GlobalEconomicMonotonicAnchorProtocolViolationV1(
                "external monotonic anchor CAS acknowledgment is false"
            )
        return True


_BOUND_ANCHOR_BACKEND_LOCK_V1 = Lock()
_BOUND_ANCHOR_BACKEND_AUTHORITIES_V1: WeakKeyDictionary[
    BoundGlobalEconomicMonotonicAnchorBackendV1,
    _BoundAnchorBackendAuthorityV1,
] = WeakKeyDictionary()


def _register_bound_anchor_backend_v1(
    handle: BoundGlobalEconomicMonotonicAnchorBackendV1,
    authority: _BoundAnchorBackendAuthorityV1,
) -> None:
    with _BOUND_ANCHOR_BACKEND_LOCK_V1:
        if handle in _BOUND_ANCHOR_BACKEND_AUTHORITIES_V1:
            raise TypeError("monotonic anchor backend is already registered")
        _BOUND_ANCHOR_BACKEND_AUTHORITIES_V1[handle] = authority


def _bound_anchor_backend_authority_v1(
    handle: BoundGlobalEconomicMonotonicAnchorBackendV1,
) -> _BoundAnchorBackendAuthorityV1:
    if type(handle) is not BoundGlobalEconomicMonotonicAnchorBackendV1:
        raise TypeError("monotonic anchor backend handle type is not closed")
    with _BOUND_ANCHOR_BACKEND_LOCK_V1:
        authority = _BOUND_ANCHOR_BACKEND_AUTHORITIES_V1.get(handle)
    if authority is None:
        raise TypeError("monotonic anchor backend handle is not registered")
    return authority


def bind_global_economic_monotonic_anchor_backend_v1(
    *,
    release: GlobalEconomicMonotonicAnchorBackendReleaseV1,
    measured_artifact_bytes: bytes,
    anchor_namespace_root: str,
    chain_id: str,
    deployment_root: str,
    backend: object,
) -> BoundGlobalEconomicMonotonicAnchorBackendV1:
    """Bind a measured SHADOW backend; this cannot select production authority."""

    if type(release) is not GlobalEconomicMonotonicAnchorBackendReleaseV1:
        raise TypeError("monotonic anchor backend release type is not closed")
    GlobalEconomicMonotonicAnchorBackendReleaseV1(
        release_id=release.release_id,
        semantic_version=release.semantic_version,
        implementation_root=release.implementation_root,
        specification_root=release.specification_root,
        source_root=release.source_root,
        toolchain_root=release.toolchain_root,
        evidence_manifest_root=release.evidence_manifest_root,
        backend_protocol_root=release.backend_protocol_root,
        status=release.status,
        evidence_statuses=tuple(release.evidence_statuses),
    )
    if release.status is not GlobalEconomicMonotonicAnchorBackendStatusV1.SHADOW:
        raise ValueError("monotonic anchor backend release is not shadow-only")
    if release.backend_protocol_root != (
        global_economic_monotonic_anchor_backend_protocol_root_v1()
    ):
        raise ValueError("monotonic anchor backend protocol root mismatch")
    measured_root = global_economic_monotonic_anchor_backend_implementation_root_v1(
        measured_artifact_bytes
    )
    if measured_root != release.implementation_root:
        raise ValueError("monotonic anchor measured implementation root mismatch")
    if type(anchor_namespace_root) is not str:
        raise TypeError("monotonic anchor namespace root must be exact str")
    _require_root(anchor_namespace_root, name="monotonic anchor namespace root")
    if type(chain_id) is not str:
        raise TypeError("monotonic anchor chain id must be exact str")
    _require_token(chain_id, name="monotonic anchor chain id")
    if type(deployment_root) is not str:
        raise TypeError("monotonic anchor deployment root must be exact str")
    _require_root(deployment_root, name="monotonic anchor deployment root")
    read_call = getattr(backend, "read_current_anchor", None)
    compare_and_set_call = getattr(backend, "compare_and_set_anchor", None)
    if not callable(read_call) or not callable(compare_and_set_call):
        raise TypeError("monotonic anchor backend protocol is incomplete")
    return BoundGlobalEconomicMonotonicAnchorBackendV1(
        _BOUND_ANCHOR_BACKEND_MINT_V1,
        _BoundAnchorBackendAuthorityV1(
            release=release,
            anchor_namespace_root=anchor_namespace_root,
            chain_id=chain_id,
            deployment_root=deployment_root,
            backend=backend,
            read_call=cast(_ReadAnchorCallV1, read_call),
            compare_and_set_call=cast(
                _CompareAndSetAnchorCallV1,
                compare_and_set_call,
            ),
        ),
    )


def build_global_economic_monotonic_anchor_v1(
    *,
    anchor_namespace_root: str,
    anchor_sequence: int,
    previous_anchor_root: str,
    authority: GlobalEconomicAuthorityHeadV1,
    publication: DurableEconomicPublicationHeadV1,
) -> GlobalEconomicMonotonicAnchorV1:
    """Project validated local heads into the external anchor ABI."""

    if type(authority) is not GlobalEconomicAuthorityHeadV1:
        raise TypeError("monotonic anchor authority head type is not closed")
    if type(publication) is not DurableEconomicPublicationHeadV1:
        raise TypeError("monotonic anchor publication head type is not closed")
    shared = (
        (publication.activation_id, authority.activation_id),
        (publication.chain_id, authority.chain_id),
        (publication.deployment_root, authority.deployment_root),
        (publication.profile_root, authority.profile_root),
        (publication.writer_epoch, authority.writer_epoch),
    )
    if any(actual != expected for actual, expected in shared):
        raise ValueError("monotonic anchor local authority/publication mismatch")
    return GlobalEconomicMonotonicAnchorV1(
        anchor_namespace_root=anchor_namespace_root,
        anchor_sequence=anchor_sequence,
        previous_anchor_root=previous_anchor_root,
        authority_root=authority.authority_root,
        authority_generation=authority.generation,
        activation_id=publication.activation_id,
        chain_id=publication.chain_id,
        deployment_root=publication.deployment_root,
        epoch_store_root=authority.epoch_store_root,
        profile_root=publication.profile_root,
        writer_epoch=publication.writer_epoch,
        publication_id=publication.publication_id,
        publication_sequence=publication.sequence,
        height=publication.height,
        state_root=publication.state_root,
        commit_id=publication.commit_id,
        certificate_root=publication.certificate_root,
    )


def require_global_economic_monotonic_anchor_matches_local_v1(
    anchor: GlobalEconomicMonotonicAnchorV1,
    *,
    authority: GlobalEconomicAuthorityHeadV1,
    publication: DurableEconomicPublicationHeadV1,
) -> None:
    if type(anchor) is not GlobalEconomicMonotonicAnchorV1:
        raise TypeError("monotonic anchor type is not closed")
    projected = build_global_economic_monotonic_anchor_v1(
        anchor_namespace_root=anchor.anchor_namespace_root,
        anchor_sequence=anchor.anchor_sequence,
        previous_anchor_root=anchor.previous_anchor_root,
        authority=authority,
        publication=publication,
    )
    if projected != anchor:
        raise ValueError("external monotonic anchor does not match local durable heads")


def build_global_economic_epoch_anchor_successor_v1(
    current: GlobalEconomicMonotonicAnchorV1,
    *,
    authority: GlobalEconomicAuthorityHeadV1,
    publication: DurableEconomicPublicationHeadV1,
) -> GlobalEconomicMonotonicAnchorV1:
    if type(current) is not GlobalEconomicMonotonicAnchorV1:
        raise TypeError("current monotonic anchor type is not closed")
    successor = build_global_economic_monotonic_anchor_v1(
        anchor_namespace_root=current.anchor_namespace_root,
        anchor_sequence=current.anchor_sequence + 1,
        previous_anchor_root=current.anchor_root,
        authority=authority,
        publication=publication,
    )
    require_global_economic_epoch_anchor_successor_v1(current, successor)
    return successor


def global_economic_monotonic_anchor_publication_head_v1(
    anchor: GlobalEconomicMonotonicAnchorV1,
) -> DurableEconomicPublicationHeadV1:
    if type(anchor) is not GlobalEconomicMonotonicAnchorV1:
        raise TypeError("monotonic anchor type is not closed")
    return DurableEconomicPublicationHeadV1(
        publication_id=anchor.publication_id,
        sequence=anchor.publication_sequence,
        activation_id=anchor.activation_id,
        chain_id=anchor.chain_id,
        deployment_root=anchor.deployment_root,
        profile_root=anchor.profile_root,
        writer_epoch=anchor.writer_epoch,
        height=anchor.height,
        state_root=anchor.state_root,
        commit_id=anchor.commit_id,
        certificate_root=anchor.certificate_root,
    )


__all__ = [
    "BoundGlobalEconomicMonotonicAnchorBackendV1",
    "GlobalEconomicMonotonicAnchorBackendEvidenceStatusV1",
    "GlobalEconomicMonotonicAnchorBackendReleaseV1",
    "GlobalEconomicMonotonicAnchorBackendStatusV1",
    "GlobalEconomicMonotonicAnchorProtocolViolationV1",
    "GlobalEconomicMonotonicAnchorUnavailableV1",
    "bind_global_economic_monotonic_anchor_backend_v1",
    "build_global_economic_epoch_anchor_successor_v1",
    "build_global_economic_monotonic_anchor_v1",
    "global_economic_monotonic_anchor_backend_implementation_root_v1",
    "global_economic_monotonic_anchor_backend_protocol_root_v1",
    "global_economic_monotonic_anchor_publication_head_v1",
    "require_global_economic_monotonic_anchor_matches_local_v1",
]
