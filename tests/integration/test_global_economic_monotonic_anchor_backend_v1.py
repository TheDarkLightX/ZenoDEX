"""Port, authentication-boundary, and CAS tests for external anchor backends."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from src.core.global_economic_monotonic_anchor_v1 import (
    GlobalEconomicMonotonicAnchorV1,
    decode_global_economic_monotonic_anchor_v1,
)
from src.core.global_settlement_types_v1 import ZERO_ROOT_V1
from src.integration.global_economic_durable_epoch_v1 import (
    DurableEconomicPublicationHeadV1,
)
from src.integration.global_economic_monotonic_anchor_v1 import (
    GlobalEconomicMonotonicAnchorBackendEvidenceStatusV1,
    GlobalEconomicMonotonicAnchorBackendReleaseV1,
    GlobalEconomicMonotonicAnchorBackendStatusV1,
    GlobalEconomicMonotonicAnchorProtocolViolationV1,
    GlobalEconomicMonotonicAnchorUnavailableV1,
    bind_global_economic_monotonic_anchor_backend_v1,
    build_global_economic_epoch_anchor_successor_v1,
    build_global_economic_monotonic_anchor_v1,
    global_economic_monotonic_anchor_backend_implementation_root_v1,
    global_economic_monotonic_anchor_backend_protocol_root_v1,
)


def _root(index: int) -> str:
    return "0x" + f"{index:064x}"


def _authority() -> GlobalEconomicAuthorityHeadV1:
    return GlobalEconomicAuthorityHeadV1(
        generation=0,
        activation_id=_root(10),
        chain_id="tau-testnet",
        deployment_root=_root(11),
        epoch_store_root=_root(12),
        profile_root=_root(13),
        writer_epoch=14,
        verifier_registry_root=_root(15),
        verifier_release_id=_root(16),
        verifier_binding_root=_root(17),
        root_image_id=_root(18),
        status=GlobalEconomicAuthorityStatusV1.ACTIVE,
    )


def _head(*, sequence: int = 0) -> DurableEconomicPublicationHeadV1:
    return DurableEconomicPublicationHeadV1(
        publication_id=_root(10) if sequence == 0 else _root(30 + sequence),
        sequence=sequence,
        activation_id=_root(10),
        chain_id="tau-testnet",
        deployment_root=_root(11),
        profile_root=_root(13),
        writer_epoch=14,
        height=20 + sequence,
        state_root=_root(40 + sequence),
        commit_id=ZERO_ROOT_V1 if sequence == 0 else _root(50 + sequence),
        certificate_root=_root(60 + sequence),
    )


class _MemoryAnchorBackend:
    def __init__(self, anchor: GlobalEconomicMonotonicAnchorV1) -> None:
        self.current = anchor.canonical_bytes
        self.cas_result: object = True
        self.read_result: object | None = None
        self.raise_on_read = False
        self.ack_without_write = False
        self.advance_after_successful_cas: bytes | None = None

    def read_current_anchor(self, anchor_namespace_root: str) -> object:
        if self.raise_on_read:
            raise OSError("external anchor unavailable")
        return self.current if self.read_result is None else self.read_result

    def compare_and_set_anchor(
        self,
        anchor_namespace_root: str,
        expected_anchor_root: str,
        successor_anchor_bytes: bytes,
    ) -> object:
        if self.cas_result is not True:
            return self.cas_result
        if self.ack_without_write:
            return True
        current = decode_global_economic_monotonic_anchor_v1(self.current)
        if current.anchor_root != expected_anchor_root:
            return False
        self.current = successor_anchor_bytes
        if self.advance_after_successful_cas is not None:
            self.current = self.advance_after_successful_cas
        return True


def _bound_backend(
    backend: _MemoryAnchorBackend,
    *,
    namespace_root: str = _root(1),
):
    artifact = b"measured-anchor-backend-v1"
    release = GlobalEconomicMonotonicAnchorBackendReleaseV1.build(
        semantic_version="1.0.0-shadow",
        implementation_root=(
            global_economic_monotonic_anchor_backend_implementation_root_v1(artifact)
        ),
        specification_root=_root(70),
        source_root=_root(71),
        toolchain_root=_root(72),
        evidence_manifest_root=_root(73),
        backend_protocol_root=(
            global_economic_monotonic_anchor_backend_protocol_root_v1()
        ),
        status=GlobalEconomicMonotonicAnchorBackendStatusV1.SHADOW,
        evidence_statuses=tuple(GlobalEconomicMonotonicAnchorBackendEvidenceStatusV1),
    )
    return bind_global_economic_monotonic_anchor_backend_v1(
        release=release,
        measured_artifact_bytes=artifact,
        anchor_namespace_root=namespace_root,
        chain_id="tau-testnet",
        deployment_root=_root(11),
        backend=backend,
    )


def _genesis_anchor() -> GlobalEconomicMonotonicAnchorV1:
    return build_global_economic_monotonic_anchor_v1(
        anchor_namespace_root=_root(1),
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
        authority=_authority(),
        publication=_head(),
    )


def test_bound_backend_reads_and_cas_advances_one_exact_epoch_anchor() -> None:
    # Arrange
    current = _genesis_anchor()
    backend = _MemoryAnchorBackend(current)
    bound = _bound_backend(backend)
    successor = build_global_economic_epoch_anchor_successor_v1(
        current,
        authority=_authority(),
        publication=_head(sequence=1),
    )

    # Act
    observed = bound._read_current_for_publisher_v1()
    advanced = bound._compare_and_set_for_publisher_v1(current, successor)

    # Assert
    assert observed == current
    assert advanced == successor
    assert bound._read_current_for_publisher_v1() == successor


def test_bound_backend_rejects_wrong_namespace_and_nonbytes_observation() -> None:
    # Arrange
    current = _genesis_anchor()
    backend = _MemoryAnchorBackend(current)
    backend.read_result = {"anchor": current.canonical_bytes}
    bound = _bound_backend(backend)

    # Act / Assert
    with pytest.raises(GlobalEconomicMonotonicAnchorProtocolViolationV1):
        bound._read_current_for_publisher_v1()
    backend.read_result = replace(
        current,
        anchor_namespace_root=_root(2),
    ).canonical_bytes
    with pytest.raises(GlobalEconomicMonotonicAnchorProtocolViolationV1):
        bound._read_current_for_publisher_v1()


def test_bound_backend_maps_transport_failure_and_rejects_truthy_cas_value() -> None:
    # Arrange
    current = _genesis_anchor()
    backend = _MemoryAnchorBackend(current)
    bound = _bound_backend(backend)
    successor = build_global_economic_epoch_anchor_successor_v1(
        current,
        authority=_authority(),
        publication=_head(sequence=1),
    )

    # Act / Assert
    backend.raise_on_read = True
    with pytest.raises(GlobalEconomicMonotonicAnchorUnavailableV1):
        bound._read_current_for_publisher_v1()
    backend.raise_on_read = False
    backend.cas_result = 1
    with pytest.raises(GlobalEconomicMonotonicAnchorProtocolViolationV1):
        bound._compare_and_set_for_publisher_v1(current, successor)
    assert decode_global_economic_monotonic_anchor_v1(backend.current) == current


def test_bound_backend_stale_cas_is_a_no_effect_false_result() -> None:
    # Arrange
    current = _genesis_anchor()
    backend = _MemoryAnchorBackend(current)
    bound = _bound_backend(backend)
    successor = build_global_economic_epoch_anchor_successor_v1(
        current,
        authority=_authority(),
        publication=_head(sequence=1),
    )
    backend.cas_result = False

    # Act
    advanced = bound._compare_and_set_for_publisher_v1(current, successor)

    # Assert
    assert advanced is None
    assert decode_global_economic_monotonic_anchor_v1(backend.current) == current


def test_bound_backend_kills_false_cas_acknowledgment_mutant() -> None:
    # Arrange: the backend lies about installing the successor.
    current = _genesis_anchor()
    backend = _MemoryAnchorBackend(current)
    backend.ack_without_write = True
    bound = _bound_backend(backend)
    successor = build_global_economic_epoch_anchor_successor_v1(
        current,
        authority=_authority(),
        publication=_head(sequence=1),
    )

    # Act / Assert: a success result is independently checked by a current read.
    with pytest.raises(
        GlobalEconomicMonotonicAnchorProtocolViolationV1,
        match="acknowledgment",
    ):
        bound._compare_and_set_for_publisher_v1(current, successor)
    assert decode_global_economic_monotonic_anchor_v1(backend.current) == current


def test_bound_backend_accepts_a_current_forward_observation_after_its_cas() -> None:
    # Arrange: Alice installs epoch one, then Bob validly installs epoch two
    # before Alice's independent confirmation read linearizes.
    current = _genesis_anchor()
    successor = build_global_economic_epoch_anchor_successor_v1(
        current,
        authority=_authority(),
        publication=_head(sequence=1),
    )
    observed_after_concurrent_advance = build_global_economic_epoch_anchor_successor_v1(
        successor,
        authority=_authority(),
        publication=_head(sequence=2),
    )
    backend = _MemoryAnchorBackend(current)
    backend.advance_after_successful_cas = (
        observed_after_concurrent_advance.canonical_bytes
    )
    bound = _bound_backend(backend)

    # Act
    observed = bound._compare_and_set_for_publisher_v1(current, successor)

    # Assert: linearizable progress after Alice's CAS is not a false acknowledgment.
    assert observed == observed_after_concurrent_advance
