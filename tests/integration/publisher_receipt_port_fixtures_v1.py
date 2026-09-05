"""Synthetic process replies for publisher behavior tests, never crypto evidence.

The real measured-set factory acquires each endpoint, and each verification still
remeasures and seals its ELF and checks the exact transport response. Only the
process reply is simulated using an explicitly captured test callback. The real
five-receipt qualification is separate from these journal and fault scenarios.
"""

import hashlib
import struct
from contextlib import contextmanager
from contextvars import ContextVar
from pathlib import Path
from threading import Lock

import pytest

from src.core.economic_receipt_verifier_evidence_v1 import (
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import EconomicReceiptVerifierRegistryV1
from src.core.global_settlement_types_v1 import ReleaseStatusV1
from src.integration import global_receipt_verifier_v1 as bridge
from src.integration.isolated_economic_verifier_set_v1 import (
    IsolatedVerifierArtifactV1,
    read_isolated_verifier_artifact_set_v1,
)
from src.integration.isolated_profile_receipt_ports_v1 import (
    bind_isolated_profile_receipt_ports_v1,
)
from tests.core.test_economic_receipt_verifier_release_v1 import _manifest, _release
from tests.core.test_global_settlement_abi_v1 import _profile, _root


def _images(profile):
    releases = (
        *profile.lane_registry.releases,
        *profile.lane_coordinator_registry.releases,
        *profile.route_registry.routes,
    )
    return tuple(
        sorted(
            {profile.root_image_id}
            | {
                row.guest_image_id
                for row in releases
                if row.status is ReleaseStatusV1.ACTIVE_NEW and row.accepts_new_objects
            }
        )
    )


class _SyntheticProcessV1:
    def __init__(self, directory: Path):
        self.directory = directory
        self.calls = {}
        self.lock = Lock()
        self.sequence = 0
        self.current = ContextVar("publisher_test_verifier_call")
        profile, _route = _profile()
        self.template = self.artifacts(profile, None)

    def artifacts(self, profile, call):
        with self.lock:
            directory = self.directory / str(self.sequence)
            self.sequence += 1
            directory.mkdir()
            rows = []
            for index, image in enumerate(_images(profile)):
                path = directory / f"endpoint-{index}"
                path.write_bytes(
                    b"\x7fELFpublisher-synthetic-process-v1:" + bytes.fromhex(image[2:])
                )
                self.calls[str(path)] = call
                rows.append(IsolatedVerifierArtifactV1(image, str(path)))
        return tuple(rows)

    def manifest(self):
        return _manifest(
            implementation_root=economic_receipt_verifier_implementation_root_v1(
                read_isolated_verifier_artifact_set_v1(self.template)
            ),
            root_image_id=_root(411),
            max_receipt_bytes=4096,
            max_journal_bytes=1048576,
        )

    def invoke(self, executable_fd, request, timeout_ms):
        # This independent transport oracle decodes the specified V1 wire layout.
        assert request[:8] == b"ZDXRV1RQ"
        image = "0x" + request[8:40].hex()
        journal_size, receipt_size = struct.unpack("<II", request[40:48])
        assert len(request) == 48 + journal_size + receipt_size
        journal = request[48 : 48 + journal_size]
        receipt = request[48 + journal_size :]
        call = self.current.get()
        assert call is not None
        result = call(receipt, expected_image_id=image, expected_journal_bytes=journal)
        assert result is None
        return b"ZDXRV1OK" + hashlib.sha256(request).digest() + bytes.fromhex(image[2:]), b"", 0


_CURRENT: _SyntheticProcessV1 | None = None


@pytest.fixture
def simulated_measured_publisher_crypto_v1(tmp_path_factory):
    """Own the synthetic endpoint transport for exactly one test, across its threads."""
    global _CURRENT
    owner = _SyntheticProcessV1(tmp_path_factory.mktemp("publisher-receipt-ports"))
    original_seal = bridge._sealed_executable_v1

    @contextmanager
    def selected_seal(endpoint):
        with original_seal(endpoint) as descriptor:
            token = owner.current.set(owner.calls[endpoint.executable_path])
            try:
                yield descriptor
            finally:
                owner.current.reset(token)

    assert _CURRENT is None
    _CURRENT = owner
    # A test's own monkeypatch.undo() must leave this fixture's transport intact.
    with pytest.MonkeyPatch.context() as patch:
        patch.setattr(bridge, "_sealed_executable_v1", selected_seal)
        patch.setattr(bridge, "_invoke_v1", owner.invoke)
        try:
            yield owner
        finally:
            _CURRENT = None


def _owner():
    if _CURRENT is None:
        raise RuntimeError("publisher test requires simulated_measured_publisher_crypto_v1")
    return _CURRENT


def publisher_receipt_manifest_v1():
    return _owner().manifest()


def publisher_synthetic_artifact_bytes_v1():
    return read_isolated_verifier_artifact_set_v1(_owner().template)


def bind_publisher_test_receipt_ports_v1(candidate, backend):
    owner = _owner()
    manifest = owner.manifest()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    assert registry.registry_root == candidate.profile.verifier_registry_root
    # The callback is explicitly test-only; production constructors accept no backend.
    artifacts = owner.artifacts(candidate.profile, backend.verify_succinct_receipt)
    return bind_isolated_profile_receipt_ports_v1(
        profile=candidate.profile,
        verifier_registry=registry,
        evidence_manifest=manifest,
        artifacts=artifacts,
        deployment_root=candidate.pre_state.deployment_root,
        timeout_ms=1000,
    )
