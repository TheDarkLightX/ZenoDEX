"""Profile ports over measured synthetic ELFs; endpoint mocks prove no cryptography."""

import copy
import dataclasses
import hashlib
import inspect
import pickle
from pathlib import Path

import pytest

from src.core import global_settlement_types_v1 as abi
from src.core.economic_receipt_verifier_evidence_v1 import (
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import EconomicReceiptVerifierRegistryV1
from src.integration import isolated_profile_receipt_ports_v1 as ports
from src.integration.global_receipt_verifier_v1 import GlobalReceiptVerifierV1
from src.integration.isolated_economic_verifier_set_v1 import (
    IsolatedVerifierArtifactV1,
    read_isolated_verifier_artifact_set_v1,
)
from tests.core.test_economic_receipt_verifier_release_v1 import _manifest, _release
from tests.core.test_global_settlement_abi_v1 import _profile, _root


def _rebuild(profile, **changes):
    values = {
        field.name: getattr(profile, field.name)
        for field in dataclasses.fields(profile)
        if field.name != "profile_id"
    }
    return abi.EconomicProfileSnapshotV1.build(**{**values, **changes})


def _setup(tmp_path):
    profile, _ = _profile()
    disabled = dict(
        status=abi.ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
        evidence_statuses=(abi.EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,),
    )
    lanes = abi.LaneRegistryV1(
        tuple(
            row
            if row.lane_id is abi.LaneIdV1.ASSET_TRANSFER
            else dataclasses.replace(row, **disabled)
            for row in profile.lane_registry.releases
        )
    )
    coordinators = abi.LaneCoordinatorRegistryV1(
        tuple(
            row
            if row.lane_id is abi.LaneIdV1.ASSET_TRANSFER
            else dataclasses.replace(row, **disabled)
            for row in profile.lane_coordinator_registry.releases
        )
    )
    profile = _rebuild(profile, lane_registry=lanes, lane_coordinator_registry=coordinators)
    images = sorted(
        (
            profile.root_image_id,
            lanes.releases[0].guest_image_id,
            coordinators.releases[0].guest_image_id,
            profile.route_registry.routes[0].guest_image_id,
        )
    )
    artifacts = []
    for index, image in enumerate(images):
        path = tmp_path / f"endpoint-{index}"
        path.write_bytes(b"\x7fELFexplicit-synthetic-port-test-" + bytes([index]))
        artifacts.append(IsolatedVerifierArtifactV1(image, str(path)))
    artifacts = tuple(artifacts)
    manifest = _manifest(
        implementation_root=economic_receipt_verifier_implementation_root_v1(
            read_isolated_verifier_artifact_set_v1(artifacts)
        )
    )
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    return dict(
        profile=_rebuild(profile, verifier_registry_root=registry.registry_root),
        verifier_registry=registry,
        evidence_manifest=manifest,
        artifacts=artifacts,
        deployment_root=_root(551),
        timeout_ms=1000,
    )


def _selected(scope, profile, role):
    lane = abi.LaneIdV1.ASSET_TRANSFER
    if role == "root":
        return scope.root_port(), profile.root_image_id
    if role == "module":
        return scope.module_port(lane), profile.lane_registry.release_for(lane).guest_image_id
    if role == "coordinator":
        return scope.coordinator_port(lane), profile.lane_coordinator_registry.release_for(
            lane
        ).guest_image_id
    route = profile.route_registry.routes[0]
    return scope.route_port(route.route_release_id), route.guest_image_id


def _record_endpoint(monkeypatch):
    calls = []

    def record(endpoint, receipt_bytes, *, expected_image_id, expected_journal_bytes):
        assert (
            hashlib.sha256(Path(endpoint.executable_path).read_bytes()).hexdigest()
            == endpoint.executable_sha256
        )
        assert endpoint.expected_image_id == expected_image_id
        calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))

    monkeypatch.setattr(GlobalReceiptVerifierV1, "verify_succinct_receipt", record)
    return calls


@pytest.mark.parametrize("role", ["root", "module", "coordinator", "route"])
def test_each_port_keeps_exact_role_profile_image_and_journal(tmp_path, monkeypatch, role):
    setup = _setup(tmp_path)
    calls = _record_endpoint(monkeypatch)
    scope = ports.bind_isolated_profile_receipt_ports_v1(**setup)
    port, image = _selected(scope, setup["profile"], role)
    assert (
        port.verify_succinct_receipt(
            b"receipt", expected_image_id=image, expected_journal_bytes=b"journal"
        )
        is None
    )
    assert calls == [(b"receipt", image, b"journal")]
    calls.clear()
    for foreign in ("root", "module", "coordinator", "route"):
        if foreign != role:
            _, wrong_image = _selected(scope, setup["profile"], foreign)
            with pytest.raises(ValueError, match="image|profile"):
                port.verify_succinct_receipt(
                    b"receipt", expected_image_id=wrong_image, expected_journal_bytes=b"journal"
                )
    assert calls == []


def test_private_publisher_mount_requires_minted_handle_and_all_current_bindings(tmp_path):
    setup = _setup(tmp_path)
    scope = ports.bind_isolated_profile_receipt_ports_v1(**setup)
    coordinates = dict(
        profile=setup["profile"],
        verifier_registry_root=setup["verifier_registry"].registry_root,
        deployment_root=setup["deployment_root"],
    )
    bound = ports._bound_isolated_profile_receipt_verifier_v1(scope, **coordinates)
    assert bound is ports._bound_isolated_profile_receipt_verifier_v1(scope, **coordinates)
    for changed in (
        {"deployment_root": _root(999)},
        {"verifier_registry_root": _root(999)},
        {"profile": _rebuild(setup["profile"], authority_epoch=8)},
        {"profile": dataclasses.replace(setup["profile"], status=abi.ProfileStatusV1.SHADOW)},
    ):
        with pytest.raises(ValueError, match="binding|ACTIVE"):
            ports._bound_isolated_profile_receipt_verifier_v1(scope, **{**coordinates, **changed})
    for forged in (bound, object(), object.__new__(ports.IsolatedProfileReceiptPortsV1)):
        with pytest.raises((TypeError, ValueError), match="factory|minted"):
            ports._bound_isolated_profile_receipt_verifier_v1(forged, **coordinates)


def test_caller_alias_mutation_cannot_replace_captured_profile_or_receipt_call(
    tmp_path, monkeypatch
):
    setup = _setup(tmp_path)
    calls = _record_endpoint(monkeypatch)
    scope = ports.bind_isolated_profile_receipt_ports_v1(**setup)
    port, image = _selected(scope, setup["profile"], "module")
    object.__setattr__(setup["profile"].lane_registry.releases[0], "guest_image_id", _root(999))
    object.__setattr__(setup["profile"], "profile_id", _root(999))
    port.verify_succinct_receipt(
        b"receipt", expected_image_id=image, expected_journal_bytes=b"journal"
    )
    assert calls == [(b"receipt", image, b"journal")]
    for handle in (scope, port):
        with pytest.raises(AttributeError):
            object.__setattr__(handle, "_authority", lambda *args: None)
        for clone in (copy.copy, copy.deepcopy, pickle.dumps):
            with pytest.raises(TypeError):
                clone(handle)


def test_disabled_missing_or_noncanonical_selectors_never_reach_endpoint(tmp_path, monkeypatch):
    setup = _setup(tmp_path)
    calls = _record_endpoint(monkeypatch)
    scope = ports.bind_isolated_profile_receipt_ports_v1(**setup)
    for select in (scope.module_port, scope.coordinator_port):
        with pytest.raises(ValueError, match="accepting"):
            select(abi.LaneIdV1.SPOT_LIQUIDITY)
        for malformed in ("ASSET_TRANSFER", True, None):
            with pytest.raises(TypeError, match="lane"):
                select(malformed)
    with pytest.raises(ValueError, match="route"):
        scope.route_port(_root(999))
    assert calls == []


def test_forged_ports_and_public_constructors_cannot_supply_authority(tmp_path, monkeypatch):
    calls = _record_endpoint(monkeypatch)
    for cls in (ports.IsolatedProfileReceiptPortsV1, ports.IsolatedReceiptPortV1):
        with pytest.raises(TypeError, match="factory"):
            cls()
    forged = object.__new__(ports.IsolatedReceiptPortV1)
    with pytest.raises(ValueError, match="minted"):
        forged.verify_succinct_receipt(
            b"receipt", expected_image_id=_root(1), expected_journal_bytes=b"journal"
        )
    assert calls == []
    signature = inspect.signature(ports.bind_isolated_profile_receipt_ports_v1)
    assert set(signature.parameters) == {
        "profile",
        "verifier_registry",
        "evidence_manifest",
        "artifacts",
        "deployment_root",
        "timeout_ms",
    }


def test_subclass_forgery_is_refused_before_user_hash_hooks():
    hashes = []

    class ForeignPort(ports.IsolatedReceiptPortV1):
        def __hash__(self):
            hashes.append(self)
            return 1

    class ForeignScope(ports.IsolatedProfileReceiptPortsV1):
        def __hash__(self):
            hashes.append(self)
            return 1

    with pytest.raises(TypeError, match="exact factory type"):
        object.__new__(ForeignPort).verify_succinct_receipt(
            b"receipt", expected_image_id=_root(1), expected_journal_bytes=b"journal"
        )
    with pytest.raises(TypeError, match="exact factory type"):
        object.__new__(ForeignScope).root_port()
    assert hashes == []


def test_backend_refusal_and_receipt_bounds_remain_fail_closed(tmp_path, monkeypatch):
    setup = _setup(tmp_path)
    scope = ports.bind_isolated_profile_receipt_ports_v1(**setup)
    port, image = _selected(scope, setup["profile"], "route")
    calls = _record_endpoint(monkeypatch)
    for payload in (bytearray(b"receipt"), b"x" * 17):
        with pytest.raises((TypeError, ValueError)):
            port.verify_succinct_receipt(
                payload, expected_image_id=image, expected_journal_bytes=b"journal"
            )
    assert calls == []

    def refuse(*args, **kwargs):
        raise RuntimeError("isolated verifier unavailable")

    monkeypatch.setattr(GlobalReceiptVerifierV1, "verify_succinct_receipt", refuse)
    with pytest.raises(RuntimeError, match="unavailable"):
        port.verify_succinct_receipt(
            b"receipt", expected_image_id=image, expected_journal_bytes=b"journal"
        )
