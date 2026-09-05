"""Measured endpoint-set admission; synthetic ELF fixtures supply no real proof."""

import hashlib
from pathlib import Path

import pytest

from src.core.economic_receipt_verifier_evidence_v1 import (
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import EconomicReceiptVerifierRegistryV1
from src.integration import isolated_economic_verifier_set_v1 as factory
from src.integration.global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1,
    GlobalReceiptVerifierRejectV1,
    GlobalReceiptVerifierV1,
)
from tests.core.test_economic_receipt_verifier_release_v1 import _manifest, _release
from tests.core.test_global_settlement_abi_v1 import _profile, _root


def _setup(tmp_path: Path):
    profile, _route = _profile()
    # The retained profile activates all 12 modules, one asset coordinator and one route.
    images = sorted(
        {
            profile.root_image_id,
            *(row.guest_image_id for row in profile.lane_registry.releases),
            profile.lane_coordinator_registry.releases[0].guest_image_id,
            *(row.guest_image_id for row in profile.route_registry.routes),
        }
    )
    artifacts = []
    expected = b"ZDXVSET1" + len(images).to_bytes(2, "little")
    for index, image in enumerate(images):
        raw = b"\x7fELFsynthetic-verifier-" + index.to_bytes(2, "little")
        path = tmp_path / f"verifier-{index}"
        path.write_bytes(raw)
        artifacts.append(factory.IsolatedVerifierArtifactV1(image, str(path)))
        expected += bytes.fromhex(image[2:]) + len(raw).to_bytes(4, "little") + raw
    manifest = _manifest(
        implementation_root=economic_receipt_verifier_implementation_root_v1(expected)
    )
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    profile, _route = _profile(verifier_registry_root=registry.registry_root)
    return profile, registry, manifest, tuple(artifacts), expected


def _bind(setup, artifacts=None):
    profile, registry, manifest, original, _expected = setup
    return factory.bind_isolated_economic_verifier_set_v1(
        profile=profile,
        verifier_registry=registry,
        evidence_manifest=manifest,
        artifacts=original if artifacts is None else artifacts,
        deployment_root=_root(551),
        timeout_ms=1000,
    )


def test_artifact_commitment_includes_each_exact_image_and_elf_without_local_paths(
    tmp_path: Path,
) -> None:
    setup = _setup(tmp_path)
    assert factory.read_isolated_verifier_artifact_set_v1(setup[3]) == setup[4]
    bound = _bind(setup)
    assert bound.release_id == setup[1].releases[0].release_id


@pytest.mark.parametrize("change", ["missing", "duplicate", "reverse", "foreign"])
def test_incomplete_or_foreign_profile_image_sets_reject_before_artifact_io(
    tmp_path: Path, monkeypatch, change: str
) -> None:
    setup = _setup(tmp_path)
    artifacts = setup[3]
    changed = {
        "missing": artifacts[1:],
        "duplicate": (artifacts[0], *artifacts),
        "reverse": tuple(reversed(artifacts)),
        "foreign": (*artifacts, factory.IsolatedVerifierArtifactV1("0x" + "ff" * 32, "/absent")),
    }[change]
    monkeypatch.setattr(
        factory, "_acquire_artifact_v1", lambda *_args: pytest.fail("invalid image set reached IO")
    )
    with pytest.raises(ValueError, match="artifact"):
        _bind(setup, changed)


def test_changed_nonroot_executable_breaks_the_complete_implementation_commitment(
    tmp_path: Path,
) -> None:
    setup = _setup(tmp_path)
    leaf = next(row for row in setup[3] if row.image_id != setup[0].root_image_id)
    Path(leaf.executable_path).write_bytes(b"\x7fELFchanged-leaf-verifier")
    with pytest.raises(ValueError, match="implementation root mismatch"):
        _bind(setup)


@pytest.mark.parametrize("role", ["root", "module", "coordinator", "route"])
def test_isolated_role_selects_only_its_profile_image_and_measured_executable(
    tmp_path: Path, monkeypatch, role: str
) -> None:
    setup = _setup(tmp_path)
    profile = setup[0]
    calls = []

    def record(endpoint, receipt_bytes, *, expected_image_id, expected_journal_bytes):
        raw = Path(endpoint.executable_path).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == endpoint.executable_sha256
        assert expected_image_id == endpoint.expected_image_id
        calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))

    monkeypatch.setattr(GlobalReceiptVerifierV1, "verify_succinct_receipt", record)
    bound = _bind(setup)
    expected = profile.root_image_id
    keywords = {"expected_image_id": expected, "expected_journal_bytes": b"journal"}
    method = bound.verify_succinct_receipt
    if role == "module":
        release = profile.lane_registry.releases[0]
        expected = release.guest_image_id
        keywords.update(
            profile=profile,
            lane_id=release.lane_id,
            expected_module_release_id=release.release_id,
            expected_image_id=expected,
        )
        method = bound.verify_profile_lane_receipt
    elif role == "coordinator":
        release = profile.lane_coordinator_registry.releases[0]
        expected = release.guest_image_id
        keywords.update(
            profile=profile,
            lane_id=release.lane_id,
            expected_coordinator_release_id=release.coordinator_release_id,
            expected_image_id=expected,
        )
        method = bound.verify_profile_lane_coordinator_receipt
    elif role == "route":
        release = profile.route_registry.routes[0]
        expected = release.guest_image_id
        keywords.update(
            profile=profile,
            expected_route_release_id=release.route_release_id,
            expected_image_id=expected,
        )
        method = bound.verify_profile_route_receipt
    method(b"receipt", **keywords)
    assert calls == [(b"receipt", expected, b"journal")]
    calls.clear()
    with pytest.raises(ValueError, match="image|profile"):
        method(b"receipt", **{**keywords, "expected_image_id": _root(987654)})
    assert calls == []


def test_replaced_root_after_set_binding_rejects_before_process_launch(
    tmp_path: Path, monkeypatch
) -> None:
    import src.integration.global_receipt_verifier_v1 as bridge

    setup = _setup(tmp_path)
    bound = _bind(setup)
    root = next(row for row in setup[3] if row.image_id == setup[0].root_image_id)
    Path(root.executable_path).write_bytes(b"\x7fELFreplaced-root")
    monkeypatch.setattr(
        bridge, "_invoke_v1", lambda *_args: pytest.fail("changed executable launched")
    )
    with pytest.raises(GlobalReceiptVerifierErrorV1) as error:
        bound.verify_succinct_receipt(
            b"receipt", expected_image_id=root.image_id, expected_journal_bytes=b"journal"
        )
    assert error.value.reason is GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING


def test_shadow_coordinator_in_selected_profile_rejects_before_backend(
    tmp_path: Path, monkeypatch
) -> None:
    setup = _setup(tmp_path)
    profile = setup[0]
    shadow = profile.lane_coordinator_registry.releases[1]
    monkeypatch.setattr(
        GlobalReceiptVerifierV1,
        "verify_succinct_receipt",
        lambda *_args, **_kwargs: pytest.fail("shadow release reached verifier"),
    )
    with pytest.raises(ValueError, match="outside isolated status"):
        _bind(setup).verify_profile_lane_coordinator_receipt(
            b"receipt",
            profile=profile,
            lane_id=shadow.lane_id,
            expected_coordinator_release_id=shadow.coordinator_release_id,
            expected_image_id=shadow.guest_image_id,
            expected_journal_bytes=b"journal",
        )


def test_relocating_identical_artifacts_preserves_the_complete_commitment(tmp_path: Path) -> None:
    setup = _setup(tmp_path)
    relocated = []
    for index, row in enumerate(setup[3]):
        destination = tmp_path / f"relocated-{index}"
        destination.write_bytes(Path(row.executable_path).read_bytes())
        relocated.append(factory.IsolatedVerifierArtifactV1(row.image_id, str(destination)))
    assert factory.read_isolated_verifier_artifact_set_v1(tuple(relocated)) == setup[4]
    assert _bind(setup, tuple(relocated)).binding_root == _bind(setup).binding_root


def test_complete_artifact_byte_limit_counts_framing_and_all_endpoints(tmp_path: Path) -> None:
    # Use the actual 32 MiB bound; neither per-file limit alone catches the one-byte excess.
    maximum = factory.MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1
    first = tmp_path / "first-large"
    second = tmp_path / "second-large"
    first.write_bytes(b"\x7fELF" + b"x" * (maximum - 90))
    second.write_bytes(b"\x7fELF")
    artifacts = (
        factory.IsolatedVerifierArtifactV1(_root(1), str(first)),
        factory.IsolatedVerifierArtifactV1(_root(2), str(second)),
    )
    assert len(factory.read_isolated_verifier_artifact_set_v1(artifacts)) == maximum
    second.write_bytes(b"\x7fELFx")
    with pytest.raises(ValueError, match="complete verifier artifact exceeds byte limit"):
        factory.read_isolated_verifier_artifact_set_v1(artifacts)


def test_caller_coordinate_mutation_during_acquisition_cannot_change_owned_selection(
    tmp_path: Path, monkeypatch
) -> None:
    setup = _setup(tmp_path)
    original = setup[3][-1]
    acquire = factory._acquire_artifact_v1
    calls = []

    def mutate_caller(path):
        object.__setattr__(original, "executable_path", "/absent/caller-mutation")
        calls.append(path)
        return acquire(path)

    expected_paths = [row.executable_path for row in setup[3]]
    monkeypatch.setattr(factory, "_acquire_artifact_v1", mutate_caller)
    assert _bind(setup).release_id == setup[1].releases[0].release_id
    assert calls == expected_paths
