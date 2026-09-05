"""Research publisher purpose and measured setup; synthetic ELF is not a proof."""

from pathlib import Path

import pytest

from src.core.economic_receipt_verifier_deployment_v1 import (
    bind_economic_receipt_verifier_deployment_v1,
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierRegistryV1,
    EconomicReceiptVerifierSelectionPurposeV1,
)
from src.core.global_settlement_types_v1 import ProfileStatusV1
from src.integration.global_economic_durable_publisher_v1 import VerifiedDurableEconomicPublisherV1
from tests.core.test_economic_receipt_verifier_release_v1 import (
    _ARTIFACT_BYTES,
    _manifest,
    _RecordingBackend,
    _release,
)
from tests.core.test_global_settlement_abi_v1 import _profile
from tests.integration.test_global_economic_durable_publisher_v1 import (
    _publisher_fixture_v1,
    _receipt_verifier_manifest_v1,
)


def test_shadow_verifier_cannot_construct_economic_publisher(tmp_path: Path) -> None:
    admission, candidate, _body = _publisher_fixture_v1()
    manifest = _receipt_verifier_manifest_v1()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    backend = _RecordingBackend()
    shadow = bind_economic_receipt_verifier_deployment_v1(
        profile=candidate.profile, verifier_registry=registry,
        selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW,
        evidence_manifest=manifest, measured_artifact_bytes=_ARTIFACT_BYTES,
        deployment_root=candidate.pre_state.deployment_root, backend=backend,
    )
    with pytest.raises(ValueError, match="selection purpose"):
        publisher = VerifiedDurableEconomicPublisherV1.create(
            tmp_path / "economic.sqlite", admission, shadow,
        )
        publisher.close()
    assert backend.calls == []
    assert tuple(tmp_path.iterdir()) == ()


def _setup(tmp_path: Path):
    raw = b"\x7fELFsynthetic-measured-transport-fixture"
    path = tmp_path / "verifier"
    path.write_bytes(raw)
    manifest = _manifest(implementation_root=economic_receipt_verifier_implementation_root_v1(raw))
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    profile, _route = _profile(verifier_registry_root=registry.registry_root)
    return path, manifest, registry, profile


def _bind(setup):
    from src.integration.isolated_economic_receipt_verifier_v1 import (
        bind_isolated_economic_root_verifier_v1,
    )

    path, manifest, registry, profile = setup
    return bind_isolated_economic_root_verifier_v1(
        executable_path=str(path), profile=profile, verifier_registry=registry,
        evidence_manifest=manifest, deployment_root="0x" + "55" * 32, timeout_ms=1000,
    )


def test_factory_binds_owned_artifact_to_isolated_purpose(tmp_path: Path) -> None:
    setup = _setup(tmp_path)
    bound = _bind(setup)
    assert bound.selection_purpose is EconomicReceiptVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
    bound.require_binding(
        verifier_registry_root=setup[2].registry_root, profile_root=setup[3].profile_id,
        deployment_root="0x" + "55" * 32, root_image_id=setup[3].root_image_id,
        selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION,
    )


@pytest.mark.parametrize("change", ["different_bytes", "missing", "symlink", "directory", "not_elf"])
def test_factory_rejects_wrong_or_unavailable_artifact(tmp_path: Path, change: str) -> None:
    setup = _setup(tmp_path)
    path = setup[0]
    if change == "different_bytes":
        path.write_bytes(path.read_bytes() + b"changed")
    elif change == "not_elf":
        path.write_bytes(b"#!/bin/sh\nexit 0\n")
    else:
        path.unlink()
        if change == "symlink":
            other = tmp_path / "other"
            other.write_bytes(b"\x7fELFforeign")
            path.symlink_to(other)
        elif change == "directory":
            path.mkdir()
    with pytest.raises((ValueError, RuntimeError)):
        _bind(setup)


def test_replacement_after_binding_rejects_before_process_launch(tmp_path: Path, monkeypatch) -> None:
    import src.integration.global_receipt_verifier_v1 as bridge

    setup = _setup(tmp_path)
    bound = _bind(setup)
    setup[0].write_bytes(b"\x7fELFother executable")
    monkeypatch.setattr(bridge, "_invoke_v1", lambda *_args: pytest.fail("unmeasured executable launched"))
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        bound.verify_succinct_receipt(
            b"receipt", expected_image_id=setup[3].root_image_id,
            expected_journal_bytes=b"journal",
        )
    assert error.value.reason is bridge.GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING


def test_observational_profile_cannot_select_isolated_publisher_purpose(tmp_path: Path) -> None:
    path, manifest, registry, _active = _setup(tmp_path)
    shadow, _route = _profile(verifier_registry_root=registry.registry_root, status=ProfileStatusV1.SHADOW)
    path.unlink()
    with pytest.raises(ValueError, match="active profile semantics"):
        _bind((path, manifest, registry, shadow))


def test_factory_checks_artifact_ceiling_before_reading(tmp_path: Path, monkeypatch) -> None:
    import src.integration.isolated_economic_receipt_verifier_v1 as factory

    setup = _setup(tmp_path)
    with setup[0].open("wb") as output:
        output.truncate(factory.MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1 + 1)
    monkeypatch.setattr(factory.os, "read", lambda *_args: pytest.fail("over-limit artifact read"))
    with pytest.raises(factory.GlobalReceiptVerifierErrorV1) as error:
        _bind(setup)
    assert error.value.reason is factory.GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING


@pytest.mark.parametrize("port", ["backend", "measured_artifact_bytes"])
def test_factory_has_no_caller_backend_or_measurement_port(tmp_path: Path, port: str) -> None:
    from src.integration.isolated_economic_receipt_verifier_v1 import (
        bind_isolated_economic_root_verifier_v1,
    )

    path, manifest, registry, profile = _setup(tmp_path)
    with pytest.raises(TypeError, match="unexpected keyword"):
        bind_isolated_economic_root_verifier_v1(
            executable_path=str(path), profile=profile, verifier_registry=registry,
            evidence_manifest=manifest, deployment_root="0x" + "55" * 32,
            timeout_ms=1000, **{port: _RecordingBackend()},
        )
