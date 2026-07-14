from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
from dataclasses import replace
from pathlib import Path
from typing import Iterator

import pytest

import src.integration._zrpf_spot_v7_operational_capability_v2 as operational_v2
import src.integration.zrpf_spot_v7_full_blob_da_adapter as da_adapter
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedOperationalPolicyMaterialV2,
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _build_test_only_full_blob_artifacts_v1,
    _TestOnlyFullBlobArtifactsV1,
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration.zrpf_spot_v7_full_blob_da_adapter import (
    FullBlobDaAdapterRejectedV1,
    FullBlobDaAdapterRejectV1,
    PinnedFullBlobDataAvailabilityCheckerV1,
)
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[2]
CHECKER_MANIFEST = ROOT / "zk/zrpf_full_blob_da_checker/Cargo.toml"
CHECKER_PACKAGE = "zenodex-zrpf-full-blob-da-checker-v1"


def _hash(seed: int) -> str:
    return "0x" + (bytes([seed]) * 32).hex()


def _test_policy() -> _TestOnlySpotV7OperationalPolicyV1:
    return _TestOnlySpotV7OperationalPolicyV1(
        application_id=_hash(1),
        chain_or_domain_id=_hash(2),
        data_schema_id=_hash(3),
        storage_policy_hash=_hash(4),
        minimum_retention_epochs=20,
        minimum_remaining_epochs=5,
        maximum_blob_bytes=1_024 * 1_024,
        finality_network_id=_hash(5),
        finality_protocol_id=_hash(6),
        external_finality_policy_hash=_hash(7),
        finality_verifier_set_root=_hash(8),
        genesis_application_checkpoint_sequence=0,
        genesis_application_checkpoint_hash=_hash(9),
    )


def _governed_policy(
    value: _TestOnlySpotV7OperationalPolicyV1 | None = None,
) -> _GovernedSpotV7OperationalPolicyV2:
    policy = value or _test_policy()
    return _GovernedSpotV7OperationalPolicyV2(
        _GovernedOperationalPolicyMaterialV2(
            application_id=policy.application_id,
            chain_or_domain_id=policy.chain_or_domain_id,
            data_schema_id=policy.data_schema_id,
            storage_policy_hash=policy.storage_policy_hash,
            minimum_retention_epochs=policy.minimum_retention_epochs,
            minimum_remaining_epochs=policy.minimum_remaining_epochs,
            maximum_blob_bytes=policy.maximum_blob_bytes,
            finality_network_id=policy.finality_network_id,
            finality_protocol_id=policy.finality_protocol_id,
            external_finality_policy_hash=policy.external_finality_policy_hash,
            finality_verifier_set_root=policy.finality_verifier_set_root,
            genesis_application_checkpoint_sequence=(
                policy.genesis_application_checkpoint_sequence
            ),
            genesis_application_checkpoint_hash=(policy.genesis_application_checkpoint_hash),
        ),
        seal=operational_v2._GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    )


def _artifacts(
    policy: _TestOnlySpotV7OperationalPolicyV1 | None = None,
) -> _TestOnlyFullBlobArtifactsV1:
    return _build_test_only_full_blob_artifacts_v1(
        policy=policy or _test_policy(),
        epoch_id=40,
        checked_epoch=52,
        retention_through_epoch=65,
        exact_blob_bytes=b"exact governed full-blob DA bytes\x00\xff",
    )


@pytest.fixture(scope="session")
def rust_checker(tmp_path_factory: pytest.TempPathFactory) -> Iterator[Path]:
    target = tmp_path_factory.mktemp("full-blob-da-rust-target")
    cargo = shutil.which("cargo")
    if cargo is None:
        raise FileNotFoundError("cargo is required for the full-blob DA checker fixture")
    cargo_path = Path(cargo)
    home = os.environ.get("HOME", str(Path.home()))
    environment = {
        "CARGO_HOME": os.environ.get("CARGO_HOME", f"{home}/.cargo"),
        "CARGO_NET_OFFLINE": "true",
        "CARGO_TARGET_DIR": str(target),
        "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS": ("-C target-feature=+crt-static"),
        "HOME": home,
        "PATH": f"{cargo_path.parent}:/usr/bin:/bin",
        "RUSTUP_HOME": os.environ.get("RUSTUP_HOME", f"{home}/.rustup"),
    }
    subprocess.run(
        (
            str(cargo_path),
            "build",
            "--locked",
            "--release",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--manifest-path",
            str(CHECKER_MANIFEST),
            "-p",
            CHECKER_PACKAGE,
        ),
        cwd=ROOT,
        env=environment,
        check=True,
        capture_output=True,
    )
    executable = target / "x86_64-unknown-linux-gnu" / "release" / "zrpf-full-blob-da-checker-v1"
    assert executable.is_file()
    executable.chmod(0o555)
    yield executable


def _manifest(executable: Path, **changes: object) -> bytes:
    document: dict[str, object] = {
        "schema": "zenodex.zrpf.full_blob_da_checker_authority.v1",
        "checker_protocol_version": 1,
        "request_schema": "zenodex.zrpf.full_blob_da_checker.request.v1",
        "response_schema": "zenodex.zrpf.full_blob_da_checker.response.v1",
        "executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "executable_format": "static_elf_x86_64",
        "settlement_authority": False,
        "production_authority": False,
    }
    document.update(changes)
    return canonical_json_bytes(document)


def _checker(
    executable: Path, **manifest_changes: object
) -> PinnedFullBlobDataAvailabilityCheckerV1:
    manifest = _manifest(executable, **manifest_changes)
    return PinnedFullBlobDataAvailabilityCheckerV1(
        executable=executable,
        authority_manifest_json=manifest,
        authority_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
    )


def test_exact_rust_check_mints_policy_and_byte_bound_authority_false_capability(
    rust_checker: Path,
) -> None:
    policy = _governed_policy()
    artifacts = _artifacts()

    result = _checker(rust_checker).check_exact(
        policy=policy,
        expected_certificate_epoch=artifacts.epoch_id,
        checked_epoch=artifacts.checked_epoch,
        exact_certificate_bytes=artifacts.exact_certificate_bytes,
        exact_blob_bytes=artifacts.exact_blob_bytes,
    )

    assert result._governed_policy is policy
    assert result._projection.application_id == _test_policy().application_id
    assert result._projection.chain_or_domain_id == _test_policy().chain_or_domain_id
    assert result._projection.epoch_id == artifacts.epoch_id
    assert result._projection.certificate_root == artifacts.certificate_root
    assert result._projection.data_root == artifacts.data_root
    assert result._projection.policy_root == artifacts.policy_root
    assert result._projection.checked_epoch == artifacts.checked_epoch
    assert result._projection.retention_through_epoch == artifacts.retention_through_epoch
    assert result._exact_certificate_bytes == artifacts.exact_certificate_bytes
    assert result._exact_blob_bytes == artifacts.exact_blob_bytes
    assert result.settlement_authority is False
    assert result.production_authority is False


@pytest.mark.parametrize(
    ("mutation", "reason"),
    (
        ("blob", FullBlobDaAdapterRejectV1.CHECKER_REJECTED),
        ("certificate", FullBlobDaAdapterRejectV1.CHECKER_REJECTED),
        ("expected_epoch", FullBlobDaAdapterRejectV1.CHECKER_REJECTED),
        ("checked_epoch", FullBlobDaAdapterRejectV1.CHECKER_REJECTED),
    ),
)
def test_exact_content_scope_and_retention_mutations_reject_before_mint(
    rust_checker: Path,
    mutation: str,
    reason: FullBlobDaAdapterRejectV1,
) -> None:
    policy = _governed_policy()
    artifacts = _artifacts()
    blob = artifacts.exact_blob_bytes
    certificate = artifacts.exact_certificate_bytes
    expected_epoch = artifacts.epoch_id
    checked_epoch = artifacts.checked_epoch
    if mutation == "blob":
        blob = b"X" + blob[1:]
    elif mutation == "certificate":
        certificate = certificate[:-1] + bytes([certificate[-1] ^ 1])
    elif mutation == "expected_epoch":
        expected_epoch += 1
    else:
        checked_epoch = artifacts.retention_through_epoch

    with pytest.raises(FullBlobDaAdapterRejectedV1) as rejected:
        _checker(rust_checker).check_exact(
            policy=policy,
            expected_certificate_epoch=expected_epoch,
            checked_epoch=checked_epoch,
            exact_certificate_bytes=certificate,
            exact_blob_bytes=blob,
        )

    assert rejected.value.reason is reason


def test_raw_mapping_cannot_stand_in_for_governed_policy(
    rust_checker: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    called = False

    def forbidden(**_kwargs: object) -> bytes:
        nonlocal called
        called = True
        raise AssertionError("checker process must not execute")

    monkeypatch.setattr(da_adapter, "execute_pinned_verifier_once", forbidden)
    artifacts = _artifacts()

    with pytest.raises(TypeError, match="exact governed Spot V7 operational policy"):
        _checker(rust_checker).check_exact(
            policy={"ok": True},
            expected_certificate_epoch=artifacts.epoch_id,
            checked_epoch=artifacts.checked_epoch,
            exact_certificate_bytes=artifacts.exact_certificate_bytes,
            exact_blob_bytes=artifacts.exact_blob_bytes,
        )

    assert called is False


@pytest.mark.parametrize(
    ("field", "replacement"),
    (
        ("expected_certificate_epoch", True),
        ("checked_epoch", -1),
        ("exact_certificate_bytes", b""),
        ("exact_blob_bytes", b""),
    ),
)
def test_invalid_request_values_reject_before_checker_execution(
    rust_checker: Path,
    monkeypatch: pytest.MonkeyPatch,
    field: str,
    replacement: object,
) -> None:
    called = False

    def forbidden(**_kwargs: object) -> bytes:
        nonlocal called
        called = True
        raise AssertionError("checker process must not execute")

    monkeypatch.setattr(da_adapter, "execute_pinned_verifier_once", forbidden)
    artifacts = _artifacts()
    request: dict[str, object] = {
        "policy": _governed_policy(),
        "expected_certificate_epoch": artifacts.epoch_id,
        "checked_epoch": artifacts.checked_epoch,
        "exact_certificate_bytes": artifacts.exact_certificate_bytes,
        "exact_blob_bytes": artifacts.exact_blob_bytes,
    }
    request[field] = replacement

    with pytest.raises(FullBlobDaAdapterRejectedV1) as rejected:
        _checker(rust_checker).check_exact(**request)  # type: ignore[arg-type]

    assert rejected.value.reason is FullBlobDaAdapterRejectV1.REQUEST_INVALID
    assert called is False


@pytest.mark.parametrize(
    "changes",
    (
        {"settlement_authority": True},
        {"production_authority": 0},
        {"checker_protocol_version": 2},
        {"unknown": "field"},
        {"executable_format": "test_script"},
    ),
)
def test_authority_manifest_fail_closed(changes: dict[str, object], rust_checker: Path) -> None:
    with pytest.raises(FullBlobDaAdapterRejectedV1) as rejected:
        _checker(rust_checker, **changes)

    assert rejected.value.reason is FullBlobDaAdapterRejectV1.AUTHORITY_MANIFEST_INVALID


def test_noncanonical_or_digest_mismatched_authority_manifest_rejects(
    rust_checker: Path,
) -> None:
    canonical = _manifest(rust_checker)
    noncanonical = canonical.replace(b",", b", ", 1)
    with pytest.raises(FullBlobDaAdapterRejectedV1) as rejected_noncanonical:
        PinnedFullBlobDataAvailabilityCheckerV1(
            executable=rust_checker,
            authority_manifest_json=noncanonical,
            authority_manifest_sha256=hashlib.sha256(noncanonical).hexdigest(),
        )
    with pytest.raises(FullBlobDaAdapterRejectedV1) as rejected_digest:
        PinnedFullBlobDataAvailabilityCheckerV1(
            executable=rust_checker,
            authority_manifest_json=canonical,
            authority_manifest_sha256="00" * 32,
        )

    assert (
        rejected_noncanonical.value.reason is FullBlobDaAdapterRejectV1.AUTHORITY_MANIFEST_INVALID
    )
    assert rejected_digest.value.reason is FullBlobDaAdapterRejectV1.AUTHORITY_MANIFEST_INVALID


def test_executable_digest_substitution_rejects_before_response_is_trusted(
    rust_checker: Path,
) -> None:
    manifest = _manifest(rust_checker, executable_sha256="00" * 32)
    checker = PinnedFullBlobDataAvailabilityCheckerV1(
        executable=rust_checker,
        authority_manifest_json=manifest,
        authority_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
    )
    artifacts = _artifacts()

    with pytest.raises(FullBlobDaAdapterRejectedV1) as rejected:
        checker.check_exact(
            policy=_governed_policy(),
            expected_certificate_epoch=artifacts.epoch_id,
            checked_epoch=artifacts.checked_epoch,
            exact_certificate_bytes=artifacts.exact_certificate_bytes,
            exact_blob_bytes=artifacts.exact_blob_bytes,
        )

    assert rejected.value.reason is FullBlobDaAdapterRejectV1.CHECKER_REJECTED


def test_response_parser_rejects_every_single_byte_mutation(rust_checker: Path) -> None:
    policy = _governed_policy()
    artifacts = _artifacts()
    request = da_adapter._encode_checker_request_v1(
        da_adapter._FullBlobDaCheckInputV1(
            policy,
            artifacts.epoch_id,
            artifacts.checked_epoch,
            artifacts.exact_certificate_bytes,
            artifacts.exact_blob_bytes,
        )
    )
    accepted = subprocess.run(
        (str(rust_checker),),
        input=request,
        check=True,
        capture_output=True,
    ).stdout
    expected = da_adapter._ExpectedFullBlobDaResponseV1(
        request_sha256=hashlib.sha256(request).digest(),
        application_id=bytes.fromhex(_test_policy().application_id[2:]),
        chain_or_domain_id=bytes.fromhex(_test_policy().chain_or_domain_id[2:]),
        expected_certificate_epoch=artifacts.epoch_id,
        policy_root=bytes.fromhex(artifacts.policy_root[2:]),
        exact_certificate_sha256=hashlib.sha256(artifacts.exact_certificate_bytes).digest(),
        exact_blob_sha256=hashlib.sha256(artifacts.exact_blob_bytes).digest(),
        checked_epoch=artifacts.checked_epoch,
    )
    parsed = da_adapter._parse_checker_response_v1(accepted, expected=expected)
    assert parsed.retention_through_epoch == artifacts.retention_through_epoch

    for index in range(len(accepted)):
        mutated = bytearray(accepted)
        mutated[index] ^= 1
        with pytest.raises(FullBlobDaAdapterRejectedV1) as rejected:
            da_adapter._parse_checker_response_v1(bytes(mutated), expected=expected)
        assert rejected.value.reason is FullBlobDaAdapterRejectV1.CHECKER_RESPONSE_INVALID


def test_capability_rejects_policy_projection_substitution() -> None:
    original = _governed_policy()
    changed_test_policy = replace(_test_policy(), minimum_remaining_epochs=6)
    changed = _governed_policy(changed_test_policy)
    artifacts = _artifacts()
    projection = operational_v2._GovernedFullBlobPolicyProjectionV1(
        application_id=_test_policy().application_id,
        chain_or_domain_id=_test_policy().chain_or_domain_id,
        epoch_id=artifacts.epoch_id,
        certificate_root=artifacts.certificate_root,
        data_root=artifacts.data_root,
        policy_root=artifacts.policy_root,
        exact_blob_sha256=artifacts.blob_sha256,
        checked_epoch=artifacts.checked_epoch,
        retention_through_epoch=artifacts.retention_through_epoch,
    )

    with pytest.raises(ValueError, match="policy projection"):
        operational_v2._GovernedExactFullBlobPolicySatisfactionV2(
            projection,
            governed_policy=changed,
            exact_blob_bytes=artifacts.exact_blob_bytes,
            exact_certificate_bytes=artifacts.exact_certificate_bytes,
            seal=operational_v2._GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
        )

    assert original._projection.full_blob_da_policy_root == artifacts.policy_root


def test_adapter_source_uses_shared_pre_exec_runner_without_direct_spawn() -> None:
    source = Path(da_adapter.__file__).read_text(encoding="utf-8")

    assert "execute_pinned_verifier_once(" in source
    assert "subprocess.Popen" not in source
    assert "resource.prlimit" not in source
