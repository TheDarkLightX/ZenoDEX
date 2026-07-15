from __future__ import annotations

import copy
import hashlib
from pathlib import Path
from typing import Any

import pytest

from tools import check_zrpf_stage_execution_profile_v1 as execution_profile
from tools import zrpf_paid_run_prerequisites_v1 as checker

CURRENT_EPOCH = 2_000_000


def _sha(marker: str) -> str:
    return hashlib.sha256(marker.encode()).hexdigest()


def _artifact(marker: str, size: int) -> dict[str, object]:
    return {"sha256": _sha(marker), "size_bytes": size}


def _authority() -> dict[str, bool]:
    return dict(checker.AUTHORITY_FALSE)


def _profile() -> dict[str, Any]:
    journal = _artifact("journal", 431)
    result: dict[str, Any] = {
        "schema": execution_profile.SCHEMA,
        "status": execution_profile.STATUS,
        "profile_record_id": checker.ZERO_SHA256,
        "stage_id": "source_spot_proof",
        "proof_profile_id": checker.PROOF_PROFILE,
        "prover_compute_profile_id": checker.CUDA_COMPUTE_PROFILE,
        "program": {
            "artifact": _artifact("program-603", 603),
            "image_id": _sha("source-image"),
        },
        "r0vm": _artifact("cuda-r0vm", 108_998_817),
        "guest_input": _artifact("guest-input", 947),
        "assumptions": [],
        "expected_journal": journal,
        "observed_journal": copy.deepcopy(journal),
        "receipt_claim_sha256": _sha("receipt-claim"),
        "segment_limit_po2": 20,
        "segments": [
            {
                "ordinal": 0,
                "po2": 19,
                "user_cycles": 345_679,
                "padded_cycle_capacity": 1 << 19,
            }
        ],
        "segment_count": 1,
        "total_user_cycles": 345_679,
        "total_padded_cycle_capacity": 1 << 19,
        "exit_system": 0,
        "exit_user": 0,
        "duration_milliseconds": 137,
        "authority": {field: False for field in execution_profile.AUTHORITY_FIELDS},
        "non_claims": list(execution_profile.NON_CLAIMS),
    }
    result["profile_record_id"] = execution_profile._derive_record_id(result)
    return result


def _build(profile: dict[str, Any]) -> dict[str, Any]:
    result: dict[str, Any] = {
        "schema": checker.BUILD_SCHEMA,
        "status": checker.BUILD_STATUS,
        "build_attestation_id": checker.ZERO_SHA256,
        "source_repository": checker.RISC0_REPOSITORY,
        "source_tag": checker.RISC0_TAG,
        "source_commit": checker.RISC0_COMMIT,
        "rust_toolchain": checker.RUST_TOOLCHAIN,
        "cargo_lock_sha256": _sha("lock"),
        "dependency_source_root": _sha("sources"),
        "builder_image_sha256": _sha("builder"),
        "cuda_toolkit_version": "12.8.1",
        "nvcc_version": "12.8.93",
        "nvcc_flags": ["--generate-code", "arch=compute_90,code=sm_90"],
        "host_target": "x86_64-unknown-linux-gnu",
        "linker_identity": "GNU ld 2.42 position-distinct",
        "package": checker.R0VM_PACKAGE,
        "features": list(checker.R0VM_FEATURES),
        "risc0_skip_build_kernels": False,
        "output_r0vm": copy.deepcopy(profile["r0vm"]),
        "runtime_dependency_root": _sha("runtime"),
        "source_archive_root": _sha("archive"),
        "authority": _authority(),
    }
    result["build_attestation_id"] = checker.derive_build_attestation_id(result)
    return result


def _preflight(profile: dict[str, Any]) -> dict[str, Any]:
    result: dict[str, Any] = {
        "schema": checker.PREFLIGHT_SCHEMA,
        "status": checker.PREFLIGHT_STATUS,
        "h100_preflight_id": checker.ZERO_SHA256,
        "observed_at_epoch_seconds": CURRENT_EPOCH - 100,
        "valid_until_epoch_seconds": CURRENT_EPOCH + 100,
        "gpu": {
            "model_id": checker.H100_MODEL_ID,
            "uuid": "GPU-a17c29e4-5b63-4d08-9f21-731ace9046bd",
            "name": "NVIDIA H100 80GB HBM3",
            "compute_capability_major": 9,
            "compute_capability_minor": 0,
            "memory_total_bytes": 80_000_000_000,
            "driver_version": "570.86.15",
        },
        "r0vm": copy.deepcopy(profile["r0vm"]),
        "runtime_image_sha256": _sha("runtime-image"),
        "visible_device_count": 1,
        "visible_device_ordinal": 0,
        "cuda_visible_devices": "0",
        "authority": _authority(),
    }
    result["h100_preflight_id"] = checker.derive_h100_preflight_id(result)
    return result


def _fixture(tmp_path: Path) -> tuple[dict[str, dict[str, Any]], dict[str, Path]]:
    tmp_path.mkdir(parents=True, exist_ok=True)
    profile = _profile()
    documents = {
        "profile": profile,
        "build": _build(profile),
        "preflight": _preflight(profile),
    }
    paths: dict[str, Path] = {}
    for role, document in documents.items():
        path = tmp_path / f"{role}.json"
        path.write_bytes(checker.canonical_bytes(document))
        paths[role] = path
    return documents, paths


def _validate(paths: dict[str, Path]) -> checker.ValidatedPrerequisites:
    return checker.validate_prerequisites(
        paths["profile"],
        paths["build"],
        paths["preflight"],
        expected_stage="source_spot_proof",
        trusted_current_epoch_seconds=CURRENT_EPOCH,
    )


def _rewrite(path: Path, document: dict[str, Any], identity_field: str) -> None:
    if identity_field == "build_attestation_id":
        document[identity_field] = checker.derive_build_attestation_id(document)
    elif identity_field == "h100_preflight_id":
        document[identity_field] = checker.derive_h100_preflight_id(document)
    path.write_bytes(checker.canonical_bytes(document))


def test_exact_prerequisites_bind_profile_build_preflight_and_shape(
    tmp_path: Path,
) -> None:
    documents, paths = _fixture(tmp_path)

    result = _validate(paths)

    assert result.profile.document == documents["profile"]
    assert result.build.document["output_r0vm"] == result.profile.document["r0vm"]
    assert result.preflight.document["r0vm"] == result.profile.document["r0vm"]
    assert result.execution_shape["segment_count"] == 1


def test_cpu_profile_r0vm_substitution_and_stale_h100_reject(tmp_path: Path) -> None:
    documents, paths = _fixture(tmp_path / "cpu")
    documents["profile"]["prover_compute_profile_id"] = "risc0_ipc_cpu_v1"
    documents["profile"]["profile_record_id"] = execution_profile._derive_record_id(
        documents["profile"]
    )
    paths["profile"].write_bytes(checker.canonical_bytes(documents["profile"]))
    with pytest.raises(checker.PrerequisiteError, match="compute profile"):
        _validate(paths)

    documents, paths = _fixture(tmp_path / "r0vm")
    documents["build"]["output_r0vm"] = _artifact("substitute", 108_998_817)
    _rewrite(paths["build"], documents["build"], "build_attestation_id")
    with pytest.raises(checker.PrerequisiteError, match="r0vm identity"):
        _validate(paths)

    documents, paths = _fixture(tmp_path / "stale")
    documents["preflight"]["valid_until_epoch_seconds"] = CURRENT_EPOCH - 1
    _rewrite(paths["preflight"], documents["preflight"], "h100_preflight_id")
    with pytest.raises(checker.PrerequisiteError, match="not current"):
        _validate(paths)


@pytest.mark.parametrize("role", ["build", "preflight"])
def test_authority_promotion_rejects(tmp_path: Path, role: str) -> None:
    documents, paths = _fixture(tmp_path)
    documents[role]["authority"]["production_authority"] = True
    identity = "build_attestation_id" if role == "build" else "h100_preflight_id"
    _rewrite(paths[role], documents[role], identity)

    with pytest.raises(checker.PrerequisiteError, match="must remain false"):
        _validate(paths)


def test_noncanonical_and_duplicate_json_reject(tmp_path: Path) -> None:
    _, paths = _fixture(tmp_path / "whitespace")
    paths["build"].write_bytes(paths["build"].read_bytes() + b"\n")
    with pytest.raises(checker.PrerequisiteError, match="not canonical"):
        _validate(paths)

    _, paths = _fixture(tmp_path / "duplicate")
    raw = paths["preflight"].read_bytes()
    paths["preflight"].write_bytes(raw.replace(b'{"schema":', b'{"schema":"shadow","schema":', 1))
    with pytest.raises(checker.PrerequisiteError, match="decode failed"):
        _validate(paths)


def test_integer_cannot_substitute_for_cuda_build_boolean(tmp_path: Path) -> None:
    documents, paths = _fixture(tmp_path)
    documents["build"]["risc0_skip_build_kernels"] = 0
    _rewrite(paths["build"], documents["build"], "build_attestation_id")

    with pytest.raises(checker.PrerequisiteError, match="exact false"):
        _validate(paths)
