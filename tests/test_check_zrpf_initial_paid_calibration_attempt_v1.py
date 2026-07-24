from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
from typing import Any, Callable

import pytest

from tools import check_zrpf_initial_paid_calibration_attempt_v1 as checker
from tools import check_zrpf_stage_execution_profile_v1 as execution_profile
from tools import plan_zrpf_remote_reproof_handoff_v2 as handoff
from tools import zrpf_paid_run_prerequisites_v1 as shared

CURRENT_EPOCH = 2_000_000


def _sha(marker: str) -> str:
    return hashlib.sha256(marker.encode("utf-8")).hexdigest()


def _artifact(marker: str, size: int) -> dict[str, object]:
    return {"sha256": _sha(marker), "size_bytes": size}


def _authority() -> dict[str, bool]:
    return dict(checker.AUTHORITY_FALSE)


def _shape(profile: dict[str, Any]) -> dict[str, object]:
    return {
        "segment_limit_po2": profile["segment_limit_po2"],
        "segment_shape_sha256": shared.derive_segment_shape_sha256(profile["segments"]),
        "segment_count": profile["segment_count"],
        "total_user_cycles": profile["total_user_cycles"],
        "total_padded_cycle_capacity": profile["total_padded_cycle_capacity"],
    }


def _profile() -> dict[str, Any]:
    journal = _artifact("source-journal-position-distinct", 431)
    result: dict[str, Any] = {
        "schema": execution_profile.SCHEMA,
        "status": execution_profile.STATUS,
        "profile_record_id": checker.ZERO_SHA256,
        "stage_id": checker.SOURCE_STAGE_ID,
        "proof_profile_id": shared.PROOF_PROFILE,
        "prover_compute_profile_id": shared.CUDA_COMPUTE_PROFILE,
        "program": {
            "artifact": _artifact("source-program-position-distinct-603", 603),
            "image_id": _sha("source-program-image-v1"),
        },
        "r0vm": _artifact("cuda-r0vm-sm90-position-1603", 108_998_817),
        "guest_input": _artifact("source-guest-input-position-947", 947),
        "assumptions": [],
        "expected_journal": journal,
        "observed_journal": copy.deepcopy(journal),
        "receipt_claim_sha256": _sha("source-receipt-claim"),
        "segment_limit_po2": 20,
        "segments": [
            {
                "ordinal": 0,
                "po2": 19,
                "user_cycles": 345_679,
                "padded_cycle_capacity": 1 << 19,
            },
            {
                "ordinal": 1,
                "po2": 20,
                "user_cycles": 456_791,
                "padded_cycle_capacity": 1 << 20,
            },
        ],
        "segment_count": 2,
        "total_user_cycles": 802_470,
        "total_padded_cycle_capacity": (1 << 19) + (1 << 20),
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
        "schema": shared.BUILD_SCHEMA,
        "status": shared.BUILD_STATUS,
        "build_attestation_id": checker.ZERO_SHA256,
        "source_repository": shared.RISC0_REPOSITORY,
        "source_tag": shared.RISC0_TAG,
        "source_commit": shared.RISC0_COMMIT,
        "rust_toolchain": shared.RUST_TOOLCHAIN,
        "cargo_lock_sha256": _sha("risc0-3.0.5-cargo-lock"),
        "dependency_source_root": _sha("dependency-source-root"),
        "builder_image_sha256": _sha("builder-image-cuda-12.8"),
        "cuda_toolkit_version": "12.8.1",
        "nvcc_version": "12.8.93",
        "nvcc_flags": ["--generate-code", "arch=compute_90,code=sm_90"],
        "host_target": "x86_64-unknown-linux-gnu",
        "linker_identity": "GNU ld 2.42 sha256:position-distinct",
        "package": shared.R0VM_PACKAGE,
        "features": list(shared.R0VM_FEATURES),
        "risc0_skip_build_kernels": False,
        "output_r0vm": copy.deepcopy(profile["r0vm"]),
        "runtime_dependency_root": _sha("cuda-runtime-dependencies-sm90"),
        "source_archive_root": _sha("risc0-source-archive-v3.0.5"),
        "authority": _authority(),
    }
    result["build_attestation_id"] = shared.derive_build_attestation_id(result)
    return result


def _gpu() -> dict[str, object]:
    return {
        "model_id": shared.H100_MODEL_ID,
        "uuid": "GPU-a17c29e4-5b63-4d08-9f21-731ace9046bd",
        "name": "NVIDIA H100 80GB HBM3",
        "compute_capability_major": 9,
        "compute_capability_minor": 0,
        "memory_total_bytes": 80_000_000_000,
        "driver_version": "570.86.15",
    }


def _preflight(profile: dict[str, Any]) -> dict[str, Any]:
    result: dict[str, Any] = {
        "schema": shared.PREFLIGHT_SCHEMA,
        "status": shared.PREFLIGHT_STATUS,
        "h100_preflight_id": checker.ZERO_SHA256,
        "observed_at_epoch_seconds": CURRENT_EPOCH - 100,
        "valid_until_epoch_seconds": CURRENT_EPOCH + 100,
        "gpu": _gpu(),
        "r0vm": copy.deepcopy(profile["r0vm"]),
        "runtime_image_sha256": _sha("runpod-h100-runtime-image"),
        "visible_device_count": 1,
        "visible_device_ordinal": 0,
        "cuda_visible_devices": "0",
        "authority": _authority(),
    }
    result["h100_preflight_id"] = shared.derive_h100_preflight_id(result)
    return result


def _packet() -> dict[str, Any]:
    result: dict[str, Any] = {
        "schema": handoff.EXECUTION_PACKET_SCHEMA,
        "status": "exact_inputs_bound_without_execution_provenance",
        "execution_packet_id": checker.ZERO_SHA256,
        "handoff_id": _sha("exact-handoff-v5"),
        "source_binding_id": _sha("exact-source-binding"),
        "task_id": _sha("source-spot-proof-task"),
        "stage_id": checker.SOURCE_STAGE_ID,
        "ordinal": checker.SOURCE_STAGE_ORDINAL,
        "worker_commit": "12" * 20,
        "worker_tree": "34" * 20,
        "proof_profile_id": shared.PROOF_PROFILE,
        "input_artifact_ids": [
            _sha("source-request-artifact"),
            _sha("source-program-artifact"),
            _sha("source-profile-artifact"),
            _sha("cuda-r0vm-artifact"),
        ],
        "input_publication_marker_ids": [
            _sha("identity-publication-marker"),
            _sha("ancestry-publication-marker"),
            _sha("worker-build-publication-marker"),
            _sha("source-profile-publication-marker"),
        ],
        "authority": handoff.false_authority(),
        "non_claims": list(handoff.NON_CLAIMS),
    }
    result["execution_packet_id"] = handoff.derive_execution_packet_id(result)
    return result


def _budget(
    profile: dict[str, Any],
    build: dict[str, Any],
    preflight: dict[str, Any],
    packet: dict[str, Any],
) -> dict[str, Any]:
    return {
        "schema": checker.ATTEMPT_BUDGET_SCHEMA,
        "status": checker.ATTEMPT_BUDGET_STATUS,
        "attempt_budget_record_id": checker.ZERO_SHA256,
        "execution_profile_sha256": _sha("unanchored-profile"),
        "execution_profile_record_id": profile["profile_record_id"],
        "cuda_build_attestation_id": build["build_attestation_id"],
        "h100_preflight_id": preflight["h100_preflight_id"],
        "execution_packet_id": packet["execution_packet_id"],
        "handoff_id": packet["handoff_id"],
        "source_task_id": packet["task_id"],
        "stage_id": profile["stage_id"],
        "proof_profile_id": profile["proof_profile_id"],
        "prover_compute_profile_id": profile["prover_compute_profile_id"],
        "program": copy.deepcopy(profile["program"]),
        "r0vm": copy.deepcopy(profile["r0vm"]),
        "gpu": copy.deepcopy(preflight["gpu"]),
        "runtime_image_sha256": preflight["runtime_image_sha256"],
        "execution_shape": _shape(profile),
        "attempt_budget_microusd": 1_000,
        "price_microusd_per_hour": 3_600_000,
        "price_observed_at_epoch_seconds": CURRENT_EPOCH - 100,
        "price_valid_until_epoch_seconds": CURRENT_EPOCH + 100,
        "hard_attempt_cap_milliseconds": 1_001,
        "authority": _authority(),
    }


def _reanchor(documents: dict[str, dict[str, Any]]) -> None:
    profile = documents["profile"]
    profile["profile_record_id"] = execution_profile._derive_record_id(profile)
    profile_bytes = shared.canonical_bytes(profile)
    build = documents["build"]
    build["build_attestation_id"] = shared.derive_build_attestation_id(build)
    preflight = documents["preflight"]
    preflight["h100_preflight_id"] = shared.derive_h100_preflight_id(preflight)
    packet = documents["packet"]
    packet["execution_packet_id"] = handoff.derive_execution_packet_id(packet)
    budget = documents["budget"]
    budget["execution_profile_sha256"] = hashlib.sha256(profile_bytes).hexdigest()
    budget["attempt_budget_record_id"] = checker.derive_attempt_budget_record_id(budget)


def _write(tmp_path: Path, documents: dict[str, dict[str, Any]]) -> dict[str, Path]:
    paths: dict[str, Path] = {}
    for role, document in documents.items():
        path = tmp_path / f"{role}.json"
        raw = (
            handoff.canonical_json_bytes(document)
            if role == "packet"
            else shared.canonical_bytes(document)
        )
        path.write_bytes(raw)
        paths[role] = path
    return paths


def _fixture(
    tmp_path: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Path]]:
    tmp_path.mkdir(parents=True, exist_ok=True)
    profile = _profile()
    build = _build(profile)
    preflight = _preflight(profile)
    packet = _packet()
    budget = _budget(profile, build, preflight, packet)
    documents = {
        "profile": profile,
        "build": build,
        "preflight": preflight,
        "packet": packet,
        "budget": budget,
    }
    _reanchor(documents)
    return documents, _write(tmp_path, documents)


def _rewrite(paths: dict[str, Path], documents: dict[str, dict[str, Any]]) -> None:
    _reanchor(documents)
    for role, document in documents.items():
        raw = (
            handoff.canonical_json_bytes(document)
            if role == "packet"
            else shared.canonical_bytes(document)
        )
        paths[role].write_bytes(raw)


def _evaluate(paths: dict[str, Path]) -> dict[str, object]:
    return checker.evaluate_qualification(
        paths.get("profile"),
        paths.get("build"),
        paths.get("preflight"),
        paths.get("packet"),
        paths.get("budget"),
        trusted_current_epoch_seconds=CURRENT_EPOCH,
    )


def test_budget_limited_one_second_boundary_has_no_completion_forecast(
    tmp_path: Path,
) -> None:
    _, paths = _fixture(tmp_path)

    result = _evaluate(paths)

    assert result["qualified"] is True
    assert result["paid_window_milliseconds"] == 1_000
    assert result["hard_attempt_cap_milliseconds"] == 1_001
    assert result["hard_attempt_deadline_milliseconds"] == 1_000
    assert result["deadline_limiting_factor"] == "paid_window"
    assert result["completion_forecast_status"] == "not_available"
    assert "receipt" not in result
    non_claims = result["non_claims"]
    assert isinstance(non_claims, list)
    assert any("no forecast or claim" in item for item in non_claims)
    assert any("externally enforced pod TTL" in item for item in non_claims)
    assert result["authority"] == checker.AUTHORITY_FALSE


def test_hard_cap_one_millisecond_below_paid_window_is_active(tmp_path: Path) -> None:
    documents, paths = _fixture(tmp_path)
    documents["budget"]["attempt_budget_microusd"] = 2_000
    documents["budget"]["hard_attempt_cap_milliseconds"] = 1_999
    _rewrite(paths, documents)

    result = _evaluate(paths)

    assert result["hard_attempt_deadline_milliseconds"] == 1_999
    assert result["deadline_limiting_factor"] == "hard_cap"


@pytest.mark.parametrize("missing", ["profile", "build", "preflight", "packet", "budget"])
def test_every_missing_input_returns_authority_false_unknown(tmp_path: Path, missing: str) -> None:
    _, paths = _fixture(tmp_path)
    paths.pop(missing)

    result = _evaluate(paths)

    assert result["status"] == checker.UNKNOWN_STATUS
    assert result["reason_code"] == "required_input_missing"
    assert result["authority"] == checker.AUTHORITY_FALSE


def test_zero_stale_future_and_zero_window_prices_reject(tmp_path: Path) -> None:
    documents, paths = _fixture(tmp_path / "zero-price")
    documents["budget"]["price_microusd_per_hour"] = 0
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "zero_price"

    documents, paths = _fixture(tmp_path / "stale")
    documents["budget"]["price_valid_until_epoch_seconds"] = CURRENT_EPOCH - 1
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "stale_price"

    documents, paths = _fixture(tmp_path / "future")
    documents["budget"]["price_observed_at_epoch_seconds"] = CURRENT_EPOCH + 1
    documents["budget"]["price_valid_until_epoch_seconds"] = CURRENT_EPOCH + 2
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "price_from_future"

    documents, paths = _fixture(tmp_path / "zero-window")
    documents["budget"]["attempt_budget_microusd"] = 1
    documents["budget"]["price_microusd_per_hour"] = checker.MAX_U64
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "attempt_window_below_worker_minimum"


def test_overflow_four_dollar_and_hard_deadline_caps_reject(tmp_path: Path) -> None:
    documents, paths = _fixture(tmp_path / "overflow")
    documents["budget"]["attempt_budget_microusd"] = checker.MAX_U64
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "arithmetic_overflow"

    documents, paths = _fixture(tmp_path / "four-dollar")
    documents["budget"]["attempt_budget_microusd"] = checker.MAX_ATTEMPT_BUDGET_MICROUSD + 1
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "attempt_budget_exceeds_cap"

    documents, paths = _fixture(tmp_path / "deadline")
    documents["budget"]["hard_attempt_cap_milliseconds"] = (
        checker.MAX_HARD_ATTEMPT_CAP_MILLISECONDS + 1
    )
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "hard_attempt_cap_exceeded"


Mutation = Callable[[dict[str, dict[str, Any]]], None]


def _mutate_packet_stage(documents: dict[str, dict[str, Any]]) -> None:
    documents["packet"]["stage_id"] = "v2_adapter_receipt"


def _mutate_packet_profile(documents: dict[str, dict[str, Any]]) -> None:
    documents["packet"]["proof_profile_id"] = "risc0_composite_v1"


def _mutate_budget_packet_id(documents: dict[str, dict[str, Any]]) -> None:
    documents["budget"]["execution_packet_id"] = _sha("substitute-packet")


def _mutate_program(documents: dict[str, dict[str, Any]]) -> None:
    documents["budget"]["program"]["image_id"] = _sha("substitute-program")


def _mutate_r0vm(documents: dict[str, dict[str, Any]]) -> None:
    documents["build"]["output_r0vm"] = _artifact("substitute-r0vm", 108_998_817)


def _mutate_gpu(documents: dict[str, dict[str, Any]]) -> None:
    documents["budget"]["gpu"]["uuid"] = "GPU-bbbbbbbb-cccc-dddd-eeee-ffffffffffff"


@pytest.mark.parametrize(
    "mutation",
    [
        _mutate_packet_stage,
        _mutate_packet_profile,
        _mutate_budget_packet_id,
        _mutate_program,
        _mutate_r0vm,
        _mutate_gpu,
    ],
)
def test_reanchored_substitution_remains_unknown(tmp_path: Path, mutation: Mutation) -> None:
    documents, paths = _fixture(tmp_path)
    mutation(documents)
    _rewrite(paths, documents)

    result = _evaluate(paths)

    assert result["qualified"] is False
    assert result["authority"] == checker.AUTHORITY_FALSE


def test_cpu_profile_and_packet_authority_reject(tmp_path: Path) -> None:
    documents, paths = _fixture(tmp_path / "cpu")
    documents["profile"]["prover_compute_profile_id"] = "risc0_ipc_cpu_v1"
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "prerequisite_invalid"

    documents, paths = _fixture(tmp_path / "authority")
    documents["packet"]["authority"]["production_authority"] = True
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "authority_promotion_rejected"


def test_attempt_budget_authority_and_noncanonical_packet_reject(tmp_path: Path) -> None:
    documents, paths = _fixture(tmp_path / "authority")
    documents["budget"]["authority"]["proof_authority"] = True
    _rewrite(paths, documents)
    assert _evaluate(paths)["reason_code"] == "authority_promotion_rejected"

    _, paths = _fixture(tmp_path / "packet")
    parsed = json.loads(paths["packet"].read_text(encoding="ascii"))
    paths["packet"].write_bytes(shared.canonical_bytes(parsed))
    assert _evaluate(paths)["reason_code"] == "execution_packet_invalid"


def test_content_change_reanchors_attempt_identity(tmp_path: Path) -> None:
    documents, paths = _fixture(tmp_path)
    first = _evaluate(paths)
    documents["budget"]["hard_attempt_cap_milliseconds"] = 1_999
    _rewrite(paths, documents)
    second = _evaluate(paths)

    assert first["qualified"] is True and second["qualified"] is True
    assert first["qualification_id"] != second["qualification_id"]


def test_cli_without_inputs_emits_unknown(capsys: Any) -> None:
    assert checker.main([]) == 1
    result = json.loads(capsys.readouterr().out)
    assert result["status"] == checker.UNKNOWN_STATUS
    assert result["reason_code"] == "required_input_missing"
    assert result["authority"] == checker.AUTHORITY_FALSE


def test_cli_protocol_output_does_not_disclose_input_paths(tmp_path: Path, capsys: Any) -> None:
    private_root = tmp_path / "private-path-sentinel-should-never-be-emitted"
    _documents, paths = _fixture(private_root)
    assert (
        checker.main(
            [
                "--source-execution-profile",
                str(paths["profile"]),
                "--cuda-r0vm-build-attestation",
                str(paths["build"]),
                "--h100-preflight",
                str(paths["preflight"]),
                "--source-execution-packet",
                str(paths["packet"]),
                "--attempt-budget-and-price",
                str(paths["budget"]),
                "--trusted-current-epoch-seconds",
                str(CURRENT_EPOCH),
            ]
        )
        == 0
    )
    output = capsys.readouterr().out
    assert str(private_root) not in output
    result = json.loads(output)
    assert result["qualified"] is True
    assert result["authority"] == checker.AUTHORITY_FALSE
