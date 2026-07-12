from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

from tools import check_risc0_recursive_live_replay as checker


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _write(path: Path, raw: bytes) -> Path:
    path.write_bytes(raw)
    return path


def _paths(tmp_path: Path) -> tuple[checker.rebuild.RebuildEvidencePaths, dict[str, bytes]]:
    payloads = {
        "positive_request": b"positive request",
        "malformed_request": b"malformed request",
        "positive_transcript": b'{"ok":true}',
        "malformed_stdout": json.dumps(
            {"error": checker.rebuild.CRYPTOGRAPHIC_INVALID_ERROR, "ok": False},
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8"),
        "verifier": b"exact verifier bytes",
    }
    reject_transcript = json.dumps(
        {
            "process_exit_code": 0,
            "response": {
                "error": checker.rebuild.CRYPTOGRAPHIC_INVALID_ERROR,
                "ok": False,
            },
            "stderr": "",
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    payloads["reject_transcript"] = reject_transcript
    workspace = tmp_path / "workspace"
    programs = tmp_path / "programs"
    workspace.mkdir()
    programs.mkdir()
    paths = checker.rebuild.RebuildEvidencePaths(
        workspace_root=workspace,
        workspace_archive=_write(tmp_path / "workspace.tar", b"archive"),
        artifact_report=_write(tmp_path / "artifact-report.json", b"{}"),
        program_directory=programs,
        static_verifier=_write(tmp_path / "verifier", payloads["verifier"]),
        root_proof=_write(tmp_path / "proof.json", b"{}"),
        positive_verify_request=_write(
            tmp_path / "positive-request.json",
            payloads["positive_request"],
        ),
        verified_transcript=_write(
            tmp_path / "positive-transcript.json",
            payloads["positive_transcript"],
        ),
        malformed_root_proof=_write(tmp_path / "malformed-proof.json", b"{}"),
        malformed_verify_request=_write(
            tmp_path / "malformed-request.json",
            payloads["malformed_request"],
        ),
        malformed_reject_transcript=_write(
            tmp_path / "malformed-transcript.json",
            payloads["reject_transcript"],
        ),
    )
    return paths, payloads


def _artifact_report(payloads: dict[str, bytes]) -> dict[str, object]:
    return {
        "ok": True,
        "positive_verify_request_sha256": _sha256(payloads["positive_request"]),
        "malformed_verify_request_sha256": _sha256(payloads["malformed_request"]),
        "verified_transcript_sha256": _sha256(payloads["positive_transcript"]),
        "malformed_reject_transcript_sha256": _sha256(payloads["reject_transcript"]),
        "static_verifier_sha256": _sha256(payloads["verifier"]),
    }


def _reference(payloads: dict[str, bytes]) -> dict[str, object]:
    return {
        "malformed_proof_reject": {
            "verify_request": {"size_bytes": len(payloads["malformed_request"])},
            "reject_transcript": {"size_bytes": len(payloads["reject_transcript"])},
        },
        "positive_verify_request": {"size_bytes": len(payloads["positive_request"])},
        "static_verifier": {"size_bytes": len(payloads["verifier"])},
        "verified_transcript": {"size_bytes": len(payloads["positive_transcript"])},
    }


class _FakeSealedExecutable:
    def __init__(self, source: Path) -> None:
        raw = source.read_bytes()
        self.identity = SimpleNamespace(
            sha256=_sha256(raw),
            size_bytes=len(raw),
            transport="linux_memfd_full_seals_v1",
        )

    def __enter__(self) -> _FakeSealedExecutable:
        return self

    def __exit__(self, *_args: object) -> None:
        return None


def _install_successful_runtime(
    monkeypatch: pytest.MonkeyPatch,
    payloads: dict[str, bytes],
) -> list[str | None]:
    observed_dev_modes: list[str | None] = []
    dev_reject = json.dumps(
        {"error": checker.support.DEV_MODE_REJECT_ERROR, "ok": False},
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")

    def fake_run(
        _executable: object,
        *,
        request: checker.support.RuntimeInput,
        runtime_directory: Path,
        dev_mode_value: str | None,
    ) -> subprocess.CompletedProcess[bytes]:
        assert runtime_directory.is_dir()
        observed_dev_modes.append(dev_mode_value)
        if dev_mode_value in checker.support.DEV_MODE_ENABLED_VALUES:
            stdout = dev_reject
        elif request.raw == payloads["positive_request"]:
            stdout = payloads["positive_transcript"]
        else:
            stdout = payloads["malformed_stdout"]
        return subprocess.CompletedProcess(("verifier",), 0, stdout, b"")

    monkeypatch.setattr(checker.support, "run_verifier", fake_run)
    return observed_dev_modes


def _install_artifact_boundary(
    monkeypatch: pytest.MonkeyPatch,
    payloads: dict[str, bytes],
) -> None:
    monkeypatch.setattr(
        checker.rebuild,
        "check_risc0_recursive_rebuild_evidence",
        lambda _paths: _artifact_report(payloads),
    )
    monkeypatch.setattr(
        checker.support,
        "authenticated_reference",
        lambda: _reference(payloads),
    )
    monkeypatch.setattr(checker.support, "require_unprivileged_linux", lambda: None)
    monkeypatch.setattr(
        checker.support.sealed_executable,
        "SealedExecutable",
        _FakeSealedExecutable,
    )


def test_live_replay_accepts_only_after_all_exact_controls(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, payloads = _paths(tmp_path)
    _install_artifact_boundary(monkeypatch, payloads)
    observed_dev_modes = _install_successful_runtime(monkeypatch, payloads)

    report = checker.check_risc0_recursive_live_replay(
        paths,
        runtime_directory=tmp_path / "runtime",
    )

    assert report["ok"] is True
    assert report["status"] == checker.ACCEPTED_STATUS
    assert report["same_host_pinned_v1_verifier_live_replay"] is True
    assert report["positive_request_verified"] is True
    assert report["ambient_dev_mode_zero_parity_verified"] is True
    assert report["ambient_dev_mode_enabled_values_rejected"] is True
    assert report["exact_seal_mutation_rejected"] is True
    assert observed_dev_modes == [None, "0", "1", "true", "yes", "on", None]
    assert set(report["live_runs"]["ambient_dev_mode_disabled_parity"]) == {"0"}
    assert set(report["live_runs"]["ambient_dev_mode_enabled_rejections"]) == {
        "1",
        "true",
        "yes",
        "on",
    }
    assert report["runtime_transports"] == {
        "executable": "linux_memfd_full_seals_v1",
        "stdin": "linux_memfd_full_seals_v1",
    }
    for claim in (
        "historical_execution_provenance_verified",
        "network_isolation_verified",
        "sandbox_escape_controls_passed",
        "proofs_regenerated",
        "semantic_composition_verified",
        "data_availability_verified",
        "durable_atomic_admission_verified",
        "release_authority",
        "settlement_authority",
        "production_authority",
        "zero_knowledge_privacy",
        "hardware_side_channel_resistance",
        "covert_channel_freedom",
    ):
        assert report[claim] is False
    assert not (tmp_path / "runtime").exists()


def test_artifact_rejection_prevents_runtime_creation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, _payloads = _paths(tmp_path)
    monkeypatch.setattr(
        checker.rebuild,
        "check_risc0_recursive_rebuild_evidence",
        lambda _paths: {"ok": False, "error_codes": ["STATIC_VERIFIER_SHA256_MISMATCH"]},
    )

    report = checker.check_risc0_recursive_live_replay(
        paths,
        runtime_directory=tmp_path / "runtime",
    )

    assert report["error_codes"] == ["ARTIFACT_EVIDENCE"]
    assert report["artifact_evidence_verified"] is False
    assert not (tmp_path / "runtime").exists()


def test_request_path_substitution_after_artifact_check_rejects(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, payloads = _paths(tmp_path)
    _install_artifact_boundary(monkeypatch, payloads)
    paths.positive_verify_request.write_bytes(b"substituted request")

    report = checker.check_risc0_recursive_live_replay(
        paths,
        runtime_directory=tmp_path / "runtime",
    )

    assert report["error_codes"] == ["ARTIFACT_IDENTITY"]
    assert report["same_host_pinned_v1_verifier_live_replay"] is False


def test_dev_mode_acceptance_or_response_drift_rejects(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, payloads = _paths(tmp_path)
    _install_artifact_boundary(monkeypatch, payloads)

    def unsafe_run(
        _executable: object,
        *,
        request: checker.support.RuntimeInput,
        runtime_directory: Path,
        dev_mode_value: str | None,
    ) -> subprocess.CompletedProcess[bytes]:
        assert runtime_directory.is_dir()
        stdout = payloads["positive_transcript"]
        if dev_mode_value is None and request.raw == payloads["malformed_request"]:
            stdout = payloads["malformed_stdout"]
        return subprocess.CompletedProcess(("verifier",), 0, stdout, b"")

    monkeypatch.setattr(checker.support, "run_verifier", unsafe_run)

    report = checker.check_risc0_recursive_live_replay(
        paths,
        runtime_directory=tmp_path / "runtime",
    )

    assert report["error_codes"] == ["VERIFIER_STDOUT"]
    assert report["same_host_pinned_v1_verifier_live_replay"] is False


@pytest.mark.parametrize(
    ("returncode", "stdout", "stderr", "expected_code"),
    [
        (2, b"expected", b"", "VERIFIER_EXIT"),
        (0, b"expected", b"unexpected", "VERIFIER_STDERR"),
        (0, b"other", b"", "VERIFIER_STDOUT"),
    ],
)
def test_outcome_rejects_every_process_boundary_drift(
    returncode: int,
    stdout: bytes,
    stderr: bytes,
    expected_code: str,
) -> None:
    process = subprocess.CompletedProcess(("verifier",), returncode, stdout, stderr)

    with pytest.raises(checker.support.LiveReplayError) as rejected:
        checker.support.outcome(
            process,
            expected_stdout=b"expected",
            label="control",
            environment_profile="profile",
        )

    assert rejected.value.code == expected_code
