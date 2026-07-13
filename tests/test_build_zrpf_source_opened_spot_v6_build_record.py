from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

import pytest

from tools import (
    build_zrpf_source_opened_spot_v6_build_record as builder,
)
from tools import (
    check_zrpf_source_opened_spot_v6_build_record as checker,
)

RECORDED_AT = "2026-07-12"


def _source_commit() -> str:
    return subprocess.check_output(
        ["git", "-C", str(checker.REPO_ROOT), "rev-parse", "HEAD"],
        text=True,
    ).strip()


def _artifact_bytes(stage: str) -> bytes:
    return b"R0BF\x01\x00\x00\x00" + f"bounded-test-program:{stage}\n".encode()


def _write_executable(path: Path, source: str) -> Path:
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)
    return path.resolve()


def _fake_r0vm_source() -> str:
    image_ids = {
        stage: image_id
        for stage, _package, _filename, image_id, _child_stage, _child_id in (
            checker.PROGRAM_SPECS
        )
    }
    return (
        "#!/usr/bin/python3\n"
        "import sys\n"
        f"images = {image_ids!r}\n"
        "if sys.argv[1:] == ['--version']:\n"
        "    print('risc0-r0vm 3.0.5')\n"
        "elif len(sys.argv) == 4 and sys.argv[1] == '--elf' and sys.argv[3] == '--id':\n"
        "    raw = open(sys.argv[2], 'rb').read().decode('utf-8', errors='ignore')\n"
        "    stage = raw.split('bounded-test-program:', 1)[1].strip()\n"
        "    print(images[stage])\n"
        "else:\n"
        "    raise SystemExit(2)\n"
    )


def _fake_cargo_risczero_source() -> str:
    return (
        "#!/usr/bin/python3\n"
        "import sys\n"
        "if sys.argv[1:] != ['risczero', '--version']:\n"
        "    raise SystemExit(2)\n"
        "print('cargo-risczero 3.0.5')\n"
    )


def _fixture_inputs(tmp_path: Path) -> tuple[Path, Path, Path]:
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    for stage, _package, filename, _image_id, _child_stage, _child_id in (
        checker.PROGRAM_SPECS
    ):
        (artifacts / filename).write_bytes(_artifact_bytes(stage))
    r0vm = _write_executable(
        tmp_path / "r0vm",
        _fake_r0vm_source(),
    )
    cargo_risczero = _write_executable(
        tmp_path / "cargo-risczero",
        _fake_cargo_risczero_source(),
    )
    return artifacts.resolve(), r0vm, cargo_risczero


@pytest.fixture(autouse=True)
def _stable_current_source_contract(monkeypatch: pytest.MonkeyPatch) -> None:
    """Isolate these unit tests from concurrent policy fixed-point commits."""

    commit = _source_commit()
    committed = checker.compute_git_source_closure(checker.REPO_ROOT, commit)
    monkeypatch.setattr(checker, "compute_source_closure", lambda _root: committed)
    monkeypatch.setattr(checker, "_validate_policy_sources", lambda _root: None)
    monkeypatch.setattr(
        checker,
        "OFFICIAL_R0VM_SHA256",
        hashlib.sha256(_fake_r0vm_source().encode("utf-8")).hexdigest(),
    )
    monkeypatch.setattr(
        checker,
        "OFFICIAL_CARGO_RISCZERO_SHA256",
        hashlib.sha256(_fake_cargo_risczero_source().encode("utf-8")).hexdigest(),
    )


def _build(tmp_path: Path) -> tuple[builder.BuildResult, Path, Path, Path]:
    artifacts, r0vm, cargo_risczero = _fixture_inputs(tmp_path)
    result = builder.build_record(
        source_commit=_source_commit(),
        artifact_directory=artifacts,
        r0vm_path=r0vm,
        cargo_risczero_path=cargo_risczero,
        recorded_at=RECORDED_AT,
    )
    return result, artifacts, r0vm, cargo_risczero


def test_builder_derives_one_deterministic_checker_accepted_record(
    tmp_path: Path,
) -> None:
    first, artifacts, r0vm, cargo_risczero = _build(tmp_path)
    second = builder.build_record(
        source_commit=_source_commit(),
        artifact_directory=artifacts,
        r0vm_path=r0vm,
        cargo_risczero_path=cargo_risczero,
        recorded_at=RECORDED_AT,
    )

    assert first.raw == second.raw == checker.canonical_bytes(first.document)
    assert first.record_sha256 == hashlib.sha256(first.raw).hexdigest()
    assert first.checker_report["candidate_record_validated"] is True
    assert first.checker_report["governed_record_anchor_checked"] is False
    assert first.checker_report["live_governed_artifact_set_observed"] is False
    assert first.checker_report["program_image_ids_recomputed"] == 4
    assert first.document["source_observation"]["repository_commit"] == _source_commit()
    expected_tree = subprocess.check_output(
        ["git", "-C", str(checker.REPO_ROOT), "rev-parse", "HEAD^{tree}"],
        text=True,
    ).strip()
    assert first.document["source_observation"]["repository_tree"] == expected_tree
    assert first.document["toolchain"]["cargo_lock_sha256"] == hashlib.sha256(
        (checker.REPO_ROOT / checker.CARGO_LOCK_RELATIVE).read_bytes()
    ).hexdigest()
    assert first.document["toolchain"]["r0vm"].endswith(
        hashlib.sha256(r0vm.read_bytes()).hexdigest()
    )
    assert first.document["toolchain"]["cargo_risczero"].endswith(
        hashlib.sha256(cargo_risczero.read_bytes()).hexdigest()
    )
    for row in first.document["programs"]:
        raw = (artifacts / row["artifact_file"]).read_bytes()
        assert row["program_binary_bytes"] == len(raw)
        assert row["program_binary_sha256"] == hashlib.sha256(raw).hexdigest()


def test_builder_preserves_every_checker_false_claim(tmp_path: Path) -> None:
    result, _artifacts, _r0vm, _cargo_risczero = _build(tmp_path)

    assert set(result.document["claims"]) == checker.TRUE_CLAIMS | checker.FALSE_CLAIMS
    assert all(result.document["claims"][field] is False for field in checker.FALSE_CLAIMS)
    assert result.checker_report["proofs_generated"] is False
    assert result.checker_report["release_authority"] is False
    assert result.checker_report["production_authority"] is False
    assert "executed_commands" not in result.document
    assert "repository_dirty" not in result.document["source_observation"]
    assert result.document["publisher_reported_observations"][
        "same_host_current_v6_images_built"
    ] is True


def test_build_and_write_validates_before_atomic_publication(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifacts, r0vm, cargo_risczero = _fixture_inputs(tmp_path)
    output = tmp_path / "build-record.json"

    def reject(*_args, **_kwargs):
        raise checker.BuildRecordError("governed checker rejection")

    monkeypatch.setattr(checker, "validate_candidate_record", reject)
    with pytest.raises(checker.BuildRecordError, match="governed checker rejection"):
        builder.build_and_write_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=cargo_risczero,
            recorded_at=RECORDED_AT,
            output=output,
        )
    assert not output.exists()


def test_atomic_publication_refuses_overwrite_then_explicitly_replaces(
    tmp_path: Path,
) -> None:
    result, artifacts, r0vm, cargo_risczero = _build(tmp_path)
    output = tmp_path / "build-record.json"
    output.write_bytes(b"preserve-me")

    with pytest.raises(builder.BuildRecordBuildError, match="already exists"):
        builder.build_and_write_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=cargo_risczero,
            recorded_at=RECORDED_AT,
            output=output,
        )
    assert output.read_bytes() == b"preserve-me"

    replaced = builder.build_and_write_record(
        source_commit=_source_commit(),
        artifact_directory=artifacts,
        r0vm_path=r0vm,
        cargo_risczero_path=cargo_risczero,
        recorded_at=RECORDED_AT,
        output=output,
        replace=True,
    )
    assert replaced.raw == result.raw == output.read_bytes()
    loaded, raw = checker.load_record(output)
    assert loaded == result.document
    assert raw == result.raw


def test_current_selected_source_must_match_exact_commit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifacts, r0vm, cargo_risczero = _fixture_inputs(tmp_path)
    monkeypatch.setattr(
        checker,
        "compute_source_closure",
        lambda _root: ("0" * 64, 1, 1),
    )

    with pytest.raises(builder.BuildRecordBuildError, match="selected source"):
        builder.build_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=cargo_risczero,
            recorded_at=RECORDED_AT,
        )


@pytest.mark.parametrize(
    "source_commit",
    ["HEAD", "A" * 40, "0" * 39, "0" * 41],
)
def test_source_commit_must_be_exact_lowercase_hex(
    tmp_path: Path,
    source_commit: str,
) -> None:
    artifacts, r0vm, cargo_risczero = _fixture_inputs(tmp_path)

    with pytest.raises(builder.BuildRecordBuildError, match="40 lowercase"):
        builder.build_record(
            source_commit=source_commit,
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=cargo_risczero,
            recorded_at=RECORDED_AT,
        )


@pytest.mark.parametrize("recorded_at", ["", "2026-7-12", "2026-07-12T00:00:00Z"])
def test_recorded_date_is_explicit_and_canonical(
    tmp_path: Path,
    recorded_at: str,
) -> None:
    artifacts, r0vm, cargo_risczero = _fixture_inputs(tmp_path)

    with pytest.raises(builder.BuildRecordBuildError, match="canonical ISO date"):
        builder.build_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=cargo_risczero,
            recorded_at=recorded_at,
        )


def test_artifact_inventory_must_be_exact_and_r0bf(tmp_path: Path) -> None:
    artifacts, r0vm, cargo_risczero = _fixture_inputs(tmp_path)
    (artifacts / "unreviewed.bin").write_bytes(b"R0BF-extra")
    with pytest.raises(builder.BuildRecordBuildError, match="exactly the four"):
        builder.build_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=cargo_risczero,
            recorded_at=RECORDED_AT,
        )

    (artifacts / "unreviewed.bin").unlink()
    first = checker.PROGRAM_SPECS[0][2]
    (artifacts / first).write_bytes(b"not-r0bf")
    with pytest.raises(checker.BuildRecordError, match="stable RISC0"):
        builder.build_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=cargo_risczero,
            recorded_at=RECORDED_AT,
        )


def test_tool_paths_are_absolute_non_symlink_and_version_pinned(
    tmp_path: Path,
) -> None:
    artifacts, r0vm, cargo_risczero = _fixture_inputs(tmp_path)
    symlink = tmp_path / "cargo-risczero-link"
    symlink.symlink_to(cargo_risczero)
    with pytest.raises(builder.BuildRecordBuildError, match="non-symlink executable"):
        builder.build_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=symlink,
            recorded_at=RECORDED_AT,
        )

    bad_cargo = _write_executable(
        tmp_path / "bad-cargo-risczero",
        "#!/bin/sh\nprintf '%s\\n' 'cargo-risczero 3.0.4'\n",
    )
    with pytest.raises(builder.BuildRecordBuildError, match="must be exactly"):
        builder.build_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=bad_cargo,
            recorded_at=RECORDED_AT,
        )


def test_wrong_recomputed_program_image_id_rejects(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifacts, _r0vm, cargo_risczero = _fixture_inputs(tmp_path)
    r0vm = _write_executable(
        tmp_path / "wrong-r0vm",
        "#!/usr/bin/python3\n"
        "import sys\n"
        "if sys.argv[1:] == ['--version']:\n"
        "    print('risc0-r0vm 3.0.5')\n"
        "else:\n"
        "    print('0' * 64)\n",
    )
    monkeypatch.setattr(
        checker,
        "OFFICIAL_R0VM_SHA256",
        hashlib.sha256(r0vm.read_bytes()).hexdigest(),
    )

    with pytest.raises(builder.BuildRecordBuildError, match="governed policy"):
        builder.build_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=cargo_risczero,
            recorded_at=RECORDED_AT,
        )


def test_output_may_not_alias_a_governed_input(tmp_path: Path) -> None:
    artifacts, r0vm, cargo_risczero = _fixture_inputs(tmp_path)
    output = artifacts / checker.PROGRAM_SPECS[0][2]

    with pytest.raises(builder.BuildRecordBuildError, match="aliases"):
        builder.build_and_write_record(
            source_commit=_source_commit(),
            artifact_directory=artifacts,
            r0vm_path=r0vm,
            cargo_risczero_path=cargo_risczero,
            recorded_at=RECORDED_AT,
            output=output,
            replace=True,
        )


def test_cli_requires_explicit_inputs_and_emits_bounded_nonclaims(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    artifacts, r0vm, cargo_risczero = _fixture_inputs(tmp_path)
    output = tmp_path / "cli-build-record.json"

    status = builder.main(
        [
            "--source-commit",
            _source_commit(),
            "--artifact-directory",
            str(artifacts),
            "--r0vm",
            str(r0vm),
            "--cargo-risczero",
            str(cargo_risczero),
            "--recorded-at",
            RECORDED_AT,
            "--output",
            str(output),
            "--json",
        ]
    )

    assert status == 0
    report = json.loads(capsys.readouterr().out)
    assert report["ok"] is True
    assert report["candidate_record_validated"] is True
    assert report["governed_record_anchor_checked"] is False
    assert report["live_governed_artifact_set_observed"] is False
    assert report["proofs_generated"] is False
    assert report["release_authority"] is False
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False
    assert output.is_file()
