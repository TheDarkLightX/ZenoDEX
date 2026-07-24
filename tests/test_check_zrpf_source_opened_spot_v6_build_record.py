from __future__ import annotations

import copy
import fcntl
import hashlib
import json
import os
import subprocess
from pathlib import Path

import pytest

from tools import check_zrpf_source_opened_spot_v6_build_record as checker


def _artifact_bytes(stage: str) -> bytes:
    return b"R0BF\x01\x00\x00\x00" + (f"bounded-test-program:{stage}\n").encode()


def _install_programs_and_fake_r0vm(tmp_path: Path, document: dict) -> Path:
    for row in document["programs"]:
        (tmp_path / row["artifact_file"]).write_bytes(_artifact_bytes(row["stage"]))
    image_ids = {
        row["stage"]: row["image_id_hex"] for row in document["programs"]
    }
    r0vm = tmp_path / "r0vm"
    r0vm.write_text(
        "#!/usr/bin/python3\n"
        "import sys\n"
        f"images = {image_ids!r}\n"
        "if len(sys.argv) != 4 or sys.argv[1] != '--elf' or sys.argv[3] != '--id':\n"
        "    raise SystemExit(2)\n"
        "raw = open(sys.argv[2], 'rb').read().decode('utf-8', errors='ignore')\n"
        "stage = raw.split('bounded-test-program:', 1)[1].strip()\n"
        "print(images[stage])\n",
        encoding="utf-8",
    )
    r0vm.chmod(0o755)
    document["toolchain"]["r0vm"] = (
        f"{checker.OFFICIAL_R0VM_VERSION} sha256:"
        + hashlib.sha256(r0vm.read_bytes()).hexdigest()
    )
    return r0vm


def valid_record() -> dict:
    commit = subprocess.check_output(
        ["git", "-C", str(checker.REPO_ROOT), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    tree = subprocess.check_output(
        ["git", "-C", str(checker.REPO_ROOT), "rev-parse", "HEAD^{tree}"],
        text=True,
    ).strip()
    source_root, source_count, source_bytes = checker.compute_source_closure(
        checker.REPO_ROOT
    )
    programs = []
    for stage, package, artifact_file, image_id, child_stage, child_image_id in (
        checker.PROGRAM_SPECS
    ):
        raw = _artifact_bytes(stage)
        programs.append(
            {
                "stage": stage,
                "package": package,
                "artifact_file": artifact_file,
                "program_binary_bytes": len(raw),
                "program_binary_sha256": hashlib.sha256(raw).hexdigest(),
                "image_id_hex": image_id,
                "image_id_words_le": checker._image_words_le(image_id),
                "verified_child_stage": child_stage,
                "verified_child_image_id": child_image_id,
            }
        )
    return {
        "schema": checker.RECORD_SCHEMA,
        "recorded_at": "2026-07-12",
        "source_observation": {
            "repository_commit": commit,
            "repository_tree": tree,
            "source_root_sha256": source_root,
            "source_file_count": source_count,
            "source_bytes": source_bytes,
        },
        "toolchain": {
            "rustc": checker.OFFICIAL_RUSTC_VERSION,
            "cargo": checker.OFFICIAL_CARGO_VERSION,
            "r0vm": (
                f"{checker.OFFICIAL_R0VM_VERSION} "
                f"sha256:{checker.OFFICIAL_R0VM_SHA256}"
            ),
            "cargo_risczero": (
                f"{checker.OFFICIAL_CARGO_RISCZERO_VERSION} "
                f"sha256:{checker.OFFICIAL_CARGO_RISCZERO_SHA256}"
            ),
            "risc0_zkvm": checker.OFFICIAL_RISC0_ZKVM_VERSION,
            "cargo_lock_sha256": hashlib.sha256(
                (checker.REPO_ROOT / checker.CARGO_LOCK_RELATIVE).read_bytes()
            ).hexdigest(),
            "target": checker.OFFICIAL_RISC0_TARGET,
            "build_jobs": checker.OFFICIAL_BUILD_JOBS,
            "offline": True,
            "locked": True,
        },
        "programs": programs,
        "publisher_reported_observations": {
            "commands_reported_executed": {
                field: True
                for field in sorted(checker.PUBLISHER_REPORTED_COMMAND_FIELDS)
            },
            "same_host_current_v6_images_built": True,
        },
        "claims": {
            **{field: True for field in sorted(checker.TRUE_CLAIMS)},
            **{field: False for field in sorted(checker.FALSE_CLAIMS)},
        },
    }


def test_valid_build_record_binds_current_policy_chain() -> None:
    document = valid_record()
    raw = checker.canonical_bytes(document)

    report = checker.validate_candidate_record(document, raw)

    assert report["ok"] is True
    assert report["governed_record_anchor_checked"] is False
    assert report["policy_dependencies_checked"] == 5
    assert report["external_artifact_files_checked"] == 0
    assert report["leaf_image_id"] == checker.LEAF_IMAGE_ID
    assert report["settlement_image_id"] == checker.SETTLEMENT_IMAGE_ID
    assert report["proofs_generated"] is False
    assert report["production_authority"] is False


def test_optional_artifact_directory_rechecks_all_four_program_binaries(
    tmp_path: Path,
) -> None:
    document = valid_record()
    for row in document["programs"]:
        (tmp_path / row["artifact_file"]).write_bytes(_artifact_bytes(row["stage"]))

    report = checker.validate_candidate_record(
        document,
        checker.canonical_bytes(document),
        artifact_directory=tmp_path,
    )

    assert report["external_artifact_files_checked"] == 4
    assert report["program_image_ids_recomputed"] == 0
    assert report["live_governed_artifact_set_observed"] is False


def test_checker_owned_r0vm_recomputes_all_program_image_ids(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = valid_record()
    r0vm = _install_programs_and_fake_r0vm(tmp_path, document)
    r0vm_sha256 = hashlib.sha256(r0vm.read_bytes()).hexdigest()
    monkeypatch.setattr(checker, "OFFICIAL_R0VM_SHA256", r0vm_sha256)
    raw = checker.canonical_bytes(document)
    monkeypatch.setattr(
        checker,
        "GOVERNED_RECORD_SHA256",
        hashlib.sha256(raw).hexdigest(),
    )

    report = checker.validate_record(
        document,
        raw,
        artifact_directory=tmp_path,
        r0vm_path=r0vm.resolve(),
        expected_record_sha256=hashlib.sha256(raw).hexdigest(),
    )

    assert report["external_artifact_files_checked"] == 4
    assert report["program_image_ids_recomputed"] == 4
    assert report["live_governed_artifact_set_observed"] is True

    r0vm.write_text(r0vm.read_text(encoding="utf-8") + "# mutation\n", encoding="utf-8")
    with pytest.raises(checker.BuildRecordError, match="r0vm executable identity mismatch"):
        checker.validate_record(
            document,
            raw,
            artifact_directory=tmp_path,
            r0vm_path=r0vm.resolve(),
            expected_record_sha256=hashlib.sha256(raw).hexdigest(),
        )


@pytest.mark.parametrize("false_hash", ["0" * 64, "f" * 64])
def test_false_cargo_lock_hash_cannot_reach_scoped_promotion(
    tmp_path: Path,
    false_hash: str,
) -> None:
    document = valid_record()
    document["toolchain"]["cargo_lock_sha256"] = false_hash

    with pytest.raises(
        checker.BuildRecordError,
        match="cargo_lock_sha256 differs from the verified source closure",
    ):
        checker.validate_candidate_record(
            document,
            checker.canonical_bytes(document),
        )


def test_program_and_r0vm_snapshots_are_fully_sealed(tmp_path: Path) -> None:
    program = tmp_path / "program.bin"
    program.write_bytes(_artifact_bytes("spot_value_leaf_v6"))
    r0vm = tmp_path / "r0vm"
    r0vm.write_bytes(b"#!/bin/sh\nexit 0\n")
    r0vm.chmod(0o755)

    program_fd, _size, _digest = checker._open_stable_program_binary(program)
    r0vm_fd = checker._open_verified_r0vm(
        r0vm.resolve(),
        hashlib.sha256(r0vm.read_bytes()).hexdigest(),
    )
    try:
        for descriptor in (program_fd, r0vm_fd):
            assert fcntl.fcntl(descriptor, fcntl.F_GET_SEALS) == checker.MEMFD_SEALS
            with pytest.raises(OSError):
                os.write(descriptor, b"mutation")
    finally:
        os.close(program_fd)
        os.close(r0vm_fd)


def test_optional_artifact_directory_rejects_mutation_and_symlink(
    tmp_path: Path,
) -> None:
    document = valid_record()
    for row in document["programs"]:
        (tmp_path / row["artifact_file"]).write_bytes(_artifact_bytes(row["stage"]))
    first = document["programs"][0]["artifact_file"]
    (tmp_path / first).write_bytes(b"mutated")
    with pytest.raises(
        checker.BuildRecordError,
        match="bounded regular file|stable RISC0|identity mismatch",
    ):
        checker.validate_candidate_record(
            document,
            checker.canonical_bytes(document),
            artifact_directory=tmp_path,
        )
    (tmp_path / first).unlink()
    (tmp_path / "target.bin").write_bytes(
        _artifact_bytes(document["programs"][0]["stage"])
    )
    (tmp_path / first).symlink_to("target.bin")
    with pytest.raises(checker.BuildRecordError, match="symlink rejected"):
        checker.validate_candidate_record(
            document,
            checker.canonical_bytes(document),
            artifact_directory=tmp_path,
        )


def test_optional_artifact_directory_rejects_non_risc0_program_binary(
    tmp_path: Path,
) -> None:
    document = valid_record()
    for row in document["programs"]:
        (tmp_path / row["artifact_file"]).write_bytes(_artifact_bytes(row["stage"]))
    first = document["programs"][0]
    non_risc0 = b"NOTBIN00" + _artifact_bytes(first["stage"])[8:]
    (tmp_path / first["artifact_file"]).write_bytes(non_risc0)
    first["program_binary_sha256"] = hashlib.sha256(non_risc0).hexdigest()
    first["program_binary_bytes"] = len(non_risc0)

    with pytest.raises(checker.BuildRecordError, match="not a stable RISC0"):
        checker.validate_candidate_record(
            document,
            checker.canonical_bytes(document),
            artifact_directory=tmp_path,
        )


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (
            lambda value: value["programs"][1].__setitem__(
                "verified_child_image_id", "0" * 64
            ),
            "verified_child_image_id mismatch",
        ),
        (
            lambda value: value["programs"][0].__setitem__(
                "image_id_hex", "0" * 64
            ),
            "image_id_hex mismatch",
        ),
        (
            lambda value: value["programs"][0].__setitem__(
                "image_id_words_le", [0] * 8
            ),
            "image_id_words_le mismatch",
        ),
        (
            lambda value: value["publisher_reported_observations"][
                "commands_reported_executed"
            ].__setitem__("risc0_guests_built", 1),
            "must be exactly True",
        ),
        (
            lambda value: value["claims"].__setitem__(
                "production_authority", True
            ),
            "must be exactly False",
        ),
        (
            lambda value: value["toolchain"].__setitem__("unreviewed", True),
            "toolchain field set mismatch",
        ),
        (
            lambda value: value["source_observation"].__setitem__(
                "source_root_sha256", "0" * 64
            ),
            "recorded Git commit",
        ),
    ],
)
def test_validator_rejects_identity_boolean_claim_and_field_mutations(
    mutate,
    message: str,
) -> None:
    document = valid_record()
    mutate(document)

    with pytest.raises(checker.BuildRecordError, match=message):
        checker.validate_candidate_record(
            document,
            checker.canonical_bytes(document),
        )


@pytest.mark.parametrize(
    "raw",
    [
        b'{"schema":"a","schema":"b"}\n',
        b'{"schema":1.0}\n',
        b'{"schema":NaN}\n',
    ],
)
def test_loader_rejects_ambiguous_or_floating_json(tmp_path: Path, raw: bytes) -> None:
    path = tmp_path / "record.json"
    path.write_bytes(raw)

    with pytest.raises(checker.BuildRecordError):
        checker.load_record(path)


def test_loader_rejects_equivalent_noncanonical_json(tmp_path: Path) -> None:
    document = valid_record()
    path = tmp_path / "record.json"
    path.write_text(json.dumps(document), encoding="utf-8")

    with pytest.raises(checker.BuildRecordError, match="noncanonical"):
        checker.load_record(path)


def test_governed_validation_binds_document_to_anchored_raw_bytes() -> None:
    document, raw = checker.load_record(checker.DEFAULT_RECORD)
    forged = copy.deepcopy(document)
    forged["recorded_at"] = "2026-07-12"

    with pytest.raises(checker.BuildRecordError, match="canonical raw bytes"):
        checker.validate_record(forged, raw)


def test_governed_record_anchor_rejects_coherent_mutation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = valid_record()
    raw = checker.canonical_bytes(document)
    expected = hashlib.sha256(raw).hexdigest()
    changed = copy.deepcopy(document)
    changed["recorded_at"] = "2026-07-13"

    monkeypatch.setattr(checker, "GOVERNED_RECORD_SHA256", expected)

    with pytest.raises(checker.BuildRecordError, match="governed record SHA-256"):
        checker.validate_record(
            changed,
            checker.canonical_bytes(changed),
            expected_record_sha256=expected,
        )


def test_cli_check_can_require_live_governed_artifact_observation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = valid_record()
    path = tmp_path / "build-record.json"
    path.write_bytes(checker.canonical_bytes(document))
    monkeypatch.setattr(
        checker,
        "GOVERNED_RECORD_SHA256",
        hashlib.sha256(path.read_bytes()).hexdigest(),
    )

    report = checker.check_record(path, require_live_artifact_observation=True)

    assert report["ok"] is False
    assert report["live_governed_artifact_set_observed"] is False
    assert report["errors"] == [
        "live governed artifact-set observation is not established"
    ]


def test_caller_supplied_self_hash_cannot_promote_an_ungoverned_record() -> None:
    document = valid_record()
    raw = checker.canonical_bytes(document)

    with pytest.raises(checker.BuildRecordError, match="governed record SHA-256"):
        checker.validate_record(
            document,
            raw,
            expected_record_sha256=hashlib.sha256(raw).hexdigest(),
        )


def test_governed_local_path_dependency_graph_includes_aggregate_shared() -> None:
    observed = checker.derive_local_path_dependency_directories(checker.REPO_ROOT)
    commit = subprocess.check_output(
        ["git", "-C", str(checker.REPO_ROOT), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    committed = checker.derive_git_local_path_dependency_directories(
        checker.REPO_ROOT,
        commit,
    )

    assert observed == committed == checker.GOVERNED_LOCAL_PATH_CRATE_DIRECTORIES
    assert "zk/zrpf_risc0/aggregate_shared" in observed
    assert "zk/zrpf_risc0/value_node_shared" not in observed
    assert "zk/zrpf_risc0/aggregate_shared" in checker.source_closure_directories(
        checker.REPO_ROOT
    )


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("rustc", "bogus-rustc"),
        ("cargo", "bogus-cargo"),
        ("r0vm", f"risc0-r0vm 3.0.5 sha256:{'0' * 64}"),
        ("cargo_risczero", f"cargo-risczero 3.0.5 sha256:{'0' * 64}"),
    ],
)
def test_candidate_toolchain_versions_are_checker_owned(
    field: str,
    value: str,
) -> None:
    document = valid_record()
    document["toolchain"][field] = value

    with pytest.raises(checker.BuildRecordError, match=f"toolchain.{field} mismatch"):
        checker.validate_candidate_record(
            document,
            checker.canonical_bytes(document),
        )


def test_record_qualifies_historical_build_and_cleanliness_observations() -> None:
    document, _raw = checker.load_record(checker.DEFAULT_RECORD)

    assert "repository_dirty" not in document["source_observation"]
    assert "executed_commands" not in document
    assert "same_host_current_v6_images_built" not in document["claims"]
    publisher = document["publisher_reported_observations"]
    assert publisher["same_host_current_v6_images_built"] is True
    assert set(publisher["commands_reported_executed"]) == set(
        checker.PUBLISHER_REPORTED_COMMAND_FIELDS
    )


def test_default_record_matches_checker_owned_governed_anchor() -> None:
    report = checker.check_record()

    assert report["ok"] is True
    assert report["record_sha256"] == checker.GOVERNED_RECORD_SHA256
    assert report["governed_record_anchor_checked"] is True
    assert report["live_governed_artifact_set_observed"] is False


def test_loader_uses_a_bounded_descriptor_read(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    path = tmp_path / "record.json"
    path.write_bytes(b"{}\n")

    def path_read_bytes_is_forbidden(_path: Path) -> bytes:
        raise AssertionError("Path.read_bytes bypasses the pre-read byte bound")

    monkeypatch.setattr(Path, "read_bytes", path_read_bytes_is_forbidden)
    document, raw = checker.load_record(path)

    assert document == {}
    assert raw == b"{}\n"


def test_loader_rejects_fifo_without_blocking(tmp_path: Path) -> None:
    path = tmp_path / "record.pipe"
    os.mkfifo(path)

    with pytest.raises(checker.BuildRecordError, match="bounded regular file"):
        checker.load_record(path)


def test_loader_rejects_oversized_integer_with_stable_error(tmp_path: Path) -> None:
    path = tmp_path / "record.json"
    path.write_bytes(b'{"value":' + (b"9" * 5_000) + b"}\n")

    with pytest.raises(checker.BuildRecordError, match="JSON integer exceeds bound"):
        checker.load_record(path)


def test_loader_rejects_lone_unicode_surrogate(tmp_path: Path) -> None:
    path = tmp_path / "record.json"
    path.write_bytes(b'{"value":"\\ud800"}\n')

    with pytest.raises(checker.BuildRecordError, match="Unicode scalar"):
        checker.load_record(path)


@pytest.mark.parametrize(
    ("document_factory", "message"),
    [
        (
            lambda: {
                "value": "x" * (checker.MAX_JSON_STRING_CHARS + 1),
            },
            "JSON string exceeds bound",
        ),
        (
            lambda: {
                "value": [None] * (checker.MAX_JSON_NODES + 1),
            },
            "JSON node count exceeds bound",
        ),
    ],
)
def test_loader_rejects_bounded_json_shape(
    tmp_path: Path,
    document_factory,
    message: str,
) -> None:
    path = tmp_path / "record.json"
    path.write_bytes(checker.canonical_bytes(document_factory()))

    with pytest.raises(checker.BuildRecordError, match=message):
        checker.load_record(path)


def test_loader_rejects_excessive_json_depth(tmp_path: Path) -> None:
    nested: object = None
    for _ in range(checker.MAX_JSON_DEPTH + 1):
        nested = [nested]
    path = tmp_path / "record.json"
    path.write_bytes(checker.canonical_bytes({"value": nested}))

    with pytest.raises(checker.BuildRecordError, match="JSON depth exceeds bound"):
        checker.load_record(path)


def test_local_source_inventory_has_a_governed_node_bound(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(checker, "MAX_SOURCE_INVENTORY_NODES", 1)

    with pytest.raises(checker.BuildRecordError, match="source inventory exceeds bound"):
        checker.compute_source_closure(checker.REPO_ROOT)


def test_source_hash_enforces_file_count_and_total_byte_bounds(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths = {"a.rs", "b.rs"}
    monkeypatch.setattr(checker, "MAX_SOURCE_FILES", 1)
    with pytest.raises(checker.BuildRecordError, match="file inventory exceeds bound"):
        checker._hash_source_closure(paths, lambda _relative: b"x")

    monkeypatch.setattr(checker, "MAX_SOURCE_FILES", 2)
    monkeypatch.setattr(checker, "MAX_SOURCE_BYTES", 1)
    with pytest.raises(checker.BuildRecordError, match="total bytes exceed bound"):
        checker._hash_source_closure(paths, lambda _relative: b"x")


def test_git_output_has_a_governed_byte_bound(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    commit = subprocess.check_output(
        ["git", "-C", str(checker.REPO_ROOT), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    monkeypatch.setattr(checker, "MAX_GIT_STDOUT_BYTES", 1)

    with pytest.raises(checker.BuildRecordError, match="Git stdout exceeds bound"):
        checker.compute_git_source_closure(checker.REPO_ROOT, commit)


def test_candidate_validation_rechecks_the_whole_source_closure_at_end(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = valid_record()
    initial = (
        document["source_observation"]["source_root_sha256"],
        document["source_observation"]["source_file_count"],
        document["source_observation"]["source_bytes"],
    )
    observations = iter((initial, ("0" * 64, initial[1], initial[2])))
    monkeypatch.setattr(checker, "compute_source_closure", lambda _root: next(observations))
    monkeypatch.setattr(checker, "_validate_policy_sources", lambda _root: None)

    with pytest.raises(checker.BuildRecordError, match="changed after initial observation"):
        checker.validate_candidate_record(
            document,
            checker.canonical_bytes(document),
        )
