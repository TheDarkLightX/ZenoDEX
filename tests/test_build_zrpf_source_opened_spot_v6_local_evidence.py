from __future__ import annotations

import hashlib
import json
import os
import subprocess
from dataclasses import dataclass
from pathlib import Path

import pytest

from tools import build_zrpf_source_opened_spot_v6_local_evidence as builder
from tools import check_zrpf_source_opened_spot_v6_build_record as build_checker
from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence_checker


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _json_line(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=False, separators=(",", ":")) + "\n").encode()


def _json_compact(value: object) -> bytes:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode()


def _receipt(label: str) -> bytes:
    return _json_compact(
        {
            "inner": {"Succinct": {"seal": [10, 20, 30]}},
            "journal": {"label": label},
            "metadata": {},
        }
    )


def _mutation(receipt_raw: bytes) -> bytes:
    value = json.loads(receipt_raw)
    value["inner"]["Succinct"]["seal"][1] ^= 1
    return _json_compact(value)


def _program(stage: str) -> bytes:
    return b"R0BF\x01\x00\x00\x00bounded-test-program:" + stage.encode() + b"\n"


@dataclass(frozen=True)
class _Fixture:
    artifacts: dict[str, Path]
    reports: dict[str, Path]
    build_record: Path
    r0vm: Path


@pytest.fixture(autouse=True)
def _isolate_builder_tests_from_in_flight_policy_id_rotation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The checker suite owns policy-source parity; this suite owns building.

    The shared integration branch rotates guest IDs while these tests run. The
    synthetic build record still exercises every other build-record invariant,
    program binding, and fresh fake-r0vm image-ID recomputation.
    """

    monkeypatch.setattr(build_checker, "_validate_policy_sources", lambda _root: None)


def _write(path: Path, raw: bytes) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return path


def _build_record(program_raw: dict[str, bytes], r0vm: Path) -> dict:
    commit = subprocess.check_output(
        ["git", "-C", str(build_checker.REPO_ROOT), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    tree = subprocess.check_output(
        ["git", "-C", str(build_checker.REPO_ROOT), "rev-parse", "HEAD^{tree}"],
        text=True,
    ).strip()
    source_root, source_count, source_bytes = build_checker.compute_source_closure(
        build_checker.REPO_ROOT
    )
    programs = []
    for stage, package, artifact_file, image_id, child_stage, child_image_id in (
        build_checker.PROGRAM_SPECS
    ):
        raw = program_raw[stage]
        programs.append(
            {
                "stage": stage,
                "package": package,
                "artifact_file": artifact_file,
                "program_binary_bytes": len(raw),
                "program_binary_sha256": _sha256(raw),
                "image_id_hex": image_id,
                "image_id_words_le": build_checker._image_words_le(image_id),
                "verified_child_stage": child_stage,
                "verified_child_image_id": child_image_id,
            }
        )
    return {
        "schema": build_checker.RECORD_SCHEMA,
        "recorded_at": "2026-07-12",
        "source_snapshot": {
            "repository_commit": commit,
            "repository_tree": tree,
            "repository_dirty": False,
            "source_root_sha256": source_root,
            "source_file_count": source_count,
            "source_bytes": source_bytes,
        },
        "toolchain": {
            "rustc": "rustc 1.88.0",
            "cargo": "cargo 1.88.0",
            "r0vm": "risc0-r0vm 3.0.5 sha256:" + _sha256(r0vm.read_bytes()),
            "cargo_risczero": "cargo-risczero 3.0.5 sha256:" + "6" * 64,
            "risc0_zkvm": "3.0.5",
            "cargo_lock_sha256": _sha256(
                (build_checker.REPO_ROOT / build_checker.CARGO_LOCK_RELATIVE).read_bytes()
            ),
            "target": "riscv32im-risc0-zkvm-elf",
            "build_jobs": 2,
            "offline": True,
            "locked": True,
        },
        "programs": programs,
        "executed_commands": {
            field: True for field in sorted(build_checker.EXECUTED_COMMAND_FIELDS)
        },
        "claims": {
            **{field: True for field in sorted(build_checker.TRUE_CLAIMS)},
            **{field: False for field in sorted(build_checker.FALSE_CLAIMS)},
        },
    }


def _fixture(tmp_path: Path) -> _Fixture:
    source = tmp_path / "source"
    raw: dict[str, bytes] = {
        "source_request": _json_line({"kind": "bounded-source-request"}),
        "source_proof": _json_line({"kind": "bounded-source-proof"}),
        "adapter_receipt": _receipt("adapter"),
        "leaf_source_envelope": b"bounded-source-envelope\n",
        "leaf_receipt": _receipt("leaf"),
        "l1_receipt": _receipt("level-one"),
        "l2_receipt": _receipt("level-two"),
        "settlement_receipt": _receipt("settlement"),
        "settlement_admission_journal": b"bounded-admission-journal\n",
        "settlement_guest_input": b"bounded-guest-input\n",
        "settlement_replay": b"bounded-replay\n",
        "settlement_da_certificate": b"bounded-da-certificate\n",
    }
    for positive, mutation in (
        ("leaf_receipt", "leaf_mutation_receipt"),
        ("l1_receipt", "l1_mutation_receipt"),
        ("l2_receipt", "l2_mutation_receipt"),
        ("settlement_receipt", "settlement_mutation_receipt"),
    ):
        raw[mutation] = _mutation(raw[positive])

    program_raw: dict[str, bytes] = {}
    stage_to_artifact = {
        stage: artifact_id
        for (stage, _package, _file, _image, _child, _child_image), (
            artifact_id,
            _path,
            _kind,
        ) in zip(build_checker.PROGRAM_SPECS, evidence_checker.ARTIFACT_SPECS[16:20], strict=True)
    }
    for stage, artifact_id in stage_to_artifact.items():
        program_raw[stage] = _program(stage)
        raw[artifact_id] = program_raw[stage]

    facts = {artifact_id: _sha256(value) for artifact_id, value in raw.items()}
    external = {
        "ok": True,
        "schema": "zenodex.source_opened_spot_settlement_verifier_v6.response.v1",
        "verified_settlement_admission": {
            "receipt_sha256": facts["settlement_receipt"],
            "guest_input_sha256": facts["settlement_guest_input"],
            "admission_journal_sha256": facts["settlement_admission_journal"],
        },
    }
    raw["external_verifier_output"] = _json_line(external)
    chain = {
        "ok": True,
        "schema": "zenodex.source_opened_spot_v6_chain_verifier.response.v1",
        "positive_receipts_verified": 4,
        "exact_seal_mutations_rejected": 4,
        "fake_receipt_rejected": True,
        "receipt_profile_id": evidence_checker.SUCCINCT_PROFILE_ID,
        "leaf_receipt_sha256": facts["leaf_receipt"],
        "level_one_receipt_sha256": facts["l1_receipt"],
        "level_two_receipt_sha256": facts["l2_receipt"],
        "settlement_receipt_sha256": facts["settlement_receipt"],
        "settlement_claim_binding": "e" * 64,
        "settlement_admission_journal_sha256": facts[
            "settlement_admission_journal"
        ],
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }
    raw["chain_verifier_output"] = _json_line(chain)
    facts = {artifact_id: _sha256(value) for artifact_id, value in raw.items()}

    artifacts = {
        artifact_id: _write(source / f"input-{index:02d}.artifact", raw[artifact_id])
        for index, (artifact_id, _path, _kind) in enumerate(
            evidence_checker.ARTIFACT_SPECS
        )
    }

    reports_raw = {
        "source_opening": _json_line(
            {
                "schema": "zenodex/zrpf_spot_source_opening_run/v1",
                "ok": True,
                "source_image_id": build_checker.SOURCE_SPOT_IMAGE_ID,
                "source_program_sha256": "1" * 64,
                "source_cli_sha256": "2" * 64,
                "generator_sha256": "3" * 64,
                "r0vm_sha256": "4" * 64,
                "request_bytes": len(raw["source_request"]),
                "request_sha256": facts["source_request"],
                "proof_bytes": len(raw["source_proof"]),
                "proof_sha256": facts["source_proof"],
                "receipt_kind": "succinct",
                "nonclaims": list(builder.SOURCE_OPENING_NONCLAIMS),
            }
        ),
        "leaf": _json_line(
            {
                "action_nullifier_root": "b" * 64,
                "adapter_receipt_sha256": facts["adapter_receipt"],
                "candidate_accepted": True,
                "guest_program_binary_bytes": len(raw["leaf_program_binary"]),
                "guest_program_binary_sha256": facts["leaf_program_binary"],
                "ok": True,
                "receipt_bytes": len(raw["leaf_receipt"]),
                "receipt_profile_id": evidence_checker.SUCCINCT_PROFILE_ID,
                "receipt_sha256": facts["leaf_receipt"],
                "source_envelope_bytes": len(raw["leaf_source_envelope"]),
                "source_envelope_sha256": facts["leaf_source_envelope"],
                "schema": "zenodex/zrpf_source_opened_spot_value_leaf_v6_proof_report/v2",
                "source_proof_sha256": facts["source_proof"],
                "statement_hash": "c" * 64,
                "status": "source_opened_spot_value_leaf_v6_succinct_receipt_verified",
                "v6_image_id": build_checker.LEAF_IMAGE_ID,
                "verified_program_manifest_root": "d" * 64,
                "nonclaims": list(builder.LEAF_NONCLAIMS),
            }
        ),
        "level_one": _json_line(
            {
                "child_receipt_sha256": facts["leaf_receipt"],
                "image_id": build_checker.L1_IMAGE_ID,
                "ok": True,
                "receipt_bytes": len(raw["l1_receipt"]),
                "receipt_sha256": facts["l1_receipt"],
                "schema": "zenodex/zrpf_source_opened_spot_value_aggregate_l1_v6_proof_report/v1",
                "status": "source_opened_spot_value_aggregate_l1_v6_succinct_receipt_verified",
                "verified_child_count": 1,
            }
        ),
        "level_two": _json_line(
            {
                "child_receipt_sha256": facts["l1_receipt"],
                "image_id": build_checker.L2_IMAGE_ID,
                "ok": True,
                "receipt_bytes": len(raw["l2_receipt"]),
                "receipt_sha256": facts["l2_receipt"],
                "schema": "zenodex/zrpf_source_opened_spot_value_aggregate_l2_v6_proof_report/v1",
                "status": "source_opened_spot_value_aggregate_l2_v6_succinct_receipt_verified",
                "verified_child_count": 1,
            }
        ),
        "settlement": _json_line(
            {
                "action_count": 1,
                "admission_journal_bytes": len(raw["settlement_admission_journal"]),
                "admission_journal_sha256": facts["settlement_admission_journal"],
                "consumed_object_count": 1,
                "data_availability_certificate_bytes": len(
                    raw["settlement_da_certificate"]
                ),
                "data_availability_certificate_sha256": facts[
                    "settlement_da_certificate"
                ],
                "image_id": build_checker.SETTLEMENT_IMAGE_ID,
                "l2_receipt_sha256": facts["l2_receipt"],
                "mutation_receipt_sha256": facts["settlement_mutation_receipt"],
                "mutation_rejected": True,
                "ok": True,
                "receipt_bytes": len(raw["settlement_receipt"]),
                "receipt_sha256": facts["settlement_receipt"],
                "replay_bytes": len(raw["settlement_replay"]),
                "replay_sha256": facts["settlement_replay"],
                "schema": "zenodex/zrpf_source_opened_spot_settlement_v6_proof_report/v1",
                "source_envelope_sha256": facts["leaf_source_envelope"],
                "status": "source_opened_spot_settlement_v6_succinct_receipt_verified",
                "settlement_claim_binding": "e" * 64,
                "settlement_program_manifest_root": "f" * 64,
                "settlement_program_id": build_checker.SETTLEMENT_IMAGE_ID,
                "succinct_receipt_profile_id": evidence_checker.SUCCINCT_PROFILE_ID,
                "guest_input_bytes": len(raw["settlement_guest_input"]),
                "guest_input_sha256": facts["settlement_guest_input"],
                "nonclaims": list(builder.SETTLEMENT_NONCLAIMS),
            }
        ),
        "retained_replay": _json_line(
            {
                "ambient_dev_chain_output_sha256": facts["chain_verifier_output"],
                "chain_verifier_sha256": "7" * 64,
                "exact_seal_mutations_rejected": 4,
                "fake_receipt_rejected": True,
                "normal_chain_output_sha256": facts["chain_verifier_output"],
                "normal_dev_outputs_equal": True,
                "ok": True,
                "positive_receipts_verified": 4,
                "production_authority": False,
                "release_authority": False,
                "schema": "zenodex/zrpf_source_opened_spot_v6_retained_replay/v1",
                "settlement_authority": False,
                "settlement_mutation_error_code": evidence_checker.MUTATION_ERROR_CODE,
                "settlement_verifier_sha256": "8" * 64,
                "settlement_verifier_output_sha256": facts[
                    "external_verifier_output"
                ],
            }
        ),
    }
    reports = {
        report_id: _write(source / f"report-{report_id}.json", value)
        for report_id, value in reports_raw.items()
    }

    r0vm = source / "r0vm"
    image_ids = {
        stage: image_id
        for stage, _package, _file, image_id, _child, _child_image in (
            build_checker.PROGRAM_SPECS
        )
    }
    r0vm.write_text(
        "#!/usr/bin/python3\n"
        "import sys\n"
        f"images = {image_ids!r}\n"
        "raw = open(sys.argv[2], 'rb').read().decode('utf-8', errors='ignore')\n"
        "stage = raw.split('bounded-test-program:', 1)[1].strip()\n"
        "print(images[stage])\n",
        encoding="utf-8",
    )
    r0vm.chmod(0o700)
    source_report = json.loads(reports["source_opening"].read_bytes())
    source_report["r0vm_sha256"] = _sha256(r0vm.read_bytes())
    reports["source_opening"].write_bytes(_json_line(source_report))
    build_record = _write(
        source / "build-record.json",
        build_checker.canonical_bytes(_build_record(program_raw, r0vm)),
    )
    return _Fixture(artifacts, reports, build_record, r0vm)


def _run_build(tmp_path: Path, fixture: _Fixture, suffix: str = "one") -> builder.BuildResult:
    return builder.build_evidence(
        recorded_at="2026-07-12",
        artifact_paths=fixture.artifacts,
        report_paths=fixture.reports,
        build_record_path=fixture.build_record,
        r0vm_path=fixture.r0vm,
        bundle_directory=tmp_path / f"bundle-{suffix}",
        evidence_path=tmp_path / f"evidence-{suffix}.json",
    )


def test_builder_emits_checker_accepted_exact_bundle_and_nonclaims(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)

    result = _run_build(tmp_path, fixture)

    assert result.artifact_count == len(evidence_checker.ARTIFACT_SPECS)
    assert result.scoped_local_replay_claim_allowed is True
    evidence, raw = evidence_checker.load_evidence(result.evidence_path)
    assert _sha256(raw) == result.evidence_sha256
    assert set(path.name for path in result.bundle_directory.iterdir()) == {
        path for _artifact_id, path, _kind in evidence_checker.ARTIFACT_SPECS
    }
    assert evidence["claims"] == {
        **{field: True for field in sorted(evidence_checker.TRUE_CLAIMS)},
        **{field: False for field in sorted(evidence_checker.FALSE_CLAIMS)},
    }
    report = evidence_checker.check_evidence(
        result.evidence_path,
        artifact_directory=result.bundle_directory,
        build_record_path=fixture.build_record,
        r0vm_path=fixture.r0vm,
        expected_evidence_sha256=result.evidence_sha256,
        require_scoped_claim=True,
    )
    assert report["ok"] is True
    assert report["release_authority"] is False
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False


def test_same_inputs_produce_identical_evidence_and_bundle_bytes(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)

    first = _run_build(tmp_path, fixture, "first")
    second = _run_build(tmp_path, fixture, "second")

    assert first.evidence_sha256 == second.evidence_sha256
    assert first.evidence_path.read_bytes() == second.evidence_path.read_bytes()
    for _artifact_id, path, _kind in evidence_checker.ARTIFACT_SPECS:
        assert (first.bundle_directory / path).read_bytes() == (
            second.bundle_directory / path
        ).read_bytes()


@pytest.mark.parametrize("kind", ["missing", "extra"])
def test_artifact_inventory_must_be_exact(tmp_path: Path, kind: str) -> None:
    fixture = _fixture(tmp_path)
    paths = dict(fixture.artifacts)
    if kind == "missing":
        paths.pop("source_request")
    else:
        paths["unreviewed"] = next(iter(paths.values()))

    with pytest.raises(builder.EvidenceBuildError, match="artifact path inventory mismatch"):
        builder.build_evidence(
            recorded_at="2026-07-12",
            artifact_paths=paths,
            report_paths=fixture.reports,
            build_record_path=fixture.build_record,
            r0vm_path=fixture.r0vm,
            bundle_directory=tmp_path / "bundle",
            evidence_path=tmp_path / "evidence.json",
        )


def test_symlink_artifact_rejects_before_output(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    paths = dict(fixture.artifacts)
    target = paths["source_request"]
    link = tmp_path / "source-request-link"
    link.symlink_to(target)
    paths["source_request"] = link

    with pytest.raises(builder.EvidenceBuildError, match="symlink"):
        builder.build_evidence(
            recorded_at="2026-07-12",
            artifact_paths=paths,
            report_paths=fixture.reports,
            build_record_path=fixture.build_record,
            r0vm_path=fixture.r0vm,
            bundle_directory=tmp_path / "bundle",
            evidence_path=tmp_path / "evidence.json",
        )
    assert not (tmp_path / "bundle").exists()
    assert not (tmp_path / "evidence.json").exists()


def test_report_hash_drift_rejects_before_output(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    leaf_report = json.loads(fixture.reports["leaf"].read_bytes())
    leaf_report["receipt_sha256"] = "9" * 64
    fixture.reports["leaf"].write_bytes(_json_line(leaf_report))

    with pytest.raises(builder.EvidenceBuildError, match="leaf receipt SHA-256 mismatch"):
        _run_build(tmp_path, fixture)
    assert not (tmp_path / "bundle-one").exists()
    assert not (tmp_path / "evidence-one.json").exists()


def test_source_report_must_bind_the_build_r0vm(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    source_report = json.loads(fixture.reports["source_opening"].read_bytes())
    source_report["r0vm_sha256"] = "9" * 64
    fixture.reports["source_opening"].write_bytes(_json_line(source_report))

    with pytest.raises(builder.EvidenceBuildError, match="source/build r0vm SHA-256"):
        _run_build(tmp_path, fixture)


def test_replay_report_cannot_promote_authority(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    replay = json.loads(fixture.reports["retained_replay"].read_bytes())
    replay["settlement_authority"] = True
    fixture.reports["retained_replay"].write_bytes(_json_line(replay))

    with pytest.raises(builder.EvidenceBuildError, match="settlement_authority"):
        _run_build(tmp_path, fixture)


def test_checker_contract_expansion_requires_builder_review(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fixture = _fixture(tmp_path)
    monkeypatch.setattr(
        evidence_checker,
        "TRUE_CLAIMS",
        evidence_checker.TRUE_CLAIMS | {"future_unreviewed_claim"},
    )

    with pytest.raises(builder.EvidenceBuildError, match="positive-claim contract changed"):
        _run_build(tmp_path, fixture)
    assert not (tmp_path / "bundle-one").exists()


@pytest.mark.parametrize(
    "raw",
    [
        b'{"schema":"a","schema":"b"}\n',
        b'{"schema":1.0}\n',
        b'{"schema":NaN}\n',
        b'{ "schema":"a" }\n',
    ],
)
def test_report_json_must_be_unambiguous_integer_only_and_canonical(
    tmp_path: Path, raw: bytes
) -> None:
    fixture = _fixture(tmp_path)
    fixture.reports["source_opening"].write_bytes(raw)

    with pytest.raises(builder.EvidenceBuildError, match="report|JSON|canonical"):
        _run_build(tmp_path, fixture)


def test_existing_output_is_never_overwritten(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    bundle = tmp_path / "bundle-one"
    bundle.mkdir()
    sentinel = bundle / "sentinel"
    sentinel.write_bytes(b"preserve")

    with pytest.raises(builder.EvidenceBuildError, match="already exists"):
        _run_build(tmp_path, fixture)
    assert sentinel.read_bytes() == b"preserve"


def test_non_regular_input_rejects_without_blocking(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    fifo = tmp_path / "artifact.fifo"
    os.mkfifo(fifo)
    paths = dict(fixture.artifacts)
    paths["source_request"] = fifo

    with pytest.raises(builder.EvidenceBuildError, match="regular file"):
        builder.build_evidence(
            recorded_at="2026-07-12",
            artifact_paths=paths,
            report_paths=fixture.reports,
            build_record_path=fixture.build_record,
            r0vm_path=fixture.r0vm,
            bundle_directory=tmp_path / "bundle",
            evidence_path=tmp_path / "evidence.json",
        )


@pytest.mark.parametrize("mutation", ["in_place", "replace_path"])
def test_stable_read_rejects_concurrent_file_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutation: str,
) -> None:
    candidate = tmp_path / "candidate.bin"
    candidate.write_bytes(b"a" * (builder.READ_CHUNK_BYTES + 128))
    real_read = builder.os.read
    changed = False

    def read_and_mutate(descriptor: int, maximum: int) -> bytes:
        nonlocal changed
        chunk = real_read(descriptor, maximum)
        if not changed:
            changed = True
            if mutation == "in_place":
                candidate.write_bytes(b"b" * (builder.READ_CHUNK_BYTES + 128))
            else:
                replacement = tmp_path / "replacement.bin"
                replacement.write_bytes(b"c" * (builder.READ_CHUNK_BYTES + 128))
                os.replace(replacement, candidate)
        return chunk

    monkeypatch.setattr(builder.os, "read", read_and_mutate)
    with pytest.raises(builder.EvidenceBuildError, match="changed during stable read"):
        builder._read_stable_bytes(
            candidate,
            maximum_bytes=2 * builder.READ_CHUNK_BYTES,
            label="candidate",
        )
