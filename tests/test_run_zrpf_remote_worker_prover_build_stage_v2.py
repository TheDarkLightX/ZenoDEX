from __future__ import annotations

import gzip
import hashlib
import io
import json
import tarfile
from pathlib import Path
from typing import cast

import pytest

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import run_zrpf_remote_worker_prover_build_stage_v2 as stage
from tools.zrpf_v6_identity_executor_types import BuildRequest, BuildResult

SOURCE_COMMIT = hashlib.sha1(b"worker-governance-G", usedforsecurity=False).hexdigest()
V7_IMAGE_ID = hashlib.sha256(b"worker-v7-program-image").hexdigest()


def _governance() -> dict[str, object]:
    image_raw = bytes(range(32))
    return {
        "schema": stage.governance.CHECK_SCHEMA,
        "status": "committed_post_pin_governance_binding_checked",
        "c0_commit": hashlib.sha1(b"worker-C0", usedforsecurity=False).hexdigest(),
        "c1_commit": hashlib.sha1(b"worker-C1", usedforsecurity=False).hexdigest(),
        "c2_commit": hashlib.sha1(b"worker-C2", usedforsecurity=False).hexdigest(),
        "governance_commit": SOURCE_COMMIT,
        "plan_sha256": hashlib.sha256(b"worker-plan").hexdigest(),
        "observations_sha256": hashlib.sha256(b"worker-observations").hexdigest(),
        "candidate_report_sha256": hashlib.sha256(b"worker-candidate-report").hexdigest(),
        "materialization_manifest_sha256": hashlib.sha256(
            b"worker-materialization-manifest"
        ).hexdigest(),
        "v6_settlement_image_id": image_raw.hex(),
        "v6_settlement_image_id_words": [
            int.from_bytes(image_raw[index : index + 4], "little") for index in range(0, 32, 4)
        ],
        "v7_child_policy_tree": hashlib.sha1(
            b"worker-v7-child-policy-tree", usedforsecurity=False
        ).hexdigest(),
        "v7_child_policy_sha256": hashlib.sha256(b"worker-v7-child-policy").hexdigest(),
        "validated_facts": dict(stage.GOVERNANCE_VALIDATED_FACTS),
        "authority": {field: False for field in stage.governance.AUTHORITY_FIELDS},
        "non_claims": list(stage.GOVERNANCE_NON_CLAIMS),
    }


def _runner_posture() -> dict[str, object]:
    return {
        "schema": planner.RUNNER_SECURITY_POSTURE_SCHEMA,
        "tool_identities": {
            "cargo": {"sha256": planner.TOOLCHAIN["outer_cargo_sha256"], "bytes": 101},
            "rustc": {"sha256": planner.TOOLCHAIN["rustc_sha256"], "bytes": 211},
            "r0vm": {"sha256": planner.TOOLCHAIN["r0vm_sha256"], "bytes": 307},
            "cargo_risczero": {
                "sha256": planner.TOOLCHAIN["cargo_risczero_sha256"],
                "bytes": 401,
            },
        },
        "observed_docker_client_identity": {"sha256": "d" * 64, "bytes": 503},
        "cargo_registry_identity": {
            "schema": planner.CARGO_REGISTRY_IDENTITY_SCHEMA,
            "root_sha256": "a" * 64,
            "file_count": 17,
            "total_bytes": 6_031,
            "components": ["cache", "index", "src"],
            "maximum_files": planner.MAX_CARGO_REGISTRY_FILES,
            "maximum_total_bytes": planner.MAX_CARGO_REGISTRY_BYTES,
            "maximum_file_bytes": planner.MAX_CARGO_REGISTRY_FILE_BYTES,
        },
        "resource_policy": dict(planner.RUNNER_RESOURCE_POLICY),
        "same_uid_resistance": False,
        "complete_build_input_closure_verified": False,
    }


def _outputs(tmp_path: Path) -> dict[str, Path]:
    return {role: tmp_path / "outputs" / f"{role}.bin" for role in stage.OUTPUT_ROLES}


class FakeArchiveRunner:
    def __init__(self, *, rename_first: bool = False) -> None:
        self.requests: list[BuildRequest] = []
        self.rename_first = rename_first

    def security_posture(self) -> dict[str, object]:
        return _runner_posture()

    def run(self, request: BuildRequest) -> BuildResult:
        self.requests.append(request)
        members: list[tuple[str, bytes, int]] = []
        for index, member in enumerate(request.archive_members):
            name = "00-wrong-position" if self.rename_first and index == 0 else member.name
            ordinal = int(member.name[:2]) - 1
            size = 603 + 4 * ordinal
            magic = b"\x7fELF" if member.executable else b"R0BF"
            seed = hashlib.sha256(member.name.encode("ascii")).digest()
            raw = (magic + seed * ((size // len(seed)) + 1))[:size]
            assert len(raw) == size
            assert raw != raw[::-1]
            members.append((name, raw, 0o555 if member.executable else 0o444))
        archive = _archive(members)
        request.output_directory.mkdir(mode=0o700)
        output = request.output_directory / request.artifact_file
        output.write_bytes(archive)
        return BuildResult(
            artifact_bytes=len(archive),
            artifact_sha256=hashlib.sha256(archive).hexdigest(),
            image_id=None,
        )


def _archive(members: list[tuple[str, bytes, int]]) -> bytes:
    buffer = io.BytesIO()
    with gzip.GzipFile(fileobj=buffer, mode="wb", mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode="w", format=tarfile.USTAR_FORMAT) as archive:
            for name, raw, mode in sorted(members):
                info = tarfile.TarInfo(name)
                info.size = len(raw)
                info.mode = mode
                info.uid = 0
                info.gid = 0
                info.mtime = 0
                archive.addfile(info, io.BytesIO(raw))
    return buffer.getvalue()


def test_worker_build_materializes_position_distinct_outputs_and_report(
    tmp_path: Path,
) -> None:
    outputs = _outputs(tmp_path)
    governance = _governance()
    governance_path = tmp_path / "governance.json"
    governance_path.write_bytes(planner.canonical_bytes(governance))
    runner = FakeArchiveRunner()
    run_root = tmp_path / "worker-build"

    stage.execute_worker_build_stage(
        source_commit=SOURCE_COMMIT,
        governance_path=governance_path,
        build_run_root=run_root,
        output_paths=outputs,
        runner=runner,
        image_id_computer=lambda raw: V7_IMAGE_ID if raw.startswith(b"R0BF") else "0" * 64,
        governance_checker=lambda _root: governance,
        repo_root=planner.REPO_ROOT,
    )

    assert not run_root.exists()
    assert [request.stage_id for request in runner.requests] == [
        "worker_v6_host_bundle",
        "worker_v7_bundle",
    ]
    assert len({outputs[role].read_bytes() for role in stage.BINARY_OUTPUT_ROLES}) == len(
        stage.BINARY_OUTPUT_ROLES
    )
    for ordinal, role in enumerate(stage.BUILD_OUTPUT_ROLES):
        assert len(outputs[role].read_bytes()) == 603 + 4 * ordinal
    assert outputs["v7_program"].read_bytes().startswith(b"R0BF")
    report_raw = outputs["worker_build_report"].read_bytes()
    assert (
        stage.validate_worker_build_report(
            report_raw,
            {role: outputs[role].read_bytes() for role in stage.BUILD_OUTPUT_ROLES},
            governance_path.read_bytes(),
            expected_source_commit=SOURCE_COMMIT,
            expected_v7_image_id=V7_IMAGE_ID,
        )
        == V7_IMAGE_ID
    )


def test_worker_build_run_root_cleanup_rejection_precedes_output_publication(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    outputs = _outputs(tmp_path)
    governance = _governance()
    governance_path = tmp_path / "governance.json"
    governance_path.write_bytes(planner.canonical_bytes(governance))

    def reject_cleanup(_path: Path) -> None:
        raise stage.WorkerBuildError("injected completed run-root cleanup failure")

    monkeypatch.setattr(stage, "_remove_completed_run_root", reject_cleanup)

    with pytest.raises(stage.WorkerBuildError, match="run-root cleanup failure"):
        stage.execute_worker_build_stage(
            source_commit=SOURCE_COMMIT,
            governance_path=governance_path,
            build_run_root=tmp_path / "cleanup-reject-run",
            output_paths=outputs,
            runner=FakeArchiveRunner(),
            image_id_computer=lambda _raw: V7_IMAGE_ID,
            governance_checker=lambda _root: governance,
            repo_root=planner.REPO_ROOT,
        )

    assert all(path.exists() is False for path in outputs.values())


def test_worker_build_fixture_distinguishes_every_commit_digest_and_role() -> None:
    governed = _governance()
    commits: list[str] = [
        cast(str, governed["c0_commit"]),
        cast(str, governed["c1_commit"]),
        cast(str, governed["c2_commit"]),
        cast(str, governed["governance_commit"]),
    ]
    digests: list[str] = [
        cast(str, governed["plan_sha256"]),
        cast(str, governed["observations_sha256"]),
        cast(str, governed["candidate_report_sha256"]),
        cast(str, governed["materialization_manifest_sha256"]),
        cast(str, governed["v6_settlement_image_id"]),
        cast(str, governed["v7_child_policy_sha256"]),
        V7_IMAGE_ID,
    ]
    assert len(set(commits)) == len(commits)
    assert len(set(digests)) == len(digests)
    assert all(bytes.fromhex(value) != bytes.fromhex(value)[::-1] for value in commits)
    assert all(bytes.fromhex(value) != bytes.fromhex(value)[::-1] for value in digests)


def test_worker_build_member_table_is_one_exact_literal_role_mapping() -> None:
    assert [
        (item.role, item.name, item.source, item.executable)
        for item in (*stage.V6_MEMBERS, *stage.V7_MEMBERS)
    ] == [
        (
            "v2_adapter_prover",
            "01-prove-v2-leaf-adapter",
            "/build/zrpf-worker-v6/target/release/prove_v2_leaf_adapter",
            True,
        ),
        (
            "v6_leaf_prover",
            "02-prove-spot-value-leaf-v6",
            "/build/zrpf-worker-v6/target/release/prove_spot_value_leaf_v6",
            True,
        ),
        (
            "v6_l1_prover",
            "03-prove-spot-value-aggregate-l1-v6",
            "/build/zrpf-worker-v6/target/release/prove_spot_value_aggregate_l1_v6",
            True,
        ),
        (
            "v6_l2_prover",
            "04-prove-spot-value-aggregate-l2-v6",
            "/build/zrpf-worker-v6/target/release/prove_spot_value_aggregate_l2_v6",
            True,
        ),
        (
            "v6_settlement_prover",
            "05-prove-source-opened-spot-settlement-v6",
            "/build/zrpf-worker-v6/target/release/prove_source_opened_spot_settlement_v6",
            True,
        ),
        (
            "v6_host_verifier",
            "06-source-opened-spot-settlement-verifier-v6",
            "/build/zrpf-worker-v6/target/release/source-opened-spot-settlement-verifier-v6",
            True,
        ),
        (
            "mutation_verifier",
            "07-verify-spot-v7-remote-mutations",
            "/build/zrpf-worker-v7/target/release/verify-spot-v7-remote-mutations",
            True,
        ),
        (
            "v7_program",
            "08-spot-settlement-v7-program",
            (
                "/build/zrpf-worker-v7/target/riscv-guest/"
                "zenodex-zrpf-risc0-spot-settlement-v7-methods/"
                "zenodex-zrpf-risc0-spot-settlement-v7-guest/"
                "riscv32im-risc0-zkvm-elf/release/"
                "zenodex-zrpf-risc0-spot-settlement-v7-guest.bin"
            ),
            False,
        ),
        (
            "v7_prover",
            "09-prove-spot-settlement-v7",
            "/build/zrpf-worker-v7/target/release/prove_spot_settlement_v7",
            True,
        ),
    ]


def test_worker_build_rejects_governance_source_and_archive_position_substitution(
    tmp_path: Path,
) -> None:
    governance = _governance()
    governance_path = tmp_path / "governance.json"
    governance_path.write_bytes(planner.canonical_bytes(governance))

    with pytest.raises(stage.WorkerBuildError, match="governance"):
        stage.execute_worker_build_stage(
            source_commit=SOURCE_COMMIT,
            governance_path=governance_path,
            build_run_root=tmp_path / "wrong-governance-run",
            output_paths=_outputs(tmp_path / "wrong-governance"),
            runner=FakeArchiveRunner(),
            image_id_computer=lambda _raw: V7_IMAGE_ID,
            governance_checker=lambda _root: {**governance, "governance_commit": "5" * 40},
            repo_root=planner.REPO_ROOT,
        )

    with pytest.raises(stage.WorkerBuildError, match="archive inventory"):
        stage.execute_worker_build_stage(
            source_commit=SOURCE_COMMIT,
            governance_path=governance_path,
            build_run_root=tmp_path / "renamed-run",
            output_paths=_outputs(tmp_path / "renamed"),
            runner=FakeArchiveRunner(rename_first=True),
            image_id_computer=lambda _raw: V7_IMAGE_ID,
            governance_checker=lambda _root: governance,
            repo_root=planner.REPO_ROOT,
        )


def test_worker_build_report_rejects_each_position_and_boolean_substitution(
    tmp_path: Path,
) -> None:
    outputs = _outputs(tmp_path)
    governance = _governance()
    governance_path = tmp_path / "governance.json"
    governance_path.write_bytes(planner.canonical_bytes(governance))
    stage.execute_worker_build_stage(
        source_commit=SOURCE_COMMIT,
        governance_path=governance_path,
        build_run_root=tmp_path / "report-run",
        output_paths=outputs,
        runner=FakeArchiveRunner(),
        image_id_computer=lambda _raw: V7_IMAGE_ID,
        governance_checker=lambda _root: governance,
        repo_root=planner.REPO_ROOT,
    )
    raw_outputs = {role: outputs[role].read_bytes() for role in stage.BUILD_OUTPUT_ROLES}
    report = planner.load_canonical_json(outputs["worker_build_report"], "worker report")

    for index in range(len(report["outputs"])):
        mutated = {**report, "outputs": [dict(row) for row in report["outputs"]]}
        mutated["outputs"][index]["sha256"] = f"{index + 1:064x}"
        mutated["report_id"] = stage.derive_worker_build_report_id(mutated)
        with pytest.raises(stage.WorkerBuildError, match="output"):
            stage.validate_worker_build_report(
                planner.canonical_bytes(mutated),
                raw_outputs,
                governance_path.read_bytes(),
                expected_source_commit=SOURCE_COMMIT,
                expected_v7_image_id=V7_IMAGE_ID,
            )

    for field in stage.AUTHORITY_FIELDS:
        for substituted in (True, 0, 1, None, "false"):
            mutated = dict(report)
            mutated["authority"] = dict(report["authority"])
            mutated["authority"][field] = substituted
            mutated["report_id"] = stage.derive_worker_build_report_id(mutated)
            with pytest.raises(stage.WorkerBuildError, match="authority"):
                stage.validate_worker_build_report(
                    planner.canonical_bytes(mutated),
                    raw_outputs,
                    governance_path.read_bytes(),
                    expected_source_commit=SOURCE_COMMIT,
                    expected_v7_image_id=V7_IMAGE_ID,
                )

    for field in stage.WORKER_VALIDATED_FACTS:
        for substituted in (False, 0, 1, None, "true"):
            mutated = dict(report)
            mutated["validated_facts"] = dict(report["validated_facts"])
            mutated["validated_facts"][field] = substituted
            mutated["report_id"] = stage.derive_worker_build_report_id(mutated)
            with pytest.raises(stage.WorkerBuildError, match="validated facts"):
                stage.validate_worker_build_report(
                    planner.canonical_bytes(mutated),
                    raw_outputs,
                    governance_path.read_bytes(),
                    expected_source_commit=SOURCE_COMMIT,
                    expected_v7_image_id=V7_IMAGE_ID,
                )

    wrong_source = dict(report)
    wrong_source["source_commit"] = "5" * 40
    wrong_source["report_id"] = stage.derive_worker_build_report_id(wrong_source)
    with pytest.raises(stage.WorkerBuildError, match="source"):
        stage.validate_worker_build_report(
            planner.canonical_bytes(wrong_source),
            raw_outputs,
            governance_path.read_bytes(),
            expected_source_commit=SOURCE_COMMIT,
            expected_v7_image_id=V7_IMAGE_ID,
        )

    wrong_image = dict(report)
    wrong_image["v7_image_id"] = "6" * 64
    wrong_image["report_id"] = stage.derive_worker_build_report_id(wrong_image)
    with pytest.raises(stage.WorkerBuildError, match="image ID"):
        stage.validate_worker_build_report(
            planner.canonical_bytes(wrong_image),
            raw_outputs,
            governance_path.read_bytes(),
            expected_source_commit=SOURCE_COMMIT,
            expected_v7_image_id=V7_IMAGE_ID,
        )

    wrong_governance = {**governance, "governance_commit": "7" * 40}
    wrong_governance_raw = planner.canonical_bytes(wrong_governance)
    wrong_binding = dict(report)
    wrong_binding["governance_sha256"] = hashlib.sha256(wrong_governance_raw).hexdigest()
    wrong_binding["report_id"] = stage.derive_worker_build_report_id(wrong_binding)
    with pytest.raises(stage.WorkerBuildError, match="governance"):
        stage.validate_worker_build_report(
            planner.canonical_bytes(wrong_binding),
            raw_outputs,
            wrong_governance_raw,
            expected_source_commit=SOURCE_COMMIT,
            expected_v7_image_id=V7_IMAGE_ID,
        )

    for _label, mutate in (
        (
            "schema",
            lambda value: value.update({"schema": "wrong-governance-schema"}),
        ),
        (
            "authority",
            lambda value: value["authority"].update({"production_authority": True}),
        ),
        (
            "validated fact",
            lambda value: value["validated_facts"].update(
                {"governance_checkout_is_clean_and_exact": False}
            ),
        ),
    ):
        mutated_governance = json.loads(json.dumps(governance))
        mutate(mutated_governance)
        mutated_governance_raw = planner.canonical_bytes(mutated_governance)
        mutated_report = dict(report)
        mutated_report["governance_sha256"] = hashlib.sha256(mutated_governance_raw).hexdigest()
        mutated_report["report_id"] = stage.derive_worker_build_report_id(mutated_report)
        with pytest.raises(stage.WorkerBuildError, match="governance"):
            stage.validate_worker_build_report(
                planner.canonical_bytes(mutated_report),
                raw_outputs,
                mutated_governance_raw,
                expected_source_commit=SOURCE_COMMIT,
                expected_v7_image_id=V7_IMAGE_ID,
            )

    for field in stage.GOVERNANCE_VALIDATED_FACTS:
        for substituted in (False, 0, 1, None, "true"):
            mutated_governance = json.loads(json.dumps(governance))
            mutated_governance["validated_facts"][field] = substituted
            mutated_governance_raw = planner.canonical_bytes(mutated_governance)
            mutated_report = dict(report)
            mutated_report["governance_sha256"] = hashlib.sha256(mutated_governance_raw).hexdigest()
            mutated_report["report_id"] = stage.derive_worker_build_report_id(mutated_report)
            with pytest.raises(stage.WorkerBuildError, match="validated facts"):
                stage.validate_worker_build_report(
                    planner.canonical_bytes(mutated_report),
                    raw_outputs,
                    mutated_governance_raw,
                    expected_source_commit=SOURCE_COMMIT,
                    expected_v7_image_id=V7_IMAGE_ID,
                )


def test_worker_build_rejects_output_ancestor_alias_before_creating_paths(
    tmp_path: Path,
) -> None:
    outputs = _outputs(tmp_path)
    outputs["v2_adapter_prover"] = tmp_path / "published"
    outputs["v6_leaf_prover"] = tmp_path / "published" / "child"

    with pytest.raises(stage.WorkerBuildError, match="antichain"):
        stage._validate_output_paths(outputs, planner.REPO_ROOT)

    assert not (tmp_path / "published").exists()
