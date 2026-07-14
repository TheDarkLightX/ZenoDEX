from __future__ import annotations

import copy
import hashlib
import json
import os
import select
import subprocess
from pathlib import Path
from typing import Any, cast

import pytest

from tests import test_plan_zrpf_source_opened_spot_v6_identity_rebuild as identity_fixture
from tools import plan_zrpf_remote_reproof_handoff_v2 as handoff

REPO_ROOT = Path(__file__).resolve().parents[1]
C0 = subprocess.check_output(["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD"], text=True).strip()


@pytest.fixture(scope="module")
def plan() -> dict[str, Any]:
    return cast(dict[str, Any], handoff.build_handoff(REPO_ROOT, C0, C0))


def _git(repo: Path, *arguments: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), *arguments], text=True).strip()


def _commit(repo: Path, message: str, name: str) -> str:
    path = repo / name
    path.write_text(message + "\n", encoding="ascii")
    subprocess.run(["git", "-C", str(repo), "add", name], check=True)
    subprocess.run(["git", "-C", str(repo), "commit", "-qm", message], check=True)
    return _git(repo, "rev-parse", "HEAD")


def _linear_repo(tmp_path: Path) -> tuple[Path, list[str]]:
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "-C", str(repo), "init", "-q"], check=True)
    subprocess.run(
        ["git", "-C", str(repo), "config", "user.email", "test@example.com"],
        check=True,
    )
    subprocess.run(["git", "-C", str(repo), "config", "user.name", "test"], check=True)
    return repo, [_commit(repo, label, f"{label}.txt") for label in ("c0", "c1", "c2", "g")]


def _ancestry_repo(tmp_path: Path) -> tuple[Path, list[str]]:
    repo = tmp_path / "ancestry-repo"
    subprocess.run(
        ["git", "clone", "-q", "--shared", "--no-checkout", str(REPO_ROOT), str(repo)],
        check=True,
    )
    tree = _git(repo, "rev-parse", f"{C0}^{{tree}}")
    commits = [C0]
    environment = {
        "GIT_AUTHOR_NAME": "ZRPF test",
        "GIT_AUTHOR_EMAIL": "zrpf-test@example.invalid",
        "GIT_AUTHOR_DATE": "2000-01-01T00:00:00+0000",
        "GIT_COMMITTER_NAME": "ZRPF test",
        "GIT_COMMITTER_EMAIL": "zrpf-test@example.invalid",
        "GIT_COMMITTER_DATE": "2000-01-01T00:00:00+0000",
    }
    for label in ("C1", "C2", "G"):
        commit = subprocess.check_output(
            ["git", "-C", str(repo), "commit-tree", tree, "-p", commits[-1]],
            input=f"{label}\n",
            text=True,
            env={**os.environ, **environment},
        ).strip()
        commits.append(commit)
    return repo, commits


def _artifact_bytes(role: str) -> bytes:
    return f"artifact:{role}\n".encode("ascii")


def _program_image_ids() -> dict[str, str]:
    stage_by_role = {role: stage for stage, role in handoff.IDENTITY_STAGE_ROLES.items()}
    return {
        role: hashlib.sha256(f"image:{stage_by_role.get(role, role)}".encode("ascii")).hexdigest()
        for role in handoff.PROGRAM_ROLES
    }


def _plan_for_chain(repo: Path, chain: list[str]) -> dict[str, Any]:
    return cast(dict[str, Any], handoff.build_handoff(repo, chain[0], chain[3]))


def _write_complete_artifacts(plan: dict[str, object], root: Path, repository: Path) -> None:
    contracts = plan["artifact_contracts"]
    assert isinstance(contracts, list)
    source = cast(dict[str, object], plan["source"])
    rebuild = handoff.identity.build_plan(
        str(source["c0_commit"]), handoff.IDENTITY_RUN_ROOT, repo_root=repository
    )
    observations = identity_fixture._observations(rebuild)
    programs: list[dict[str, object]] = []
    for spec, stage in zip(handoff.identity.STAGES, observations["stages"], strict=True):
        role = handoff.IDENTITY_STAGE_ROLES[spec.stage_id]
        raw = _artifact_bytes(role)
        program = stage["program"]
        program["program_binary_bytes"] = len(raw)
        program["program_binary_sha256"] = hashlib.sha256(raw).hexdigest()
        stage["child_pin"] = (
            None
            if not programs
            else {
                "stage_id": handoff.identity.STAGES[spec.ordinal - 2].stage_id,
                "image_id": programs[-1]["image_id"],
                "program_binary_sha256": programs[-1]["program_binary_sha256"],
            }
        )
        stage["repins"] = [
            {
                "path": repin.path,
                "symbol": repin.symbol,
                "value_kind": repin.value_kind,
                "visibility": repin.visibility,
                "value": handoff.identity._repin_value(
                    repin.value_kind,
                    program,
                    stage["source_tree_root_sha256"],
                ),
            }
            for repin in spec.repins
        ]
        programs.append(copy.deepcopy(program))
    source_cli = _artifact_bytes("source_cli")
    observations["stages"][0]["companion_host_binary"] = {
        "binary_file": "tau-state-proof-risc0-cli",
        "binary_bytes": len(source_cli),
        "binary_sha256": hashlib.sha256(source_cli).hexdigest(),
    }
    observations["settlement_self_image_two_pass"]["second_pass_program"] = copy.deepcopy(
        programs[-1]
    )
    observations["final_clean_rebuild"]["programs"] = copy.deepcopy(programs)
    observations["host_verifier"]["expected_settlement_image_id"] = programs[-1]["image_id"]
    report = handoff.identity.check_observations(rebuild, observations, repo_root=repository)
    exact_identity = {
        "identity_plan": handoff.identity.canonical_bytes(rebuild),
        "identity_observations": handoff.identity.canonical_bytes(observations),
        "identity_candidate_report": handoff.identity.canonical_bytes(report),
        "source_cli": source_cli,
        **{role: _artifact_bytes(role) for role in handoff.IDENTITY_STAGE_ROLES.values()},
    }
    for contract in contracts:
        assert isinstance(contract, dict)
        path = root / str(contract["path"])
        path.parent.mkdir(parents=True, exist_ok=True)
        raw = exact_identity.get(str(contract["role"]), _artifact_bytes(str(contract["role"])))
        path.write_bytes(raw)


def _write_execution_packets(
    plan: dict[str, object],
    artifact_root: Path,
    repository: Path,
    chain: list[str],
    packet_directory: Path,
) -> None:
    packet_directory.mkdir(mode=0o700)
    handoff.validate_handoff(plan, repository)
    ancestry = handoff.validate_literal_ancestry(repository, *chain)
    contracts = cast(list[dict[str, object]], plan["artifact_contracts"])
    records = {
        str(contract["role"]): handoff._artifact_record(contract, artifact_root)
        for contract in contracts
    }
    packets = handoff._execution_packets_from_records(plan, ancestry, records)
    for ordinal, (stage_id, packet) in enumerate(zip(handoff.TASK_ORDER, packets, strict=True)):
        name = f"{ordinal:02d}-{stage_id}.json"
        (packet_directory / name).write_bytes(handoff.canonical_json_bytes(packet))


def test_handoff_is_deterministic_content_addressed_and_topological(
    plan: dict[str, Any],
) -> None:
    assert plan == handoff.build_handoff(REPO_ROOT, C0, C0)
    assert plan["handoff_id"] == handoff.derive_handoff_id(plan)
    tasks = plan["tasks"]
    assert isinstance(tasks, list)
    contracts = {
        row["contract_id"]: row for row in cast(list[dict[str, Any]], plan["artifact_contracts"])
    }
    assert [task["stage_id"] for task in tasks] == list(handoff.TASK_ORDER)
    positions = {task["stage_id"]: index for index, task in enumerate(tasks)}
    for task in tasks:
        assert task["task_id"] == handoff.derive_task_id(task)
        assert all(positions[parent] < positions[task["stage_id"]] for parent in task["depends_on"])
        assert task["authority"] == handoff.false_authority()
        assert task["commands"]
        assert task["success_predicates"]
        input_roles = {contracts[item]["role"] for item in task["input_artifact_contract_ids"]}
        output_roles = {contracts[item]["role"] for item in task["output_artifact_contract_ids"]}
        for command in task["commands"]:
            if command["stdin_artifact_role"] is not None:
                assert command["stdin_artifact_role"] in input_roles
            if command["stdout_artifact_role"] is not None:
                assert command["stdout_artifact_role"] in output_roles
    planned = [task["stage_id"] for task in tasks if task["command_status"] == "template_planned"]
    assert planned == ["release_checks"]
    implemented = [
        task["stage_id"] for task in tasks if task["execution_adapter_status"] == "implemented"
    ]
    assert implemented == [
        "ancestry_materialization",
        "source_spot_proof",
        "v2_adapter_receipt",
        "v6_leaf_receipt",
        "v6_l1_receipt",
        "v6_l2_receipt",
        "v6_settlement_receipt",
        "v7_receipt",
        "mutation_verification",
    ]
    assert all(
        task["execution_adapter_status"] == "missing"
        for task in tasks
        if task["stage_id"] not in implemented
    )
    identity_state = handoff.task_states(plan, [{"role": "r0vm"}])[0]
    assert identity_state["status"] == "blocked"
    assert identity_state["command_template_available"] is True
    assert identity_state["execution_adapter_available"] is False
    handoff.validate_handoff(plan, REPO_ROOT)


def test_mutation_task_binds_every_program_receipt_and_exact_runner(
    plan: dict[str, Any],
) -> None:
    contracts = {
        row["contract_id"]: row for row in cast(list[dict[str, Any]], plan["artifact_contracts"])
    }
    task = next(row for row in plan["tasks"] if row["stage_id"] == "mutation_verification")
    input_roles = [contracts[item]["role"] for item in task["input_artifact_contract_ids"]]
    assert input_roles == [
        "v6_leaf_envelope",
        "v6_settlement_guest_input",
        "v7_guest_input",
        "v6_leaf_program",
        "v6_l1_program",
        "v6_l2_program",
        "v6_settlement_program",
        "v7_program",
        "v6_leaf_receipt",
        "v6_l1_receipt",
        "v6_l2_receipt",
        "v6_settlement_receipt",
        "v7_receipt",
        "v7_seal_mutation",
        "v6_settlement_seal_mutation",
        "mutation_verifier",
    ]
    assert task["commands"] == [
        {
            "runner": "@mutation_verifier",
            "argv": [
                "--leaf-source-envelope",
                "@v6_leaf_envelope",
                "--settlement-guest-input",
                "@v6_settlement_guest_input",
                "--v7-guest-input",
                "@v7_guest_input",
                "--leaf-program",
                "@v6_leaf_program",
                "--level-one-program",
                "@v6_l1_program",
                "--level-two-program",
                "@v6_l2_program",
                "--settlement-program",
                "@v6_settlement_program",
                "--v7-program",
                "@v7_program",
                "--leaf-receipt",
                "@v6_leaf_receipt",
                "--level-one-receipt",
                "@v6_l1_receipt",
                "--level-two-receipt",
                "@v6_l2_receipt",
                "--settlement-receipt",
                "@v6_settlement_receipt",
                "--v7-receipt",
                "@v7_receipt",
                "--settlement-mutation",
                "@v6_settlement_seal_mutation",
                "--v7-mutation",
                "@v7_seal_mutation",
                "--leaf-mutation-out",
                "@v6_leaf_seal_mutation",
                "--level-one-mutation-out",
                "@v6_l1_seal_mutation",
                "--level-two-mutation-out",
                "@v6_l2_seal_mutation",
            ],
            "stdin_artifact_role": None,
            "stdout_artifact_role": "mutation_report",
        }
    ]
    output_contracts = [contracts[item] for item in task["output_artifact_contract_ids"]]
    assert [(item["role"], item["maximum_bytes"]) for item in output_contracts] == [
        ("v6_leaf_seal_mutation", 16 * 1024 * 1024),
        ("v6_l1_seal_mutation", 16 * 1024 * 1024),
        ("v6_l2_seal_mutation", 16 * 1024 * 1024),
        ("mutation_report", 64 * 1024),
    ]


def test_source_proof_task_is_required_and_missing_source_proof_blocks_adapter(
    plan: dict[str, Any],
) -> None:
    tasks = copy.deepcopy(plan["tasks"])
    assert isinstance(tasks, list)
    tasks[:] = [task for task in tasks if task["stage_id"] != "source_spot_proof"]
    substituted = copy.deepcopy(plan)
    substituted["tasks"] = tasks
    substituted["handoff_id"] = handoff.derive_handoff_id(substituted)
    with pytest.raises(handoff.HandoffError, match="task order"):
        handoff.validate_handoff(substituted, REPO_ROOT)

    states = handoff.task_states(plan, [])
    adapter = next(row for row in states if row["stage_id"] == "v2_adapter_receipt")
    assert adapter["status"] == "blocked"
    assert "source_spot_proof" in adapter["missing_dependency_stages"]
    assert "source_proof" in adapter["missing_input_artifacts"]


def test_missing_adapter_receipt_blocks_v6_leaf(plan: dict[str, Any]) -> None:
    completed = [
        {"role": role}
        for role in (
            "identity_candidate_report",
            "identity_observations",
            "identity_plan",
            "r0vm",
            "source_cli",
            "source_program",
            "source_request",
            "source_proof",
            "v2_adapter_program",
            "v2_adapter_prover",
            "v6_leaf_program",
            "v6_leaf_prover",
        )
    ]
    states = handoff.task_states(plan, completed)
    leaf = next(row for row in states if row["stage_id"] == "v6_leaf_receipt")
    assert leaf["status"] == "blocked"
    assert leaf["missing_input_artifacts"] == ["v2_adapter_receipt"]


def test_stale_mac_bundle_and_task_substitution_reject(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    _write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    bundle = handoff.capture_return_bundle(
        plan,
        artifact_root,
        repo,
        execution_packet_directory=packet_directory,
        c0_commit=chain[0],
        c1_commit=chain[1],
        c2_commit=chain[2],
        governance_commit=chain[3],
        program_image_ids=_program_image_ids(),
    )

    stale = copy.deepcopy(bundle)
    stale["handoff_id"] = "0" * 64
    with pytest.raises(handoff.HandoffError, match="handoff ID"):
        handoff.validate_return_bundle(plan, stale, artifact_root, repo)

    substituted = copy.deepcopy(bundle)
    substituted["tasks"][0]["task_id"] = "1" * 64
    substituted["bundle_id"] = handoff.derive_bundle_id(substituted)
    with pytest.raises(handoff.HandoffError, match="task capture inventory"):
        handoff.validate_return_bundle(plan, substituted, artifact_root, repo)


def test_integer_boolean_substitution_rejects_handoff_and_task(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)

    authority_substitution = copy.deepcopy(plan)
    authority_substitution["authority"]["production_authority"] = 0
    authority_substitution["handoff_id"] = handoff.derive_handoff_id(authority_substitution)
    with pytest.raises(handoff.HandoffError, match="exact Boolean false"):
        handoff.validate_handoff(authority_substitution, repo)

    task_substitution = copy.deepcopy(plan)
    task = task_substitution["tasks"][0]
    task["authority"]["settlement_authority"] = 0
    task["ordinal"] = False
    task["task_id"] = handoff.derive_task_id(task)
    task_substitution["handoff_id"] = handoff.derive_handoff_id(task_substitution)
    with pytest.raises(handoff.HandoffError, match="governed source-derived plan"):
        handoff.validate_handoff(task_substitution, repo)


def test_integer_boolean_substitution_rejects_execution_packet(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    _write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    packet_path = packet_directory / "00-identity_rebuild.json"
    packet = handoff.load_canonical_json(packet_path, "execution packet")
    assert isinstance(packet, dict)
    packet["authority"]["release_authority"] = 0
    packet["ordinal"] = False
    packet["execution_packet_id"] = handoff.derive_execution_packet_id(packet)
    packet_path.write_bytes(handoff.canonical_json_bytes(packet))
    with pytest.raises(handoff.HandoffError, match="exact current input artifacts"):
        handoff.capture_return_bundle(
            plan,
            artifact_root,
            repo,
            execution_packet_directory=packet_directory,
            c0_commit=chain[0],
            c1_commit=chain[1],
            c2_commit=chain[2],
            governance_commit=chain[3],
            program_image_ids=_program_image_ids(),
        )


def test_integer_boolean_substitution_rejects_return_bundle(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    _write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    bundle = handoff.capture_return_bundle(
        plan,
        artifact_root,
        repo,
        execution_packet_directory=packet_directory,
        c0_commit=chain[0],
        c1_commit=chain[1],
        c2_commit=chain[2],
        governance_commit=chain[3],
        program_image_ids=_program_image_ids(),
    )

    authority_substitution = copy.deepcopy(bundle)
    authority_substitution["authority"]["ledger_authority"] = 0
    authority_substitution["bundle_id"] = handoff.derive_bundle_id(authority_substitution)
    with pytest.raises(handoff.HandoffError, match="exact Boolean false"):
        handoff.validate_return_bundle(plan, authority_substitution, artifact_root, repo)

    ancestry_substitution = copy.deepcopy(bundle)
    ancestry_substitution["ancestry"]["literal_direct_parent_chain_verified"] = 1
    ancestry_substitution["bundle_id"] = handoff.derive_bundle_id(ancestry_substitution)
    with pytest.raises(handoff.HandoffError, match="literal ancestry"):
        handoff.validate_return_bundle(plan, ancestry_substitution, artifact_root, repo)


def test_wrong_literal_ancestry_and_merge_commit_reject(tmp_path: Path) -> None:
    repo, chain = _linear_repo(tmp_path)
    with pytest.raises(handoff.HandoffError, match="literal parent"):
        handoff.validate_literal_ancestry(repo, chain[0], chain[2], chain[1], chain[3])

    primary_branch = _git(repo, "branch", "--show-current")
    subprocess.run(["git", "-C", str(repo), "switch", "-qc", "side", chain[1]], check=True)
    side = _commit(repo, "side", "side.txt")
    subprocess.run(["git", "-C", str(repo), "switch", "-q", primary_branch], check=True)
    subprocess.run(
        ["git", "-C", str(repo), "merge", "--no-ff", "-qm", "merge", side],
        check=True,
    )
    merge = _git(repo, "rev-parse", "HEAD")
    with pytest.raises(handoff.HandoffError, match="exactly one literal parent"):
        handoff.validate_literal_ancestry(repo, chain[0], chain[1], merge, merge)


def test_linked_worktree_common_graft_rejects(tmp_path: Path) -> None:
    repo, chain = _linear_repo(tmp_path)
    linked = tmp_path / "linked"
    subprocess.run(
        ["git", "-C", str(repo), "worktree", "add", "-q", str(linked), chain[3]],
        check=True,
    )
    grafts = repo / ".git/info/grafts"
    grafts.parent.mkdir(parents=True, exist_ok=True)
    grafts.write_text(f"{chain[3]} {chain[0]}\n", encoding="ascii")
    with pytest.raises(handoff.HandoffError, match="grafts"):
        handoff.validate_literal_ancestry(linked, *chain)


def test_oversized_commit_object_is_stream_bounded(tmp_path: Path) -> None:
    repo, chain = _linear_repo(tmp_path)
    tree = _git(repo, "rev-parse", f"{chain[2]}^{{tree}}")
    oversized = subprocess.check_output(
        ["git", "-C", str(repo), "commit-tree", tree, "-p", chain[2]],
        input="G\n" + ("x" * (70 * 1024)),
        text=True,
    ).strip()
    with pytest.raises(handoff.HandoffError, match="bounded Git stdout"):
        handoff.validate_literal_ancestry(repo, chain[0], chain[1], chain[2], oversized)


def test_git_capture_kills_descendant_holding_output_pipes(tmp_path: Path) -> None:
    child_pid_path = tmp_path / "child.pid"
    script = "\n".join(
        (
            "import os",
            "import time",
            f"path = {str(child_pid_path)!r}",
            "pid = os.fork()",
            "if pid:",
            "    with open(path, 'w', encoding='ascii') as handle:",
            "        handle.write(str(pid))",
            "    os._exit(0)",
            "time.sleep(60)",
        )
    )
    process = subprocess.Popen(
        ["/usr/bin/python3", "-c", script],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        with pytest.raises(TimeoutError, match="timed out"):
            handoff._capture_bounded_process(
                process,
                maximum_stdout=1024,
                maximum_stderr=1024,
                timeout_seconds=1,
            )
    finally:
        handoff._terminate_process_group(process)
    child_pid = int(child_pid_path.read_text(encoding="ascii"))
    try:
        child_pidfd = os.pidfd_open(child_pid)
    except ProcessLookupError:
        return
    try:
        exited, _, _ = select.select([child_pidfd], [], [], 2)
        assert exited == [child_pidfd]
    finally:
        os.close(child_pidfd)


def test_git_object_read_does_not_lazy_fetch(tmp_path: Path) -> None:
    repo, chain = _linear_repo(tmp_path)
    commit = chain[3]
    object_path = repo / ".git/objects" / commit[:2] / commit[2:]
    assert object_path.is_file()
    marker = tmp_path / "promisor-remote-ran"
    helper = tmp_path / "promisor-helper"
    helper.write_text(f"#!/bin/sh\ntouch {marker}\nexit 1\n", encoding="ascii")
    helper.chmod(0o755)
    subprocess.run(
        ["git", "-C", str(repo), "config", "extensions.partialClone", "origin"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(repo), "config", "remote.origin.promisor", "true"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(repo), "config", "remote.origin.partialclonefilter", "blob:none"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(repo), "config", "remote.origin.url", f"ext::{helper}"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(repo), "config", "protocol.ext.allow", "always"],
        check=True,
    )
    object_path.unlink()
    with pytest.raises(handoff.HandoffError, match="bounded Git command rejected"):
        handoff._git(repo, ["cat-file", "commit", commit], 64 * 1024)
    assert not marker.exists()


def test_return_governance_commit_must_equal_handoff_worker(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    wrong_worker_plan = cast(dict[str, Any], handoff.build_handoff(repo, chain[0], chain[2]))
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(wrong_worker_plan, artifact_root, repo)
    with pytest.raises(handoff.HandoffError, match="governance worker"):
        handoff.capture_return_bundle(
            wrong_worker_plan,
            artifact_root,
            repo,
            execution_packet_directory=tmp_path / "unused-packets",
            c0_commit=chain[0],
            c1_commit=chain[1],
            c2_commit=chain[2],
            governance_commit=chain[3],
            program_image_ids=_program_image_ids(),
        )


def test_duplicate_and_missing_return_artifacts_reject(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    _write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    bundle = handoff.capture_return_bundle(
        plan,
        artifact_root,
        repo,
        execution_packet_directory=packet_directory,
        c0_commit=chain[0],
        c1_commit=chain[1],
        c2_commit=chain[2],
        governance_commit=chain[3],
        program_image_ids=_program_image_ids(),
    )

    missing = copy.deepcopy(bundle)
    missing["artifacts"].pop()
    missing["bundle_id"] = handoff.derive_bundle_id(missing)
    with pytest.raises(handoff.HandoffError, match="artifact inventory"):
        handoff.validate_return_bundle(plan, missing, artifact_root, repo)

    duplicate = copy.deepcopy(bundle)
    duplicate["artifacts"][-1] = copy.deepcopy(duplicate["artifacts"][0])
    duplicate["bundle_id"] = handoff.derive_bundle_id(duplicate)
    with pytest.raises(handoff.HandoffError, match="artifact inventory"):
        handoff.validate_return_bundle(plan, duplicate, artifact_root, repo)


def test_aggregate_artifact_bound_applies_during_collection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    contracts = cast(list[dict[str, object]], plan["artifact_contracts"])
    monkeypatch.setattr(handoff, "MAX_TOTAL_ARTIFACT_BYTES", 1)
    with pytest.raises(handoff.HandoffError, match="aggregate artifact bytes"):
        handoff._artifact_records(contracts, artifact_root)


def test_artifact_substitution_rejects(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    _write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    bundle = handoff.capture_return_bundle(
        plan,
        artifact_root,
        repo,
        execution_packet_directory=packet_directory,
        c0_commit=chain[0],
        c1_commit=chain[1],
        c2_commit=chain[2],
        governance_commit=chain[3],
        program_image_ids=_program_image_ids(),
    )
    record = bundle["artifacts"][0]
    assert isinstance(record, dict)
    path = artifact_root / str(record["path"])
    path.write_bytes(b"substituted\n")
    with pytest.raises(handoff.HandoffError, match="artifact SHA-256"):
        handoff.validate_return_bundle(plan, bundle, artifact_root, repo)


def test_identity_plan_substitution_rejects_before_capture(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    _write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    contracts = cast(list[dict[str, Any]], plan["artifact_contracts"])
    identity_plan = next(row for row in contracts if row["role"] == "identity_plan")
    (artifact_root / identity_plan["path"]).write_bytes(b"{}\n")
    with pytest.raises(handoff.HandoffError, match="identity rebuild plan"):
        handoff.capture_return_bundle(
            plan,
            artifact_root,
            repo,
            execution_packet_directory=packet_directory,
            c0_commit=chain[0],
            c1_commit=chain[1],
            c2_commit=chain[2],
            governance_commit=chain[3],
            program_image_ids=_program_image_ids(),
        )


def test_execution_packet_input_substitution_rejects(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    _write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    contracts = cast(list[dict[str, Any]], plan["artifact_contracts"])
    source_request = next(row for row in contracts if row["role"] == "source_request")
    (artifact_root / source_request["path"]).write_bytes(b"substituted request\n")
    with pytest.raises(handoff.HandoffError, match="exact current input artifacts"):
        handoff.capture_return_bundle(
            plan,
            artifact_root,
            repo,
            execution_packet_directory=packet_directory,
            c0_commit=chain[0],
            c1_commit=chain[1],
            c2_commit=chain[2],
            governance_commit=chain[3],
            program_image_ids=_program_image_ids(),
        )


def test_missing_and_surplus_execution_packets_reject(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)

    missing_directory = tmp_path / "missing-packets"
    _write_execution_packets(plan, artifact_root, repo, chain, missing_directory)
    (missing_directory / "11-release_checks.json").unlink()
    with pytest.raises(handoff.HandoffError, match="execution packet inventory"):
        handoff.capture_return_bundle(
            plan,
            artifact_root,
            repo,
            execution_packet_directory=missing_directory,
            c0_commit=chain[0],
            c1_commit=chain[1],
            c2_commit=chain[2],
            governance_commit=chain[3],
            program_image_ids=_program_image_ids(),
        )

    surplus_directory = tmp_path / "surplus-packets"
    _write_execution_packets(plan, artifact_root, repo, chain, surplus_directory)
    source = surplus_directory / "00-identity_rebuild.json"
    (surplus_directory / "99-duplicate.json").write_bytes(source.read_bytes())
    with pytest.raises(handoff.HandoffError, match="execution packet inventory"):
        handoff.capture_return_bundle(
            plan,
            artifact_root,
            repo,
            execution_packet_directory=surplus_directory,
            c0_commit=chain[0],
            c1_commit=chain[1],
            c2_commit=chain[2],
            governance_commit=chain[3],
            program_image_ids=_program_image_ids(),
        )


def test_prepare_task_cli_writes_only_the_governed_packet_name(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    handoff_path = tmp_path / "handoff.json"
    handoff_path.write_bytes(handoff.canonical_json_bytes(plan))
    packet_directory = tmp_path / "packets"
    packet_directory.mkdir()
    output = packet_directory / "03-source_spot_proof.json"
    assert (
        handoff.main(
            [
                "prepare-task",
                "--repository",
                str(repo),
                "--handoff",
                str(handoff_path),
                "--artifact-root",
                str(artifact_root),
                "--stage",
                "source_spot_proof",
                "--c0-commit",
                chain[0],
                "--c1-commit",
                chain[1],
                "--c2-commit",
                chain[2],
                "--governance-commit",
                chain[3],
                "--output",
                str(output),
            ]
        )
        == 0
    )
    packet = handoff.load_canonical_json(output, "execution packet")
    assert isinstance(packet, dict)
    assert packet["stage_id"] == "source_spot_proof"
    assert packet["execution_packet_id"] == handoff.derive_execution_packet_id(packet)


def test_symlinked_artifact_and_missing_program_identity_reject(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    _write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    with pytest.raises(handoff.HandoffError, match="program image ID inventory"):
        handoff.capture_return_bundle(
            plan,
            artifact_root,
            repo,
            execution_packet_directory=packet_directory,
            c0_commit=chain[0],
            c1_commit=chain[1],
            c2_commit=chain[2],
            governance_commit=chain[3],
            program_image_ids={},
        )

    contracts = cast(list[dict[str, Any]], plan["artifact_contracts"])
    victim = artifact_root / contracts[0]["path"]
    target = artifact_root / "symlink-target"
    target.write_bytes(victim.read_bytes())
    victim.unlink()
    victim.symlink_to(target)
    with pytest.raises(handoff.HandoffError, match="symlink"):
        handoff.capture_return_bundle(
            plan,
            artifact_root,
            repo,
            execution_packet_directory=packet_directory,
            c0_commit=chain[0],
            c1_commit=chain[1],
            c2_commit=chain[2],
            governance_commit=chain[3],
            program_image_ids=_program_image_ids(),
        )


def test_return_bundle_is_authority_neutral(tmp_path: Path) -> None:
    repo, chain = _ancestry_repo(tmp_path)
    plan = _plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    _write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    _write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    bundle = handoff.capture_return_bundle(
        plan,
        artifact_root,
        repo,
        execution_packet_directory=packet_directory,
        c0_commit=chain[0],
        c1_commit=chain[1],
        c2_commit=chain[2],
        governance_commit=chain[3],
        program_image_ids=_program_image_ids(),
    )
    assert bundle["authority"] == handoff.false_authority()
    assert bundle["bundle_id"] == handoff.derive_bundle_id(bundle)
    assert handoff.validate_return_bundle(plan, bundle, artifact_root, repo) == bundle

    expanded = copy.deepcopy(bundle)
    expanded["unexpected"] = False
    expanded["bundle_id"] = handoff.derive_bundle_id(expanded)
    with pytest.raises(handoff.HandoffError, match="return bundle fields mismatch"):
        handoff.validate_return_bundle(plan, expanded, artifact_root, repo)


def test_canonical_decoder_rejects_duplicate_and_noncanonical_json() -> None:
    with pytest.raises(handoff.HandoffError, match="duplicate JSON key"):
        handoff.strict_json_loads(b'{"schema":"a","schema":"b"}\n')
    with pytest.raises(handoff.HandoffError, match="canonical"):
        handoff.strict_json_loads(json.dumps({"schema": "a"}).encode("ascii"))
    with pytest.raises(handoff.HandoffError, match="digit bound"):
        handoff.strict_json_loads(b'{"value":123456789012345678901}\n')


def test_contract_ids_bind_roles_and_producers(plan: dict[str, Any]) -> None:
    contracts = plan["artifact_contracts"]
    assert isinstance(contracts, list)
    ids = [contract["contract_id"] for contract in contracts]
    assert len(ids) == len(set(ids))
    for contract in contracts:
        expected = hashlib.sha256(
            handoff.ARTIFACT_CONTRACT_DOMAIN
            + handoff.canonical_json_bytes({**contract, "contract_id": "0" * 64})
        ).hexdigest()
        assert contract["contract_id"] == expected
