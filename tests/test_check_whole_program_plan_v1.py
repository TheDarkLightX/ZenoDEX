from __future__ import annotations

import copy
import dataclasses
import hashlib
import inspect
import json
import os
import re
import shutil
import subprocess
import sys
from collections.abc import Callable, Iterator, Mapping
from pathlib import Path
from typing import Any

import pytest

import tools.check_whole_program_plan_v1 as checker_module
import tools.whole_program_artifact_binding_v1 as artifact_binding_module
from tools.check_whole_program_plan_v1 import (
    GENERATED_BEGIN,
    GENERATED_END,
    ORDINARY_VALIDATION_PROFILE_V1,
    PLAN_JSON_PATH,
    PLAN_MARKDOWN_PATH,
    POST_REGENERATION_PROFILE_V1,
    CleanlinessScopeV1,
    ConfinedRootV1,
    PlanCheckModeV1,
    PlanValidationKindV1,
    PlanValidationProfileV1,
    canonical_plan_json_v1,
    check_whole_program_plan_v1,
    compare_live_gate_execution_v1,
    execute_live_gates_v1,
    lineage_findings_v1,
    load_plan_v1,
    main,
    plan_artifact_findings_v1,
    plan_live_gate_effects_v1,
    plan_report_v1,
    read_confined_file_v1,
    refresh_plan_v1,
    render_generated_markdown_v1,
    replace_confined_file_v1,
    scoped_worktree_dirty_paths_v1,
    snapshot_entries_from_listing_v1,
    source_snapshot_v1,
    subject_state_findings_v1,
    validate_plan_v1,
)
from tools.live_gate_registry_v1 import (
    LIVE_GATE_REGISTRY,
    PROCESS_ENVIRONMENT_BASE,
    AnchoredDirectoryV1,
    AnchorRefused,
    LiveGateObservationV1,
    ProcessBoundsV1,
    gate_environment_v1,
    git_v1,
    run_bounded_process_v1,
)

ROOT = Path(__file__).resolve().parents[1]
FAST_GATE_ID = "m6_asset_precision_policy"
GIT_ENV = {
    **PROCESS_ENVIRONMENT_BASE,
    "GIT_AUTHOR_NAME": "fixture",
    "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
    "GIT_COMMITTER_NAME": "fixture",
    "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
    "GIT_AUTHOR_DATE": "2026-08-25T00:00:00+0000",
    "GIT_COMMITTER_DATE": "2026-08-25T00:00:00+0000",
}

_DISPOSABLE_COMPLETE_SUBJECTS: list[Path] = []
_CLONE_FIXTURE_NAME_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,63}\Z")


def _remove_disposable_subject(root: Path) -> None:
    if root.is_symlink():
        root.unlink()
    elif root.exists():
        shutil.rmtree(root)


@pytest.fixture(autouse=True)
def _remove_disposable_complete_subjects_after_each_test() -> Iterator[None]:
    """Bound peak disk use without weakening full-clone attack isolation."""

    try:
        yield
    finally:
        owned = list(dict.fromkeys(_DISPOSABLE_COMPLETE_SUBJECTS))
        failed: list[Path] = []
        errors: list[BaseException] = []
        for root in reversed(owned):
            try:
                _remove_disposable_subject(root)
            except BaseException as exc:
                failed.append(root)
                errors.append(exc)
        failed_set = set(failed)
        _DISPOSABLE_COMPLETE_SUBJECTS[:] = [
            root for root in owned if root in failed_set
        ]
        if errors:
            primary = errors[0]
            for later in errors[1:]:
                primary.add_note(
                    f"later clone cleanup also failed: {type(later).__name__}: {later}"
                )
            raise primary


def _git(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["/usr/bin/git", *args], cwd=repo, env=GIT_ENV, check=True, capture_output=True, text=True
    )
    return result.stdout.strip()


def _owned_clone_destination_v1(tmp_path: Path, name: str) -> tuple[Path, Path]:
    """Create one exclusive helper-owned container and its clone destination."""

    if type(name) is not str or _CLONE_FIXTURE_NAME_RE.fullmatch(name) is None:
        raise ValueError("clone fixture name must be one canonical basename")
    requested = tmp_path / name
    try:
        requested.mkdir(mode=0o700)
    except FileExistsError as exc:
        raise FileExistsError(
            f"clone fixture destination already exists: {name}"
        ) from exc
    _DISPOSABLE_COMPLETE_SUBJECTS.append(requested)
    return requested, requested


def _replace_aware_git(repo: Path, *args: str) -> str:
    """Run fixture Git with replacement refs enabled to construct an adversarial repository."""

    environment = dict(GIT_ENV)
    environment.pop("GIT_NO_REPLACE_OBJECTS", None)
    result = subprocess.run(
        ["/usr/bin/git", *args], cwd=repo, env=environment, check=True, capture_output=True, text=True
    )
    return result.stdout.strip()


def _clone_complete_subject(tmp_path: Path, name: str = "subject") -> Path:
    """Create a clean disposable complete subject from the committed test root."""

    container, root = _owned_clone_destination_v1(tmp_path, name)
    try:
        subprocess.run(
            ["/usr/bin/git", "clone", "-q", "--no-hardlinks", str(ROOT), str(root)],
            check=True,
            capture_output=True,
            text=True,
        )
    except BaseException as primary:
        try:
            _remove_disposable_subject(container)
        except BaseException as cleanup_error:
            primary.add_note(
                f"partial clone cleanup also failed: {type(cleanup_error).__name__}"
            )
        else:
            _DISPOSABLE_COMPLETE_SUBJECTS.remove(container)
        raise
    return root


def _clone_transport_subject(tmp_path: Path, name: str = "transport-subject") -> Path:
    """Transfer only advertised candidate history, without local object leakage."""

    container, root = _owned_clone_destination_v1(tmp_path, name)
    try:
        subprocess.run(
            [
                "/usr/bin/git",
                "clone",
                "-q",
                "--no-local",
                str(ROOT),
                str(root),
            ],
            check=True,
            capture_output=True,
            text=True,
        )
    except BaseException as primary:
        try:
            _remove_disposable_subject(container)
        except BaseException as cleanup_error:
            primary.add_note(
                f"partial clone cleanup also failed: {type(cleanup_error).__name__}"
            )
        else:
            _DISPOSABLE_COMPLETE_SUBJECTS.remove(container)
        raise
    return root


@pytest.mark.parametrize(
    "clone_helper",
    (_clone_complete_subject, _clone_transport_subject),
    ids=("complete", "transport"),
)
def test_failed_clone_is_removed_before_the_helper_propagates(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    clone_helper: Callable[[Path, str], Path],
) -> None:
    def fail_after_partial_clone(*args: object, **_kwargs: object) -> object:
        command = args[0]
        assert isinstance(command, list)
        root = Path(command[-1])
        (root / "partial.pack").write_bytes(b"partial")
        raise subprocess.CalledProcessError(128, ["git", "clone"])

    monkeypatch.setattr(subprocess, "run", fail_after_partial_clone)

    with pytest.raises(subprocess.CalledProcessError):
        clone_helper(tmp_path, "partial")

    assert not any(tmp_path.iterdir())
    assert _DISPOSABLE_COMPLETE_SUBJECTS == []


@pytest.mark.parametrize(
    "clone_helper",
    (_clone_complete_subject, _clone_transport_subject),
    ids=("complete", "transport"),
)
def test_failed_clone_never_deletes_a_preexisting_destination(
    tmp_path: Path,
    clone_helper: Callable[[Path, str], Path],
) -> None:
    # Arrange
    destination = tmp_path / "preexisting"
    destination.mkdir()
    sentinel = destination / "keep.txt"
    sentinel.write_text("caller-owned\n", encoding="utf-8")

    # Act / Assert
    with pytest.raises(FileExistsError):
        clone_helper(tmp_path, "preexisting")
    assert sentinel.read_text(encoding="utf-8") == "caller-owned\n"
    assert _DISPOSABLE_COMPLETE_SUBJECTS == []


@pytest.mark.parametrize("name", ("../escape", "/tmp/escape", "nested/path", ""))
def test_clone_fixture_name_is_one_canonical_basename(
    tmp_path: Path, name: str
) -> None:
    with pytest.raises(ValueError):
        _clone_complete_subject(tmp_path, name)
    assert not any(tmp_path.iterdir())
    assert _DISPOSABLE_COMPLETE_SUBJECTS == []


def _replacement_commit_for_head(repo: Path, raw_head: str, message: str) -> str:
    """Build a replacement commit with the raw subject's parent, avoiding a replacement-parent cycle."""

    replacement_tree = _git(repo, "write-tree")
    parents = tuple(part for part in _git(repo, "show", "-s", "--format=%P", raw_head).split() if part)
    args = ["commit-tree", replacement_tree]
    for parent in parents:
        args.extend(("-p", parent))
    args.extend(("-m", message))
    return _git(repo, *args)


def _plan() -> dict[str, Any]:
    return copy.deepcopy(dict(load_plan_v1(ROOT)))


def _markdown() -> str:
    return (ROOT / PLAN_MARKDOWN_PATH).read_text(encoding="utf-8")


def _findings(plan: dict[str, Any], markdown: str | None) -> list[Any]:
    return validate_plan_v1(plan, root=ROOT, markdown=markdown)


def _rules(plan: dict[str, Any]) -> list[str]:
    return sorted({finding.rule_id for finding in _findings(plan, _markdown())})


def _task(plan: dict[str, Any], task_id: str) -> dict[str, Any]:
    for task in plan["tasks"]:
        if task["task_id"] == task_id:
            return task
    raise KeyError(task_id)


def _gate(plan: dict[str, Any], gate_id: str) -> dict[str, Any]:
    for gate in plan["live_gates"]:
        if gate["gate_id"] == gate_id:
            return gate
    raise KeyError(gate_id)


def _first_closed_task(plan: dict[str, Any]) -> dict[str, Any]:
    for task in plan["tasks"]:
        if task["status"] in {"DONE", "DONE_BOUNDED"} and any(
            item["kind"] in {"doc", "test", "checker", "manifest"} for item in task["evidence"]
        ):
            return task
    raise AssertionError("plan must contain one closed task with file evidence")


def _first_file_evidence(task: dict[str, Any]) -> dict[str, Any]:
    for item in task["evidence"]:
        if item["kind"] in {"doc", "test", "checker", "manifest"}:
            return item
    raise AssertionError("task must have file evidence")


def test_current_plan_is_valid_and_keeps_authority_none() -> None:
    # Arrange
    plan = _plan()

    # Act
    report = check_whole_program_plan_v1(ROOT)

    # Assert
    assert report["ok"] is True, report["findings"]
    assert report["authority"] == {
        "claim_authority": "NONE",
        "production_authority": "NONE",
        "production_ready": False,
        "release_ready": False,
    }
    assert plan["authority"] == report["authority"]
    assert report["task_count"] == len(plan["tasks"]) > 0
    vm_gate_status = report["vm_gate_status"]
    assert isinstance(vm_gate_status, dict)
    assert set(vm_gate_status) == {f"VM-{index:02d}" for index in range(1, 13)}
    assert "PASS" not in vm_gate_status.values()
    assert report["executed_live_gates"] == 0
    assert PlanCheckModeV1.EXECUTE.value == "execute"


@pytest.mark.parametrize(
    ("field", "promoted_value"),
    [("ready", True), ("authority", "SHADOW"), ("authority", "PRODUCTION")],
)
def test_authority_promotion_is_rejected_regardless_of_field(field: str, promoted_value: object) -> None:
    # Arrange: the mutant promotes one ceiling field; the key is composed at runtime so no
    # committed line literally asserts a promoted claim.
    plan = _plan()
    plan["authority"][f"production_{field}"] = promoted_value

    # Act / Assert
    assert _rules(plan) == ["authority_ceiling_violated"]


def test_plan_command_field_never_reaches_a_subprocess(tmp_path: Path) -> None:
    # Arrange: Mallory edits the tracked plan so a gate "command" would drop a marker file.
    marker = tmp_path / "marker"
    hostile = [sys.executable, "-c", f"open({str(marker)!r}, 'w').write('x')"]
    plan = _plan()
    gate = _gate(plan, FAST_GATE_ID)
    gate["command"] = hostile

    # Act: structural validation, single-gate comparison, and a full refresh attempt.
    validation_rules = _rules(plan)
    compare_findings = compare_live_gate_execution_v1(gate, ROOT)
    _refreshed, refresh_findings = refresh_plan_v1(plan, root=ROOT, observed_at="2026-08-25", repin_tasks=())

    # Assert: every path rejects before execution and the side effect never happens.
    assert "live_gate_registry_mismatch" in validation_rules
    assert [item.rule_id for item in compare_findings] == ["live_gate_registry_mismatch"]
    assert compare_findings[0].evidence == "command"
    assert "live_gate_registry_mismatch" in {item.rule_id for item in refresh_findings}
    assert not marker.exists()


def test_every_registry_binding_field_is_enforced_exactly() -> None:
    # Arrange
    mutations = {
        "checker_path": "tools/check_whole_program_plan_v1.py",
        "output_format": "text",
        "observed_projection": ["ok"],
        "timeout_seconds": 301,
    }

    # Act / Assert
    for field, value in mutations.items():
        plan = _plan()
        _gate(plan, FAST_GATE_ID)[field] = value
        findings = _findings(plan, _markdown())
        assert any(
            item.rule_id == "live_gate_registry_mismatch" and item.evidence == field for item in findings
        ), field


def test_external_gate_locations_cannot_be_machine_specific_absolute_paths() -> None:
    # Arrange
    rejected = {
        "/tmp/coordination/checkpoint_admission.py",
        "packet at /tmp/coordination/RUBRIC.sha256",
        "~/coordination/RUBRIC.sha256",
        "C:\\coordination\\RUBRIC.sha256",
    }
    accepted = "coordination packet (untracked, outside the repository): tools/example.py --flag a/b"

    # Act / Assert
    for location in sorted(rejected):
        plan = _plan()
        plan["external_gates"][0]["location"] = location
        assert "external_gate_location_absolute" in _rules(plan), location
    plan = _plan()
    plan["external_gates"][0]["location"] = accepted
    assert "external_gate_location_absolute" not in _rules(plan)


def test_registry_gate_set_must_match_exactly() -> None:
    # Arrange
    missing = _plan()
    missing["live_gates"] = [gate for gate in missing["live_gates"] if gate["gate_id"] != FAST_GATE_ID]
    foreign = _plan()
    extra = copy.deepcopy(_gate(foreign, FAST_GATE_ID))
    extra["gate_id"] = "zz_not_registered"
    foreign["live_gates"].append(extra)

    # Act / Assert
    assert "live_gate_registry_set_mismatch" in _rules(missing)
    foreign_rules = _rules(foreign)
    assert "live_gate_not_in_registry" in foreign_rules
    assert "live_gate_registry_set_mismatch" in foreign_rules


def test_registry_gate_execution_reproduces_recorded_observation_and_detects_drift() -> None:
    # Arrange
    plan = _plan()
    gate = _gate(plan, FAST_GATE_ID)
    drifted = copy.deepcopy(gate)
    drifted["observed"]["decimal_places"] = 9
    exit_drifted = copy.deepcopy(gate)
    exit_drifted["exit_code"] = 7

    # Act
    clean = compare_live_gate_execution_v1(gate, ROOT)
    drift = compare_live_gate_execution_v1(drifted, ROOT)
    exit_drift = compare_live_gate_execution_v1(exit_drifted, ROOT)

    # Assert
    assert clean == []
    assert [item.rule_id for item in drift] == ["live_gate_observation_drift"]
    assert drift[0].evidence == "decimal_places"
    assert [item.rule_id for item in exit_drift] == ["live_gate_exit_code_drift"]


def test_unknown_dependency_self_dependency_and_cycle_are_rejected() -> None:
    # Arrange
    plan = _plan()
    first, second = plan["tasks"][0], plan["tasks"][1]
    first["depends_on"] = [second["task_id"], "P9-T99", first["task_id"]]
    second["depends_on"] = [first["task_id"]]

    # Act
    rules = _rules(plan)

    # Assert
    assert {"task_dependency_unknown", "task_depends_on_itself", "task_dependency_cycle"} <= set(rules)
    assert "task_id_malformed" not in rules


def test_closed_task_requires_pinned_existing_evidence() -> None:
    # Arrange: four mutants of one closed task.
    without_evidence = _plan()
    _first_closed_task(without_evidence)["evidence"] = []
    drifted = _plan()
    _first_file_evidence(_first_closed_task(drifted))["sha256"] = "0" * 64
    missing = _plan()
    _first_file_evidence(_first_closed_task(missing))["reference"] = "docs/research/does_not_exist_v1.md"
    unpinned = _plan()
    _first_file_evidence(_first_closed_task(unpinned))["sha256"] = None

    # Act / Assert
    assert "closed_task_without_evidence" in _rules(without_evidence)
    assert "evidence_hash_drift" in _rules(drifted)
    assert "evidence_missing" in _rules(missing)
    assert "closed_task_evidence_unpinned" in _rules(unpinned)


def test_vm_improvement_claim_requires_ripr_counterexample_and_real_mutation_killer() -> None:
    # Arrange
    bare_claim = _plan()
    task = _first_closed_task(bare_claim)
    task["claims_vm_improvement"] = True
    task["ripr_counterexample"] = None
    task["mutation_killers"] = []
    ghost_killer = _plan()
    task = _first_closed_task(ghost_killer)
    task["claims_vm_improvement"] = True
    task["ripr_counterexample"] = "reach; infect; propagate; reveal"
    task["mutation_killers"] = ["tests/test_check_whole_program_plan_v1.py::test_does_not_exist"]
    open_claim = _plan()
    task = _task(open_claim, "P2-T01")
    task["claims_vm_improvement"] = True
    task["ripr_counterexample"] = "reach; infect; propagate; reveal"
    task["mutation_killers"] = [
        "tests/test_check_whole_program_plan_v1.py::test_current_plan_is_valid_and_keeps_authority_none"
    ]

    # Act
    bare_rules = _rules(bare_claim)
    ghost_rules = _rules(ghost_killer)
    open_rules = _rules(open_claim)

    # Assert
    assert {"vm_claim_without_ripr_counterexample", "vm_claim_without_mutation_killer"} <= set(bare_rules)
    assert "mutation_killer_missing" in ghost_rules
    assert "vm_claim_on_open_task" in open_rules


def test_vm_gate_pass_requires_every_mapped_task_done_and_exact_task_map() -> None:
    # Arrange
    passed = _plan()
    passed["vm_gate_status"][0]["status"] = "PASS"
    drifted = _plan()
    drifted["vm_gate_status"][0]["tasks"] = []

    # Act / Assert
    assert "vm_gate_pass_with_open_tasks" in _rules(passed)
    assert "vm_gate_task_map_drift" in _rules(drifted)


def test_finding_registry_cannot_close_without_a_killing_task() -> None:
    # Arrange
    plan = _plan()
    entry = next(item for item in plan["finding_registry"] if item["status"] == "OPEN")
    entry["status"] = "CLOSED"

    # Act / Assert
    assert "finding_closed_without_killer" in _rules(plan)


def test_duplicate_task_finding_and_policy_ids_are_rejected() -> None:
    # Arrange
    dup_task = _plan()
    dup_task["tasks"][1]["task_id"] = dup_task["tasks"][0]["task_id"]
    dup_finding = _plan()
    dup_finding["finding_registry"][1]["finding_id"] = dup_finding["finding_registry"][0]["finding_id"]
    dup_policy = _plan()
    dup_policy["unresolved_policies"][1]["policy_id"] = dup_policy["unresolved_policies"][0]["policy_id"]

    # Act / Assert
    assert "task_id_duplicate" in _rules(dup_task)
    assert "finding_id_duplicate" in _rules(dup_finding)
    assert "policy_id_duplicate" in _rules(dup_policy)


def test_unknown_status_and_deferred_task_without_policy_are_rejected() -> None:
    # Arrange
    unknown = _plan()
    unknown["tasks"][0]["status"] = "SHIPPED"
    deferred = _plan()
    deferred["tasks"][0]["status"] = "DEFERRED_SEMANTIC_DECISION"
    deferred["tasks"][0]["semantic_decisions_avoided"] = []

    # Act / Assert
    assert "task_status_unknown" in _rules(unknown)
    assert "deferred_task_without_policy" in _rules(deferred)


def test_live_gate_checker_hash_drift_and_projection_mismatch_are_findings() -> None:
    # Arrange
    drifted = _plan()
    drifted["live_gates"][0]["checker_sha256"] = "f" * 64
    mismatched = _plan()
    mismatched["live_gates"][0]["observed"] = {"unexpected_key": 1}

    # Act / Assert
    assert "live_gate_checker_hash_drift" in _rules(drifted)
    assert "live_gate_observed_projection_mismatch" in _rules(mismatched)


def test_markdown_generated_block_drift_and_missing_markers_are_findings() -> None:
    # Arrange
    plan = _plan()
    markdown = _markdown()
    begin = markdown.index(GENERATED_BEGIN)
    end = markdown.index(GENERATED_END)
    stale_block = markdown[:begin] + GENERATED_BEGIN + "\nstale\n" + markdown[end:]
    no_markers = markdown.replace(GENERATED_BEGIN, "").replace(GENERATED_END, "")

    # Act
    stale_rules = {item.rule_id for item in _findings(plan, stale_block)}
    marker_rules = {item.rule_id for item in _findings(plan, no_markers)}
    absent_rules = [item.rule_id for item in _findings(plan, None)]

    # Assert
    assert "plan_markdown_generated_block_drift" in stale_rules
    assert "plan_markdown_generated_block_missing" in marker_rules
    assert absent_rules == ["plan_markdown_missing"]
    assert render_generated_markdown_v1(plan) in markdown


def test_semantic_anchor_drift_from_closure_ledger_is_a_finding() -> None:
    # Arrange
    plan = _plan()
    plan["semantic_anchors"]["hyperdeflation"] = "A fixed 10% initial supply floor applies."

    # Act / Assert
    assert _rules(plan) == ["semantic_anchor_drift"]


@pytest.mark.parametrize(
    ("case", "expected_evidence"),
    [
        ("missing", "missing=hyperdeflation"),
        ("extra_null", "extra=unexpected_null_anchor"),
        ("extra_non_null", "extra=unexpected_non_null_anchor"),
    ],
)
def test_semantic_anchor_key_set_is_exact_before_value_comparison(
    case: str, expected_evidence: str
) -> None:
    # Arrange: a missing key and either form of extra key are distinct shape
    # drift, including the null value that ``mapping.get`` used to conflate
    # with a missing key.
    plan = _plan()
    if case == "missing":
        del plan["semantic_anchors"]["hyperdeflation"]
    elif case == "extra_null":
        plan["semantic_anchors"]["unexpected_null_anchor"] = None
    else:
        plan["semantic_anchors"]["unexpected_non_null_anchor"] = "unexpected"

    # Act
    findings = _findings(plan, _markdown())
    anchor_findings = [
        item for item in findings if item.rule_id == "semantic_anchor_drift"
    ]

    # Assert: exact key-set rejection happens before any value comparison.
    assert len(anchor_findings) == 1
    assert anchor_findings[0].evidence == expected_evidence


def test_subject_base_commit_must_exist_in_lineage_and_snapshot_must_match() -> None:
    # Arrange
    unknown = _plan()
    unknown["subject"]["base_commit"] = "0123456789abcdef0123456789abcdef01234567"
    drifted_digest = _plan()
    drifted_digest["subject"]["source_snapshot_sha256"] = "f" * 64
    drifted_count = _plan()
    drifted_count["subject"]["source_snapshot_file_count"] += 1
    misrecorded = _plan()
    misrecorded["subject"]["scoped_worktree_clean"] = False

    # Act
    snapshot, snapshot_findings = source_snapshot_v1(ROOT)

    # Assert: digest mutants also drift the rendered header, so both findings appear.
    assert "subject_commit_unknown" in _rules(unknown)
    assert _rules(drifted_digest) == ["plan_markdown_generated_block_drift", "source_snapshot_drift"]
    assert _rules(drifted_count) == ["plan_markdown_generated_block_drift", "source_snapshot_drift"]
    assert _rules(misrecorded) == ["scoped_worktree_clean_misrecorded"]
    assert snapshot_findings == [] and snapshot is not None
    assert (snapshot.sha256, snapshot.entry_count) == (
        _plan()["subject"]["source_snapshot_sha256"],
        _plan()["subject"]["source_snapshot_file_count"],
    )
    assert scoped_worktree_dirty_paths_v1(ROOT, CleanlinessScopeV1.FULL) == []


def _mutated_artifact(relative: Path) -> tuple[Path, bytes]:
    path = ROOT / relative
    original = path.read_bytes()
    path.write_bytes(original + b"\n")
    return path, original


@pytest.mark.parametrize("artifact", [PLAN_JSON_PATH, PLAN_MARKDOWN_PATH], ids=["json", "markdown"])
def test_dirty_plan_artifact_fails_ordinary_check_and_execute_but_not_regeneration_scope(artifact: Path) -> None:
    # Arrange: exactly one tracked plan artifact differs from the committed subject (other dirt, if any, is left as found).
    dirty_before = scoped_worktree_dirty_paths_v1(ROOT, CleanlinessScopeV1.FULL)
    assert dirty_before is not None and artifact.as_posix() not in dirty_before
    path, original = _mutated_artifact(artifact)
    try:
        # Act
        structural = check_whole_program_plan_v1(ROOT)
        executed = check_whole_program_plan_v1(ROOT, mode=PlanCheckModeV1.EXECUTE)
        direct_execute = execute_live_gates_v1(_plan(), ROOT)
        regeneration_rules = {item.rule_id for item in validate_plan_v1(_plan(), root=ROOT, markdown=_markdown(), profile=POST_REGENERATION_PROFILE_V1)}
        dirty_full = scoped_worktree_dirty_paths_v1(ROOT, CleanlinessScopeV1.FULL)
        dirty_regeneration = scoped_worktree_dirty_paths_v1(ROOT, CleanlinessScopeV1.REGENERATION)
    finally:
        path.write_bytes(original)

    # Assert: ordinary check and execution refuse; only the regeneration phase tolerates the artifact.
    assert structural["ok"] is False and structural["cleanliness_scope"] == "full"
    structural_findings = structural["findings"]
    assert isinstance(structural_findings, list)
    assert any(f["rule_id"] == "scoped_worktree_dirty" and f["evidence"] == artifact.as_posix() for f in structural_findings)
    assert executed["ok"] is False and executed["executed_live_gates"] == 0
    direct_rules = [item.rule_id for item in direct_execute]
    assert "scoped_worktree_dirty" in direct_rules and not any(rule in EXECUTION_EVIDENCE_RULES for rule in direct_rules)
    assert "scoped_worktree_dirty" not in regeneration_rules
    assert dirty_full is not None and dirty_regeneration is not None
    assert artifact.as_posix() in dirty_full and artifact.as_posix() not in dirty_regeneration
    assert sorted(set(dirty_full) - {artifact.as_posix()}) == dirty_before and dirty_regeneration == dirty_before
    assert scoped_worktree_dirty_paths_v1(ROOT, CleanlinessScopeV1.FULL) == dirty_before


@pytest.mark.parametrize("artifact", [PLAN_JSON_PATH, PLAN_MARKDOWN_PATH], ids=["json", "markdown"])
def test_plan_artifact_changed_during_execution_refuses_the_whole_observation_set(
    artifact: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: all observers would match the recorded result, but the first one
    # leaves a tracked plan artifact dirty after ordinary validation completed.
    path = ROOT / artifact
    original = path.read_bytes()
    recorded = {gate["gate_id"]: gate for gate in _plan()["live_gates"]}
    calls: list[str] = []
    baseline_dirty = scoped_worktree_dirty_paths_v1(
        ROOT, CleanlinessScopeV1.FULL
    )
    assert baseline_dirty is not None and artifact.as_posix() not in baseline_dirty
    original_status = checker_module.scoped_worktree_dirty_paths_v1

    def status_without_development_dirt(
        root: object, scope: CleanlinessScopeV1
    ) -> list[str] | None:
        observed = original_status(root, scope)
        if observed is None:
            return None
        return sorted(set(observed) - set(baseline_dirty))

    def mutate_then_match(spec: Any, _root: object, **_kwargs: object) -> LiveGateObservationV1:
        calls.append(spec.gate_id)
        if len(calls) == 1:
            path.write_bytes(original + b"\n")
        row = recorded[spec.gate_id]
        return LiveGateObservationV1(
            row["exit_code"], copy.deepcopy(row["observed"]), ""
        )

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", mutate_then_match)
    monkeypatch.setattr(
        checker_module,
        "scoped_worktree_dirty_paths_v1",
        status_without_development_dirt,
    )
    try:
        # Act
        report = check_whole_program_plan_v1(ROOT, mode=PlanCheckModeV1.EXECUTE)
    finally:
        path.write_bytes(original)

    # Assert: the first observation is refused and no later observer runs.
    findings = report["findings"]
    assert report["ok"] is False and report["executed_live_gates"] == 1
    assert calls == [sorted(LIVE_GATE_REGISTRY)[0]]
    assert isinstance(findings, list)
    assert [item["rule_id"] for item in findings] == [
        "live_gate_effect_worktree_drift"
    ]
    assert artifact.as_posix() in findings[0]["evidence"]
    assert (
        scoped_worktree_dirty_paths_v1(ROOT, CleanlinessScopeV1.FULL)
        == baseline_dirty
    )


def test_plan_only_head_substitution_after_snapshot_is_refused_before_observation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: the source digest excludes both plan artifacts. Mallory commits a
    # malformed plan-only replacement after the planning snapshot was read but
    # before the old implementation captured its expected HEAD.
    markers = tmp_path / "markers"
    markers.mkdir()
    root, rows = _fake_gate_root(tmp_path, markers)
    for relative in (PLAN_JSON_PATH, PLAN_MARKDOWN_PATH):
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(f"original {relative.name}\n", encoding="utf-8")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "tracked plan artifacts")
    owner = ConfinedRootV1.bind(root)
    gate = next(row for row in rows if row["gate_id"] == FAST_GATE_ID)
    real_snapshot = checker_module.source_snapshot_v1
    committed = False
    calls: list[str] = []

    def commit_after_snapshot(root_view: object) -> Any:
        nonlocal committed
        snapshot = real_snapshot(root_view)
        if not committed:
            (root / PLAN_JSON_PATH).write_text(
                '{"schema":"attacker-plan-not-validated"}\n', encoding="utf-8"
            )
            _git(root, "add", PLAN_JSON_PATH.as_posix())
            _git(root, "commit", "-q", "-m", "plan-only substitution")
            committed = True
        return snapshot

    def matching_observer(spec: Any, _root: object, **_kwargs: object) -> LiveGateObservationV1:
        calls.append(spec.gate_id)
        return LiveGateObservationV1(
            int(gate["exit_code"]), copy.deepcopy(gate["observed"]), ""
        )

    monkeypatch.setattr(checker_module, "source_snapshot_v1", commit_after_snapshot)
    monkeypatch.setattr(checker_module, "observe_live_gate_v1", matching_observer)

    # Act
    try:
        findings = compare_live_gate_execution_v1(gate, owner)
    finally:
        owner.close()

    # Assert: the persistent clean HEAD change is detected before the observer.
    assert committed and _git(root, "status", "--porcelain=v2", "--untracked-files=all") == ""
    assert [item.rule_id for item in findings] == ["live_gate_effect_head_drift"]
    assert calls == []


def test_full_execute_binds_head_before_plan_read_and_refuses_plan_only_commit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: clone a clean complete subject. The hook returns an already
    # validated in-memory plan, then commits malformed plan-only bytes before
    # effect planning. The full entrypoint must retain its pre-read HEAD.
    root = tmp_path / "subject"
    subprocess.run(
        ["/usr/bin/git", "clone", "-q", "--no-hardlinks", str(ROOT), str(root)],
        check=True,
        capture_output=True,
        text=True,
    )
    real_structural_report = checker_module._structural_report
    real_bind_context = checker_module._bind_execution_context_v1
    calls: list[str] = []
    events: list[str] = []
    committed = False

    def record_context_bind(
        root_view: ConfinedRootV1, *, subject: str
    ) -> tuple[Any, list[Any]]:
        events.append("context_bound")
        return real_bind_context(root_view, subject=subject)

    def validate_then_commit(
        root_view: ConfinedRootV1,
        profile: PlanValidationProfileV1,
        artifacts: Any = None,
    ) -> tuple[dict[str, Any], list[Any]]:
        nonlocal committed
        events.append("first_plan_read")
        plan, findings = real_structural_report(root_view, profile, artifacts)
        assert findings == []
        (root / PLAN_JSON_PATH).write_text(
            '{"schema":"attacker-plan-not-validated"}\n', encoding="utf-8"
        )
        _git(root, "add", PLAN_JSON_PATH.as_posix())
        _git(root, "commit", "-q", "-m", "plan-only substitution")
        committed = True
        return dict(plan), findings

    def forbidden_observer(*_args: object, **_kwargs: object) -> Any:
        calls.append("observer")
        raise AssertionError("plan-only HEAD drift must refuse before observation")

    monkeypatch.setattr(
        checker_module, "_bind_execution_context_v1", record_context_bind
    )
    monkeypatch.setattr(checker_module, "_structural_report", validate_then_commit)
    monkeypatch.setattr(checker_module, "_observe_anchored", forbidden_observer)

    # Act
    report = check_whole_program_plan_v1(root, mode=PlanCheckModeV1.EXECUTE)

    # Assert: the replacement commit is clean, but differs from the context
    # captured before either plan artifact was read.
    assert committed
    assert events[:2] == ["context_bound", "first_plan_read"]
    assert _git(root, "status", "--porcelain=v2", "--untracked-files=all") == ""
    assert report["ok"] is False and report["executed_live_gates"] == 0
    assert calls == []
    assert [item["rule_id"] for item in report["findings"]] == [
        "live_gate_effect_head_drift"
    ]


def test_transient_plan_artifact_rewrite_restore_refuses_before_observation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: Mallory substitutes mutually consistent JSON and Markdown only
    # while each artifact is read, then restores both before every later
    # HEAD/status check. The exact committed blobs must still own semantics.
    root = tmp_path / "subject"
    subprocess.run(
        ["/usr/bin/git", "clone", "-q", "--no-hardlinks", str(ROOT), str(root)],
        check=True,
        capture_output=True,
        text=True,
    )
    original_json = (root / PLAN_JSON_PATH).read_bytes()
    original_markdown = (root / PLAN_MARKDOWN_PATH).read_bytes()
    hostile_plan = copy.deepcopy(dict(load_plan_v1(root)))
    next(
        row for row in hostile_plan["vm_gate_status"] if row["gate_id"] == "VM-04"
    )["status"] = "PARTIAL"
    hostile_json = canonical_plan_json_v1(hostile_plan).encode("utf-8")
    split = checker_module._split_markdown(original_markdown.decode("utf-8"))
    assert split is not None
    hostile_markdown = (
        split[0] + render_generated_markdown_v1(hostile_plan) + split[2]
    ).encode("utf-8")
    real_open_file = checker_module.AnchoredDirectoryV1.open_file
    calls: list[str] = []
    opened: list[str] = []

    hostile_by_path = {
        PLAN_JSON_PATH.as_posix(): hostile_json,
        PLAN_MARKDOWN_PATH.as_posix(): hostile_markdown,
    }
    original_by_path = {
        PLAN_JSON_PATH.as_posix(): original_json,
        PLAN_MARKDOWN_PATH.as_posix(): original_markdown,
    }

    def transient_open_file(root_view: object, relative: str) -> Any:
        hostile = hostile_by_path.get(relative)
        if hostile is None:
            return real_open_file(root_view, relative)
        opened.append(relative)
        (root / relative).write_bytes(hostile)
        try:
            return real_open_file(root_view, relative)
        finally:
            (root / relative).write_bytes(original_by_path[relative])

    recorded = {gate["gate_id"]: gate for gate in hostile_plan["live_gates"]}

    def counting_observer(spec: Any, _root: object, **_kwargs: object) -> Any:
        calls.append(spec.gate_id)
        row = recorded[spec.gate_id]
        return LiveGateObservationV1(
            int(row["exit_code"]), copy.deepcopy(row["observed"]), ""
        )

    monkeypatch.setattr(
        checker_module.AnchoredDirectoryV1, "open_file", transient_open_file
    )
    monkeypatch.setattr(checker_module, "observe_live_gate_v1", counting_observer)
    fd_count_before = len(os.listdir("/proc/self/fd"))
    try:
        # Act
        report = check_whole_program_plan_v1(root, mode=PlanCheckModeV1.EXECUTE)
    finally:
        (root / PLAN_JSON_PATH).write_bytes(original_json)
        (root / PLAN_MARKDOWN_PATH).write_bytes(original_markdown)

    # Assert: both the restored source descriptor and the exact HEAD blob reject
    # the transient artifact snapshots before any observer call.
    findings = report["findings"]
    assert isinstance(findings, list)
    assert report["ok"] is False and report["executed_live_gates"] == 0
    assert calls == []
    assert opened == [PLAN_JSON_PATH.as_posix(), PLAN_MARKDOWN_PATH.as_posix()]
    assert len(os.listdir("/proc/self/fd")) == fd_count_before
    assert {item["rule_id"] for item in findings} == {
        "plan_artifact_head_blob_mismatch",
        "plan_artifact_source_drift",
    }
    assert {item["subject"] for item in findings} == {
        PLAN_JSON_PATH.as_posix(),
        PLAN_MARKDOWN_PATH.as_posix(),
    }
    assert scoped_worktree_dirty_paths_v1(root, CleanlinessScopeV1.FULL) == []


def test_validation_profiles_are_closed_and_cleanliness_is_never_caller_selected() -> None:
    # Act / Assert: only the three named kinds exist and scope derives from the kind.
    with pytest.raises(ValueError, match="closed profiles"):
        PlanValidationProfileV1("ordinary")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="re-pin"):
        PlanValidationProfileV1(PlanValidationKindV1.ORDINARY, frozenset({"P1-T01"}))
    with pytest.raises(ValueError, match="re-pin"):
        PlanValidationProfileV1(PlanValidationKindV1.POST_REGENERATION, frozenset({"P1-T01"}))
    with pytest.raises(ValueError, match="frozenset"):
        PlanValidationProfileV1(PlanValidationKindV1.PRE_REGENERATION, {"P1-T01"})  # type: ignore[arg-type]
    assert ORDINARY_VALIDATION_PROFILE_V1.cleanliness is CleanlinessScopeV1.FULL and ORDINARY_VALIDATION_PROFILE_V1.compares_regenerable
    assert POST_REGENERATION_PROFILE_V1.cleanliness is CleanlinessScopeV1.REGENERATION and POST_REGENERATION_PROFILE_V1.compares_regenerable
    pre = PlanValidationProfileV1.pre_regeneration(["P1-T01"])
    assert pre.cleanliness is CleanlinessScopeV1.REGENERATION and not pre.compares_regenerable and pre.repin_tasks == frozenset({"P1-T01"})
    assert {kind.value for kind in PlanValidationKindV1} == {"ordinary", "pre_regeneration", "post_regeneration"}
    assert "cleanliness" not in inspect.signature(check_whole_program_plan_v1).parameters
    assert "cleanliness" not in inspect.signature(validate_plan_v1).parameters
    assert main(["--root", str(ROOT), "--render", "--execute"]) == 2


class _ForgedValidationProfile:
    """Duck-typed profile used to prove the public validator requires its exact value type."""

    kind = PlanValidationKindV1.ORDINARY
    repin_tasks = frozenset()
    cleanliness = CleanlinessScopeV1.FULL
    compares_regenerable = False


@pytest.mark.parametrize("mode", ("execute", True, object()), ids=("string", "bool", "object"))
def test_public_check_rejects_nonenum_mode_before_any_observer(
    mode: object, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange: every observer raises if wrong-mode input reaches execution.
    observer_calls: list[object] = []

    def forbidden_observer(*args: object, **_kwargs: object) -> object:
        observer_calls.append(args)
        raise AssertionError("an invalid check mode must refuse before any observer")

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", forbidden_observer)

    # Act
    report = check_whole_program_plan_v1(_clone_complete_subject(tmp_path), mode=mode)  # type: ignore[arg-type]

    # Assert: a string, Boolean alias, and arbitrary object are not structural mode fallbacks.
    assert report["ok"] is False
    assert report["executed_live_gates"] == 0
    assert observer_calls == []
    assert [finding["rule_id"] for finding in report["findings"]] == [
        "plan_check_mode_invalid"
    ]
    assert report["requested_check_mode"] == "invalid"
    assert report["accepted_check_mode"] == "none"
    assert report["authority"] == {
        "claim_authority": "NONE",
        "production_authority": "NONE",
        "production_ready": False,
        "release_ready": False,
    }


def test_public_profile_boundaries_refuse_a_duck_typed_profile_and_normalize_the_report(
    tmp_path: Path,
) -> None:
    # Arrange
    forged = _ForgedValidationProfile()
    root = _clone_complete_subject(tmp_path)
    plan = dict(load_plan_v1(root))

    # Act
    validation_findings = validate_plan_v1(
        plan, root=root, markdown=(root / PLAN_MARKDOWN_PATH).read_text(encoding="utf-8"), profile=forged  # type: ignore[arg-type]
    )
    report = plan_report_v1(
        plan, [], executed=11, profile=forged, mode="execute"  # type: ignore[arg-type]
    )

    # Assert: no public boundary may accept a profile merely because it exposes matching attributes.
    assert [finding.rule_id for finding in validation_findings] == [
        "validation_profile_invalid"
    ]
    assert report["ok"] is False and report["executed_live_gates"] == 0
    assert {finding["rule_id"] for finding in report["findings"]} == {
        "plan_check_mode_invalid",
        "validation_profile_invalid",
    }
    assert report["requested_check_mode"] == "invalid"
    assert report["accepted_check_mode"] == "none"
    assert report["authority"]["production_authority"] == "NONE"


def test_closed_report_refuses_an_unaccepted_mode_without_observers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: a direct public constructor call must not turn an explicit refusal into a green report.
    observer_calls: list[object] = []

    def forbidden_observer(*args: object, **_kwargs: object) -> object:
        observer_calls.append(args)
        raise AssertionError("closed report construction must never observe live gates")

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", forbidden_observer)

    # Act
    report = plan_report_v1(
        {},
        [],
        executed=0,
        profile=ORDINARY_VALIDATION_PROFILE_V1,
        mode=PlanCheckModeV1.STRUCTURAL,
        mode_accepted=False,
    )

    # Assert: the refused mode is an explicit typed failure, with no claimed execution or authority.
    assert report["ok"] is False
    assert report["accepted_check_mode"] == "none"
    assert report["executed_live_gates"] == 0
    assert [finding["rule_id"] for finding in report["findings"]] == [
        "report_mode_not_accepted"
    ]
    assert observer_calls == []
    assert report["authority"] == {
        "claim_authority": "NONE",
        "production_authority": "NONE",
        "production_ready": False,
        "release_ready": False,
    }


@pytest.mark.parametrize(
    "executed",
    (len(LIVE_GATE_REGISTRY) - 1, len(LIVE_GATE_REGISTRY) + 1),
    ids=("too_few", "too_many"),
)
def test_closed_report_refuses_accepted_execute_with_nonexact_observer_count(
    executed: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: a direct report constructor has no observation capability of its own.
    observer_calls: list[object] = []

    def forbidden_observer(*args: object, **_kwargs: object) -> object:
        observer_calls.append(args)
        raise AssertionError("closed report construction must never observe live gates")

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", forbidden_observer)

    # Act
    report = plan_report_v1(
        {},
        [],
        executed=executed,
        profile=ORDINARY_VALIDATION_PROFILE_V1,
        mode=PlanCheckModeV1.EXECUTE,
    )

    # Assert: an otherwise green execute report must bind the exact registry cardinality.
    assert report["ok"] is False
    assert report["accepted_check_mode"] == PlanCheckModeV1.EXECUTE.value
    assert report["executed_live_gates"] == 0
    assert [finding["rule_id"] for finding in report["findings"]] == [
        "report_execute_observer_count_invalid"
    ]
    assert observer_calls == []
    assert report["authority"]["production_authority"] == "NONE"


class _FindingStringSubclass(str):
    pass


class _FindingSuppressingList(list[object]):
    def __iter__(self) -> Iterator[object]:
        return iter(())


class _GapEqualString(str):
    def __new__(cls) -> _GapEqualString:
        return str.__new__(cls, "EVIL")

    def __hash__(self) -> int:
        return hash("GAP")

    def __eq__(self, other: object) -> bool:
        return other == "GAP"


class _CallbackGateMapping(Mapping[str, object]):
    def __init__(self, calls: list[str]) -> None:
        self.calls = calls

    def __getitem__(self, key: str) -> object:
        self.calls.append(f"getitem:{key}")
        raise KeyError(key)

    def __iter__(self) -> Iterator[str]:
        self.calls.append("iter")
        return iter(())

    def __len__(self) -> int:
        self.calls.append("len")
        return 0


class _ExplodingGateMapping(Mapping[str, object]):
    def __getitem__(self, key: str) -> object:
        raise RuntimeError(f"hostile getitem: {key}")

    def __iter__(self) -> Iterator[str]:
        raise RuntimeError("hostile iterator")

    def __len__(self) -> int:
        raise RuntimeError("hostile length")


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("rule_id", object()),
        ("subject", []),
        ("evidence", True),
        ("rule_id", _FindingStringSubclass("rule")),
    ],
)
def test_plan_finding_constructor_requires_exact_string_fields(
    field: str, value: object
) -> None:
    values: dict[str, object] = {
        "rule_id": "rule",
        "subject": "subject",
        "evidence": "evidence",
    }
    values[field] = value

    with pytest.raises(TypeError, match=f"PlanFinding.{field}"):
        checker_module.PlanFinding(**values)  # type: ignore[arg-type]


def test_closed_report_normalizes_a_same_process_forged_finding() -> None:
    forged = object.__new__(checker_module.PlanFinding)
    object.__setattr__(forged, "rule_id", object())
    object.__setattr__(forged, "subject", "subject")
    object.__setattr__(forged, "evidence", "evidence")

    report = plan_report_v1(
        {},
        [forged],
        executed=0,
        profile=ORDINARY_VALIDATION_PROFILE_V1,
    )

    assert report["ok"] is False
    assert [finding["rule_id"] for finding in report["findings"]] == [
        "report_findings_invalid"
    ]
    json.dumps(report)


def test_public_report_cannot_claim_success_without_checker_validation() -> None:
    report = plan_report_v1(
        {}, [], executed=0, profile=ORDINARY_VALIDATION_PROFILE_V1
    )

    assert report["ok"] is False
    assert [finding["rule_id"] for finding in report["findings"]] == [
        "report_validation_missing"
    ]


def test_public_report_refuses_a_hostile_findings_container() -> None:
    findings = _FindingSuppressingList(
        [checker_module.PlanFinding("injected", "plan", "must remain visible")]
    )

    report = plan_report_v1(
        {}, findings, executed=0, profile=ORDINARY_VALIDATION_PROFILE_V1  # type: ignore[arg-type]
    )

    assert report["ok"] is False
    assert [finding["rule_id"] for finding in report["findings"]] == [
        "report_findings_invalid"
    ]


def test_plan_validation_refuses_hostile_recursive_string_subclasses() -> None:
    plan = _plan()
    row = next(item for item in plan["vm_gate_status"] if item["status"] == "GAP")
    row["status"] = _GapEqualString()

    findings = validate_plan_v1(plan, root=ROOT, markdown=_markdown())

    assert [finding.rule_id for finding in findings] == ["plan_value_not_owned"]
    assert findings[0].subject.endswith(".status")


def test_private_donor_validator_rejects_integer_beyond_decode_bound() -> None:
    """The in-process donor boundary enforces the file decoder's integer bound."""

    snapshot = json.loads(
        (ROOT / checker_module.DONOR_PROVENANCE_PATH).read_text(encoding="utf-8")
    )
    snapshot["captured_at"] = 10**5000

    with ConfinedRootV1.bind(ROOT) as bound:
        findings = checker_module._validate_donor_provenance_content_v1(
            snapshot, bound
        )

    assert [finding.rule_id for finding in findings] == [
        "donor_snapshot_value_not_owned"
    ]


def test_public_plan_validator_rejects_integer_beyond_decode_bound() -> None:
    """The public plan API returns a typed finding for an oversized exact integer."""

    plan = _plan()
    plan["vm_gate_status"][0]["gate_id"] = 10**5000

    findings = validate_plan_v1(plan, root=ROOT, markdown=None)

    assert [finding.rule_id for finding in findings] == ["plan_value_not_owned"]
    assert findings[0].subject.endswith(".gate_id")


@pytest.mark.parametrize(
    ("value_offset", "sign", "ownership_rejected"),
    [
        (-1, 1, False),
        (0, 1, True),
        (-1, -1, False),
        (0, -1, True),
    ],
)
def test_public_integer_ownership_matches_decoder_digit_bva(
    value_offset: int, sign: int, ownership_rejected: bool
) -> None:
    """The in-process API and byte decoder agree at both signed neighbors."""

    limit = 10 ** checker_module.PLAN_JSON_LIMITS_V1.max_integer_digits
    plan = _plan()
    plan["vm_gate_status"][0]["gate_id"] = sign * (limit + value_offset)

    findings = validate_plan_v1(plan, root=ROOT, markdown=None)
    rules = {finding.rule_id for finding in findings}

    assert ("plan_value_not_owned" in rules) is ownership_rejected


@pytest.mark.parametrize(
    "hostile_value",
    [
        pytest.param(
            "x" * (checker_module.PLAN_JSON_LIMITS_V1.max_bytes + 1),
            id="aggregate-byte-limit-next",
        ),
        pytest.param("\ud800", id="lone-surrogate"),
    ],
)
def test_public_string_ownership_rejects_before_root_binding(
    hostile_value: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Oversized or non-UTF-8 strings stay outside the owned plan boundary."""

    plan = _plan()
    plan["vm_gate_status"][0]["gate_id"] = hostile_value
    calls: list[object] = []

    def refuse_bind(
        cls: type[ConfinedRootV1], root: object
    ) -> ConfinedRootV1:
        calls.append((cls, root))
        raise checker_module.RootUnavailable("root bind must not run")

    monkeypatch.setattr(ConfinedRootV1, "bind", classmethod(refuse_bind))

    findings = validate_plan_v1(plan, root=ROOT, markdown=None)

    assert calls == []
    assert [finding.rule_id for finding in findings] == ["plan_value_not_owned"]


@pytest.mark.parametrize("invalid_kind", ("task", "evidence", "live-gate"))
def test_public_multiplicity_preflight_precedes_root_binding(
    invalid_kind: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Every closed-set multiplicity defect rejects before filesystem effects."""

    plan = copy.deepcopy(_plan())
    if invalid_kind == "task":
        plan["tasks"] = [
            copy.deepcopy(plan["tasks"][0]),
            copy.deepcopy(plan["tasks"][0]),
        ]
        expected_rule = "task_id_duplicate"
    elif invalid_kind == "evidence":
        evidence = copy.deepcopy(plan["tasks"][0]["evidence"][0])
        plan["tasks"][0]["evidence"] = [
            copy.deepcopy(evidence),
            copy.deepcopy(evidence),
        ]
        expected_rule = "task_evidence_duplicate"
    else:
        plan["live_gates"][-1] = copy.deepcopy(plan["live_gates"][0])
        expected_rule = "live_gate_registry_set_mismatch"
    calls: list[object] = []

    def refuse_bind(
        cls: type[ConfinedRootV1], root: object
    ) -> ConfinedRootV1:
        calls.append((cls, root))
        raise checker_module.RootUnavailable("root bind must not run")

    monkeypatch.setattr(ConfinedRootV1, "bind", classmethod(refuse_bind))

    findings = validate_plan_v1(plan, root=ROOT, markdown=None)

    assert calls == []
    assert expected_rule in {finding.rule_id for finding in findings}


def test_direct_gate_multiplicity_preflight_precedes_context_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A duplicate full gate set cannot trigger Git or artifact context binding."""

    gates = copy.deepcopy(_plan()["live_gates"])
    gates.append(copy.deepcopy(gates[0]))
    calls: list[str] = []

    def refuse_context(
        *_args: object, **_kwargs: object
    ) -> tuple[None, list[checker_module.PlanFinding]]:
        calls.append("context")
        return None, [
            checker_module.PlanFinding(
                "context_binding_reached",
                "live_gates",
                "pure preflight must run first",
            )
        ]

    monkeypatch.setattr(
        checker_module, "_bind_execution_context_v1", refuse_context
    )
    with ConfinedRootV1.bind(ROOT) as bound:
        effects, findings = checker_module.plan_live_gate_effects_v1(
            gates, bound
        )

    assert effects == ()
    assert calls == []
    assert "live_gate_registry_set_mismatch" in {
        finding.rule_id for finding in findings
    }


def test_escaped_string_amplification_rejects_before_root_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Public ownership and the bounded file decoder share one encoded-byte cap."""

    plan = _plan()
    plan["tasks"][0]["notes"] = "\x00" * 700_000
    assert (
        len(canonical_plan_json_v1(plan).encode("utf-8"))
        > checker_module.PLAN_JSON_LIMITS_V1.max_bytes
    )
    calls: list[object] = []

    def refuse_bind(
        cls: type[ConfinedRootV1], root: object
    ) -> ConfinedRootV1:
        calls.append((cls, root))
        raise checker_module.RootUnavailable("encoded byte refusal must be pure")

    monkeypatch.setattr(ConfinedRootV1, "bind", classmethod(refuse_bind))

    findings = validate_plan_v1(plan, root=ROOT, markdown=None)

    assert calls == []
    assert [finding.rule_id for finding in findings] == ["plan_value_not_owned"]
    assert "canonical plan bytes" in findings[0].evidence


def test_owned_plan_breaks_aliases_and_rejects_cycles_within_bounds() -> None:
    """The owned graph is a bounded JSON tree even for aliased Python input."""

    aliased = _plan()
    shared: list[object] = ["λ", "🧠"]
    aliased["nonclaims"] = [shared, shared]
    owned, alias_findings = checker_module._owned_plan_v1(aliased)
    cyclic = _plan()
    cycle: list[object] = []
    cycle.append(cycle)
    cyclic["nonclaims"] = cycle
    _rejected, cycle_findings = checker_module._owned_plan_v1(cyclic)

    assert alias_findings == [] and owned is not None
    owned_nonclaims = owned["nonclaims"]
    assert type(owned_nonclaims) is list
    assert owned_nonclaims[0] == owned_nonclaims[1]
    assert owned_nonclaims[0] is not owned_nonclaims[1]
    assert [finding.rule_id for finding in cycle_findings] == [
        "plan_value_not_owned"
    ]


@pytest.mark.parametrize("hostile_kind", ("callback", "exploding"))
def test_direct_gate_preflight_owns_rows_without_callbacks(
    hostile_kind: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Arbitrary Mapping methods cannot run before typed direct-row refusal."""

    calls: list[str] = []
    gate: object = (
        _CallbackGateMapping(calls)
        if hostile_kind == "callback"
        else _ExplodingGateMapping()
    )
    context_calls: list[str] = []

    def refuse_context(*_args: object, **_kwargs: object) -> object:
        context_calls.append("context")
        raise AssertionError("hostile direct rows must not bind context")

    monkeypatch.setattr(checker_module, "_bind_execution_context_v1", refuse_context)
    with ConfinedRootV1.bind(ROOT) as bound:
        effects, findings = plan_live_gate_effects_v1([gate], bound)

    assert effects == ()
    assert calls == []
    assert context_calls == []
    assert [finding.rule_id for finding in findings] == [
        "live_gate_field_set_not_closed"
    ]


@pytest.mark.parametrize("operation", ("execute", "write", "refresh"))
def test_all_public_plan_operations_preflight_before_root_binding(
    operation: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Malformed caller plans stay in the pure phase for every public operation."""

    plan = _plan()
    plan["live_gates"].append(copy.deepcopy(plan["live_gates"][0]))
    root_calls: list[object] = []

    def refuse_bind(
        cls: type[ConfinedRootV1], root: object
    ) -> ConfinedRootV1:
        root_calls.append((cls, root))
        raise checker_module.RootUnavailable("invalid caller plan must remain pure")

    monkeypatch.setattr(ConfinedRootV1, "bind", classmethod(refuse_bind))
    if operation == "execute":
        findings = execute_live_gates_v1(plan, ROOT)
    elif operation == "write":
        findings = checker_module.write_markdown_v1(ROOT, plan)
    else:
        _refreshed, findings = refresh_plan_v1(
            plan,
            root=ROOT,
            observed_at="2026-08-26",
            repin_tasks=(),
        )

    assert root_calls == []
    assert "live_gate_registry_set_mismatch" in {
        finding.rule_id for finding in findings
    }


def _synthetic_repository(tmp_path: Path) -> tuple[Path, str]:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    (repo / "a.txt").write_text("base\n", encoding="utf-8")
    _git(repo, "add", "a.txt")
    _git(repo, "commit", "-q", "-m", "base")
    return repo, _git(repo, "rev-parse", "HEAD")


def test_commit_evidence_must_be_in_the_subject_lineage(tmp_path: Path) -> None:
    repo, base = _synthetic_repository(tmp_path)
    _git(repo, "checkout", "-q", "-b", "side")
    (repo / "side.txt").write_text("side\n", encoding="utf-8")
    _git(repo, "add", "side.txt")
    _git(repo, "commit", "-q", "-m", "side")
    side = _git(repo, "rev-parse", "HEAD")
    _git(repo, "checkout", "-q", "main")

    with ConfinedRootV1.bind(repo) as bound:
        accepted = checker_module._validate_evidence_item(
            {"kind": "commit", "reference": base, "sha256": None},
            label="task.evidence[0]",
            context=checker_module.EvidenceContextV1(
                closed=True, compare_digests=True
            ),
            root=bound,
        )
        refused = checker_module._validate_evidence_item(
            {"kind": "commit", "reference": side, "sha256": None},
            label="task.evidence[1]",
            context=checker_module.EvidenceContextV1(
                closed=True, compare_digests=True
            ),
            root=bound,
        )

    assert accepted == []
    assert [finding.rule_id for finding in refused] == [
        "evidence_commit_outside_subject_lineage"
    ]


def test_transport_faithful_clone_replays_without_out_of_line_donor_objects(
    tmp_path: Path,
) -> None:
    root = _clone_transport_subject(tmp_path)

    unavailable = [
        commit
        for commit in (
            "d5198b89480eeb36dd56ad55e8b77c4e38c98f45",
            "c2e80678415543df43dba0f4678fae9931a1bb91",
        )
        if subprocess.run(
            ["/usr/bin/git", "cat-file", "-e", f"{commit}^{{commit}}"],
            cwd=root,
            env=GIT_ENV,
            check=False,
            capture_output=True,
        ).returncode
        != 0
    ]
    report = check_whole_program_plan_v1(root)

    assert "d5198b89480eeb36dd56ad55e8b77c4e38c98f45" in unavailable
    assert report["ok"] is True, report["findings"]
    assert report["authority"]["production_authority"] == "NONE"


def test_donor_snapshot_lineage_labels_are_equivalent_to_raw_git_ancestry() -> None:
    with ConfinedRootV1.bind(ROOT) as bound:
        snapshot = checker_module._read_bounded_json_file(
            bound,
            checker_module.DONOR_PROVENANCE_PATH,
            name="donor provenance snapshot",
        )
        accepted = checker_module._validate_donor_provenance_content_v1(snapshot, bound)
        forged = copy.deepcopy(snapshot)
        donor = next(row for row in forged["donors"] if row["id"] == "M6_FCIS_REVIEWED_DONOR")
        donor["object_transport"] = "SUBJECT_LINEAGE_COMMIT"
        refused = checker_module._validate_donor_provenance_content_v1(forged, bound)
        false_metadata = copy.deepcopy(snapshot)
        false_metadata["donors"][0]["tree"] = "0" * 40
        metadata_refused = checker_module._validate_donor_provenance_content_v1(false_metadata, bound)

    assert accepted == []
    assert {finding.rule_id for finding in refused} == {
        "donor_identity_mismatch",
        "donor_transport_ancestry_mismatch",
        "donor_transport_label_invalid",
    }
    assert {finding.rule_id for finding in metadata_refused} == {
        "donor_commit_metadata_mismatch",
        "donor_identity_mismatch",
    }


def test_donor_descriptor_registry_binds_absent_metadata_and_manifest_path() -> None:
    with ConfinedRootV1.bind(ROOT) as bound:
        snapshot = checker_module._read_bounded_json_file(
            bound,
            checker_module.DONOR_PROVENANCE_PATH,
            name="donor provenance snapshot",
        )
        fabricated = copy.deepcopy(snapshot)
        donor = fabricated["donors"][0]
        donor.update(
            commit="f" * 40,
            commit_object_sha256="e" * 64,
            parents=["d" * 40],
            tree="c" * 40,
        )
        absent_refused = checker_module._validate_donor_provenance_content_v1(
            fabricated, bound
        )
        substituted = copy.deepcopy(snapshot)
        substituted["donors"][0]["preservation_manifest"] = {
            "path": "README.md",
            "sha256": hashlib.sha256((ROOT / "README.md").read_bytes()).hexdigest(),
        }
        manifest_refused = checker_module._validate_donor_provenance_content_v1(
            substituted, bound
        )

    assert {finding.rule_id for finding in absent_refused} >= {
        "donor_identity_mismatch",
        "donor_metadata_unverifiable",
    }
    assert "donor_preservation_manifest_binding_mismatch" in {
        finding.rule_id for finding in manifest_refused
    }


def test_donor_ref_and_required_nonclaims_are_checker_owned() -> None:
    with ConfinedRootV1.bind(ROOT) as bound:
        snapshot = checker_module._read_bounded_json_file(
            bound,
            checker_module.DONOR_PROVENANCE_PATH,
            name="donor provenance snapshot",
        )
        bad_ref = copy.deepcopy(snapshot)
        bad_ref["donors"][0]["source_ref_observed"] = "refs/"
        bad_nonclaims = copy.deepcopy(snapshot)
        bad_nonclaims["nonclaims"] = ["candidate-selected"]

        ref_findings = checker_module._validate_donor_provenance_content_v1(
            bad_ref, bound
        )
        nonclaim_findings = checker_module._validate_donor_provenance_content_v1(
            bad_nonclaims, bound
        )

    assert "donor_source_ref_malformed" in {
        finding.rule_id for finding in ref_findings
    }
    assert {finding.rule_id for finding in nonclaim_findings} == {
        "donor_snapshot_nonclaims_mismatch"
    }


def test_donor_ancestry_query_failure_is_not_non_lineage(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = _clone_complete_subject(tmp_path)
    target = "c2e80678415543df43dba0f4678fae9931a1bb91"
    real_git = checker_module._git

    def fail_ancestry(root: object, args: list[str]) -> tuple[int, str]:
        if args == ["merge-base", "--is-ancestor", target, "HEAD"]:
            return -1, ""
        return real_git(root, args)  # type: ignore[arg-type]

    monkeypatch.setattr(checker_module, "_git", fail_ancestry)
    with ConfinedRootV1.bind(root) as bound:
        snapshot = checker_module._read_bounded_json_file(
            bound,
            checker_module.DONOR_PROVENANCE_PATH,
            name="donor provenance snapshot",
        )
        findings = checker_module._validate_donor_provenance_content_v1(
            snapshot, bound
        )
    report = check_whole_program_plan_v1(root)

    assert "donor_ancestry_query_failed" in {
        finding.rule_id for finding in findings
    }
    assert report["ok"] is False
    assert "donor_ancestry_query_failed" in {
        finding["rule_id"] for finding in report["findings"]
    }


def test_invalid_donor_cardinality_rejects_before_git_io(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with ConfinedRootV1.bind(ROOT) as bound:
        snapshot = checker_module._read_bounded_json_file(
            bound,
            checker_module.DONOR_PROVENANCE_PATH,
            name="donor provenance snapshot",
        )
        by_id = {row["id"]: row for row in snapshot["donors"]}
        malformed = copy.deepcopy(snapshot)
        malformed["donors"] = [
            *[
                copy.deepcopy(by_id["M6_FCIS_REVIEWED_DONOR"])
                for _ in range(16)
            ],
            copy.deepcopy(by_id["ZRPF_REVIEWED_DONOR"]),
            copy.deepcopy(by_id["DIRTY_PRIMARY_CHECKOUT_DONOR"]),
        ]
        calls = {"git": 0, "git_bytes": 0}

        def unexpected_git(*_args: object, **_kwargs: object) -> tuple[int, str]:
            calls["git"] += 1
            return -1, ""

        def unexpected_git_bytes(*_args: object, **_kwargs: object) -> bytes | None:
            calls["git_bytes"] += 1
            return None

        monkeypatch.setattr(checker_module, "_git", unexpected_git)
        monkeypatch.setattr(checker_module, "_git_bytes", unexpected_git_bytes)
        findings = checker_module._validate_donor_provenance_content_v1(
            malformed, bound
        )

    assert {"donor_id_duplicate", "donor_commit_duplicate"} <= {
        finding.rule_id for finding in findings
    }
    assert calls == {"git": 0, "git_bytes": 0}


def test_donor_object_probe_failure_is_never_safe_absence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    target = "c2e80678415543df43dba0f4678fae9931a1bb91"
    real_probe = checker_module._git_commit_probe

    def fail_target(root: object, commit: str) -> object:
        if commit == target:
            return checker_module.GitObjectProbeV1(
                checker_module.GitObjectPresenceV1.QUERY_FAILED,
                "injected object database failure",
            )
        return real_probe(root, commit)  # type: ignore[arg-type]

    monkeypatch.setattr(checker_module, "_git_commit_probe", fail_target)
    with ConfinedRootV1.bind(ROOT) as bound:
        snapshot = checker_module._read_bounded_json_file(
            bound,
            checker_module.DONOR_PROVENANCE_PATH,
            name="donor provenance snapshot",
        )

        # Act
        findings = checker_module._validate_donor_provenance_content_v1(
            snapshot, bound
        )

    # Assert
    assert "donor_object_query_failed" in {
        finding.rule_id for finding in findings
    }


def test_private_donor_validator_owns_values_before_equality() -> None:
    class AlwaysEqual:
        def __eq__(self, _other: object) -> bool:
            return True

    with ConfinedRootV1.bind(ROOT) as bound:
        snapshot = checker_module._read_bounded_json_file(
            bound,
            checker_module.DONOR_PROVENANCE_PATH,
            name="donor provenance snapshot",
        )
        snapshot["donors"][2]["object_transport"] = AlwaysEqual()

        findings = checker_module._validate_donor_provenance_content_v1(
            snapshot, bound
        )

    assert {finding.rule_id for finding in findings} == {
        "donor_snapshot_value_not_owned"
    }


def test_duplicate_tasks_reject_before_evidence_observations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    plan = copy.deepcopy(_plan())
    plan["tasks"] = [copy.deepcopy(plan["tasks"][0]) for _ in range(32)]
    calls: list[str] = []
    monkeypatch.setattr(
        checker_module,
        "_git_commit_probe",
        lambda *_args, **_kwargs: calls.append("probe"),
    )
    monkeypatch.setattr(
        checker_module,
        "_git",
        lambda *_args, **_kwargs: (calls.append("git") or (-1, "")),
    )
    monkeypatch.setattr(
        checker_module,
        "read_confined_file_v1",
        lambda *_args, **_kwargs: calls.append("file"),
    )

    # Act
    findings = validate_plan_v1(plan, root=ROOT, markdown=None)

    # Assert
    assert "task_id_duplicate" in {finding.rule_id for finding in findings}
    assert calls == []


def test_duplicate_evidence_rejects_before_evidence_observations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    plan = copy.deepcopy(_plan())
    evidence = copy.deepcopy(plan["tasks"][0]["evidence"][0])
    plan["tasks"][0]["evidence"] = [copy.deepcopy(evidence) for _ in range(64)]
    calls: list[str] = []
    monkeypatch.setattr(
        checker_module,
        "_git_commit_probe",
        lambda *_args, **_kwargs: calls.append("probe"),
    )
    monkeypatch.setattr(
        checker_module,
        "_git",
        lambda *_args, **_kwargs: (calls.append("git") or (-1, "")),
    )

    # Act
    findings = validate_plan_v1(plan, root=ROOT, markdown=None)

    # Assert
    rules = {finding.rule_id for finding in findings}
    assert {"task_evidence_duplicate", "task_evidence_limit_exceeded"} <= rules
    assert calls == []


def test_clone_finalizer_attempts_every_path_and_retains_failures_for_retry(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    roots = [tmp_path / f"clone-{index}" for index in range(3)]
    for root in roots:
        root.mkdir()
    cleanup = _remove_disposable_complete_subjects_after_each_test.__wrapped__()
    next(cleanup)
    _DISPOSABLE_COMPLETE_SUBJECTS.extend(roots)
    calls: list[Path] = []
    real_remove = _remove_disposable_subject

    def refuse_one(root: Path) -> None:
        calls.append(root)
        if root == roots[-1]:
            raise OSError("injected cleanup refusal")
        real_remove(root)

    monkeypatch.setattr(
        sys.modules[__name__], "_remove_disposable_subject", refuse_one
    )
    try:
        with pytest.raises(OSError, match="cleanup refusal"):
            next(cleanup)
        assert set(calls) == set(roots)
        assert _DISPOSABLE_COMPLETE_SUBJECTS == [roots[-1]]
        assert all(not root.exists() for root in roots[:-1])
    finally:
        monkeypatch.setattr(
            sys.modules[__name__], "_remove_disposable_subject", real_remove
        )
        for root in roots:
            _remove_disposable_subject(root)
        _DISPOSABLE_COMPLETE_SUBJECTS[:] = [
            root for root in _DISPOSABLE_COMPLETE_SUBJECTS if root not in roots
        ]


def test_amended_direct_child_replays_from_a_detached_worktree_while_stale_or_unrelated_subjects_fail(
    tmp_path: Path,
) -> None:
    # Arrange: base B; provisional C1 (sources + artifacts); artifact-only amend C2; source amend C3.
    repo, base = _synthetic_repository(tmp_path)
    artifact = repo / PLAN_JSON_PATH
    artifact.parent.mkdir(parents=True)
    artifact.write_text("{\"observations\": 1}\n", encoding="utf-8")
    (repo / PLAN_MARKDOWN_PATH).write_text("tables v1\n", encoding="utf-8")
    (repo / "b.txt").write_text("candidate v1\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "candidate")
    provisional = _git(repo, "rev-parse", "HEAD")
    snapshot_c1, _ = source_snapshot_v1(repo)
    artifact.write_text("{\"observations\": 2}\n", encoding="utf-8")
    (repo / PLAN_MARKDOWN_PATH).write_text("tables v2\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "--amend", "-m", "candidate")
    artifact_only_amend = _git(repo, "rev-parse", "HEAD")
    snapshot_c2, _ = source_snapshot_v1(repo)
    (repo / "b.txt").write_text("candidate v2\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "--amend", "-m", "candidate")
    final = _git(repo, "rev-parse", "HEAD")
    snapshot_c3, _ = source_snapshot_v1(repo)
    unrelated = tmp_path / "unrelated"
    unrelated.mkdir()
    _git(unrelated, "init", "-q", "-b", "main")
    (unrelated / "z.txt").write_text("z\n", encoding="utf-8")
    _git(unrelated, "add", "z.txt")
    _git(unrelated, "commit", "-q", "-m", "unrelated")
    unrelated_commit = _git(unrelated, "rev-parse", "HEAD")
    frozen = tmp_path / "frozen"
    _git(repo, "worktree", "add", "--detach", "-q", str(frozen), final)
    assert snapshot_c1 is not None and snapshot_c2 is not None and snapshot_c3 is not None
    subject = {
        "base_commit": base,
        "scoped_worktree_clean": True,
        "source_snapshot_sha256": snapshot_c3.sha256,
        "source_snapshot_file_count": snapshot_c3.entry_count,
    }

    # Act: evaluate the subject binding from the frozen detached checkout of the amended commit.
    replay = subject_state_findings_v1(frozen, subject)
    provisional_lineage = lineage_findings_v1(frozen, provisional, "subject.base_commit")
    superseded_lineage = lineage_findings_v1(frozen, artifact_only_amend, "subject.base_commit")
    unrelated_lineage = lineage_findings_v1(frozen, unrelated_commit, "subject.base_commit")
    stale_snapshot = subject_state_findings_v1(frozen, {**subject, "source_snapshot_sha256": snapshot_c2.sha256})

    # Assert: base lineage and the committed snapshot replay; stale, superseded, and unrelated subjects fail.
    assert final != provisional != artifact_only_amend and _git(repo, "rev-parse", f"{final}^") == base
    assert replay == []
    assert snapshot_c2 == snapshot_c1 and snapshot_c3 != snapshot_c1 and snapshot_c3.entry_count == 2
    assert [item.rule_id for item in provisional_lineage] == ["subject_commit_not_in_lineage"]
    assert [item.rule_id for item in superseded_lineage] == ["subject_commit_not_in_lineage"]
    assert [item.rule_id for item in unrelated_lineage] == ["subject_commit_unknown"]
    assert [item.rule_id for item in stale_snapshot] == ["source_snapshot_drift"]


def test_scoped_cleanliness_is_recomputed_and_blocks_validation_and_execution(tmp_path: Path) -> None:
    # Arrange: a clean synthetic checkout whose recorded subject claims cleanliness.
    repo, base = _synthetic_repository(tmp_path)
    snapshot, _ = source_snapshot_v1(repo)
    assert snapshot is not None
    subject = {
        "base_commit": base,
        "scoped_worktree_clean": True,
        "source_snapshot_sha256": snapshot.sha256,
        "source_snapshot_file_count": snapshot.entry_count,
    }
    clean_findings = subject_state_findings_v1(repo, subject)
    (repo / PLAN_JSON_PATH).parent.mkdir(parents=True)
    (repo / PLAN_JSON_PATH).write_text("{}\n", encoding="utf-8")
    artifact_only_full = [item.rule_id for item in subject_state_findings_v1(repo, subject)]
    artifact_only_regeneration = subject_state_findings_v1(repo, subject, POST_REGENERATION_PROFILE_V1)
    _refreshed, artifact_only_refresh = refresh_plan_v1(_plan(), root=repo, observed_at="2026-08-25", repin_tasks=())
    (repo / "untracked.txt").write_text("stray\n", encoding="utf-8")
    untracked_rules = [item.rule_id for item in subject_state_findings_v1(repo, subject)]
    (repo / "untracked.txt").unlink()
    (repo / "a.txt").write_text("edited\n", encoding="utf-8")
    tracked_rules = [item.rule_id for item in subject_state_findings_v1(repo, subject)]

    # Act: the plan's own refresh and execute paths on the dirty checkout.
    _refreshed, refresh_findings = refresh_plan_v1(_plan(), root=repo, observed_at="2026-08-25", repin_tasks=())
    execute_findings = execute_live_gates_v1(_plan(), repo)

    # Assert: the recorded Boolean is ignored; artifact dirt blocks ordinary checks, source dirt blocks everything.
    assert clean_findings == []
    assert artifact_only_full == ["scoped_worktree_dirty", "scoped_worktree_clean_misrecorded"]
    assert artifact_only_regeneration == []
    assert "scoped_worktree_dirty" not in {item.rule_id for item in artifact_only_refresh}
    assert untracked_rules == ["scoped_worktree_dirty", "scoped_worktree_clean_misrecorded"]
    assert tracked_rules == ["scoped_worktree_dirty", "scoped_worktree_clean_misrecorded"]
    assert scoped_worktree_dirty_paths_v1(repo, CleanlinessScopeV1.REGENERATION) == ["a.txt"]
    assert scoped_worktree_dirty_paths_v1(repo, CleanlinessScopeV1.FULL) == ["a.txt", PLAN_JSON_PATH.as_posix()]
    assert "scoped_worktree_dirty" in {item.rule_id for item in refresh_findings}
    assert "scoped_worktree_dirty" in {item.rule_id for item in execute_findings}
    assert not any(item.rule_id.startswith("live_gate_execution") for item in execute_findings)


def test_test_receipt_cannot_overclaim_authority_or_miscount_failures() -> None:
    # Arrange
    overclaim = _plan()
    overclaim["test_execution_receipt"]["evidence_authority"] = "RELEASE_BACKED"
    miscount = _plan()
    miscount["test_execution_receipt"]["failed"] = miscount["test_execution_receipt"]["failed"] + 1

    # Act / Assert
    assert "test_receipt_authority_overclaimed" in _rules(overclaim)
    assert "test_receipt_failure_count_mismatch" in _rules(miscount)


def test_main_reports_valid_plan_with_exit_zero(capsys: pytest.CaptureFixture[str]) -> None:
    # Act
    exit_code = main(["--root", str(ROOT), "--json"])
    report = json.loads(capsys.readouterr().out)

    # Assert
    assert exit_code == 0
    assert report["ok"] is True
    assert report["authority"]["production_authority"] == "NONE"


@pytest.mark.parametrize(
    "argv",
    (
        ("--render", "--execute", "--json"),
        ("--refresh", "--json"),
        ("--unknown-argument", "--json"),
    ),
    ids=("regeneration_execute_conflict", "missing_observed_at", "argparse_usage_error"),
)
def test_every_cli_failure_uses_one_closed_authority_report(
    argv: tuple[str, ...], capsys: pytest.CaptureFixture[str]
) -> None:
    # Act
    code = main(["--root", str(ROOT), *argv])
    report = json.loads(capsys.readouterr().out)

    # Assert: invocation, refresh, and parser failures retain the complete report boundary.
    assert code == 2
    assert report["ok"] is False and isinstance(report["error"], str) and report["error"]
    assert report["executed_live_gates"] == 0
    assert report["accepted_check_mode"] == "none"
    assert report["authority"] == {
        "claim_authority": "NONE",
        "production_authority": "NONE",
        "production_ready": False,
        "release_ready": False,
    }
    assert report["schema"] == checker_module.CHECK_SCHEMA_V1
    assert all(set(finding) == {"rule_id", "subject", "evidence"} for finding in report["findings"])


def _refuse_gate_execution(*_args: object, **_kwargs: object) -> object:
    raise AssertionError("a registry gate executed before the plan was completely validated")


MALFORMED_PLAN_MUTATIONS: dict[str, Callable[[dict[str, Any]], object]] = {
    "top_level_missing_tasks": lambda plan: plan.pop("tasks"),
    "top_level_extra_field": lambda plan: plan.__setitem__("extra", 1),
    "top_level_authority_null": lambda plan: plan.__setitem__("authority", None),
    "tasks_not_a_list": lambda plan: plan.__setitem__("tasks", {}),
    "task_missing_nested_field": lambda plan: plan["tasks"][0].pop("notes"),
    "task_depends_on_not_a_list": lambda plan: plan["tasks"][0].__setitem__("depends_on", "P1-T01"),
    "task_evidence_row_not_an_object": lambda plan: _first_closed_task(plan)["evidence"].__setitem__(0, "doc"),
    "subject_not_an_object": lambda plan: plan.__setitem__("subject", []),
    "subject_missing_nested_field": lambda plan: plan["subject"].pop("base_commit"),
    "live_gates_null": lambda plan: plan.__setitem__("live_gates", None),
    "live_gate_missing_nested_field": lambda plan: plan["live_gates"][0].pop("observed"),
    "vm_gate_status_not_a_list": lambda plan: plan.__setitem__("vm_gate_status", "x"),
    "vm_gate_entry_missing_nested_field": lambda plan: plan["vm_gate_status"][0].pop("tasks"),
    "finding_registry_row_not_an_object": lambda plan: plan["finding_registry"].__setitem__(0, 5),
    "unresolved_policy_row_null": lambda plan: plan["unresolved_policies"].__setitem__(0, None),
    "phases_null": lambda plan: plan.__setitem__("phases", None),
    "semantic_anchors_not_an_object": lambda plan: plan.__setitem__("semantic_anchors", []),
    "external_gates_not_an_object": lambda plan: plan.__setitem__("external_gates", 1),
    "heavy_gate_row_empty": lambda plan: plan["heavy_gates_requiring_runpod"].__setitem__(0, {}),
    "test_receipt_null": lambda plan: plan.__setitem__("test_execution_receipt", None),
    "task_status_list": lambda plan: plan["tasks"][0].__setitem__("status", []),
    "task_status_object": lambda plan: plan["tasks"][0].__setitem__("status", {}),
    "evidence_kind_list": lambda plan: _first_file_evidence(_first_closed_task(plan)).__setitem__("kind", []),
    "vm_gate_id_list": lambda plan: plan["vm_gate_status"][0].__setitem__("gate_id", []),
    "vm_gate_status_object": lambda plan: plan["vm_gate_status"][0].__setitem__("status", {}),
    "task_depends_on_nested_list": lambda plan: plan["tasks"][1].__setitem__("depends_on", [[]]),
    "dependency_status_list": lambda plan: _task(plan, "P1-T01").__setitem__("status", []),
    "live_gate_id_list": lambda plan: plan["live_gates"][0].__setitem__("gate_id", []),
    "finding_id_list": lambda plan: plan["finding_registry"][0].__setitem__("finding_id", []),
    "subject_base_commit_list": lambda plan: plan["subject"].__setitem__("base_commit", []),
    "receipt_failed_object": lambda plan: plan["test_execution_receipt"].__setitem__("failed", {}),
}

EXECUTION_EVIDENCE_RULES = frozenset({"live_gate_execution_failed", "live_gate_exit_code_drift", "live_gate_observation_drift"})
ENTRYPOINTS: tuple[tuple[str, list[str]], ...] = (
    ("ordinary", ["--json"]),
    ("render", ["--render"]),
    ("refresh", ["--refresh", "--observed-at", "2026-08-25"]),
)


def _entrypoint_attempts(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    root: Path,
) -> list[tuple[str, int, dict[str, Any]]]:
    """Run each entrypoint against one disposable subject; return (entrypoint, exit code, report)."""

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", _refuse_gate_execution)
    attempts: list[tuple[str, int, dict[str, Any]]] = []
    for name, argv in ENTRYPOINTS:
        code = main(["--root", str(root), *argv])
        attempts.append((name, code, json.loads(capsys.readouterr().out)))
    return attempts


def _artifact_bytes(root: Path) -> tuple[bytes, bytes]:
    return (root / PLAN_JSON_PATH).read_bytes(), (root / PLAN_MARKDOWN_PATH).read_bytes()


def _restore_artifacts(root: Path, original_json: bytes, original_markdown: bytes) -> None:
    for relative, data in ((PLAN_JSON_PATH, original_json), (PLAN_MARKDOWN_PATH, original_markdown)):
        path = root / relative
        if path.is_symlink() or (path.exists() and not path.is_file()) or path.is_file():
            path.unlink() if not path.is_dir() else path.rmdir()
        path.write_bytes(data)


@pytest.mark.parametrize("mutation", sorted(MALFORMED_PLAN_MUTATIONS))
def test_every_entrypoint_rejects_malformed_plan_before_any_gate_or_write(
    mutation: str, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path
) -> None:
    # Arrange: mutate only a disposable subject, so a process kill cannot leave the review candidate dirty.
    root = _clone_complete_subject(tmp_path)
    plan = dict(load_plan_v1(root))
    MALFORMED_PLAN_MUTATIONS[mutation](plan)
    original_json, original_markdown = _artifact_bytes(root)
    malformed = canonical_plan_json_v1(plan).encode("utf-8")
    assert malformed != original_json
    try:
        (root / PLAN_JSON_PATH).write_bytes(malformed)

        # Act: ordinary check plus both regeneration entrypoints, with every registry gate refusing to execute.
        attempts = _entrypoint_attempts(monkeypatch, capsys, root)
        json_after, markdown_after = _artifact_bytes(root)
    finally:
        _restore_artifacts(root, original_json, original_markdown)

    # Assert: typed nonzero findings, no raw exception, no execution evidence, and both artifacts byte-identical.
    for name, code, report in attempts:
        assert code == 1, name
        assert report["ok"] is False and report["findings"], name
        for finding in report["findings"]:
            assert set(finding) == {"rule_id", "subject", "evidence"}, name
            assert finding["rule_id"] and finding["rule_id"] == finding["rule_id"].lower(), name
        assert not any(f["rule_id"] in EXECUTION_EVIDENCE_RULES for f in report["findings"]), name
    assert json_after == malformed and markdown_after == original_markdown
    assert scoped_worktree_dirty_paths_v1(root, CleanlinessScopeV1.FULL) == []


@pytest.mark.parametrize("payload", [b"[]\n", b'{"schema": ', b"null\n"], ids=["list_root", "truncated", "null_root"])
def test_every_entrypoint_reports_unreadable_plan_as_typed_error_without_writing(
    payload: bytes, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path
) -> None:
    # Arrange: unreadable-artifact cases use the same disposable-subject discipline.
    root = _clone_complete_subject(tmp_path)
    original_json, original_markdown = _artifact_bytes(root)
    try:
        (root / PLAN_JSON_PATH).write_bytes(payload)

        # Act
        attempts = _entrypoint_attempts(monkeypatch, capsys, root)
        json_after, markdown_after = _artifact_bytes(root)
    finally:
        _restore_artifacts(root, original_json, original_markdown)

    # Assert
    for name, code, report in attempts:
        assert code == 2 and report["ok"] is False and isinstance(report["error"], str) and report["error"], name
    assert json_after == payload and markdown_after == original_markdown
    assert scoped_worktree_dirty_paths_v1(root, CleanlinessScopeV1.FULL) == []


def test_invalid_utf8_markdown_is_a_typed_unreadable_error_on_every_entrypoint(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path
) -> None:
    # Arrange: the malformed companion lives only in a disposable subject.
    root = _clone_complete_subject(tmp_path)
    original_json, original_markdown = _artifact_bytes(root)
    hostile = b"\xff\xfe" + original_markdown
    try:
        (root / PLAN_MARKDOWN_PATH).write_bytes(hostile)

        # Act
        attempts = _entrypoint_attempts(monkeypatch, capsys, root)
        json_after, markdown_after = _artifact_bytes(root)
    finally:
        _restore_artifacts(root, original_json, original_markdown)

    # Assert: exit 2 with a typed error naming UTF-8, never a raw UnicodeDecodeError, and no write.
    for name, code, report in attempts:
        assert code == 2 and report["ok"] is False and "UTF-8" in report["error"], name
    assert json_after == original_json and markdown_after == hostile
    assert scoped_worktree_dirty_paths_v1(root, CleanlinessScopeV1.FULL) == []


def _structural_paths(value: object) -> dict[tuple[str, ...], tuple[object, ...]]:
    """Map every distinct structural path (list indices collapsed to ``[]``) to its first concrete path."""

    found: dict[tuple[str, ...], tuple[object, ...]] = {}

    def walk(node: object, structural: tuple[str, ...], concrete: tuple[object, ...]) -> None:
        if structural:
            found.setdefault(structural, concrete)
        if isinstance(node, dict):
            for key, child in node.items():
                walk(child, (*structural, key), (*concrete, key))
        elif isinstance(node, list):
            for index, child in enumerate(node):
                walk(child, (*structural, "[]"), (*concrete, index))

    walk(value, (), ())
    return found


@pytest.mark.parametrize("mutant", [[], {}], ids=["list", "object"])
def test_every_plan_field_survives_list_and_object_mutants_with_typed_findings(mutant: object, monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: git-backed subject state is proven by its own tests and stubbed here so every path stays affordable.
    monkeypatch.setattr(checker_module, "subject_state_findings_v1", lambda *_args, **_kwargs: [])
    base, markdown = _plan(), _markdown()
    mutated: list[str] = []

    # Act / Assert: every distinct field, list, and object in the plan is replaced by the hostile JSON type.
    for structural, concrete in sorted(_structural_paths(base).items(), key=lambda item: item[0]):
        plan = copy.deepcopy(base)
        target: Any = plan
        for step in concrete[:-1]:
            target = target[step]
        if target[concrete[-1]] == mutant:
            continue
        target[concrete[-1]] = copy.deepcopy(mutant)
        findings = validate_plan_v1(plan, root=ROOT, markdown=markdown)
        report = plan_report_v1(plan, findings, executed=0, profile=ORDINARY_VALIDATION_PROFILE_V1)
        json.dumps(report)
        label = "/".join(structural)
        assert findings and report["ok"] is False, label
        assert all(isinstance(item.rule_id, str) and item.rule_id and isinstance(item.evidence, str) for item in findings), label
        mutated.append(label)
    assert len(mutated) >= 140, mutated


@pytest.mark.parametrize("artifact", [PLAN_JSON_PATH, PLAN_MARKDOWN_PATH], ids=["json", "markdown"])
def test_symlinked_artifact_never_reads_or_writes_the_external_victim(
    artifact: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    # Arrange: the symlink attack stays in a disposable subject and cannot leak into the review worktree.
    root = _clone_complete_subject(tmp_path, "subject")
    victim = tmp_path / "victim.txt"
    victim.write_bytes(b"victim bytes\n")
    original_json, original_markdown = _artifact_bytes(root)
    dirty_before = scoped_worktree_dirty_paths_v1(root, CleanlinessScopeV1.FULL)
    assert dirty_before is not None and artifact.as_posix() not in dirty_before
    path = root / artifact
    path.unlink()
    os.symlink(victim, path)
    try:
        # Act
        attempts = _entrypoint_attempts(monkeypatch, capsys, root)
        still_symlink = path.is_symlink()
        victim_after = victim.read_bytes()
        temp_entries = sorted(entry.name for entry in tmp_path.iterdir() if entry.name != root.name)
        other_after = (root / (PLAN_MARKDOWN_PATH if artifact == PLAN_JSON_PATH else PLAN_JSON_PATH)).read_bytes()
    finally:
        _restore_artifacts(root, original_json, original_markdown)

    # Assert: typed exit 2 naming the symlink, victim untouched, no temporary entry, symlink not replaced.
    for name, code, report in attempts:
        assert code == 2 and report["ok"] is False and "symlink" in report["error"], name
    assert still_symlink and victim_after == b"victim bytes\n" and temp_entries == ["victim.txt"]
    assert other_after == (original_markdown if artifact == PLAN_JSON_PATH else original_json)
    assert scoped_worktree_dirty_paths_v1(root, CleanlinessScopeV1.FULL) == dirty_before


def test_artifact_checks_reject_committed_symlink_fifo_directory_and_device(tmp_path: Path) -> None:
    # Arrange: a synthetic repository whose committed markdown artifact is a symlink.
    repo, _base = _synthetic_repository(tmp_path)
    (repo / PLAN_JSON_PATH).parent.mkdir(parents=True)
    (repo / PLAN_JSON_PATH).write_text("{}\n", encoding="utf-8")
    os.symlink(PLAN_JSON_PATH.name, repo / PLAN_MARKDOWN_PATH)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "artifacts")

    # Act
    committed = plan_artifact_findings_v1(repo)
    symlink_read = read_confined_file_v1(repo, PLAN_MARKDOWN_PATH, max_bytes=1024)
    (repo / PLAN_MARKDOWN_PATH).unlink()
    os.mkfifo(repo / PLAN_MARKDOWN_PATH)
    fifo_read = read_confined_file_v1(repo, PLAN_MARKDOWN_PATH, max_bytes=1024)
    fifo_findings = plan_artifact_findings_v1(repo)
    (repo / PLAN_MARKDOWN_PATH).unlink()
    (repo / PLAN_MARKDOWN_PATH).mkdir()
    directory_read = read_confined_file_v1(repo, PLAN_MARKDOWN_PATH, max_bytes=1024)
    directory_findings = plan_artifact_findings_v1(repo)
    device_read = read_confined_file_v1(Path("/"), Path("dev/null"), max_bytes=1024)
    device_mount_policy = "mount boundary crossed" in device_read.reason or device_read.reason == "not a regular file"
    oversized_read = read_confined_file_v1(repo, PLAN_JSON_PATH, max_bytes=2)

    # Assert: committed and worktree forms are typed findings; no read blocks or follows.
    markdown_rules = [item.rule_id for item in committed if item.subject == PLAN_MARKDOWN_PATH.as_posix()]
    assert markdown_rules == ["plan_artifact_committed_not_regular", "plan_artifact_not_regular_file"]
    assert [item.rule_id for item in committed if item.subject == PLAN_JSON_PATH.as_posix()] == []
    assert symlink_read.data is None and "symlink" in symlink_read.reason
    assert fifo_read.data is None and fifo_read.reason == "not a regular file"
    assert "plan_artifact_not_regular_file" in {item.rule_id for item in fifo_findings}
    assert directory_read.data is None and directory_read.reason == "not a regular file"
    assert "plan_artifact_not_regular_file" in {item.rule_id for item in directory_findings}
    assert device_read.data is None and device_mount_policy, device_read
    assert oversized_read.data is None and oversized_read.reason == "exceeds 2 bytes"


def test_confined_io_refuses_symlinked_directory_components_and_replaces_atomically(tmp_path: Path) -> None:
    # Arrange: docs/research is a symlink to an external directory holding a plausible artifact.
    root, external = tmp_path / "root", tmp_path / "external"
    root.mkdir()
    external.mkdir()
    (external / PLAN_JSON_PATH.name).write_bytes(b"{}\n")
    (root / "docs").mkdir()
    os.symlink(external, root / "docs" / "research")

    # Act
    traversal_read = read_confined_file_v1(root, PLAN_JSON_PATH, max_bytes=1024)
    traversal_refusal = replace_confined_file_v1(root, PLAN_JSON_PATH, b"hostile\n")
    (root / "docs" / "research").unlink()
    (root / "docs" / "research").mkdir()
    target = root / PLAN_JSON_PATH
    target.write_bytes(b"old\n")
    replaced = replace_confined_file_v1(root, PLAN_JSON_PATH, b"new\n")
    bytes_after_replace = target.read_bytes()
    entries_after_replace = sorted(entry.name for entry in target.parent.iterdir())
    victim = tmp_path / "victim"
    victim.write_bytes(b"victim\n")
    target.unlink()
    os.symlink(victim, target)
    symlink_refusal = replace_confined_file_v1(root, PLAN_JSON_PATH, b"pwn\n")
    hostile_paths = (Path("/etc/passwd"), Path("../x"), Path("docs/../x"), Path(""))
    hostile_reads = [read_confined_file_v1(root, hostile, max_bytes=8).data for hostile in hostile_paths]
    hostile_writes = [replace_confined_file_v1(root, hostile, b"x") for hostile in hostile_paths]

    # Assert
    assert traversal_read.data is None and "symlink" in traversal_read.reason
    assert traversal_refusal and (external / PLAN_JSON_PATH.name).read_bytes() == b"{}\n"
    assert sorted(entry.name for entry in external.iterdir()) == [PLAN_JSON_PATH.name]
    assert replaced == "" and bytes_after_replace == b"new\n" and entries_after_replace == [target.name]
    assert "not a regular file" in symlink_refusal and victim.read_bytes() == b"victim\n" and target.is_symlink()
    assert hostile_reads == [None] * len(hostile_paths) and all(hostile_writes)
    assert not (tmp_path / "x").exists() and not Path("/etc/x").exists()


@pytest.mark.parametrize(
    ("observed_at", "repin", "expected_rule"),
    [
        ("2026-13-45", (), "refresh_observed_at_malformed"),
        ("2026-02-30", (), "refresh_observed_at_malformed"),
        ("2026-08-25T00:00", (), "refresh_observed_at_malformed"),
        ("25-08-2026", (), "refresh_observed_at_malformed"),
        ("", (), "refresh_observed_at_malformed"),
        ("2026-08-25", ("P6-T99",), "repin_task_unknown"),
        ("2026-08-25", ("nonsense",), "repin_task_malformed"),
        ("2026-08-25", ("P9-T99",), "repin_task_malformed"),
        ("2026-08-25", ("P1-T01", "P6-T98"), "repin_task_unknown"),
    ],
)
def test_refresh_refuses_invalid_date_or_repin_id_before_any_observer_call(
    observed_at: str, repin: tuple[str, ...], expected_rule: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: observers answer with the recorded observations, so only the invocation gate can stop the refresh.
    calls: list[str] = []
    recorded = {gate["gate_id"]: gate for gate in _plan()["live_gates"]}

    def matching_observation(spec: Any, _root: object, **_kwargs: object) -> LiveGateObservationV1:
        calls.append(spec.gate_id)
        row = recorded[spec.gate_id]
        return LiveGateObservationV1(row["exit_code"], copy.deepcopy(row["observed"]), "")

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", matching_observation)
    plan = _plan()

    # Act
    refreshed, findings = refresh_plan_v1(plan, root=ROOT, observed_at=observed_at, repin_tasks=repin)

    # Assert: zero observer calls, the typed invocation finding, and an untouched plan copy.
    assert calls == []
    assert expected_rule in {item.rule_id for item in findings}
    assert all(item.rule_id.startswith(("refresh_", "repin_")) for item in findings)
    assert refreshed == plan


def test_root_identity_is_bound_and_a_swapped_root_pathname_never_reaches_the_external_victim(tmp_path: Path) -> None:
    # Arrange: a real root with the artifact, an external victim tree with the same layout, and a bound root.
    root, external, other = tmp_path / "root", tmp_path / "external", tmp_path / "other"
    for base in (root, external, other):
        (base / PLAN_JSON_PATH).parent.mkdir(parents=True)
    target = root / PLAN_JSON_PATH
    target.write_bytes(b"original\n")
    victim, decoy = external / PLAN_JSON_PATH, other / PLAN_JSON_PATH
    victim.write_bytes(b"victim\n")
    decoy.write_bytes(b"decoy\n")
    bound = ConfinedRootV1.bind(root)
    before = read_confined_file_v1(bound, PLAN_JSON_PATH, max_bytes=64)

    # Act 1: the root pathname is replaced by a symlink to the external tree before the next operation.
    moved = tmp_path / "moved"
    root.rename(moved)
    os.symlink(external, root)
    symlink_read = read_confined_file_v1(bound, PLAN_JSON_PATH, max_bytes=64)
    symlink_write = replace_confined_file_v1(bound, PLAN_JSON_PATH, b"through-link\n")
    pathname_bind_refused = False
    try:
        ConfinedRootV1.bind(root)
    except checker_module.PlanUnreadable:
        pathname_bind_refused = True
    root.unlink()

    # Act 2: the root pathname now names a different real directory with the same layout.
    other.rename(root)
    other_read = read_confined_file_v1(bound, PLAN_JSON_PATH, max_bytes=64)
    other_write = replace_confined_file_v1(bound, PLAN_JSON_PATH, b"through-twin\n")
    root.rename(other)

    # Act 3: the original directory returns under its pathname.
    moved.rename(root)
    restored = read_confined_file_v1(bound, PLAN_JSON_PATH, max_bytes=64)
    bound.close()

    # Assert: every operation through the capability addressed the bound inode (the moved original), never the
    # symlink target or the twin; the victim and decoy trees are byte-identical; binding the symlink is refused.
    assert before.data == b"original\n"
    assert symlink_read.data == b"original\n" and symlink_write == ""
    assert other_read.data == b"through-link\n" and other_write == ""
    assert restored.data == b"through-twin\n" and target.read_bytes() == b"through-twin\n"
    assert pathname_bind_refused
    assert victim.read_bytes() == b"victim\n" and decoy.read_bytes() == b"decoy\n"
    assert sorted(entry.name for entry in victim.parent.iterdir()) == [PLAN_JSON_PATH.name]
    assert sorted(entry.name for entry in decoy.parent.iterdir()) == [PLAN_JSON_PATH.name]
    assert ConfinedRootV1.bind(bound) is bound


def test_two_root_swap_cannot_launder_a_dirty_root_through_pathname_based_work(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: root A (bound once, persistently) and its byte-identical twin B with one extra committed file
    # (distinct snapshot); A is then made dirty (untracked hostile file, JSON artifact replaced by a FIFO) and
    # B is swapped into A's pathname around every git, stat, and subprocess step.
    import shutil

    (tmp_path / "one").mkdir()
    dirty_root, dirty_base = _synthetic_repository(tmp_path / "one")
    (dirty_root / PLAN_JSON_PATH).parent.mkdir(parents=True)
    (dirty_root / PLAN_JSON_PATH).write_text("{}\n", encoding="utf-8")
    (dirty_root / PLAN_MARKDOWN_PATH).write_text("md\n", encoding="utf-8")
    _git(dirty_root, "add", "-A")
    _git(dirty_root, "commit", "-q", "-m", "artifacts")
    clean_root = tmp_path / "two"
    shutil.copytree(dirty_root, clean_root)
    (clean_root / "extra.txt").write_text("one more committed file\n", encoding="utf-8")
    _git(clean_root, "add", "-A")
    _git(clean_root, "commit", "-q", "-m", "extra")
    bound = ConfinedRootV1.bind(dirty_root)
    snapshot, _ = source_snapshot_v1(bound)
    twin_snapshot, _ = source_snapshot_v1(clean_root)
    assert snapshot is not None and twin_snapshot is not None and twin_snapshot.entry_count == snapshot.entry_count + 1
    subject = {
        "base_commit": dirty_base,
        "scoped_worktree_clean": True,
        "source_snapshot_sha256": snapshot.sha256,
        "source_snapshot_file_count": snapshot.entry_count,
    }
    (dirty_root / "hostile.txt").write_text("stray\n", encoding="utf-8")
    (dirty_root / PLAN_JSON_PATH).unlink()
    os.mkfifo(dirty_root / PLAN_JSON_PATH)
    dirty_inode = os.stat(dirty_root).st_ino
    calls: list[str] = []

    def counting_refusal(spec: Any, _root: object, **_kwargs: object) -> object:
        calls.append(spec.gate_id)
        return _refuse_gate_execution()

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", counting_refusal)
    moved = tmp_path / "moved"
    dirty_root.rename(moved)
    clean_root.rename(dirty_root)
    try:
        # Act: every check runs through the persistent capability while the pathname names the clean twin.
        toplevel = git_v1(bound.anchored, ["rev-parse", "--show-toplevel"])
        cwd_probe = run_bounded_process_v1(
            [sys.executable, "-c", "import os; print(os.stat('.').st_ino)"],
            cwd=bound.anchored,
            env=gate_environment_v1(bound.anchored),
            bounds=ProcessBoundsV1(30, 4096),
        )
        swapped_subject = subject_state_findings_v1(bound, subject)
        swapped_snapshot, _ = source_snapshot_v1(bound)
        swapped_artifacts = plan_artifact_findings_v1(bound)
        swapped_execute = execute_live_gates_v1(_plan(), bound)
        # The pathname view is exactly what a path-based check would have laundered: clean, distinct snapshot.
        pathname_subject = subject_state_findings_v1(dirty_root, subject)
        pathname_snapshot, _ = source_snapshot_v1(dirty_root)
    finally:
        dirty_root.rename(clean_root)
        moved.rename(dirty_root)
        bound.close()

    # Assert: the capability never saw B: git, the child, status, snapshot, and artifacts are A's own,
    # the pathname view is the laundered twin, and no observer or effect ran.
    assert toplevel[0] == 0 and Path(toplevel[1]) == moved
    assert cwd_probe.error == "" and int(cwd_probe.stdout) == dirty_inode
    swapped_rules = {item.rule_id for item in swapped_subject}
    assert "scoped_worktree_dirty" in swapped_rules and any("hostile.txt" in item.evidence for item in swapped_subject)
    assert "source_snapshot_drift" not in swapped_rules and swapped_snapshot == snapshot
    assert "plan_artifact_not_regular_file" in {item.rule_id for item in swapped_artifacts}
    assert swapped_execute and calls == []
    pathname_rules = {item.rule_id for item in pathname_subject}
    assert "scoped_worktree_dirty" not in pathname_rules and "source_snapshot_drift" in pathname_rules
    assert pathname_snapshot == twin_snapshot


def _close_effects(effects: object) -> None:
    close = getattr(checker_module, "close_live_gate_effects_v1", None)
    if close is not None:
        close(effects)


def _close_root(root: object) -> None:
    close = getattr(root, "close", None)
    if close is not None:
        close()


def _other_root_with_equal_checker(tmp_path: Path, checker_path: str, *, tamper: bytes = b"") -> Path:
    other = tmp_path / "other"
    (other / Path(checker_path).parent).mkdir(parents=True)
    (other / checker_path).write_bytes((ROOT / checker_path).read_bytes() + tamper)
    return other


def test_effect_planned_under_one_root_never_executes_against_a_root_with_a_different_checker(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: an effect planned against the real root; a second root whose checker bytes differ.
    calls: list[str] = []

    def counting_refusal(spec: Any, _root: object, **_kwargs: object) -> object:
        calls.append(spec.gate_id)
        return _refuse_gate_execution()

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", counting_refusal)
    owner = ConfinedRootV1.bind(ROOT)
    effects, findings = plan_live_gate_effects_v1(_plan()["live_gates"], owner)
    assert findings == [] and effects
    effect = effects[0]
    other = ConfinedRootV1.bind(_other_root_with_equal_checker(tmp_path, effect.spec.checker_path, tamper=b"\n# tampered\n"))

    # Act
    try:
        refusal = checker_module.execute_live_gate_effect_v1(effect, other)
    finally:
        _close_effects(effects)

    # Assert: the effect refuses any root but its own, so the observer never runs.
    assert [item.rule_id for item in refusal] == ["live_gate_effect_not_owned"] and calls == []
    assert effect.checker_sha256 == _gate(_plan(), effect.spec.gate_id)["checker_sha256"]


def test_witness_effect_bound_to_its_planning_root_refuses_a_distinct_root_with_equal_checker_bytes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Max ae889ac4 counterexample 1: an effect planned under root A executed under a distinct root B when both
    # roots contained equal checker bytes.
    calls: list[str] = []

    def counting_refusal(spec: Any, _root: object, **_kwargs: object) -> object:
        calls.append(spec.gate_id)
        return _refuse_gate_execution()

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", counting_refusal)
    owner = ConfinedRootV1.bind(ROOT)
    effects, findings = plan_live_gate_effects_v1(_plan()["live_gates"], owner)
    assert findings == [] and effects
    effect = effects[0]
    other = ConfinedRootV1.bind(_other_root_with_equal_checker(tmp_path, effect.spec.checker_path))

    # Act: execute under B with byte-identical checker, then under a fresh capability for the same root A.
    try:
        under_b = checker_module.execute_live_gate_effect_v1(effect, other)
        under_fresh_a = checker_module.execute_live_gate_effect_v1(effect, ConfinedRootV1.bind(ROOT))
    finally:
        _close_effects(effects)

    # Assert: zero observer calls; both refusals are the ownership rule, not a digest comparison.
    assert calls == []
    assert [item.rule_id for item in under_b] == ["live_gate_effect_not_owned"]
    assert [item.rule_id for item in under_fresh_a] == ["live_gate_effect_not_owned"]


def _fake_output_for(projection: tuple[str, ...]) -> dict[str, Any]:
    """A JSON object that satisfies every projection key of a registry gate."""

    output: dict[str, Any] = {}
    for key in projection:
        node: Any = output
        segments = key.split(".")
        for index, segment in enumerate(segments):
            last = index == len(segments) - 1
            if segment.endswith("#len"):
                node.setdefault(segment[:-4], [])
            elif segment.endswith("[]"):
                node = node.setdefault(segment[:-2], [{}])[0]
            elif last:
                node.setdefault(segment, f"value-{segment}")
            else:
                node = node.setdefault(segment, {})
    return output


def _fake_gate_root(tmp_path: Path, marker_dir: Path) -> tuple[Path, list[dict[str, Any]]]:
    """A committed synthetic root with a fake script for every registry gate plus matching plan rows."""

    import hashlib

    from tools.live_gate_registry_v1 import project_observed_value_v1

    (tmp_path / "gates").mkdir()
    root, _base = _synthetic_repository(tmp_path / "gates")
    (root / "tools").mkdir()
    for relative in (
        Path("tools/__init__.py"),
        Path("tools/bounded_json_v1.py"),
        Path("tools/live_gate_registry_v1.py"),
    ):
        (root / relative).write_bytes((ROOT / relative).read_bytes())
    rows: list[dict[str, Any]] = []
    for row in _plan()["live_gates"]:
        spec = LIVE_GATE_REGISTRY[row["gate_id"]]
        output = _fake_output_for(spec.observed_projection)
        marker = marker_dir / f"{spec.gate_id}.v1"
        source = (
            "import json, pathlib\n"
            f"pathlib.Path({str(marker)!r}).write_text('ran')\n"
            f"print(json.dumps({json.dumps(output)!r}) if False else {json.dumps(output)!r})\n"
        )
        target = root / spec.checker_path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source, encoding="utf-8")
        observed = {} if spec.output_format == "text" else {key: project_observed_value_v1(output, key) for key in spec.observed_projection}
        rows.append({**copy.deepcopy(row), "checker_sha256": hashlib.sha256(target.read_bytes()).hexdigest(), "exit_code": 0, "observed": observed})
    for relative in (PLAN_JSON_PATH, PLAN_MARKDOWN_PATH):
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((ROOT / relative).read_bytes())
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "fake gates")
    return root, rows


def test_witness_checker_bytes_that_were_hashed_are_the_bytes_that_execute(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # Max ae889ac4 counterexample 2: a swap scheduled after hashing (here: at the instant the observer is entered)
    # made different bytes execute while the gate reported success.
    markers = tmp_path / "markers"
    markers.mkdir()
    root, rows = _fake_gate_root(tmp_path, markers)
    owner = ConfinedRootV1.bind(root)
    effects, findings = plan_live_gate_effects_v1(rows, owner)
    assert findings == [] and len(effects) == len(LIVE_GATE_REGISTRY)
    effect = next(item for item in effects if item.spec.gate_id == FAST_GATE_ID)
    hashed = root / effect.spec.checker_path
    swapped_in = root.parent / "swapped.py"
    swapped_in.write_text(hashed.read_text(encoding="utf-8").replace(f"{FAST_GATE_ID}.v1", f"{FAST_GATE_ID}.v2"), encoding="utf-8")
    real_observe = checker_module.observe_live_gate_v1

    def swap_then_observe(spec: Any, root_view: Any, **kwargs: Any) -> Any:
        os.rename(swapped_in, hashed)
        return real_observe(spec, root_view, **kwargs)

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", swap_then_observe)

    # Act
    try:
        outcome = checker_module.execute_live_gate_effect_v1(effect, owner)
    finally:
        _close_effects(effects)
        _close_root(owner)

    # Assert: the hashed bytes (v1 marker) ran and the swapped-in bytes (v2
    # marker) never did. The persistent worktree change independently refuses
    # the observation after execution.
    assert [item.rule_id for item in outcome] == [
        "live_gate_effect_worktree_drift"
    ]
    assert effect.spec.checker_path in outcome[0].evidence
    assert (markers / f"{FAST_GATE_ID}.v1").exists()
    assert not (markers / f"{FAST_GATE_ID}.v2").exists()


def test_transient_checker_inode_rewrite_executes_only_the_sealed_snapshot(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: after the checker was hashed, rewrite that same inode with code
    # which restores the original bytes before returning a matching observation.
    # A mutable held fd executes the transient bytes and leaves no post-hash or
    # Git residue; a sealed snapshot can execute only the planned bytes.
    markers = tmp_path / "markers"
    markers.mkdir()
    root, rows = _fake_gate_root(tmp_path, markers)
    owner = ConfinedRootV1.bind(root)
    effects, planning_findings = plan_live_gate_effects_v1(rows, owner)
    assert planning_findings == [] and effects
    effect = next(item for item in effects if item.spec.gate_id == FAST_GATE_ID)
    checker_path = root / effect.spec.checker_path
    original = checker_path.read_text(encoding="utf-8")
    hostile_marker = tmp_path / "transient-checker.marker"
    transient = (
        "from pathlib import Path\n"
        f"Path({str(checker_path)!r}).write_text({original!r}, encoding='utf-8')\n"
        f"Path({str(hostile_marker)!r}).write_text('executed', encoding='utf-8')\n"
        + original
    )
    real_observe = checker_module._observe_anchored

    def rewrite_then_observe(
        spec: Any,
        root_view: Any,
        checker_file: Any,
        supervisor_code: Any,
    ) -> Any:
        checker_path.write_text(transient, encoding="utf-8")
        return real_observe(spec, root_view, checker_file, supervisor_code)

    monkeypatch.setattr(checker_module, "_observe_anchored", rewrite_then_observe)

    # Act
    try:
        findings, observer_calls = checker_module._execute_live_gate_effect_with_count_v1(
            effect, owner
        )
    finally:
        checker_path.write_text(original, encoding="utf-8")
        _close_effects(effects)
        owner.close()

    # Assert: only the original snapshot ran. The unexecuted transient rewrite
    # remains visible to the post-observer worktree check and is refused once.
    assert observer_calls == 1
    assert not hostile_marker.exists()
    assert (markers / f"{FAST_GATE_ID}.v1").exists()
    assert [item.rule_id for item in findings] == [
        "live_gate_effect_worktree_drift"
    ]


def test_persistent_source_change_during_observation_refuses_the_observation(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: a committed synthetic root with fake gates; a new file is committed while the observer runs.
    markers = tmp_path / "markers"
    markers.mkdir()
    root, rows = _fake_gate_root(tmp_path, markers)
    owner = ConfinedRootV1.bind(root)
    effects, findings = plan_live_gate_effects_v1(rows, owner)
    assert findings == [] and effects
    effect = next(item for item in effects if item.spec.gate_id == FAST_GATE_ID)
    real_observe = checker_module.observe_live_gate_v1

    def commit_then_observe(spec: Any, root_view: Any, **kwargs: Any) -> Any:
        (root / "changed-during-observation.txt").write_text("persistent change\n", encoding="utf-8")
        _git(root, "add", "-A")
        _git(root, "commit", "-q", "-m", "change during observation")
        return real_observe(spec, root_view, **kwargs)

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", commit_then_observe)

    # Act
    try:
        outcome = checker_module.execute_live_gate_effect_v1(effect, owner)
        later, _ = source_snapshot_v1(owner)
    finally:
        _close_effects(effects)
        _close_root(owner)

    # Assert: the gate ran (its marker exists) but the observation is refused with the typed snapshot-drift finding,
    # and nothing else from that run is reported as accepted drift.
    assert (markers / f"{FAST_GATE_ID}.v1").exists()
    assert [item.rule_id for item in outcome] == ["live_gate_effect_snapshot_drift"]
    assert "observation refused" in outcome[0].evidence and later is not None and later.sha256 != effect._snapshot


@pytest.mark.parametrize("artifact", [PLAN_JSON_PATH, PLAN_MARKDOWN_PATH], ids=["json", "markdown"])
def test_committed_plan_artifact_change_during_observation_is_head_drift(
    artifact: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: plan artifacts are excluded from the non-circular source digest,
    # so the ephemeral effect also binds the exact HEAD commit.
    markers = tmp_path / "markers"
    markers.mkdir()
    root, rows = _fake_gate_root(tmp_path, markers)
    for relative in (PLAN_JSON_PATH, PLAN_MARKDOWN_PATH):
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(f"original {relative.name}\n", encoding="utf-8")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "plan artifacts")
    owner = ConfinedRootV1.bind(root)
    effects, findings = plan_live_gate_effects_v1(rows, owner)
    assert findings == [] and effects
    effect = next(item for item in effects if item.spec.gate_id == FAST_GATE_ID)
    real_observe = checker_module.observe_live_gate_v1

    def commit_plan_then_observe(spec: Any, root_view: Any, **kwargs: Any) -> Any:
        (root / artifact).write_text("changed during observation\n", encoding="utf-8")
        _git(root, "add", artifact.as_posix())
        _git(root, "commit", "-q", "-m", "plan artifact drift")
        return real_observe(spec, root_view, **kwargs)

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", commit_plan_then_observe)

    # Act
    try:
        outcome = checker_module.execute_live_gate_effect_v1(effect, owner)
    finally:
        _close_effects(effects)
        _close_root(owner)

    # Assert: the source digest is unchanged, while the exact effect HEAD moved.
    assert (markers / f"{FAST_GATE_ID}.v1").exists()
    assert [item.rule_id for item in outcome] == ["live_gate_effect_head_drift"]
    assert effect._head in outcome[0].evidence


def test_self_restoring_path_hook_symlink_never_executes_hostile_import(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: an ignored parent symlink makes external/ESSO resolve outside the
    # bound root. The hostile json module removes that symlink as soon as it is
    # imported, which restored a clean worktree before the old post-check.
    markers = tmp_path / "markers"
    markers.mkdir()
    root, rows = _fake_gate_root(tmp_path, markers)
    (root / "sitecustomize.py").write_bytes((ROOT / "sitecustomize.py").read_bytes())
    _git(root, "add", "sitecustomize.py")
    _git(root, "commit", "-q", "-m", "tracked path hook")
    target = tmp_path / "hostile-target"
    hostile = target / "ESSO" / "json.py"
    hostile.parent.mkdir(parents=True)
    marker = tmp_path / "hostile-json-imported.marker"
    external = root / "external"
    hostile.write_text(
        "import importlib as _importlib\n"
        "from pathlib import Path as _Path\n"
        "import sys as _sys\n"
        f"_Path({str(marker)!r}).write_text('hostile import ran', encoding='utf-8')\n"
        f"_injected = _Path({str(external)!r})\n"
        "if _injected.is_symlink():\n"
        "    _injected.unlink()\n"
        "_sys.modules.pop(__name__, None)\n"
        "_saved = list(_sys.path)\n"
        "_hostile_dir = str(_Path(__file__).parent)\n"
        "_sys.path[:] = [item for item in _sys.path if item != _hostile_dir]\n"
        "try:\n"
        "    _real = _importlib.import_module(__name__)\n"
        "finally:\n"
        "    _sys.path[:] = _saved\n"
        "_sys.modules[__name__] = _real\n",
        encoding="utf-8",
    )
    owner = ConfinedRootV1.bind(root)
    effects, planning_findings = plan_live_gate_effects_v1(rows, owner)
    assert planning_findings == [] and effects
    effect = next(item for item in effects if item.spec.gate_id == FAST_GATE_ID)
    real_observe = checker_module._observe_anchored
    calls: list[str] = []

    def inject_then_observe(
        spec: Any,
        root_view: Any,
        checker_file: Any,
        supervisor_code: Any,
    ) -> Any:
        calls.append(spec.gate_id)
        os.symlink(target, external)
        return real_observe(spec, root_view, checker_file, supervisor_code)

    monkeypatch.setattr(checker_module, "_observe_anchored", inject_then_observe)

    # Act
    try:
        findings, observer_calls = checker_module._execute_live_gate_effect_with_count_v1(
            effect, owner
        )
    finally:
        if external.is_symlink():
            external.unlink()
        _close_effects(effects)
        owner.close()

    # Assert: preflight resolution failure is fail-closed. Crossing the observer
    # boundary counts exactly once; no hostile code runs and no later call exists.
    assert observer_calls == 1 and calls == [FAST_GATE_ID]
    assert not marker.exists()
    assert [item.rule_id for item in findings] == ["live_gate_effect_worktree_drift"]
    assert "external" in findings[0].evidence


def test_witness_inode_reuse_after_root_deletion_never_reaches_the_replacement(tmp_path: Path) -> None:
    # Max ae889ac4 counterexample 3: with only (st_dev, st_ino) retained, a recreated root that reused the
    # deleted root's inode was accepted.
    import shutil

    (tmp_path / "a").mkdir()
    root, base = _synthetic_repository(tmp_path / "a")
    (root / PLAN_JSON_PATH).parent.mkdir(parents=True)
    (root / PLAN_JSON_PATH).write_bytes(b'{"original": true}\n')
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "artifact")
    bound = ConfinedRootV1.bind(root)
    original_inode = os.stat(root).st_ino
    subject = {"base_commit": base, "scoped_worktree_clean": True, "source_snapshot_sha256": "0" * 64, "source_snapshot_file_count": 0}
    shutil.rmtree(root)
    reused = False
    for _attempt in range(64):
        root.mkdir()
        if os.stat(root).st_ino == original_inode:
            reused = True
            break
        keep = tmp_path / f"keep-{_attempt}"
        root.rename(keep)
    (root / PLAN_JSON_PATH).parent.mkdir(parents=True)
    (root / PLAN_JSON_PATH).write_bytes(b'{"replacement": true}\n')

    # Act
    try:
        read = read_confined_file_v1(bound, PLAN_JSON_PATH, max_bytes=64)
        refusal = replace_confined_file_v1(bound, PLAN_JSON_PATH, b"pwn\n")
        subject_rules = {item.rule_id for item in subject_state_findings_v1(bound, subject)}
    finally:
        _close_root(bound)

    # Assert: the replacement is never read, written, or validated through the capability, reused inode or not.
    assert read.data is None and read.data != b'{"replacement": true}\n'
    assert refusal and (root / PLAN_JSON_PATH).read_bytes() == b'{"replacement": true}\n'
    assert subject_rules and "scoped_worktree_dirty" not in subject_rules
    assert all(rule.endswith(("_unknown", "_unavailable")) for rule in subject_rules), (subject_rules, reused)


def test_report_states_the_transitive_code_and_containment_nonclaims() -> None:
    # Act
    nonclaims = plan_report_v1(_plan(), [], executed=0, profile=ORDINARY_VALIDATION_PROFILE_V1)["nonclaims"]

    # Assert: the narrowed claims are durable report content, not prose.
    assert isinstance(nonclaims, list)
    assert any("transitive repository code is trusted, not attested" in item for item in nonclaims)
    assert any("swapped and restored between the two snapshot checks is not detected" in item for item in nonclaims)
    assert any("kills its supervisor or double-forks into a new session" in item and "possible orphans" in item for item in nonclaims)
    assert any(
        "not separately descriptor-bound or attested" in item
        and "not an adversarially immutable repository snapshot" in item
        and "trusted git store" in item
        for item in nonclaims
    )
    assert any("reverted before the post-execution checks" in item for item in nonclaims)
    assert not any("expire when any relied-on source changes" in item for item in nonclaims)


def test_linked_worktree_git_indirection_points_outside_the_anchored_root(tmp_path: Path) -> None:
    # Arrange: a synthetic repository plus a linked worktree of it, so the example holds on any CI clone shape.
    (tmp_path / "main").mkdir()
    repo, base = _synthetic_repository(tmp_path / "main")
    linked = tmp_path / "linked"
    _git(repo, "worktree", "add", "--detach", "-q", str(linked), base)
    git_file = linked / ".git"

    # Act: every step that can fail runs inside the try; the capability is closed only if it was bound, and the
    # linked worktree is always removed.
    bound: ConfinedRootV1 | None = None
    try:
        git_entry_is_file = git_file.is_file()
        indirection = git_file.read_text(encoding="utf-8").strip()
        admin_dir = Path(indirection.removeprefix("gitdir: "))
        admin_dir_exists = admin_dir.is_dir()
        bound = ConfinedRootV1.bind(linked)
        lineage = lineage_findings_v1(bound, base, "subject.base_commit")
        with pytest.raises(AnchorRefused, match="NotADirectoryError"):
            bound.anchored.exists(".git/HEAD")
    finally:
        if bound is not None:
            bound.close()
        _git(repo, "worktree", "remove", "--force", str(linked))

    # Assert: the .git entry is a file whose gitdir indirection names an absolute path outside the anchored root; git
    # still answers through the bound cwd, but that administrative tree is not reachable through the anchor.
    assert git_entry_is_file and indirection.startswith("gitdir: ")
    assert admin_dir.is_absolute() and linked not in admin_dir.parents and admin_dir_exists
    assert lineage == []


def test_witness_ancestor_symlink_in_the_root_path_is_refused(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    # Max ae889ac4 counterexample 5: O_NOFOLLOW on the final component only; ancestor-link/subject exited 0.
    ancestor_link = tmp_path / "ancestor-link"
    os.symlink(ROOT.parent, ancestor_link)
    through_link = ancestor_link / ROOT.name

    # Act
    code = main(["--root", str(through_link), "--json"])
    report = json.loads(capsys.readouterr().out)

    # Assert
    assert code == 2 and report["ok"] is False and "symlink" in report["error"]
    with pytest.raises(checker_module.PlanUnreadable, match="symlink"):
        ConfinedRootV1.bind(through_link)


def test_symlink_root_is_refused_by_main_instead_of_resolved(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    # Arrange: an existing symlink whose target is the real repository root.
    link = tmp_path / "link"
    os.symlink(ROOT, link)

    # Act
    code = main(["--root", str(link), "--json"])
    report = json.loads(capsys.readouterr().out)

    # Assert: exit 2 with a typed error naming the symlink, never ok=true through the resolved target.
    assert code == 2 and report["ok"] is False and "symlink" in report["error"]


@pytest.mark.parametrize("target_exists", [True, False], ids=["link_to_existing_directory", "dangling_link"])
def test_binding_a_symlink_root_is_refused_not_followed(target_exists: bool, tmp_path: Path) -> None:
    # Arrange: the root pathname's final component is a symlink (to a real directory, or dangling).
    real = tmp_path / "real"
    real.mkdir()
    link = tmp_path / "link"
    os.symlink(real if target_exists else tmp_path / "does-not-exist", link)

    # Act / Assert: binding refuses instead of resolving through the link; the real directory binds directly.
    with pytest.raises(checker_module.PlanUnreadable, match="symlink"):
        ConfinedRootV1.bind(link)
    bound = ConfinedRootV1.bind(real)
    assert bound.path == real and not bound.path.is_symlink()


def test_direct_execution_validates_the_complete_plan_before_any_observer_call(monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: observers answer with exactly the recorded observations, so only validation can stop execution;
    # the malformed row is a task (not a gate row) missing one nested field.
    calls: list[str] = []
    recorded = {gate["gate_id"]: gate for gate in _plan()["live_gates"]}

    def matching_observation(spec: Any, _root: object, **_kwargs: object) -> LiveGateObservationV1:
        calls.append(spec.gate_id)
        row = recorded[spec.gate_id]
        return LiveGateObservationV1(row["exit_code"], copy.deepcopy(row["observed"]), "")

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", matching_observation)
    malformed = _plan()
    del malformed["tasks"][0]["notes"]

    # Act
    malformed_findings = execute_live_gates_v1(malformed, ROOT)
    calls_after_malformed = list(calls)
    control_findings = execute_live_gates_v1(_plan(), ROOT)

    # Assert: zero observer calls and a typed structural finding for the malformed plan; the control proves the
    # same stubbed observers are reached (all 11, no findings) once the plan validates completely.
    assert calls_after_malformed == []
    assert [item.rule_id for item in malformed_findings] == ["task_field_set_not_closed"]
    assert malformed_findings[0].subject == "tasks[0]"
    assert control_findings == [] and calls == sorted(LIVE_GATE_REGISTRY)


def test_direct_execution_rejects_stale_caller_plan_under_invalid_committed_plan(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: a clean plan-only successor commits an invalid current JSON
    # artifact. The caller retains the previously valid mapping.
    root = tmp_path / "subject"
    subprocess.run(
        ["/usr/bin/git", "clone", "-q", "--no-hardlinks", str(ROOT), str(root)],
        check=True,
        capture_output=True,
        text=True,
    )
    stale_plan = copy.deepcopy(dict(load_plan_v1(root)))
    (root / PLAN_JSON_PATH).write_text(
        '{"schema":"attacker/committed-plan/v1"}\n', encoding="utf-8"
    )
    _git(root, "add", PLAN_JSON_PATH.as_posix())
    _git(root, "commit", "-q", "-m", "invalid committed plan")
    calls: list[str] = []

    def forbidden_observer(*args: object, **_kwargs: object) -> Any:
        calls.append(str(args[0]))
        raise AssertionError("invalid current plan must refuse before observation")

    monkeypatch.setattr(checker_module, "_observe_anchored", forbidden_observer)

    # Act
    findings = execute_live_gates_v1(stale_plan, root)

    # Assert: the committed sealed plan owns semantics; the stale caller never
    # reaches an observer even though the witness repository is clean.
    assert _git(root, "status", "--porcelain=v2", "--untracked-files=all") == ""
    assert calls == []
    assert [item.rule_id for item in findings] == ["plan_field_set_not_closed"]


def test_direct_execution_requires_exact_equality_with_valid_committed_plan(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: the current committed JSON remains structurally valid and keeps
    # the same rendered Markdown, but differs from the stale caller mapping.
    root = tmp_path / "subject"
    subprocess.run(
        ["/usr/bin/git", "clone", "-q", "--no-hardlinks", str(ROOT), str(root)],
        check=True,
        capture_output=True,
        text=True,
    )
    stale_plan = copy.deepcopy(dict(load_plan_v1(root)))
    current_plan = copy.deepcopy(stale_plan)
    current_plan["regeneration"]["check_command"] = (
        "python3 tools/check_whole_program_plan_v1.py --json --exact-current"
    )
    assert render_generated_markdown_v1(current_plan) == render_generated_markdown_v1(
        stale_plan
    )
    (root / PLAN_JSON_PATH).write_text(
        canonical_plan_json_v1(current_plan), encoding="utf-8"
    )
    _git(root, "add", PLAN_JSON_PATH.as_posix())
    _git(root, "commit", "-q", "-m", "valid current plan")
    calls: list[str] = []

    def forbidden_observer(*args: object, **_kwargs: object) -> Any:
        calls.append(str(args[0]))
        raise AssertionError("stale caller plan must refuse before observation")

    monkeypatch.setattr(checker_module, "_observe_anchored", forbidden_observer)

    # Act
    findings = execute_live_gates_v1(stale_plan, root)

    # Assert: both values validate, then exact committed-byte equality decides.
    assert _git(root, "status", "--porcelain=v2", "--untracked-files=all") == ""
    assert calls == []
    assert [item.rule_id for item in findings] == [
        "caller_plan_artifact_mismatch"
    ]


def test_execute_validates_every_full_row_into_an_immutable_effect_plan_before_any_observer_call(monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: any observer call fails the test; only the LAST row is malformed in each variant.
    calls: list[object] = []

    def counting_refusal(*args: object, **kwargs: object) -> object:
        calls.append(args)
        return _refuse_gate_execution()

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", counting_refusal)
    variants: dict[str, tuple[str, object, str]] = {
        "purpose_empty": ("purpose", "", "live_gate_purpose_missing"),
        "purpose_list": ("purpose", [], "live_gate_purpose_missing"),
        "observed_list": ("observed", [], "live_gate_observed_malformed"),
        "exit_code_bool": ("exit_code", True, "live_gate_exit_code_malformed"),
        "checker_digest_stale": ("checker_sha256", "0" * 64, "live_gate_checker_hash_drift"),
        "observed_keys_wrong": ("observed", {"nothing": 1}, "live_gate_observed_projection_mismatch"),
    }

    # Act / Assert
    owner = ConfinedRootV1.bind(ROOT)
    for name, (field, value, expected_rule) in variants.items():
        plan = _plan()
        plan["live_gates"][-1][field] = value
        effects, effect_findings = plan_live_gate_effects_v1(plan["live_gates"], owner)
        rules = {item.rule_id for item in execute_live_gates_v1(plan, ROOT)}
        assert effects == () and expected_rule in {item.rule_id for item in effect_findings}, name
        assert expected_rule in rules, name
    valid_effects, valid_findings = plan_live_gate_effects_v1(_plan()["live_gates"], owner)
    try:
        assert valid_findings == [] and isinstance(valid_effects, tuple)
        assert [effect.spec.gate_id for effect in valid_effects] == sorted(LIVE_GATE_REGISTRY)
        assert all(isinstance(effect.expected_observed, tuple) for effect in valid_effects)
        expected_artifact_digests = {
            path.as_posix(): hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            for path in (PLAN_JSON_PATH, PLAN_MARKDOWN_PATH)
        }
        assert all(
            dict(effect._artifact_digests) == expected_artifact_digests
            for effect in valid_effects
        )
        with pytest.raises(dataclasses.FrozenInstanceError):
            valid_effects[0].expected_exit_code = 1  # type: ignore[misc]
    finally:
        _close_effects(valid_effects)
        owner.close()
    assert calls == []


def test_pre_regeneration_phase_tolerates_only_the_values_regeneration_rewrites() -> None:
    # Arrange: stale observations, snapshot, cleanliness flag, and checker digest, plus one structural defect.
    stale = _plan()
    stale["subject"]["source_snapshot_sha256"] = "f" * 64
    stale["subject"]["scoped_worktree_clean"] = False
    _gate(stale, FAST_GATE_ID)["checker_sha256"] = "0" * 64
    _gate(stale, FAST_GATE_ID)["observed"] = {}
    _gate(stale, FAST_GATE_ID)["exit_code"] = 99
    structural = copy.deepcopy(stale)
    del structural["tasks"][0]["notes"]

    # Act
    ordinary_rules = _rules(stale)
    profile = PlanValidationProfileV1.pre_regeneration()
    pre_rules = [item.rule_id for item in validate_plan_v1(stale, root=ROOT, markdown=_markdown(), profile=profile)]
    structural_rules = [item.rule_id for item in validate_plan_v1(structural, root=ROOT, markdown=_markdown(), profile=profile)]

    # Assert: ordinary validation reports every drift; pre-regeneration reports only structure.
    assert ordinary_rules == [
        "live_gate_checker_hash_drift",
        "live_gate_observed_projection_mismatch",
        "plan_markdown_generated_block_drift",
        "scoped_worktree_clean_misrecorded",
        "source_snapshot_drift",
    ]
    assert pre_rules == []
    assert structural_rules == ["task_field_set_not_closed"]
    assert profile.kind is PlanValidationKindV1.PRE_REGENERATION and profile.cleanliness is CleanlinessScopeV1.REGENERATION


VALID_OID = "a" * 40


def _record(mode: str, object_type: str, oid: str, path: bytes) -> bytes:
    return f"{mode} {object_type} {oid}\t".encode("ascii") + path


@pytest.mark.parametrize(
    ("record", "reason"),
    [
        (_record("100644", "commit", VALID_OID, b"a.txt"), "mode/type"),
        (_record("160000", "blob", VALID_OID, b"sub"), "mode/type"),
        (_record("120000", "tree", VALID_OID, b"link"), "mode/type"),
        (_record("040000", "tree", VALID_OID, b"dir"), "mode/type"),
        (_record("100664", "blob", VALID_OID, b"a.txt"), "mode/type"),
        (_record("100644", "blob", "0" * 40, b"a.txt"), "nonzero"),
        (_record("100644", "blob", "A" * 40, b"a.txt"), "nonzero"),
        (_record("100644", "blob", "a" * 39, b"a.txt"), "nonzero"),
        (_record("100644", "blob", "a" * 41, b"a.txt"), "nonzero"),
        (_record("100644", "blob", VALID_OID, b""), "canonical"),
        (_record("100644", "blob", VALID_OID, b"/etc/passwd"), "canonical"),
        (_record("100644", "blob", VALID_OID, b"a/../b.txt"), "canonical"),
        (_record("100644", "blob", VALID_OID, b"./a.txt"), "canonical"),
        (_record("100644", "blob", VALID_OID, b".."), "canonical"),
        (_record("100644", "blob", VALID_OID, b"a//b.txt"), "canonical"),
        (_record("100644", "blob", VALID_OID, b"a/"), "canonical"),
        (_record("100644", "blob", VALID_OID, b"a\\b.txt"), "canonical"),
        (_record("100644", "blob", VALID_OID, b"a\x01b.txt"), "canonical"),
        (_record("100644", "blob", VALID_OID, b"a\x7fb.txt"), "canonical"),
        (_record("100644", "blob", VALID_OID, b"\xff.txt"), "canonical"),
        (_record("100644", "blob", VALID_OID, b"/".join([b"d"] * 65)), "canonical"),
        (b"100644 blob " + VALID_OID.encode("ascii") + b" a.txt", "record is not"),
        (b"100644 blob " + VALID_OID.encode("ascii") + b" extra\ta.txt", "record is not"),
        (b"100644\tblob " + VALID_OID.encode("ascii") + b"\ta.txt", "record is not"),
        (_record("100644", "commit", VALID_OID, PLAN_JSON_PATH.as_posix().encode("ascii")), "mode/type"),
    ],
)
def test_source_snapshot_rejects_hostile_tree_records(record: bytes, reason: str) -> None:
    # Act
    entries, findings = snapshot_entries_from_listing_v1(record + b"\0")

    # Assert: nothing is digested and the defect is a typed finding naming the reason.
    assert entries == []
    assert [item.rule_id for item in findings] == ["source_snapshot_entry_malformed"]
    assert reason in findings[0].evidence


def test_source_snapshot_accepts_exact_mode_type_pairs_and_rejects_duplicates() -> None:
    # Arrange
    accepted = b"".join(
        record + b"\0"
        for record in (
            _record("100644", "blob", VALID_OID, b"a.txt"),
            _record("100755", "blob", VALID_OID, b"bin/run"),
            _record("120000", "blob", VALID_OID, b"link"),
            _record("160000", "commit", VALID_OID, b"vendor/sub"),
            _record("100644", "blob", VALID_OID, "docs/ünïcode.md".encode("utf-8")),
            _record("100644", "blob", VALID_OID, b"/".join([b"d"] * 64)),
            _record("100644", "blob", VALID_OID, PLAN_JSON_PATH.as_posix().encode("ascii")),
        )
    )
    duplicated = accepted + _record("100644", "blob", "b" * 40, b"a.txt") + b"\0"

    # Act
    entries, findings = snapshot_entries_from_listing_v1(accepted)
    _entries, duplicate_findings = snapshot_entries_from_listing_v1(duplicated)

    # Assert: the plan artifact is validated but excluded from the digest.
    assert findings == []
    assert [os.fsdecode(entry[0]) for entry in entries] == ["a.txt", "bin/run", "link", "vendor/sub", "docs/ünïcode.md", "/".join(["d"] * 64)]
    assert [item.rule_id for item in duplicate_findings] == ["source_snapshot_entry_duplicate"]


def test_source_snapshot_digests_real_symlink_and_gitlink_entries(tmp_path: Path) -> None:
    # Arrange: a committed regular file, symlink, and gitlink in a synthetic repository.
    repo, base = _synthetic_repository(tmp_path)
    os.symlink("a.txt", repo / "link")
    _git(repo, "add", "link")
    _git(repo, "update-index", "--add", "--cacheinfo", f"160000,{base},vendor/sub")
    _git(repo, "commit", "-q", "-m", "entries")

    # Act
    snapshot, findings = source_snapshot_v1(repo)
    listing = _git(repo, "ls-tree", "-r", "--full-tree", "HEAD")

    # Assert
    assert findings == [] and snapshot is not None and snapshot.entry_count == 3
    assert "120000 blob" in listing and "160000 commit" in listing


def test_execute_live_gates_requires_the_exact_registry_set_before_any_execution(monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: every gate refuses to execute, so reaching execution fails the test.
    monkeypatch.setattr(checker_module, "observe_live_gate_v1", _refuse_gate_execution)
    gates = _plan()["live_gates"]
    variants = {
        "subset": gates[:-1],
        "duplicate": [*gates, copy.deepcopy(gates[0])],
        "extra": [*gates, {**copy.deepcopy(gates[0]), "gate_id": "zz_unregistered"}],
        "reordered": [gates[1], gates[0], *gates[2:]],
        "not_a_list": {gate["gate_id"]: gate for gate in gates},
    }

    # Act / Assert
    for name, rows in variants.items():
        plan = _plan()
        plan["live_gates"] = rows
        rules = {item.rule_id for item in execute_live_gates_v1(plan, ROOT)}
        expected = "live_gates_malformed" if name == "not_a_list" else "live_gate_registry_set_mismatch"
        assert expected in rules, name


def test_every_dependency_must_precede_its_dependent_in_canonical_task_order() -> None:
    # Arrange: reproduce the original defect shape, a certificate at P6-T09 depending on P6-T10.
    plan = _plan()
    _task(plan, "P6-T10")["depends_on"] = ["P6-T08"]
    _task(plan, "P6-T09")["depends_on"].append("P6-T10")

    # Act / Assert
    assert all(dep < task["task_id"] for task in _plan()["tasks"] for dep in task["depends_on"])
    assert _task(_plan(), "P6-T10")["depends_on"] == ["P6-T08", "P6-T09"]
    rules = _rules(plan)
    assert "task_dependency_not_ordered" in rules
    assert "task_dependency_cycle" not in rules


def test_markdown_narrative_base_defect_range_must_end_at_the_highest_registered_finding() -> None:
    # Arrange: the stale narrative that shipped ("B-01 through B-04" while B-05 was registered).
    stale = _markdown().replace("`B-01` through `B-05`", "`B-01` through `B-04`")
    plan = _plan()
    registry = plan["finding_registry"]
    index = next(i for i, row in enumerate(registry) if row["finding_id"] == "B-05")
    registry.insert(index + 1, {**copy.deepcopy(registry[index]), "finding_id": "B-06"})

    # Act
    stale_rules = [item.rule_id for item in validate_plan_v1(_plan(), root=ROOT, markdown=stale)]
    registry_rules = _rules(plan)

    # Assert
    assert stale != _markdown()
    assert stale_rules == ["plan_markdown_narrative_stale_finding_range"]
    assert "plan_markdown_narrative_stale_finding_range" in registry_rules


def test_bound_artifact_record_is_immutable_and_forced_byte_mutation_refuses_before_observation(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange: bind a real exact-HEAD context, then model same-process mutation through the documented non-unforgeability seam.
    observer_calls: list[object] = []

    def forbidden_observer(*args: object, **_kwargs: object) -> object:
        observer_calls.append(args)
        raise AssertionError("a mutated artifact context must refuse before observation")

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", forbidden_observer)
    root = _clone_complete_subject(tmp_path)
    with ConfinedRootV1.bind(root) as bound:
        context, findings = checker_module._bind_execution_context_v1(
            bound, subject="artifact_immutability"
        )
        assert context is not None and findings == []
        artifact = context._artifacts.artifacts[0]
        original_data = artifact.data
        try:
            # Act / Assert, construction boundary: normal mutation is unavailable.
            with pytest.raises(dataclasses.FrozenInstanceError):
                artifact.data = b"hostile"  # type: ignore[misc]

            # Act, hostile same-process mutation: defensive revalidation still refuses without a gate call.
            object.__setattr__(artifact, "data", b"hostile")
            execution_findings, executed = checker_module._execute_live_gates_with_count_v1(
                dict(load_plan_v1(root)), bound, context=context
            )
        finally:
            object.__setattr__(artifact, "data", original_data)
            context.close()

    # Assert: the report never trusts a stale digest after the held data changes.
    assert executed == 0 and observer_calls == []
    assert "plan_artifact_data_digest_mismatch" in {
        finding.rule_id for finding in execution_findings
    }


@pytest.mark.parametrize(
    ("projection", "case"),
    (
        (lambda artifacts: artifacts[:1], "missing_markdown"),
        (lambda artifacts: tuple(reversed(artifacts)), "reordered_pair"),
    ),
)
def test_bound_artifact_pair_requires_the_exact_ordered_two_item_spec_before_observation(
    projection: Callable[[tuple[Any, ...]], tuple[Any, ...]],
    case: str,
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange
    observer_calls: list[object] = []

    def forbidden_observer(*args: object, **_kwargs: object) -> object:
        observer_calls.append(args)
        raise AssertionError("an incomplete or reordered bound pair must refuse before observation")

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", forbidden_observer)
    root = _clone_complete_subject(tmp_path)
    with ConfinedRootV1.bind(root) as bound:
        context, findings = checker_module._bind_execution_context_v1(
            bound, subject=f"artifact_pair.{case}"
        )
        assert context is not None and findings == []
        artifacts = context._artifacts
        original_pair = artifacts.artifacts
        replacement_pair = projection(original_pair)
        try:
            # Act / Assert, construction boundary: ordinary code cannot swap the ordered pair.
            with pytest.raises(dataclasses.FrozenInstanceError):
                artifacts.artifacts = replacement_pair  # type: ignore[misc]

            # Act: the documented same-process convention is still checked before any execution.
            object.__setattr__(artifacts, "artifacts", replacement_pair)
            execution_findings, executed = checker_module._execute_live_gates_with_count_v1(
                dict(load_plan_v1(root)), bound, context=context
            )
        finally:
            object.__setattr__(artifacts, "artifacts", original_pair)
            context.close()

    # Assert
    assert executed == 0 and observer_calls == []
    assert "plan_artifact_binding_shape_invalid" in {
        finding.rule_id for finding in execution_findings
    }


def test_plan_artifact_binding_closes_the_current_source_after_memory_error(tmp_path: Path) -> None:
    # Arrange: fail after the first source and its sealed memfd have been acquired.
    original_read = artifact_binding_module.AnchoredFileV1.read

    def raise_memory_error(_source: object, _max_bytes: int) -> bytes | None:
        raise MemoryError("review-injected")

    fd_before = len(os.listdir("/proc/self/fd"))

    # Act
    try:
        artifact_binding_module.AnchoredFileV1.read = raise_memory_error  # type: ignore[method-assign]
        with pytest.raises(MemoryError, match="review-injected"):
            with ConfinedRootV1.bind(_clone_complete_subject(tmp_path)) as bound:
                checker_module._bind_execution_context_v1(bound, subject="memory_error")
    finally:
        artifact_binding_module.AnchoredFileV1.read = original_read  # type: ignore[method-assign]

    # Assert: the current source has no chance to leak if non-OSError construction aborts.
    assert len(os.listdir("/proc/self/fd")) == fd_before


def test_plan_artifact_binding_closes_the_current_source_after_record_construction_memory_error(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange: the source is open when immutable-record construction itself aborts.
    def raise_constructor_memory_error(*_args: object, **_kwargs: object) -> object:
        raise MemoryError("review-injected-record-construction")

    monkeypatch.setattr(
        artifact_binding_module,
        "BoundPlanArtifactV1",
        raise_constructor_memory_error,
    )
    fd_before = len(os.listdir("/proc/self/fd"))

    # Act / Assert: BaseException cleanup retains the original failure and closes the untransferred source.
    with pytest.raises(MemoryError, match="review-injected-record-construction"):
        with ConfinedRootV1.bind(_clone_complete_subject(tmp_path)) as bound:
            checker_module._bind_execution_context_v1(bound, subject="record_construction_failure")
    assert len(os.listdir("/proc/self/fd")) == fd_before


def test_plan_artifact_binding_preserves_memory_error_and_closes_current_source_when_prior_cleanup_fails(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange: one artifact transfers ownership, the second read fails, and the first close itself raises after closing.
    original_read = artifact_binding_module.AnchoredFileV1.read
    original_close = artifact_binding_module.BoundPlanArtifactV1.close
    read_count = 0

    def second_read_fails(source: object, max_bytes: int) -> bytes | None:
        nonlocal read_count
        read_count += 1
        if read_count == 1:
            return original_read(source, max_bytes)  # type: ignore[arg-type]
        raise MemoryError("review-injected-second-source")

    def close_then_raise(artifact: object) -> None:
        original_close(artifact)  # type: ignore[arg-type]
        raise RuntimeError("review-injected-cleanup")

    monkeypatch.setattr(artifact_binding_module.AnchoredFileV1, "read", second_read_fails)
    monkeypatch.setattr(artifact_binding_module.BoundPlanArtifactV1, "close", close_then_raise)
    fd_before = len(os.listdir("/proc/self/fd"))

    # Act / Assert: primary failure remains typed and every owned descriptor receives cleanup.
    with pytest.raises(MemoryError, match="review-injected-second-source"):
        with ConfinedRootV1.bind(_clone_complete_subject(tmp_path)) as bound:
            checker_module._bind_execution_context_v1(bound, subject="cleanup_failure")
    assert len(os.listdir("/proc/self/fd")) == fd_before


def test_plan_artifact_pair_construction_failure_closes_every_descriptor(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    def fail_pair_construction(*_args: object, **_kwargs: object) -> object:
        raise MemoryError("review-pair-construction")

    root = _clone_complete_subject(tmp_path)
    with ConfinedRootV1.bind(root) as bound:
        head = checker_module._git(bound, ["rev-parse", "HEAD"])[1]
        fd_before = len(os.listdir("/proc/self/fd"))
        monkeypatch.setattr(
            artifact_binding_module,
            "BoundPlanArtifactsV1",
            fail_pair_construction,
        )

        with pytest.raises(MemoryError, match="review-pair-construction"):
            artifact_binding_module.bind_plan_artifacts_v1(
                bound.anchored, head
            )

        assert len(os.listdir("/proc/self/fd")) == fd_before


def test_execution_context_construction_failure_closes_bound_artifacts(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    def fail_context_construction(*_args: object, **_kwargs: object) -> object:
        raise MemoryError("review-context-construction")

    root = _clone_complete_subject(tmp_path)
    with ConfinedRootV1.bind(root) as bound:
        fd_before = len(os.listdir("/proc/self/fd"))
        monkeypatch.setattr(
            checker_module,
            "ExecutionContextV1",
            fail_context_construction,
        )

        with pytest.raises(MemoryError, match="review-context-construction"):
            checker_module._bind_execution_context_v1(
                bound, subject="review"
            )

        assert len(os.listdir("/proc/self/fd")) == fd_before


def test_integrity_refusal_preserves_primary_finding_when_cleanup_fails(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    original_close = artifact_binding_module.BoundPlanArtifactV1.close

    def refuse_integrity(
        _artifacts: object, _root: object, *, expected_head: str
    ) -> tuple[artifact_binding_module.PlanArtifactBindingFindingV1, ...]:
        del expected_head
        return (
            artifact_binding_module.PlanArtifactBindingFindingV1(
                "plan_artifact_head_blob_mismatch",
                "plan_artifacts",
                "review-primary",
            ),
        )

    def close_then_raise(
        artifact: artifact_binding_module.BoundPlanArtifactV1,
    ) -> None:
        original_close(artifact)
        raise RuntimeError("review-cleanup")

    monkeypatch.setattr(
        artifact_binding_module.BoundPlanArtifactsV1,
        "integrity_findings",
        refuse_integrity,
    )
    monkeypatch.setattr(
        artifact_binding_module.BoundPlanArtifactV1,
        "close",
        close_then_raise,
    )
    root = _clone_complete_subject(tmp_path)
    with ConfinedRootV1.bind(root) as bound:
        head = checker_module._git(bound, ["rev-parse", "HEAD"])[1]
        fd_before = len(os.listdir("/proc/self/fd"))

        artifacts, findings = artifact_binding_module.bind_plan_artifacts_v1(
            bound.anchored, head
        )

        assert artifacts is None
        assert [finding.rule_id for finding in findings] == [
            "plan_artifact_head_blob_mismatch",
            "plan_artifact_cleanup_refused",
        ]
        assert len(os.listdir("/proc/self/fd")) == fd_before


def test_git_replacement_objects_cannot_retarget_raw_snapshot_status_or_plan_artifact_binding(
    tmp_path: Path,
) -> None:
    # Arrange: a raw commit and a replacement commit disagree on both an ordinary source and the two bound artifacts.
    root = tmp_path / "replacement-subject"
    root.mkdir()
    _git(root, "init", "-q", "-b", "main")
    (root / "docs" / "research").mkdir(parents=True)
    (root / "a.txt").write_text("raw source\n", encoding="utf-8")
    (root / PLAN_JSON_PATH).write_bytes(b'{"artifact":"raw"}\n')
    (root / PLAN_MARKDOWN_PATH).write_text("raw markdown\n", encoding="utf-8")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "raw subject")
    raw_head = _git(root, "rev-parse", "HEAD")
    raw_snapshot, raw_snapshot_findings = source_snapshot_v1(root)
    assert raw_snapshot is not None and raw_snapshot_findings == []

    (root / "a.txt").write_text("replacement source\n", encoding="utf-8")
    (root / PLAN_JSON_PATH).write_bytes(b'{"artifact":"replacement"}\n')
    (root / PLAN_MARKDOWN_PATH).write_text("replacement markdown\n", encoding="utf-8")
    _git(root, "add", "-A")
    replacement_head = _replacement_commit_for_head(root, raw_head, "replacement subject")
    _git(root, "checkout", "-q", "--force", "--detach", raw_head)
    _replace_aware_git(root, "replace", raw_head, replacement_head)
    _replace_aware_git(root, "checkout", "-q", "--force", "--detach", raw_head)
    assert (root / "a.txt").read_text(encoding="utf-8") == "replacement source\n"

    # Act
    status_code, raw_status = git_v1(root, ["status", "--porcelain=v2", "--untracked-files=all"])
    observed_snapshot, observed_snapshot_findings = source_snapshot_v1(root)
    with AnchoredDirectoryV1.open(root) as anchored:
        bound_artifacts, binding_findings = artifact_binding_module.bind_plan_artifacts_v1(
            anchored, raw_head, checker_module.PLAN_ARTIFACT_SPECS_V1
        )
        if bound_artifacts is not None:
            bound_artifacts.close()

    # Assert: every Git-derived branch sees the raw object graph and the sealed worktree pair refuses it.
    assert status_code == 0 and raw_status
    assert observed_snapshot_findings == [] and observed_snapshot == raw_snapshot
    assert bound_artifacts is None
    assert {finding.rule_id for finding in binding_findings} == {
        "plan_artifact_head_blob_mismatch"
    }
    assert {finding.subject for finding in binding_findings} == {
        PLAN_JSON_PATH.as_posix(),
        PLAN_MARKDOWN_PATH.as_posix(),
    }


def test_replacement_commit_cannot_reach_any_whole_program_observer(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: materialize a valid replacement plan at the same raw HEAD through a replacement ref.
    root = tmp_path / "subject"
    subprocess.run(
        ["/usr/bin/git", "clone", "-q", "--no-hardlinks", str(ROOT), str(root)],
        check=True,
        capture_output=True,
        text=True,
    )
    raw_head = _git(root, "rev-parse", "HEAD")
    replacement_plan = copy.deepcopy(dict(load_plan_v1(root)))
    replacement_plan["tasks"][0]["notes"] = "replacement-ref semantic witness"
    (root / PLAN_JSON_PATH).write_text(canonical_plan_json_v1(replacement_plan), encoding="utf-8")
    _git(root, "add", PLAN_JSON_PATH.as_posix())
    replacement_head = _replacement_commit_for_head(root, raw_head, "replacement plan semantics")
    _git(root, "checkout", "-q", "--force", "--detach", raw_head)
    _replace_aware_git(root, "replace", raw_head, replacement_head)
    _replace_aware_git(root, "checkout", "-q", "--force", "--detach", raw_head)
    observer_calls: list[str] = []

    def forbidden_observer(spec: Any, _root: object, **_kwargs: object) -> object:
        observer_calls.append(spec.gate_id)
        raise AssertionError("a replacement commit must refuse before any observer")

    monkeypatch.setattr(checker_module, "observe_live_gate_v1", forbidden_observer)

    # Act
    report = check_whole_program_plan_v1(root, mode=PlanCheckModeV1.EXECUTE)

    # Assert: the raw subject sees a dirty worktree and cannot turn the replacement's valid plan into evidence.
    assert report["ok"] is False and report["executed_live_gates"] == 0
    assert observer_calls == []
    assert "scoped_worktree_dirty" in {
        finding["rule_id"] for finding in report["findings"]
    }
