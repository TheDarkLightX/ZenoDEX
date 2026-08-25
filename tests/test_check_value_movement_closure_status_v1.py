from __future__ import annotations

import hashlib
import json
import subprocess
from copy import deepcopy
from pathlib import Path
from typing import cast

from tools.check_value_movement_closure_status_v1 import (
    DEFAULT_STATUS_PATH,
    M6_ATDD_PATH,
    REPO_ROOT,
    _git_blob_sha256_v1,
    check_value_movement_closure_status_v1,
    validate_m6_zdex_semantic_anchor_v1,
)


def _status() -> dict[str, object]:
    return json.loads((REPO_ROOT / DEFAULT_STATUS_PATH).read_text(encoding="utf-8"))


def _write_status(tmp_path: Path, value: dict[str, object]) -> Path:
    path = tmp_path / "status.json"
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")
    return path


def _implemented_slices(value: dict[str, object]) -> list[dict[str, object]]:
    return cast(list[dict[str, object]], value["implemented_slices"])


def _findings(report: dict[str, object]) -> list[str]:
    return cast(list[str], report["findings"])


def _replay_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in _implemented_slices(value)
        if row["id"] == "ECONOMIC_INITIAL_STATE_REPLAY_PRESERVATION_V1"
    )


def _source_head_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in _implemented_slices(value)
        if row["id"] == "ECONOMIC_INITIAL_STATE_SOURCE_HEAD_ACTIVATION_V1"
    )


def _durable_activation_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in _implemented_slices(value)
        if row["id"] == "GLOBAL_ECONOMIC_DURABLE_ACTIVATION_JOURNAL_V1"
    )


def _durable_epoch_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in _implemented_slices(value)
        if row["id"] == "GLOBAL_ECONOMIC_DURABLE_EPOCH_JOURNAL_V1"
    )


def _durable_publisher_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in _implemented_slices(value)
        if row["id"] == "GLOBAL_ECONOMIC_DURABLE_PUBLISHER_V1"
    )


def _current_authority_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in _implemented_slices(value)
        if row["id"] == "GLOBAL_ECONOMIC_CURRENT_AUTHORITY_HEAD_V1"
    )


def _monotonic_anchor_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in _implemented_slices(value)
        if row["id"] == "GLOBAL_ECONOMIC_MONOTONIC_ANCHOR_V1"
    )


def _publisher_bound_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in _implemented_slices(value)
        if row["id"] == "PUBLISHER_BOUND_EPOCH_VERIFICATION"
    )


def test_current_value_movement_closure_status_is_exact_and_fail_closed() -> None:
    report = check_value_movement_closure_status_v1()

    assert report["ok"] is True
    assert _findings(report) == []
    assert report["gate_count"] == 12
    assert report["production_authority"] == "NONE"


def test_checker_rejects_authority_gate_and_semantic_promotion_drift(
    tmp_path: Path,
) -> None:
    mutated = deepcopy(_status())
    mutated["authority"]["production_authority"] = "GLOBAL_EPOCH"  # type: ignore[index]
    mutated["gate_status"] = mutated["gate_status"][:-1]  # type: ignore[index]
    mutated["semantic_anchors"]["buy_and_burn"] = "burn treasury ZDEX"  # type: ignore[index]
    mutated["claim_contract"]["status"] = "PROVED"  # type: ignore[index]

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "authority or readiness nonclaim drift" in _findings(report)
    assert "VM gate IDs must be complete and ordered" in _findings(report)
    assert "buy-and-burn semantic anchor drift" in _findings(report)
    assert "claim status drift" in _findings(report)
    assert report["production_authority"] == "NONE"


def test_checker_rejects_stale_claim_hash_and_duplicate_json_key(tmp_path: Path) -> None:
    stale = deepcopy(_status())
    stale["claim_contract"]["sha256"] = "0" * 64  # type: ignore[index]
    stale_report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, stale)
    )

    duplicate_path = tmp_path / "duplicate.json"
    duplicate_path.write_text('{"schema":"a","schema":"b"}', encoding="utf-8")
    duplicate_report = check_value_movement_closure_status_v1(
        status_path=duplicate_path
    )

    assert stale_report["ok"] is False
    assert "claim contract hash mismatch" in _findings(stale_report)
    assert duplicate_report["ok"] is False
    assert "duplicate JSON key" in _findings(duplicate_report)[0]


def test_checker_rejects_stale_replay_slice_evidence(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    replay = _replay_slice(mutated)
    replay["commit"] = "0" * 40
    replay["python_sha256"] = "0" * 64
    replay["golden_continuity_root"] = "0x" + "0" * 64

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "replay slice implementation commit mismatch" in _findings(report)
    assert (
        "replay slice artifact hash mismatch: python_sha256" in _findings(report)
    )
    assert (
        "replay slice golden evidence mismatch: golden_continuity_root"
        in _findings(report)
    )


def test_checker_rejects_stale_source_head_slice_evidence(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    source_head = _source_head_slice(mutated)
    source_head["commit"] = "0" * 40
    source_head["python_commit_port_sha256"] = "0" * 64

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "source-head slice subject commit mismatch" in _findings(report)
    assert (
        "source-head slice artifact hash mismatch: python_commit_port_sha256"
        in _findings(report)
    )


def test_checker_rejects_stale_durable_activation_slice_evidence(
    tmp_path: Path,
) -> None:
    mutated = deepcopy(_status())
    durable = _durable_activation_slice(mutated)
    durable["commit"] = "0" * 40
    durable["artifact_subject_commit"] = "1" * 40
    durable["python_journal_sha256"] = "0" * 64

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert (
        "durable activation slice implementation commit mismatch"
        in _findings(report)
    )
    assert (
        "durable activation slice artifact subject commit mismatch"
        in _findings(report)
    )
    assert (
        "durable activation slice artifact hash mismatch: python_journal_sha256"
        in _findings(report)
    )


def test_checker_rejects_stale_durable_epoch_slice_evidence(
    tmp_path: Path,
) -> None:
    mutated = deepcopy(_status())
    durable = _durable_epoch_slice(mutated)
    durable["commit"] = "0" * 40
    durable["artifact_subject_commit"] = "1" * 40
    durable["python_journal_sha256"] = "0" * 64

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "durable epoch slice implementation commit mismatch" in _findings(report)
    assert "durable epoch slice artifact subject commit mismatch" in _findings(report)
    assert (
        "durable epoch slice artifact hash mismatch: python_journal_sha256"
        in _findings(report)
    )


def test_checker_rejects_stale_durable_publisher_slice_evidence(
    tmp_path: Path,
) -> None:
    mutated = deepcopy(_status())
    publisher = _durable_publisher_slice(mutated)
    publisher["commit"] = "0" * 40
    publisher["artifact_subject_commit"] = "1" * 40
    publisher["python_publisher_sha256"] = "0" * 64
    publisher["python_verifier_deployment_sha256"] = "2" * 64

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert (
        "durable publisher slice implementation commit mismatch"
        in _findings(report)
    )
    assert (
        "durable publisher slice artifact subject commit mismatch"
        in _findings(report)
    )
    assert (
        "durable publisher slice artifact hash mismatch: python_publisher_sha256"
        in _findings(report)
    )
    assert (
        "durable publisher slice artifact hash mismatch: "
        "python_verifier_deployment_sha256"
        in _findings(report)
    )


def test_checker_rejects_stale_current_authority_slice_evidence(
    tmp_path: Path,
) -> None:
    # Arrange: the authority row claims a foreign commit and stale core artifact.
    mutated = deepcopy(_status())
    authority = _current_authority_slice(mutated)
    authority["commit"] = "0" * 40
    authority["artifact_subject_commit"] = "1" * 40
    authority["python_core_sha256"] = "2" * 64

    # Act: check the forged authority evidence row.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: commit, subject, and content bindings all fail closed.
    findings = _findings(report)
    assert report["ok"] is False
    assert "current authority slice implementation commit mismatch" in findings
    assert "current authority slice artifact subject commit mismatch" in findings
    assert (
        "current authority slice artifact hash mismatch: python_core_sha256"
        in findings
    )


def test_checker_rejects_stale_monotonic_anchor_slice_evidence(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory retargets the anchor slice and substitutes its core hash.
    mutated = deepcopy(_status())
    anchor = _monotonic_anchor_slice(mutated)
    anchor["commit"] = "0" * 40
    anchor["artifact_subject_commit"] = "1" * 40
    anchor["python_core_sha256"] = "2" * 64

    # Act
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: release, subject tree, and exact code all remain checker-owned.
    findings = _findings(report)
    assert report["ok"] is False
    assert "monotonic anchor slice implementation commit mismatch" in findings
    assert "monotonic anchor slice artifact subject commit mismatch" in findings
    assert "monotonic anchor slice artifact hash mismatch: python_core_sha256" in (
        findings
    )


def test_checker_binds_artifacts_to_exact_subject_tree(tmp_path: Path) -> None:
    # Arrange: Mallory retains current hashes while claiming the parent subject.
    mutated = deepcopy(_status())
    mutated["subject"]["commit"] = "d064088b851311a72c879daa608e80fdee23e0d3"  # type: ignore[index]
    publisher = _durable_publisher_slice(mutated)
    publisher["artifact_subject_commit"] = mutated["subject"]["commit"]  # type: ignore[index]

    # Act: validate the forged exact-subject evidence packet.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: live-file equality cannot substitute for equality to the Git blob.
    assert report["ok"] is False
    assert (
        "durable publisher slice subject-tree artifact mismatch: "
        "python_verifier_deployment_sha256"
        in _findings(report)
    )


def test_checker_requires_proof_admission_artifacts(tmp_path: Path) -> None:
    # Arrange: erase both proof-admission bindings from an otherwise exact ledger.
    mutated = deepcopy(_status())
    publisher = _durable_publisher_slice(mutated)
    publisher["python_proof_sha256"] = "0" * 64
    publisher_bound = _publisher_bound_slice(mutated)
    publisher_bound["core_sha256"] = "0" * 64

    # Act: validate the evidence packet with unbound receipt-admission code.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: neither implemented-slice row can silently omit proof admission.
    assert report["ok"] is False
    assert (
        "durable publisher slice artifact hash mismatch: python_proof_sha256"
        in _findings(report)
    )
    assert (
        "publisher-bound slice artifact hash mismatch: core_sha256"
        in _findings(report)
    )


def test_subject_blob_lookup_ignores_git_replacement_objects(tmp_path: Path) -> None:
    # Arrange: Mallory installs a local replacement commit for the named subject.
    repository = tmp_path / "replacement-object-repository"
    subprocess.run(["git", "init", "--quiet", repository], check=True)
    artifact = repository / "artifact.txt"
    artifact.write_text("original\n", encoding="utf-8")
    subprocess.run(["git", "-C", repository, "add", "artifact.txt"], check=True)
    subprocess.run(
        [
            "git",
            "-C",
            repository,
            "-c",
            "user.name=Closure Test",
            "-c",
            "user.email=closure-test@example.invalid",
            "commit",
            "--quiet",
            "-m",
            "original",
        ],
        check=True,
    )
    original_commit = subprocess.run(
        ["git", "-C", repository, "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    artifact.write_text("replacement\n", encoding="utf-8")
    subprocess.run(["git", "-C", repository, "add", "artifact.txt"], check=True)
    replacement_tree = subprocess.run(
        ["git", "-C", repository, "write-tree"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    replacement_commit = subprocess.run(
        [
            "git",
            "-C",
            repository,
            "-c",
            "user.name=Closure Test",
            "-c",
            "user.email=closure-test@example.invalid",
            "commit-tree",
            replacement_tree,
            "-m",
            "replacement",
        ],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    subprocess.run(
        ["git", "-C", repository, "replace", original_commit, replacement_commit],
        check=True,
    )
    replaced = subprocess.run(
        ["git", "-C", repository, "cat-file", "blob", f"{original_commit}:artifact.txt"],
        check=True,
        capture_output=True,
    ).stdout
    assert replaced == b"replacement\n"

    # Act: resolve the same subject through the closure checker's exact lookup.
    observed = _git_blob_sha256_v1(
        repository,
        original_commit,
        Path("artifact.txt"),
    )

    # Assert: local replace refs cannot alter the subject-tree oracle.
    assert observed == hashlib.sha256(b"original\n").hexdigest()


def test_checker_rejects_self_selected_subject(tmp_path: Path) -> None:
    # Arrange: Mallory retargets every moving subject field to another commit.
    mutated = deepcopy(_status())
    replacement = "bf2410d70b9949f701e97a684471e8a0c3e53349"
    mutated["subject"]["commit"] = replacement  # type: ignore[index]
    for row in _implemented_slices(mutated):
        if row.get("artifact_subject_commit") is not None:
            row["artifact_subject_commit"] = replacement
    _source_head_slice(mutated)["commit"] = replacement

    # Act: validate the internally consistent, caller-selected subject packet.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: the checker release owns the exact implementation subject.
    assert report["ok"] is False
    assert "subject commit differs from checker-pinned subject" in _findings(report)


def test_checker_rejects_claim_path_escape_and_contract_substitution(
    tmp_path: Path,
) -> None:
    # Arrange: an outside file carries the expected nonclaim labels and a fresh hash.
    outside = tmp_path / "outside-claim.md"
    outside.write_text("substituted claim\n", encoding="utf-8")
    digest = hashlib.sha256(outside.read_bytes()).hexdigest()

    for hostile_path in (str(outside), "../../outside-claim.md"):
        mutated = deepcopy(_status())
        mutated["claim_contract"]["path"] = hostile_path  # type: ignore[index]
        mutated["claim_contract"]["sha256"] = digest  # type: ignore[index]

        # Act: validate one absolute or traversing claim substitution.
        report = check_value_movement_closure_status_v1(
            status_path=_write_status(tmp_path, mutated)
        )

        # Assert: exact repository path and checker-pinned bytes are mandatory.
        assert report["ok"] is False
        assert (
            "claim contract path is outside the closed contract"
            in _findings(report)
        )
        assert (
            "claim contract differs from checker-pinned contract"
            in _findings(report)
        )


def test_checker_rejects_every_semantic_anchor_value_mutant(tmp_path: Path) -> None:
    # Arrange/act/assert: mutate each drift-control decision independently.
    for field in cast(dict[str, object], _status()["semantic_anchors"]):
        mutated = deepcopy(_status())
        mutated["semantic_anchors"][field] = None  # type: ignore[index]
        report = check_value_movement_closure_status_v1(
            status_path=_write_status(tmp_path, mutated)
        )

        assert report["ok"] is False
        expected = {
            "buy_and_burn": "buy-and-burn semantic anchor drift",
            "hyperdeflation": "hyperdeflation semantic anchor drift",
        }.get(field, f"semantic anchor drift: {field}")
        assert expected in _findings(report)


def test_checker_rejects_unknown_slice_and_top_level_fields(tmp_path: Path) -> None:
    # Arrange: Mallory adds authority-shaped evidence outside both closed registries.
    mutated = deepcopy(_status())
    _implemented_slices(mutated).append(
        {"id": "MALLORY_PRODUCTION_AUTHORITY", "status": "PROVED"}
    )
    mutated["mallory_extension"] = {"production_authority": True}

    # Act: validate the open-world evidence packet.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: unknown top-level and implemented-slice variants fail closed.
    assert report["ok"] is False
    assert "closure status top-level field set mismatch" in _findings(report)
    assert (
        "implemented slice IDs are incomplete, unknown, or unordered"
        in _findings(report)
    )


def test_checker_rejects_unknown_field_on_known_slice(tmp_path: Path) -> None:
    # Arrange: Mallory adds authority-shaped data without changing the closed ID list.
    mutated = deepcopy(_status())
    _durable_publisher_slice(mutated)["production_authority"] = "GRANTED"

    # Act: validate the known row with an expanded nested schema.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: every implemented-slice field set is part of the closed contract.
    assert report["ok"] is False
    assert "implemented slice field sets drift" in _findings(report)


def test_checker_rejects_dirty_live_gate_dependency_binding(tmp_path: Path) -> None:
    # Arrange: the ledger no longer binds the imported value-sink checker.
    mutated = deepcopy(_status())
    mutated["checker_dependencies"]["value_sink_checker_sha256"] = "0" * 64  # type: ignore[index]

    # Act: validate before any unbound helper may decide live-gate status.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: both subject mismatch and helper-execution suppression are visible.
    assert report["ok"] is False
    assert (
        "checker dependency artifact hash mismatch: value_sink_checker_sha256"
        in _findings(report)
    )
    assert (
        "live gate helpers skipped because dependency binding failed"
        in _findings(report)
    )


def test_checker_rejects_disaster_campaign_drift(tmp_path: Path) -> None:
    # Arrange: an open architectural disaster is hidden behind a fresh ledger hash.
    mutated = deepcopy(_status())
    mutated["disaster_campaign"]["sha256"] = "0" * 64  # type: ignore[index]
    mutated["disaster_campaign"]["status"] = "CLOSED"  # type: ignore[index]

    # Act: validate the promoted campaign packet.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: campaign bytes and conservative status are checker-owned.
    assert report["ok"] is False
    assert (
        "disaster campaign differs from checker-pinned contract"
        in _findings(report)
    )
    assert "disaster campaign status drift" in _findings(report)


def test_checker_rejects_unattested_test_receipt_promotion_or_retarget(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory retargets the receipt and upgrades its local evidence label.
    mutated = deepcopy(_status())
    receipt = cast(dict[str, object], mutated["test_execution_receipt"])
    receipt["implementation_subject_commit"] = "0" * 40
    receipt["evidence_authority"] = "INDEPENDENTLY_ATTESTED"

    # Act: validate the promoted and foreign-subject receipt binding.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: exact subject and conservative authority remain checker-owned.
    assert report["ok"] is False
    assert "test execution receipt binding drift" in _findings(report)


def test_checker_rejects_vm12_subject_and_test_receipt_drift(tmp_path: Path) -> None:
    # Arrange: stale review prose still carries a nonempty GAP evidence field.
    mutated = deepcopy(_status())
    gate_rows = cast(list[dict[str, object]], mutated["gate_status"])
    vm12 = next(row for row in gate_rows if row["id"] == "VM-12")
    vm12["evidence"] = "An older subject had fewer passing tests."

    # Act: validate the stale but superficially conservative gate row.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: VM-12 binds the current subject, test count, and residual blockers.
    assert report["ok"] is False
    assert "VM-12 exact evidence receipt drift" in _findings(report)


def test_checker_rejects_lifecycle_gate_evidence_drift(tmp_path: Path) -> None:
    # Arrange: VM-04 keeps GAP status while its lifecycle blockers are erased.
    mutated = deepcopy(_status())
    gate_rows = cast(list[dict[str, object]], mutated["gate_status"])
    vm04 = next(row for row in gate_rows if row["id"] == "VM-04")
    vm04["evidence"] = "All enabled economic lifecycles are complete."

    # Act: validate contradictory evidence under the same conservative status.
    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    # Assert: every gate's exact blocker statement is part of the contract.
    assert report["ok"] is False
    assert "VM gate evidence root drift" in _findings(report)


def test_checker_kills_fixed_floor_and_treasury_burn_semantic_mutants() -> None:
    contract = json.loads((REPO_ROOT / M6_ATDD_PATH).read_text(encoding="utf-8"))
    zdex = next(
        row
        for row in contract["managed_asset_policy"]
        if row["asset_class"] == "zdex_protocol_token"
    )

    fixed_floor = deepcopy(contract)
    fixed_floor_row = next(
        row
        for row in fixed_floor["managed_asset_policy"]
        if row["asset_class"] == "zdex_protocol_token"
    )
    fixed_floor_row["production_rule"] = "Burn treasury ZDEX until a 10% floor."
    shortcut = deepcopy(contract)
    shortcut_row = next(
        row
        for row in shortcut["managed_asset_policy"]
        if row["asset_class"] == "zdex_protocol_token"
    )
    shortcut_row["burn_authority"] = "treasury balance burn"

    assert validate_m6_zdex_semantic_anchor_v1(contract) == []
    assert validate_m6_zdex_semantic_anchor_v1(fixed_floor) == [
        "M6 ATDD ZDEX retained-supply or purchase-and-burn drift"
    ]
    assert validate_m6_zdex_semantic_anchor_v1(shortcut) == [
        "M6 ATDD ZDEX burn authority drift"
    ]
    assert zdex["production_rule"].endswith(
        "no fixed initial-supply percentage floor is authoritative."
    )


def test_checker_rejects_erased_known_semantic_conflict(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    mutated["known_semantic_conflicts"] = mutated["known_semantic_conflicts"][1:]  # type: ignore[index]

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "known semantic conflict IDs are incomplete or unordered" in _findings(
        report
    )


def test_checker_rejects_stale_value_sink_observation(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    mutated["live_gate_observations"]["value_sink_inventory"][  # type: ignore[index]
        "observed_occurrence_count"
    ] = 0

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "value sink inventory observation is stale or incomplete" in _findings(
        report
    )


def test_checker_rejects_stale_asset_precision_observation(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    mutated["live_gate_observations"]["asset_precision_policy"][  # type: ignore[index]
        "decimal_places"
    ] = 18

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "asset precision policy observation is stale or incomplete" in _findings(
        report
    )
