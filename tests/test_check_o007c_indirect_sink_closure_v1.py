"""Topology and mutation evidence for O-007C V1."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Callable

import pytest

from tools.build_o007c_indirect_sink_closure_v1 import (
    SourceBindingModeV1,
    load_stage_a_snapshot_v1,
)
from tools.check_o007c_indirect_sink_closure_v1 import (
    check_o007c_indirect_sink_closure_v1,
)
from tools.m6_indirect_value_sinks.report import build_indirect_value_sink_report
from tools.o007c_indirect_sink_closure_v1 import (
    ARTIFACT_PATH_V1,
    BASE_COMMIT_V1,
    NONCLAIMS_V1,
    NORMATIVE_ANCHORS_V1,
    PRESERVED_PATHS_V1,
    SPECIAL_STATUSES_V1,
    STAGE_A_SOURCE_PATHS_V1,
    O007CClosureRejectV1,
    canonical_json_bytes_v1,
    certificate_root_v1,
    validate_artifact_v1,
)

ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture(scope="module")
def public_closure_report() -> dict[str, object]:
    if not (ROOT / ARTIFACT_PATH_V1).is_file():
        pytest.skip("artifact-only Stage B has not been created yet")
    return check_o007c_indirect_sink_closure_v1(ROOT)


def _recertified(raw: bytes, mutation: Callable[[dict[str, Any]], None]) -> bytes:
    artifact: dict[str, Any] = json.loads(raw)
    mutation(artifact)
    payload = {key: value for key, value in artifact.items() if key != "certificate_root"}
    artifact["certificate_root"] = certificate_root_v1(payload)
    return canonical_json_bytes_v1(artifact)


def test_bdd_closure_preserves_authority_ceiling_and_explicit_blockers(
    public_closure_report: dict[str, object],
) -> None:
    assert public_closure_report["ok"] is True
    assert public_closure_report["historical_valid"] is True
    assert public_closure_report["current_applicable"] is True
    assert public_closure_report["release_ready"] is False
    assert public_closure_report["value_movement_authority"] == "NONE"
    assert public_closure_report["vm01_status"] == "OPEN"
    assert public_closure_report["special_statuses"] == list(SPECIAL_STATUSES_V1)

    artifact = json.loads((ROOT / ARTIFACT_PATH_V1).read_bytes())
    assert artifact["implementation_subject"]["parent"] == BASE_COMMIT_V1
    assert artifact["claim_ceiling"]["closed_value_movement_gates"] == 0
    assert artifact["claim_ceiling"]["value_movement_authority"] == "NONE"
    assert artifact["claim_ceiling"]["vm_01_status"] == "OPEN"
    assert artifact["normative_anchors"] == list(NORMATIVE_ANCHORS_V1)
    assert artifact["obligation"]["residual_statuses"] == list(SPECIAL_STATUSES_V1)
    assert artifact["nonclaims"] == list(NONCLAIMS_V1)
    evidence = artifact["inventory_evidence"]
    summary = evidence["inventory_summary"]
    assert evidence["all_discovered_rows_dispositioned"] is True
    assert evidence["dynamic_declaration_count"] == 61
    assert evidence["dynamic_disposition_count"] == 61
    assert evidence["literal_dynamic_count"] == 16
    assert evidence["closed_static_registry_dynamic_count"] == 1
    assert evidence["unresolved_dynamic_count"] == 44
    assert evidence["closed_local_target_set_disposition_count"] == 13
    assert evidence["source_bound_research_exclusion_disposition_count"] == 31
    assert evidence["derived_local_literal_disposition_count"] == 7
    assert evidence["derived_external_literal_disposition_count"] == 9
    assert evidence["derived_closed_static_registry_disposition_count"] == 1
    assert summary["dynamic_declaration_count"] == summary["dynamic_disposition_count"]


@pytest.mark.parametrize(
    "mutation",
    [
        lambda artifact: artifact["claim_ceiling"].__setitem__(
            "value_movement_authority", "GRANTED"
        ),
        lambda artifact: artifact["claim_ceiling"].__setitem__("vm_01_status", "CLOSED"),
        lambda artifact: artifact["dependency_bindings"]["o_007b_v3"].__setitem__(
            "certificate_root", "0" * 64
        ),
        lambda artifact: artifact["inventory_evidence"]["inventory_summary"].__setitem__(
            "source_sink_observation_count", 0
        ),
        lambda artifact: artifact["inventory_evidence"].__setitem__(
            "derived_external_literal_disposition_count", 8
        ),
        lambda artifact: artifact.__setitem__("unknown_field", True),
    ],
)
def test_recertified_authority_dependency_count_or_unknown_mutant_rejects(
    mutation: Callable[[dict[str, Any]], None],
    public_closure_report: dict[str, object],
) -> None:
    assert public_closure_report["historical_valid"] is True
    snapshot = load_stage_a_snapshot_v1(
        ROOT,
        str(public_closure_report["stage_a_commit"]),
        source_binding=SourceBindingModeV1.GIT_ONLY,
    )
    raw = (ROOT / ARTIFACT_PATH_V1).read_bytes()

    with pytest.raises(O007CClosureRejectV1):
        validate_artifact_v1(_recertified(raw, mutation), snapshot)


def test_noncanonical_and_duplicate_artifact_json_rejects(
    public_closure_report: dict[str, object],
) -> None:
    snapshot = load_stage_a_snapshot_v1(
        ROOT,
        str(public_closure_report["stage_a_commit"]),
        source_binding=SourceBindingModeV1.GIT_ONLY,
    )
    raw = (ROOT / ARTIFACT_PATH_V1).read_bytes()
    noncanonical = (json.dumps(json.loads(raw), indent=2) + "\n").encode()
    with pytest.raises(O007CClosureRejectV1) as noncanonical_error:
        validate_artifact_v1(noncanonical, snapshot)
    assert noncanonical_error.value.code == "ARTIFACT_CANONICAL"

    duplicate = raw.replace(b'{"bounded_delta":', b'{"schema":"duplicate","bounded_delta":', 1)
    with pytest.raises(O007CClosureRejectV1) as duplicate_error:
        validate_artifact_v1(duplicate, snapshot)
    assert duplicate_error.value.code == "DUPLICATE_JSON_KEY"


def test_repository_stage_topology_preserves_o007a_o007b_bytes(
    public_closure_report: dict[str, object],
) -> None:
    stage_a = str(public_closure_report["stage_a_commit"])
    delta = subprocess.run(
        [
            "git",
            "diff-tree",
            "--no-commit-id",
            "--name-status",
            "--no-renames",
            "-r",
            stage_a,
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    assert delta == [f"A\t{path}" for path in STAGE_A_SOURCE_PATHS_V1]
    for path in PRESERVED_PATHS_V1:
        base_blob = subprocess.run(
            ["git", "rev-parse", f"{BASE_COMMIT_V1}:{path}"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        stage_blob = subprocess.run(
            ["git", "rev-parse", f"{stage_a}:{path}"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        assert stage_blob == base_blob


def test_current_checker_rejects_path_write_bytes_alias_mutant(tmp_path: Path) -> None:
    if not (ROOT / ARTIFACT_PATH_V1).is_file():
        pytest.skip("artifact-only Stage B has not been created yet")
    clone = tmp_path / "repo"
    subprocess.run(
        ["git", "clone", "--quiet", "--shared", str(ROOT), str(clone)],
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )
    target = clone / "src" / "integration" / "m6_outbox_delivery_v1.py"
    source = target.read_text(encoding="utf-8")
    needle = "    ) -> M6OutboxDeliveryResultV1:\n        expected = TauWithdrawalDeliveryRequestV1.from_effect(effect)\n"
    replacement = (
        "    ) -> M6OutboxDeliveryResultV1:\n"
        "        indirect_writer = Path.write_bytes\n"
        "        expected = TauWithdrawalDeliveryRequestV1.from_effect(effect)\n"
    )
    assert source.count(needle) == 1
    target.write_text(source.replace(needle, replacement), encoding="utf-8")

    inventory = build_indirect_value_sink_report(clone)
    assert inventory["ok"] is False
    assert inventory["o007a_bound_through_o007b_v3"] is True
    assert inventory["o007b_v3_historical_valid"] is True
    assert inventory["o007b_v3_current_applicable"] is True
    assert inventory["indirect_alias_count"] == 1
    finding = inventory["finding"]
    assert isinstance(finding, dict)
    assert finding["code"] == "COMPUTED_MISMATCH"

    closure = check_o007c_indirect_sink_closure_v1(clone)
    assert closure["ok"] is False
    assert closure["historical_valid"] is True
    assert closure["current_applicable"] is False
    assert closure["value_movement_authority"] == "NONE"
