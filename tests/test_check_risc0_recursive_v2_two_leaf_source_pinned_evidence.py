from __future__ import annotations

import copy
import hashlib
import inspect
import json
from pathlib import Path
from typing import Any

import pytest

from tools import check_risc0_recursive_v2_two_leaf_source_pinned_evidence as checker


def _roots() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    evidence, reference, historical = checker.load_trust_roots()
    return dict(evidence), dict(reference), dict(historical)


def _reject_code(evidence: dict[str, Any]) -> str:
    _, reference, historical = _roots()
    with pytest.raises(checker.v2.EvidenceError) as caught:
        checker.validate_evidence(evidence, reference, historical)
    return caught.value.code


def test_committed_evidence_accepts_with_exact_claim_scope() -> None:
    evidence, reference, historical = checker.load_trust_roots()

    assert evidence["claims"] == checker.EXPECTED_CLAIMS
    assert tuple(evidence["nonclaims"]) == checker.EXPECTED_NONCLAIMS
    assert reference["claims"]["production_ready"] is False
    assert historical["claims"]["public_claim_allowed"] is False
    specialized = evidence["verification"]["specialized_host_verifier"]
    assert specialized["repository_source_pinned"] is True
    assert specialized["independent_proof_implementation"] is False
    assert checker._canonical_sha256(evidence) == (checker.EXPECTED_EVIDENCE_CANONICAL_SHA256)


def test_evidence_trust_root_is_not_caller_supplied() -> None:
    parameters = inspect.signature(checker.check_live).parameters

    assert "evidence_path" not in parameters
    assert "reference_path" not in parameters
    assert "expected_evidence_sha256" not in parameters


@pytest.mark.parametrize(
    ("mutation", "expected_code"),
    [
        ("claim_escalation", "EVIDENCE_CLAIMS"),
        ("nonclaim_removal", "EVIDENCE_NONCLAIMS"),
        ("nonclaim_reordering", "EVIDENCE_NONCLAIMS"),
        ("unknown_root_key", "EVIDENCE_SCHEMA"),
        ("unknown_nested_key", "EVIDENCE_SCHEMA"),
        ("program_image_drift", "EVIDENCE_PROGRAM_BINDING"),
        ("source_root_drift", "EVIDENCE_SOURCE_BINDING"),
        ("inner_topology_drift", "EVIDENCE_TOPOLOGY"),
        ("historical_receipt_reuse", "EVIDENCE_CROSS_RUN"),
        ("specialized_verifier_source_unpin", "EVIDENCE_CLAIMS"),
        ("specialized_verifier_source_drift", "EVIDENCE_VERIFIER_BINDING"),
        ("specialized_verifier_binary_drift", "EVIDENCE_VERIFIER_BINDING"),
        ("one_leaf_verifier_drift", "EVIDENCE_VERIFIER_BINDING"),
        ("missing_assumption_drift", "EVIDENCE_MISSING_ASSUMPTION"),
        ("build_pipeline_weakening", "EVIDENCE_CLAIMS"),
        ("absolute_path_leak", "PUBLIC_PATH_LEAK"),
    ],
)
def test_structure_preserving_boundary_mutations_reject(mutation: str, expected_code: str) -> None:
    evidence, _, historical = _roots()
    candidate = copy.deepcopy(evidence)

    if mutation == "claim_escalation":
        candidate["claims"]["production_ready"] = True
    elif mutation == "nonclaim_removal":
        candidate["nonclaims"].pop()
    elif mutation == "nonclaim_reordering":
        candidate["nonclaims"][0], candidate["nonclaims"][1] = (
            candidate["nonclaims"][1],
            candidate["nonclaims"][0],
        )
    elif mutation == "unknown_root_key":
        candidate["extra"] = False
    elif mutation == "unknown_nested_key":
        candidate["source_frozen_build"]["source_closure"]["extra"] = False
    elif mutation == "program_image_drift":
        candidate["aggregate_v2"]["image_id"] = "0" * 64
    elif mutation == "source_root_drift":
        candidate["source_frozen_build"]["source_closure"]["root_sha256"] = "0" * 64
    elif mutation == "inner_topology_drift":
        candidate["regenerated_proof_pair"]["inner"]["flat_leaf_count"] = 1
    elif mutation == "historical_receipt_reuse":
        candidate["regenerated_proof_pair"]["inner"]["receipt_sha256"] = historical["proof_pair"][
            "inner"
        ]["receipt_sha256"]
    elif mutation == "specialized_verifier_source_unpin":
        candidate["verification"]["specialized_host_verifier"]["repository_source_pinned"] = False
    elif mutation == "specialized_verifier_source_drift":
        candidate["verification"]["specialized_host_verifier"]["source_sha256"] = "0" * 64
    elif mutation == "specialized_verifier_binary_drift":
        candidate["verification"]["specialized_host_verifier"]["binary_sha256"] = "0" * 64
    elif mutation == "one_leaf_verifier_drift":
        candidate["verification"]["source_pinned_one_leaf_verifier_control"]["binary_sha256"] = (
            "0" * 64
        )
    elif mutation == "missing_assumption_drift":
        candidate["verification"]["missing_child_assumption_control"]["status"] = "accepted"
    elif mutation == "build_pipeline_weakening":
        candidate["source_frozen_build"]["build_pipeline_constrained"] = False
    elif mutation == "absolute_path_leak":
        candidate["source_frozen_build"]["clean_rebuild_report"]["status"] = "/srv/relocated/build"
    else:  # pragma: no cover - guarded by the parameter table.
        raise AssertionError(mutation)

    assert _reject_code(candidate) == expected_code


@pytest.mark.parametrize(
    ("first", "second", "expected_code"),
    [
        ("unknown_root", "claim", "EVIDENCE_SCHEMA"),
        ("claim", "absolute_path", "EVIDENCE_CLAIMS"),
        ("source_root", "inner_topology", "EVIDENCE_SOURCE_BINDING"),
    ],
)
def test_bounded_depth_two_reject_order_is_stable(
    first: str, second: str, expected_code: str
) -> None:
    evidence, _, _ = _roots()
    candidate = copy.deepcopy(evidence)

    for mutation in (first, second):
        if mutation == "unknown_root":
            candidate["extra"] = False
        elif mutation == "claim":
            candidate["claims"]["production_ready"] = True
        elif mutation == "absolute_path":
            candidate["source_frozen_build"]["clean_rebuild_report"]["status"] = (
                "/srv/relocated/build"
            )
        elif mutation == "source_root":
            candidate["source_frozen_build"]["source_closure"]["root_sha256"] = "0" * 64
        elif mutation == "inner_topology":
            candidate["regenerated_proof_pair"]["inner"]["flat_leaf_count"] = 1
        else:  # pragma: no cover - guarded by the parameter table.
            raise AssertionError(mutation)

    assert _reject_code(candidate) == expected_code


@pytest.mark.parametrize(
    "raw",
    [
        b'{"a":1,"a":2}',
        b'{"a":1.5}',
        b'{"a":NaN}',
        b'{"a":123456789012345678901}',
    ],
)
def test_strict_json_parser_rejects_ambiguous_numbers_and_duplicates(raw: bytes) -> None:
    with pytest.raises(checker.v2.EvidenceError):
        checker.v2._parse_json(raw, label="TEST")


def test_live_file_reader_rejects_symlink(tmp_path: Path) -> None:
    target = tmp_path / "target"
    target.write_bytes(b"artifact")
    link = tmp_path / "link"
    link.symlink_to(target)

    with pytest.raises(checker.v2.EvidenceError, match="SYMLINK_FORBIDDEN"):
        checker._verify_file(
            link,
            label="fixture",
            expected_sha256=hashlib.sha256(b"artifact").hexdigest(),
            expected_size=8,
            max_bytes=16,
        )


def test_live_file_reader_rejects_hash_and_size_drift(tmp_path: Path) -> None:
    artifact = tmp_path / "artifact"
    artifact.write_bytes(b"artifact")

    with pytest.raises(checker.v2.EvidenceError) as hash_error:
        checker._verify_file(
            artifact,
            label="fixture",
            expected_sha256="0" * 64,
            expected_size=8,
            max_bytes=16,
        )
    assert hash_error.value.code == "LIVE_FILE_SHA256"

    with pytest.raises(checker.v2.EvidenceError) as size_error:
        checker._verify_file(
            artifact,
            label="fixture",
            expected_sha256=hashlib.sha256(b"artifact").hexdigest(),
            expected_size=7,
            max_bytes=16,
        )
    assert size_error.value.code == "LIVE_FILE_SIZE"


def test_dry_run_surface_validation_accepts_exact_manifest_projection() -> None:
    evidence, _, _ = _roots()
    pair = evidence["regenerated_proof_pair"]
    shared = pair["shared_authenticated_roots"]

    def node(role: str) -> dict[str, Any]:
        source = pair[role]
        return {
            **shared,
            "journal_sha256": source["journal_sha256"],
            "protocol_journal_hash": source["protocol_journal_hash"],
            "profile": source["profile"],
            "immediate_child_count": source["immediate_child_count"],
            "flat_leaf_count": source["flat_leaf_count"],
            "tree_height": source["tree_height"],
            "subtree_node_count": source["subtree_node_count"],
        }

    report = {
        "ok": True,
        "dry_run": True,
        "aggregate_v2_image_id": evidence["aggregate_v2"]["image_id"],
        "input_leaf_count": 2,
        "input_leaf_receipt_sha256s": [row["receipt_sha256"] for row in evidence["leaf_claims"]],
        "inner": node("inner"),
        "epoch_root": node("root"),
    }

    checker._validate_dry_run(report, evidence)
    report["inner"]["journal_sha256"] = "0" * 64
    with pytest.raises(checker.v2.EvidenceError, match="LIVE_DRY_RUN"):
        checker._validate_dry_run(report, evidence)


def test_cli_rejection_is_machine_readable_and_nonzero(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    invalid = tmp_path / "invalid"
    invalid.write_bytes(b"invalid")
    invalid.chmod(0o755)
    arguments = [
        "--spot-leaf",
        str(invalid),
        "--zusd-leaf",
        str(invalid),
        "--inner-artifact",
        str(invalid),
        "--root-artifact",
        str(invalid),
        "--release-harness",
        str(invalid),
        "--one-leaf-verifier",
        str(invalid),
        "--two-leaf-verifier",
        str(invalid),
        "--r0vm",
        str(invalid),
        "--json",
    ]

    assert checker.main(arguments) == 1
    report = json.loads(capsys.readouterr().out)
    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["error_code"] == "LIVE_FILE_SHA256"
    assert report["public_claim_allowed"] is False
    assert report["production_ready"] is False
