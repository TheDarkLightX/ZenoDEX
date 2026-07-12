from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable

import pytest

from tools import check_zrpf_v3_firecracker_direct_replay_evidence as checker


def test_committed_direct_replay_evidence_is_exactly_bound_and_non_authoritative() -> None:
    report = checker.build_report()

    assert report["ok"] is True
    assert report["errors"] == []
    assert report["evidence_raw_sha256"] == checker.EXPECTED_EVIDENCE_RAW_SHA256
    assert report["validation_scope"] == (
        "static_record_integrity_and_internal_binding_no_historical_execution_provenance"
    )
    assert all(value is False for value in report["authority"].values())


def test_committed_evidence_reports_replay_without_claiming_execution_provenance() -> None:
    document = _committed_document()

    assert document["claims"]["direct_local_microvm_replay_reported"] is True
    assert "direct_local_microvm_replay_verified" not in document["claims"]
    assert document["claims"]["historical_vm_execution_provenance_verified"] is False
    assert document["historical_observation_basis"] == (
        "publisher_reported_retained_local_report_identity_only"
    )
    assert document["claims"]["coherent_repository_rewrite_resistance_verified"] is False
    assert document["claims"]["retained_execution_record_integrity_verified"] is True


def test_legacy_direct_replay_verified_claim_rejects(tmp_path: Path) -> None:
    document = _committed_document()
    document["claims"]["direct_local_microvm_replay_verified"] = document["claims"].pop(
        "direct_local_microvm_replay_reported"
    )

    report = checker.build_report(evidence_path=_write(tmp_path, document))

    assert report["ok"] is False
    assert "claim_boundary_mismatch" in report["errors"]


def test_evidence_hash_and_document_come_from_one_stable_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = checker.runtime.read_bounded_regular
    evidence_reads = 0

    def counted_read(path: Path, *, maximum: int) -> bytes:
        nonlocal evidence_reads
        if path == checker.EVIDENCE_PATH:
            evidence_reads += 1
        return original(path, maximum=maximum)

    monkeypatch.setattr(checker.runtime, "read_bounded_regular", counted_read)

    report = checker.build_report()

    assert report["ok"] is True
    assert evidence_reads == 1


def test_noncanonical_evidence_rejects_before_claim_acceptance(tmp_path: Path) -> None:
    document = _committed_document()
    evidence = tmp_path / "evidence.json"
    evidence.write_bytes(json.dumps(document, sort_keys=True).encode("ascii"))

    report = checker.build_report(evidence_path=evidence)

    assert report["ok"] is False
    assert "evidence_hash_mismatch" in report["errors"]
    assert "evidence_noncanonical" in report["errors"]
    assert all(value is False for value in report["authority"].values())


@pytest.mark.parametrize(
    "claim_name",
    [
        "cross_host_reproducible_build",
        "hardware_side_channel_resistance",
        "historical_vm_execution_provenance_verified",
        "microvm_replay_release_authority",
        "production_authority",
        "release_authority",
        "root_owned_launcher_verified",
        "sandbox_escape_resistance",
        "settlement_authority",
        "zero_knowledge_privacy",
    ],
)
def test_authority_sandbox_reproducibility_privacy_and_side_channel_promotions_reject(
    tmp_path: Path,
    claim_name: str,
) -> None:
    document = _committed_document()
    document["claims"][claim_name] = True

    report = checker.build_report(evidence_path=_write(tmp_path, document))

    assert report["ok"] is False
    assert "claim_boundary_mismatch" in report["errors"]
    assert all(value is False for value in report["authority"].values())


def test_integer_substitution_cannot_impersonate_false_claim(tmp_path: Path) -> None:
    document = _committed_document()
    document["claims"]["production_authority"] = 0

    report = checker.build_report(evidence_path=_write(tmp_path, document))

    assert report["ok"] is False
    assert "claim_boundary_mismatch" in report["errors"]


def test_report_false_claim_inventory_matches_pinned_policy() -> None:
    report = checker.build_report()

    assert set(report["authority"]) == set(checker.REQUIRED_FALSE_CLAIMS)
    assert report["claim_policy_scope"] == ("evidence_only_mutations_against_pinned_checker_policy")


def test_committed_payload_mutation_rejects_output_reconstruction(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = bytearray(checker.OUTPUT_PAYLOAD_PATH.read_bytes())
    payload[0] ^= 1
    mutated_path = tmp_path / "payload.json"
    mutated_path.write_bytes(payload)
    monkeypatch.setattr(checker, "OUTPUT_PAYLOAD_PATH", mutated_path)

    report = checker.build_report()

    assert report["ok"] is False
    assert "governed_output_payload_rejected" in report["errors"]


@pytest.mark.parametrize(
    ("mutation", "expected_error"),
    [
        (
            lambda document: document["request"].__setitem__("run_nonce_256", "02" * 32),
            "request_binding_mismatch",
        ),
        (
            lambda document: document["request"].__setitem__("runtime_manifest_sha256", "00" * 32),
            "request_binding_mismatch",
        ),
        (
            lambda document: document["output"].__setitem__("commit_marker_actual", "00" * 32),
            "output_fact_mismatch",
        ),
        (
            lambda document: document["output"].__setitem__(
                "trailing_zero_bytes_count",
                document["output"]["trailing_zero_bytes_count"] - 1,
            ),
            "output_fact_mismatch",
        ),
        (
            lambda document: document["artifacts"]["kernel"].__setitem__("sha256", "00" * 32),
            "artifact_binding_mismatch",
        ),
        (
            lambda document: document["governed_bindings"].__setitem__(
                "replay_intent_sha256", "00" * 32
            ),
            "governed_binding_mismatch",
        ),
        (
            lambda document: document["retained_local_report_identity"].__setitem__(
                "publicly_available", False
            ),
            "retained_report_binding_mismatch",
        ),
    ],
)
def test_structure_preserving_binding_mutations_reject_at_named_boundaries(
    tmp_path: Path,
    mutation: Callable[[dict[str, Any]], None],
    expected_error: str,
) -> None:
    document = _committed_document()
    mutation(document)

    report = checker.build_report(evidence_path=_write(tmp_path, document))

    assert report["ok"] is False
    assert "evidence_hash_mismatch" in report["errors"]
    assert expected_error in report["errors"]


def test_unknown_field_and_nonclaim_deletion_reject(tmp_path: Path) -> None:
    document = _committed_document()
    document["claims"]["covert_channel_capacity_bounded"] = False
    document["non_claims"].pop()

    report = checker.build_report(evidence_path=_write(tmp_path, document))

    assert report["ok"] is False
    assert "claim_boundary_mismatch" in report["errors"]
    assert "non_claims_mismatch" in report["errors"]


@pytest.mark.parametrize(
    ("path_name", "error_code"),
    [
        ("EXECUTED_CONFIG_PATH", "retained_config_rejected"),
        ("LOCAL_REPORT_PATH", "retained_local_report_rejected"),
        ("FIRECRACKER_STDOUT_PATH", "retained_stdout_rejected"),
    ],
)
def test_retained_execution_record_mutation_rejects(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    path_name: str,
    error_code: str,
) -> None:
    source = getattr(checker, path_name)
    raw = bytearray(source.read_bytes())
    raw[0] ^= 1
    mutated = tmp_path / source.name
    mutated.write_bytes(raw)
    monkeypatch.setattr(checker, path_name, mutated)

    report = checker.build_report()

    assert report["ok"] is False
    assert error_code in report["errors"]


def _committed_document() -> dict[str, Any]:
    value = json.loads(checker.EVIDENCE_PATH.read_bytes())
    assert isinstance(value, dict)
    return copy.deepcopy(value)


def _write(tmp_path: Path, document: dict[str, Any]) -> Path:
    path = tmp_path / "evidence.json"
    path.write_bytes(checker.runtime.canonical_document_bytes(document))
    return path
