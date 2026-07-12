from __future__ import annotations

import copy
import json
import shutil
from pathlib import Path

import pytest

from tools import check_risc0_recursive_live_replay_evidence as checker


def _document() -> dict[str, object]:
    return json.loads(checker.EVIDENCE_PATH.read_text(encoding="utf-8"))


def _validate_coherent_mutation(
    monkeypatch: pytest.MonkeyPatch,
    document: dict[str, object],
) -> checker.RecordError:
    monkeypatch.setattr(
        checker,
        "EXPECTED_EVIDENCE_CANONICAL_SHA256",
        checker._canonical_sha256(document),
    )
    with pytest.raises(checker.RecordError) as rejected:
        checker.validate_evidence(document)
    return rejected.value


def test_committed_live_replay_record_is_exact_and_non_authoritative() -> None:
    report = checker.check_retained_evidence()

    assert report["ok"] is True
    assert report["record_integrity_verified"] is True
    assert report["live_replay_execution_performed_now"] is False
    assert report["historical_execution_provenance_verified"] is False
    assert report["release_authority"] is False
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False


def test_unknown_field_rejects_even_with_coherently_updated_digest(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    document["expanded_authority"] = False

    rejected = _validate_coherent_mutation(monkeypatch, document)

    assert rejected.code == "SCHEMA"


@pytest.mark.parametrize("field", sorted(checker.TRUE_FIELDS))
def test_required_true_fact_rejects_coherent_demotion(
    field: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    document[field] = False

    rejected = _validate_coherent_mutation(monkeypatch, document)

    assert rejected.code == "CLAIM"


@pytest.mark.parametrize("field", sorted(checker.FALSE_FIELDS))
def test_required_non_claim_rejects_coherent_promotion(
    field: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    document[field] = True

    rejected = _validate_coherent_mutation(monkeypatch, document)

    assert rejected.code == "NON_CLAIM"


def test_integer_zero_cannot_substitute_for_false(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    document["production_authority"] = 0

    rejected = _validate_coherent_mutation(monkeypatch, document)

    assert rejected.code == "NON_CLAIM"


def test_checker_source_substitution_rejects_with_coherent_digest(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    closure = copy.deepcopy(document["checker_source_closure"])
    assert isinstance(closure, dict)
    closure["process_runner"] = "00" * 32
    document["checker_source_closure"] = closure

    rejected = _validate_coherent_mutation(monkeypatch, document)

    assert rejected.code == "CHECKER_SOURCE"


def test_live_run_outcome_substitution_rejects_with_coherent_digest(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    runs = copy.deepcopy(document["live_runs"])
    assert isinstance(runs, dict)
    positive = runs["positive"]
    assert isinstance(positive, dict)
    positive["exit_code"] = 1
    document["live_runs"] = runs

    rejected = _validate_coherent_mutation(monkeypatch, document)

    assert rejected.code == "LIVE_RUN"


def test_verifier_transport_substitution_rejects_with_coherent_digest(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    identity = copy.deepcopy(document["verifier_identity"])
    assert isinstance(identity, dict)
    identity["transport"] = "path_reopened_after_hash"
    document["verifier_identity"] = identity

    rejected = _validate_coherent_mutation(monkeypatch, document)

    assert rejected.code == "VERIFIER_IDENTITY"


def test_stdin_transport_substitution_rejects_with_coherent_digest(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    transports = copy.deepcopy(document["runtime_transports"])
    assert isinstance(transports, dict)
    transports["stdin"] = "mutable_temporary_file"
    document["runtime_transports"] = transports

    rejected = _validate_coherent_mutation(monkeypatch, document)

    assert rejected.code == "RUNTIME_TRANSPORTS"


def test_artifact_identity_substitution_rejects_with_coherent_digest(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    artifact = copy.deepcopy(document["artifact_evidence"])
    assert isinstance(artifact, dict)
    artifact["static_verifier_sha256"] = "ff" * 32
    document["artifact_evidence"] = artifact

    rejected = _validate_coherent_mutation(monkeypatch, document)

    assert rejected.code == "ARTIFACT_EVIDENCE"


def test_duplicate_json_key_rejects_before_record_validation(tmp_path: Path) -> None:
    evidence = tmp_path / "evidence.json"
    evidence.write_text('{"ok":true,"ok":false}', encoding="utf-8")

    report = checker.check_retained_evidence(evidence)

    assert report["ok"] is False
    assert report["error_codes"] == ["EVIDENCE_READ"]


@pytest.mark.parametrize("source_state", ["missing", "symlink"])
def test_bound_source_read_failure_returns_rejected_report(
    tmp_path: Path,
    source_state: str,
) -> None:
    root = tmp_path / "repo"
    evidence = root / checker.EVIDENCE_PATH.relative_to(checker.ROOT)
    evidence.parent.mkdir(parents=True)
    shutil.copyfile(checker.EVIDENCE_PATH, evidence)
    bound_source = root / next(
        iter(checker.live.support.CHECKER_SOURCE_PATHS.values())
    )
    if source_state == "symlink":
        bound_source.parent.mkdir(parents=True)
        bound_source.symlink_to(
            checker.ROOT / bound_source.relative_to(root),
        )

    report = checker.check_retained_evidence(repository_root=root)

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["error_codes"] == ["CHECKER_SOURCE"]


def test_bound_reference_read_failure_returns_rejected_report(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    evidence = root / checker.EVIDENCE_PATH.relative_to(checker.ROOT)
    evidence.parent.mkdir(parents=True)
    shutil.copyfile(checker.EVIDENCE_PATH, evidence)
    for relative_path in checker.live.support.CHECKER_SOURCE_PATHS.values():
        destination = root / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(checker.ROOT / relative_path, destination)

    report = checker.check_retained_evidence(repository_root=root)

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["error_codes"] == ["REFERENCE"]


@pytest.mark.parametrize("raw_path", ["bad\x00evidence", "bad\ud800evidence"])
def test_malformed_evidence_path_returns_rejected_report(raw_path: str) -> None:
    report = checker.check_retained_evidence(Path(raw_path))

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["error_codes"] == ["EVIDENCE_READ"]


def test_descriptor_close_failure_returns_rejected_report(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    real_close = checker.rebuild.os.close

    def close_then_fail(descriptor: int) -> None:
        real_close(descriptor)
        raise OSError("injected close failure")

    monkeypatch.setattr(checker.rebuild.os, "close", close_then_fail)

    report = checker.check_retained_evidence()

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["error_codes"] == ["EVIDENCE_READ"]
