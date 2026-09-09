from __future__ import annotations

import copy
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any, Callable

import pytest

from tools import v3_productivity_report as reporter

REPO_ROOT = Path(__file__).resolve().parents[2]
ASSESSMENT_TEMPLATE = REPO_ROOT / "docs/research/ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.json"


def _git(root: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", *arguments],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(root, "commit", "-m", message)
    return _git(root, "rev-parse", "HEAD")


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")


def _fixture_repo(tmp_path: Path, *, runtime_change: bool = True) -> tuple[Path, str, str]:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init")
    _git(root, "config", "user.email", "test@example.invalid")
    _git(root, "config", "user.name", "Productivity Test")
    (root / "src").mkdir()
    (root / "docs").mkdir()
    (root / "data").mkdir()
    (root / "src/app.py").write_text("value = 1\n", encoding="utf-8")
    (root / "docs/original.md").write_text("baseline\n", encoding="utf-8")
    _write_json(root / "data/original.json", {"baseline": True})
    before = _commit(root, "baseline")
    if runtime_change:
        (root / "src/app.py").write_text("value = 2\n", encoding="utf-8")
    (root / "docs/unlisted.md").write_text("unlisted docs change\n", encoding="utf-8")
    _write_json(root / "data/unlisted.json", {"unlisted": 1})
    _write_json(root / "evidence.json", {"metrics": {"input": 7, "output": 11}})
    after = _commit(root, "candidate")
    return root, before, after


def _ref(root: Path, commit: str, path: str) -> dict[str, str]:
    raw = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    ).stdout
    return {"commit": commit, "path": path, "sha256": hashlib.sha256(raw).hexdigest()}


def _resources(root: Path, commit: str, *, observed: bool = True) -> dict[str, Any]:
    evidence = _ref(root, commit, "evidence.json")
    return {
        "input_tokens": {"value": 7, "evidence": evidence, "json_pointer": "/metrics/input"}
        if observed
        else None,
        "output_tokens": None,
        "elapsed_ms": None,
        "cost_microusd": None,
    }


def _run(root: Path, commit: str, identifier: str = "run-a", *, observed: bool = True) -> dict[str, Any]:
    return {
        "id": identifier,
        "model_id": "model-a",
        "role": "implementation",
        "status": "completed",
        "task_kind": "fixture",
        "risk": "standard",
        "provenance": _ref(root, commit, "evidence.json"),
        "resources": _resources(root, commit, observed=observed),
    }


def _batch(
    root: Path,
    before: str,
    after: str,
    *,
    identifier: str = "batch-a",
    obligation: str = "W07",
    run_ids: list[str] | None = None,
    disposition: str = "accepted_partial",
    assessment: dict[str, Any] | None = None,
    findings: list[dict[str, Any]] | None = None,
    supersedes: str | None = None,
) -> dict[str, Any]:
    return {
        "id": identifier,
        "before_commit": before,
        "after_commit": after,
        "kind": "implementation",
        "obligation_ids": [obligation],
        "run_ids": [] if run_ids is None else run_ids,
        "outcome": {
            "disposition": disposition,
            "summary": "source-recorded fixture result",
            "evidence": _ref(root, after, "evidence.json") if disposition not in {"support_only", "unassessed"} else None,
        },
        "assessment": {"before": None, "after": None, "review": None} if assessment is None else assessment,
        "findings": [] if findings is None else findings,
        "supersedes": supersedes,
    }


def _manifest(runs: list[dict[str, Any]], batches: list[dict[str, Any]]) -> dict[str, Any]:
    return {"schema": reporter.MANIFEST_SCHEMA, "runs": runs, "batches": batches}


def _collect(tmp_path: Path, root: Path, manifest: dict[str, Any]) -> dict[str, Any]:
    path = tmp_path / "manifest.json"
    _write_json(path, manifest)
    return reporter.collect(path, root)


def _rejects(
    tmp_path: Path,
    root: Path,
    manifest: dict[str, Any],
    code: str,
) -> None:
    path = tmp_path / "manifest.json"
    _write_json(path, manifest)
    with pytest.raises(reporter.ProductivityReject) as error:
        reporter.collect(path, root)
    assert error.value.code == code


def _assessment_data(subject: str, *, increase: bool = False) -> dict[str, Any]:
    data = json.loads(ASSESSMENT_TEMPLATE.read_text(encoding="utf-8"))
    data["subject"] = subject
    if increase:
        row = data["full_v3"]["rows"][0]
        for field in ("low", "central", "high"):
            row[field] += 0.1
        for field in ("lower_percent", "central_percent", "upper_percent"):
            data["full_v3"][field] += 0.2
    return data


def _shift_first_full_v3_row(
    data: dict[str, Any], *, low: float = 0.0, central: float = 0.0, high: float = 0.0
) -> dict[str, Any]:
    row = data["full_v3"]["rows"][0]
    for field, amount in (("low", low), ("central", central), ("high", high)):
        row[field] += amount
    for field, amount in (("lower_percent", low), ("central_percent", central), ("upper_percent", high)):
        data["full_v3"][field] += amount * 2
    return data


def _assessment_refs(root: Path, before: str, after: str, *, increase: bool = False) -> dict[str, Any]:
    _write_json(root / "assessments/before.json", _assessment_data(before))
    _write_json(root / "assessments/after.json", _assessment_data(after, increase=increase))
    _write_json(root / "assessments/review.json", {"recorded": "review only"})
    source = _commit(root, "assessment records")
    return {
        "before": _ref(root, source, "assessments/before.json"),
        "after": _ref(root, source, "assessments/after.json"),
        "review": _ref(root, source, "assessments/review.json"),
    }


def test_given_shared_run_and_unlisted_data_docs_when_collected_then_cost_is_once_and_diff_is_complete(
    tmp_path: Path,
) -> None:
    root, before, after = _fixture_repo(tmp_path)
    run = _run(root, after)
    first = _batch(root, before, after, identifier="first", obligation="W07", run_ids=["run-a"])
    second = _batch(root, before, after, identifier="second", obligation="W09", run_ids=["run-a"])

    report = _collect(tmp_path, root, _manifest([run], [first, second]))

    assert report["team"]["resources"]["input_tokens"] == {
        "source_recorded_value_sum": 7,
        "observed_run_count": 1,
        "unknown_run_count": 0,
    }
    assert report["team"]["resources"]["output_tokens"]["source_recorded_value_sum"] is None
    assert report["runs"][0]["resources"]["output_tokens"] is None
    assert len(report["team"]["duplicate_active_ranges"]) == 1
    assert report["team"]["line_metrics"]["categories"]["docs"]["added"] > 0
    assert report["team"]["line_metrics"]["categories"]["data"]["added"] > 0
    assert report["batches"][0]["diff"]["changed_file_count"] == 4
    assert reporter._classify("zk/host/src/guest.rs") == "runtime"
    assert reporter._classify("docs/evidence.json") == "data"
    assert reporter._classify("tests/data/vector.json") == "data"
    assert report["team"]["coverage"]["dispatch_inventory_reconciled"] is False


@pytest.mark.parametrize(
    ("path", "expected"),
    [
        ("zk/asset_lane_custody_global_risc0/host/src/lib.rs", "runtime"),
        ("zk/asset_lane_custody_global_risc0/host/tests/receipt.rs", "tests"),
        ("tools/v3_progress_assessment_calc.py", "tooling"),
        ("tools/skills/zenodex-v3-progress-assessment/SKILL.md", "docs"),
        ("docs/research/ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.json", "data"),
        ("tests/fixture.toml", "config"),
        ("zk/asset_lane_custody_global_risc0/Cargo.lock", "lockfile"),
        ("lean-mathlib/Proofs/AssetLaneCustodyRefinementV2.lean", "proof"),
    ],
)
def test_given_real_category_paths_when_classified_then_tracker_and_rust_tests_do_not_inflate_runtime(
    path: str, expected: str
) -> None:
    assert reporter._classify(path) == expected


@pytest.mark.parametrize(
    ("mutate", "code"),
    [
        (
            lambda manifest: manifest["runs"][0]["resources"].__setitem__(
                "input_tokens", {"value": True, "evidence": manifest["runs"][0]["provenance"], "json_pointer": "/metrics/input"}
            ),
            "OBSERVATION_VALUE",
        ),
        (lambda manifest: manifest.__setitem__("unexpected", 1), "TOP_LEVEL_FIELDS"),
    ],
)
def test_given_bool_or_unknown_fields_when_collected_then_closed_schema_rejects(
    tmp_path: Path,
    mutate: Callable[[dict[str, Any]], None],
    code: str,
) -> None:
    root, before, after = _fixture_repo(tmp_path)
    manifest = _manifest([_run(root, after)], [_batch(root, before, after, run_ids=["run-a"])])
    mutate(manifest)
    _rejects(tmp_path, root, manifest, code)


@pytest.mark.parametrize("literal", ["NaN", "Infinity", "-Infinity", "1e400"])
def test_given_nonfinite_manifest_json_when_collected_then_no_report_is_emitted(
    tmp_path: Path, literal: str
) -> None:
    root, _, _ = _fixture_repo(tmp_path)
    path = tmp_path / "manifest.json"
    path.write_text(
        '{"schema":"zenodex/v3-productivity/v1","runs":[],"batches":[],"bad":' + literal + "}",
        encoding="utf-8",
    )
    with pytest.raises(reporter.ProductivityReject) as error:
        reporter.collect(path, root)
    assert error.value.code == "NONFINITE_JSON"


def test_given_stale_reference_or_json_pointer_mismatch_when_collected_then_rejects(tmp_path: Path) -> None:
    root, before, after = _fixture_repo(tmp_path)
    manifest = _manifest([_run(root, after)], [_batch(root, before, after, run_ids=["run-a"])])
    manifest["runs"][0]["provenance"]["sha256"] = "0" * 64
    _rejects(tmp_path, root, manifest, "STALE_PINNED_EVIDENCE")

    manifest = _manifest([_run(root, after)], [_batch(root, before, after, run_ids=["run-a"])])
    manifest["runs"][0]["resources"]["input_tokens"]["json_pointer"] = "/metrics/output"
    _rejects(tmp_path, root, manifest, "OBSERVATION_MISMATCH")


def test_given_rfc6901_root_pointer_when_observation_is_a_json_integer_then_it_is_verified(tmp_path: Path) -> None:
    root, before, after = _fixture_repo(tmp_path)
    (root / "root-value.json").write_text("7", encoding="utf-8")
    source = _commit(root, "root observation")
    run = _run(root, after)
    run["resources"]["input_tokens"] = {
        "value": 7,
        "evidence": _ref(root, source, "root-value.json"),
        "json_pointer": "",
    }
    report = _collect(tmp_path, root, _manifest([run], [_batch(root, before, after, run_ids=["run-a"])]))
    assert report["source_integrity"]["json_pointer_observations_verified"] == 1


def test_given_same_head_review_and_unattributed_batch_when_collected_then_it_is_retained(tmp_path: Path) -> None:
    root, before, _ = _fixture_repo(tmp_path)
    batch = _batch(root, before, before, disposition="support_only", identifier="same-head", obligation="W00")
    report = _collect(tmp_path, root, _manifest([], [batch]))

    assert report["batches"][0]["active"] is True
    assert report["batches"][0]["assessment"]["status"] == "NOT_RESCORED"
    assert report["batches"][0]["diff"]["commit_count"] == 0
    assert report["team"]["coverage"]["batches_without_run_ids"] == 1
    assert report["baseline_manifest"] == {"status": "NOT_CHECKED"}


def test_given_baseline_manifest_rewrite_when_checked_then_append_only_guard_rejects(tmp_path: Path) -> None:
    root, _, after = _fixture_repo(tmp_path)
    original = _manifest([_run(root, after)], [])
    committed_path = root / "docs/productivity.json"
    _write_json(committed_path, original)
    baseline = _commit(root, "baseline productivity manifest")

    rewritten = copy.deepcopy(original)
    rewritten["runs"][0]["task_kind"] = "rewritten"
    _write_json(committed_path, rewritten)
    with pytest.raises(reporter.ProductivityReject) as error:
        reporter.collect(committed_path, root, baseline)
    assert error.value.code == "BASELINE_NOT_APPEND_ONLY"


def test_given_matched_assessments_then_team_delta_is_once_and_missing_after_stays_not_rescored(
    tmp_path: Path,
) -> None:
    root, before, after = _fixture_repo(tmp_path)
    assessments = _assessment_refs(root, before, after, increase=True)
    first = _batch(root, before, after, identifier="first", obligation="W07", assessment=assessments)
    second = _batch(root, before, after, identifier="second", obligation="W09", assessment=assessments)

    report = _collect(tmp_path, root, _manifest([], [first, second]))

    assert len(report["team"]["score_transitions"]) == 1
    assert report["team"]["score_transitions"][0]["delta"]["full_v3"]["central_percent_points"] > 0
    assert report["team"]["line_metrics"]["status"] == "DEDUPLICATED_ACTIVE_RANGES"

    baseline_only = {"before": assessments["before"], "after": None, "review": None}
    report = _collect(tmp_path, root, _manifest([], [_batch(root, before, after, assessment=baseline_only)]))
    assert report["batches"][0]["assessment"]["status"] == "NOT_RESCORED"
    assert report["batches"][0]["assessment"]["delta"] is None


def test_given_docs_data_only_reviewed_assessment_when_collected_then_line_categories_do_not_decide_credit(
    tmp_path: Path,
) -> None:
    root, before, after = _fixture_repo(tmp_path, runtime_change=False)
    assessments = _assessment_refs(root, before, after, increase=True)
    report = _collect(tmp_path, root, _manifest([], [_batch(root, before, after, assessment=assessments)]))

    assert len(report["team"]["score_transitions"]) == 1
    assert "LINE_CATEGORIES_NEVER_GRANT_CREDIT" in report["line_classification_convention"]["product_credit"]


@pytest.mark.parametrize("disposition", ["support_only", "rejected"])
def test_given_nonaccepted_positive_review_when_collected_then_it_cannot_earn_product_credit(
    tmp_path: Path, disposition: str
) -> None:
    root, before, after = _fixture_repo(tmp_path)
    assessments = _assessment_refs(root, before, after, increase=True)
    batch = _batch(root, before, after, disposition=disposition, assessment=assessments)
    _rejects(tmp_path, root, _manifest([], [batch]), "NONPRODUCT_SCORE_CREDIT")


def test_given_same_head_positive_review_when_collected_then_it_cannot_create_implementation_delta(
    tmp_path: Path,
) -> None:
    root, before, _ = _fixture_repo(tmp_path)
    assessments = _assessment_refs(root, before, before, increase=True)
    batch = _batch(root, before, before, disposition="support_only", assessment=assessments)
    batch["outcome"]["disposition"] = "accepted_partial"
    batch["outcome"]["evidence"] = assessments["review"]
    _rejects(tmp_path, root, _manifest([], [batch]), "SAME_HEAD_SCORE_CREDIT")


def test_given_successive_w07_reviews_and_an_overlapping_negative_review_then_only_the_overlap_rejects(
    tmp_path: Path,
) -> None:
    root, before, after = _fixture_repo(tmp_path)
    (root / "src/app.py").write_text("value = 3\n", encoding="utf-8")
    later = _commit(root, "later candidate")
    first_assessment = _assessment_refs(root, before, after, increase=True)
    later_assessment = _assessment_refs(root, after, later, increase=True)
    later_assessment["before"] = first_assessment["after"]
    first = _batch(root, before, after, identifier="first", assessment=first_assessment)
    second = _batch(root, after, later, identifier="second", assessment=later_assessment)
    report = _collect(tmp_path, root, _manifest([], [first, second]))
    assert len(report["team"]["score_transitions"]) == 2

    negative_after = _assessment_data(later)
    row = negative_after["full_v3"]["rows"][0]
    for field in ("low", "central", "high"):
        row[field] -= 0.1
    for field in ("lower_percent", "central_percent", "upper_percent"):
        negative_after["full_v3"][field] -= 0.2
    _write_json(root / "assessments/negative-after.json", negative_after)
    negative_source = _commit(root, "negative assessment")
    negative = {
        "before": first_assessment["before"],
        "after": _ref(root, negative_source, "assessments/negative-after.json"),
        "review": _ref(root, negative_source, "assessments/review.json"),
    }
    overlapping = _batch(
        root,
        before,
        later,
        identifier="overlapping-negative",
        obligation="W09",
        assessment=negative,
    )
    _rejects(tmp_path, root, _manifest([], [first, overlapping]), "OVERLAPPING_SCORE_TRANSITION")


def test_given_reverted_range_when_collected_then_empty_net_diff_keeps_commit_activity(tmp_path: Path) -> None:
    root = tmp_path / "reverted"
    root.mkdir()
    _git(root, "init")
    _git(root, "config", "user.email", "test@example.invalid")
    _git(root, "config", "user.name", "Productivity Test")
    (root / "src").mkdir()
    (root / "src/app.py").write_text("value = 1\n", encoding="utf-8")
    before = _commit(root, "baseline")
    (root / "src/app.py").write_text("value = 2\n", encoding="utf-8")
    _commit(root, "change")
    (root / "src/app.py").write_text("value = 1\n", encoding="utf-8")
    after = _commit(root, "revert")
    batch = _batch(root, before, after, disposition="support_only", obligation="W00")
    report = _collect(tmp_path, root, _manifest([], [batch]))

    diff = report["batches"][0]["diff"]
    assert diff["commit_count"] == 2
    assert diff["changed_file_count"] == 0
    assert diff["files"] == []
    assert diff["changed_again_paths"] == [{"path": "src/app.py", "commit_occurrence_count": 2}]


def test_given_superseding_reopened_record_when_collected_then_old_positive_result_is_excluded(tmp_path: Path) -> None:
    root, before, after = _fixture_repo(tmp_path)
    first = _batch(root, before, after, identifier="accepted", obligation="W07")
    reopened = _batch(
        root,
        before,
        after,
        identifier="reopened",
        obligation="W07",
        disposition="reopened",
        supersedes="accepted",
        findings=[
            {
                "id": "finding-a",
                "status": "reopened",
                "evidence": _ref(root, after, "evidence.json"),
            }
        ],
    )
    report = _collect(tmp_path, root, _manifest([], [first, reopened]))

    assert report["batches"][0]["active"] is False
    assert report["batches"][1]["active"] is True
    assert report["team"]["active_quality"]["finding_ids"]["reopened"] == ["finding-a"]


def test_given_altered_assessment_denominator_or_subject_when_collected_then_calculator_binding_rejects(
    tmp_path: Path,
) -> None:
    root, before, after = _fixture_repo(tmp_path)
    bad_denominator = _assessment_data(after)
    bad_denominator["method"]["denominators"]["full_v3"]["weight_points"] = 99
    _write_json(root / "assessments/before.json", _assessment_data(before))
    _write_json(root / "assessments/after.json", bad_denominator)
    _write_json(root / "assessments/review.json", {"recorded": "review only"})
    source = _commit(root, "invalid assessment records")
    assessments = {
        "before": _ref(root, source, "assessments/before.json"),
        "after": _ref(root, source, "assessments/after.json"),
        "review": _ref(root, source, "assessments/review.json"),
    }
    _rejects(tmp_path, root, _manifest([], [_batch(root, before, after, assessment=assessments)]), "METHOD_DRIFT")

    wrong_subject = _assessment_data("0" * 40)
    _write_json(root / "assessments/after.json", wrong_subject)
    source = _commit(root, "wrong subject assessment")
    assessments["after"] = _ref(root, source, "assessments/after.json")
    _rejects(tmp_path, root, _manifest([], [_batch(root, before, after, assessment=assessments)]), "ASSESSMENT_SUBJECT")


def test_given_reused_resource_observation_when_collected_then_it_cannot_be_counted_twice(
    tmp_path: Path,
) -> None:
    root, _, after = _fixture_repo(tmp_path)
    first = _run(root, after, "run-a")
    second = _run(root, after, "run-b")
    _rejects(tmp_path, root, _manifest([first, second], []), "DUPLICATE_RESOURCE_OBSERVATION")

    repeated_field = _run(root, after)
    repeated_field["resources"]["output_tokens"] = copy.deepcopy(repeated_field["resources"]["input_tokens"])
    _rejects(tmp_path, root, _manifest([repeated_field], []), "DUPLICATE_RESOURCE_OBSERVATION")


def test_given_stale_selected_baseline_when_collected_then_intermediate_history_cannot_be_bypassed(
    tmp_path: Path,
) -> None:
    root, _, after = _fixture_repo(tmp_path)
    path = root / "docs/productivity.json"
    _write_json(path, _manifest([], []))
    first = _commit(root, "productivity v1")
    current = _manifest([_run(root, after)], [])
    _write_json(path, current)
    second = _commit(root, "productivity v2")

    rewritten = copy.deepcopy(current)
    rewritten["runs"][0]["task_kind"] = "rewritten after v2"
    _write_json(path, rewritten)
    with pytest.raises(reporter.ProductivityReject) as error:
        reporter.collect(path, root, first)
    assert error.value.code == "BASELINE_NOT_CURRENT"
    with pytest.raises(reporter.ProductivityReject) as error:
        reporter.collect(path, root, second)
    assert error.value.code == "BASELINE_NOT_APPEND_ONLY"


def test_given_inconsistent_assessment_checkpoints_when_collected_then_team_transition_rejects(
    tmp_path: Path,
) -> None:
    root, before, after = _fixture_repo(tmp_path)
    records = {
        "a-before.json": _assessment_data(before),
        "a-after.json": _shift_first_full_v3_row(
            _assessment_data(after), low=0.1, central=0.1, high=0.1
        ),
        "b-before.json": _shift_first_full_v3_row(
            _assessment_data(before), low=0.05, central=0.05, high=0.05
        ),
        "b-after.json": _shift_first_full_v3_row(
            _assessment_data(after), low=0.15, central=0.15, high=0.15
        ),
        "review.json": {"recorded": "review"},
    }
    for name, value in records.items():
        _write_json(root / "assessments" / name, value)
    source = _commit(root, "inconsistent assessment checkpoints")
    first_assessment = {
        "before": _ref(root, source, "assessments/a-before.json"),
        "after": _ref(root, source, "assessments/a-after.json"),
        "review": _ref(root, source, "assessments/review.json"),
    }
    second_assessment = {
        "before": _ref(root, source, "assessments/b-before.json"),
        "after": _ref(root, source, "assessments/b-after.json"),
        "review": _ref(root, source, "assessments/review.json"),
    }
    first = _batch(root, before, after, identifier="first", obligation="W07", assessment=first_assessment)
    second = _batch(root, before, after, identifier="second", obligation="W09", assessment=second_assessment)
    _rejects(tmp_path, root, _manifest([], [first, second]), "INCONSISTENT_SCORE_CHECKPOINT")

    chain_path = tmp_path / "chain"
    chain_path.mkdir()
    chain_root, chain_before, chain_after = _fixture_repo(chain_path)
    (chain_root / "src/app.py").write_text("value = 3\n", encoding="utf-8")
    chain_later = _commit(chain_root, "later candidate")
    first_assessment = _assessment_refs(chain_root, chain_before, chain_after, increase=True)
    second_assessment = _assessment_refs(chain_root, chain_after, chain_later, increase=True)
    first = _batch(chain_root, chain_before, chain_after, identifier="first", assessment=first_assessment)
    second = _batch(chain_root, chain_after, chain_later, identifier="second", assessment=second_assessment)
    _rejects(
        chain_path,
        chain_root,
        _manifest([], [first, second]),
        "INCONSISTENT_SCORE_CHECKPOINT",
    )


def test_given_band_only_or_same_head_gain_when_collected_then_credit_guards_cover_every_band(
    tmp_path: Path,
) -> None:
    root, before, _ = _fixture_repo(tmp_path)
    _write_json(root / "assessments/before.json", _assessment_data(before))
    _write_json(
        root / "assessments/after.json",
        _shift_first_full_v3_row(_assessment_data(before), low=0.05, high=0.05),
    )
    _write_json(root / "assessments/review.json", {"recorded": "review"})
    source = _commit(root, "band-only same-head assessment")
    assessment = {
        "before": _ref(root, source, "assessments/before.json"),
        "after": _ref(root, source, "assessments/after.json"),
        "review": _ref(root, source, "assessments/review.json"),
    }
    support_only = _batch(root, before, before, disposition="support_only", assessment=assessment)
    _rejects(tmp_path, root, _manifest([], [support_only]), "NONPRODUCT_SCORE_CREDIT")

    accepted = copy.deepcopy(support_only)
    accepted["outcome"]["disposition"] = "accepted_partial"
    accepted["outcome"]["evidence"] = assessment["review"]
    _rejects(tmp_path, root, _manifest([], [accepted]), "SAME_HEAD_SCORE_CREDIT")


def test_given_divergent_ranges_when_collected_then_they_are_retained_without_team_aggregation_or_credit(
    tmp_path: Path,
) -> None:
    root, before, left_after = _fixture_repo(tmp_path)
    left_assessment = _assessment_refs(root, before, left_after, increase=True)
    _git(root, "checkout", "-b", "alternate", before)
    (root / "src/app.py").write_text("value = 3\n", encoding="utf-8")
    _write_json(root / "evidence.json", {"metrics": {"input": 7, "output": 11}})
    right_after = _commit(root, "alternate candidate")
    right_assessment = _assessment_refs(root, before, right_after, increase=True)
    left = _batch(root, before, left_after, identifier="left", obligation="W07")
    right = _batch(root, before, right_after, identifier="right", obligation="W09")

    report = _collect(tmp_path, root, _manifest([], [left, right]))
    assert report["team"]["line_metrics"]["status"] == "NOT_AGGREGATED_DIVERGENT_RANGES"
    assert len(report["team"]["divergent_active_ranges"]) == 1

    left["assessment"] = left_assessment
    right["assessment"] = right_assessment
    _rejects(tmp_path, root, _manifest([], [left, right]), "DIVERGENT_SCORE_TRANSITION")


def test_given_sequential_finding_lifecycle_when_collected_then_latest_status_is_unique_and_history_remains(
    tmp_path: Path,
) -> None:
    root, before, after = _fixture_repo(tmp_path)
    (root / "src/app.py").write_text("value = 3\n", encoding="utf-8")
    later = _commit(root, "later repair")
    first = _batch(
        root,
        before,
        after,
        identifier="confirmed",
        findings=[{"id": "finding-a", "status": "confirmed", "evidence": _ref(root, after, "evidence.json")}],
    )
    repaired = _batch(
        root,
        after,
        later,
        identifier="repaired",
        findings=[{"id": "finding-a", "status": "repaired", "evidence": _ref(root, later, "evidence.json")}],
    )
    report = _collect(tmp_path, root, _manifest([], [first, repaired]))
    quality = report["team"]["active_quality"]
    assert quality["finding_ids"]["repaired"] == ["finding-a"]
    assert len(quality["finding_lifecycle"][0]["events"]) == 2

    conflicting = _batch(
        root,
        before,
        after,
        identifier="conflicting",
        obligation="W09",
        findings=[{"id": "finding-a", "status": "reopened", "evidence": _ref(root, after, "evidence.json")}],
    )
    _rejects(tmp_path, root, _manifest([], [first, conflicting]), "DUPLICATE_ACTIVE_FINDING")


def test_given_binary_receipt_change_when_collected_then_it_is_reported_without_fake_line_counts(
    tmp_path: Path,
) -> None:
    root, _, after = _fixture_repo(tmp_path)
    (root / "receipt.bin").write_bytes(b"\x00receipt\xff")
    binary_after = _commit(root, "binary receipt")
    report = _collect(
        tmp_path,
        root,
        _manifest([], [_batch(root, after, binary_after, disposition="support_only", obligation="W00")]),
    )

    diff = report["batches"][0]["diff"]
    assert diff["binary_file_count"] == 1
    assert diff["files"] == [
        {
            "path": "receipt.bin",
            "category": "other",
            "added": None,
            "deleted": None,
            "net": None,
            "physical_lines": "UNAVAILABLE_FOR_BINARY_FILE",
        }
    ]
    assert report["team"]["line_metrics"]["binary_file_count"] == 1
