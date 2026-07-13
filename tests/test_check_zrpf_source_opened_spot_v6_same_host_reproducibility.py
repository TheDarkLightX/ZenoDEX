from __future__ import annotations

import copy
import hashlib
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

from tools import (
    check_zrpf_source_opened_spot_v6_same_host_reproducibility as checker,
)


EXPECTED_REPORT_FIELDS = {
    "ok",
    "schema",
    "errors",
    "evidence_sha256",
    "governed_anchor_checked",
    "static_artifact_records_checked",
    "live_output_sets_checked",
    "live_artifact_files_checked",
    "live_output_roots_pairwise_distinct",
    "live_source_head_observations_checked",
    "live_a_b_head_commit_tree_identity_observed",
    "three_live_retained_output_sets_byte_identity_observed",
    "same_host_build_reproducibility_verified",
    "source_to_output_provenance_verified",
    "complete_build_input_closure_verified",
    "image_ids_recomputed_in_this_comparison",
    "build_host_identifier_committed",
    "build_execution_transcripts_committed",
    "path4_exact_source_equivalence_verified",
    "cross_host_reproducibility_verified",
    "proofs_regenerated",
    "release_authority",
    "settlement_authority",
    "production_authority",
    "nonclaims",
}


def _assert_exact_report_schema(report: dict[str, object]) -> None:
    assert set(report) == EXPECTED_REPORT_FIELDS
    assert report["same_host_build_reproducibility_verified"] is False
    assert report["source_to_output_provenance_verified"] is False
    assert report["complete_build_input_closure_verified"] is False
    assert report["image_ids_recomputed_in_this_comparison"] is False
    assert report["build_host_identifier_committed"] is False
    assert report["build_execution_transcripts_committed"] is False
    assert report["path4_exact_source_equivalence_verified"] is False
    assert report["cross_host_reproducibility_verified"] is False
    assert report["proofs_regenerated"] is False
    assert report["release_authority"] is False
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False


@dataclass(frozen=True)
class SyntheticCase:
    evidence_path: Path
    document: dict[str, object]
    raw: bytes
    output_directories: dict[str, Path]
    source_directories: dict[str, Path]


def _git(path: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["/usr/bin/git", "-C", str(path), *arguments],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=20,
    )
    return completed.stdout.strip()


def _source_roots(tmp_path: Path) -> tuple[dict[str, Path], dict[str, tuple[str, str]]]:
    origin = tmp_path / "origin"
    origin.mkdir()
    _git(origin, "init", "--quiet")
    _git(origin, "config", "user.name", "ZRPF Test")
    _git(origin, "config", "user.email", "zrpf-test@example.invalid")
    (origin / "source.txt").write_text("first\n", encoding="utf-8")
    _git(origin, "add", "source.txt")
    _git(origin, "commit", "--quiet", "-m", "first")
    first_commit = _git(origin, "rev-parse", "HEAD^{commit}")
    first_tree = _git(origin, "rev-parse", "HEAD^{tree}")

    roots: dict[str, Path] = {}
    for label in ("build_a", "build_b"):
        roots[label] = tmp_path / f"source-{label}"
        subprocess.run(
            ["/usr/bin/git", "clone", "--quiet", str(origin), str(roots[label])],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            timeout=20,
        )

    (origin / "source.txt").write_text("second\n", encoding="utf-8")
    _git(origin, "add", "source.txt")
    _git(origin, "commit", "--quiet", "-m", "second")
    second_commit = _git(origin, "rev-parse", "HEAD^{commit}")
    second_tree = _git(origin, "rev-parse", "HEAD^{tree}")
    roots["path4"] = tmp_path / "source-path4"
    subprocess.run(
        ["/usr/bin/git", "clone", "--quiet", str(origin), str(roots["path4"])],
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        timeout=20,
    )
    expected = {
        "build_a": (first_commit, first_tree),
        "build_b": (first_commit, first_tree),
        "path4": (second_commit, second_tree),
    }
    return roots, expected


@pytest.fixture
def synthetic_case(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> SyntheticCase:
    payloads = {
        "spot_value_leaf_v6.bin": b"leaf-v6\0",
        "spot_value_aggregate_l1_v6.bin": b"aggregate-l1-v6\0",
        "spot_value_aggregate_l2_v6.bin": b"aggregate-l2-v6\0",
        "source_opened_spot_settlement_v6.bin": b"settlement-v6\0",
    }
    specs = tuple(
        checker.ArtifactSpec(
            existing.stage,
            existing.artifact_file,
            len(payloads[existing.artifact_file]),
            hashlib.sha256(payloads[existing.artifact_file]).hexdigest(),
            existing.image_id_hex,
        )
        for existing in checker.ARTIFACT_SPECS
    )
    artifact_set_sha256 = checker._artifact_set_sha256(payloads)
    monkeypatch.setattr(checker, "ARTIFACT_SPECS", specs)
    monkeypatch.setattr(
        checker, "EXPECTED_ARTIFACT_SET_SHA256", artifact_set_sha256
    )

    output_directories: dict[str, Path] = {}
    for label in checker.OUTPUT_LABELS:
        root = tmp_path / f"output-{label}"
        root.mkdir()
        for artifact_file, raw in payloads.items():
            (root / artifact_file).write_bytes(raw)
        output_directories[label] = root

    source_directories, expected_sources = _source_roots(tmp_path)
    monkeypatch.setattr(
        checker, "EXPECTED_SOURCE_HEAD_OBSERVATIONS", expected_sources
    )

    document, _ = checker.load_evidence(checker.DEFAULT_EVIDENCE)
    changed = copy.deepcopy(document)
    publisher_observations = changed["publisher_reported_observations"]
    publisher_observations["retained_output_sets"] = [
        {
            "output_label": label,
            "artifact_set_sha256": artifact_set_sha256,
        }
        for label in checker.OUTPUT_LABELS
    ]
    publisher_observations["source_head_commit_tree_observations"] = [
        {
            "source_label": label,
            "repository_commit": expected_sources[label][0],
            "repository_tree": expected_sources[label][1],
        }
        for label in checker.SOURCE_HEAD_OBSERVATION_LABELS
    ]
    changed["artifacts"] = [
        {
            "stage": spec.stage,
            "artifact_file": spec.artifact_file,
            "size_bytes": spec.size_bytes,
            "sha256": spec.sha256,
            "image_id_hex": spec.image_id_hex,
        }
        for spec in specs
    ]
    raw = checker.canonical_bytes(changed)
    evidence_path = tmp_path / "evidence.json"
    evidence_path.write_bytes(raw)
    monkeypatch.setattr(
        checker, "EXPECTED_EVIDENCE_SHA256", hashlib.sha256(raw).hexdigest()
    )
    return SyntheticCase(
        evidence_path=evidence_path,
        document=changed,
        raw=raw,
        output_directories=output_directories,
        source_directories=source_directories,
    )


def test_committed_evidence_is_strictly_accepted_without_live_promotion() -> None:
    report = checker.check_evidence()

    _assert_exact_report_schema(report)
    assert report["ok"] is True
    assert report["errors"] == []
    assert report["evidence_sha256"] == checker.EXPECTED_EVIDENCE_SHA256
    assert report["governed_anchor_checked"] is True
    assert report["static_artifact_records_checked"] == 4
    assert report["live_output_sets_checked"] == 0
    assert report[checker.LIVE_RETAINED_OUTPUT_IDENTITY_FIELD] is False


def test_static_positive_observations_are_publisher_qualified() -> None:
    document, _ = checker.load_evidence(checker.DEFAULT_EVIDENCE)

    assert "retained_output_sets" not in document
    assert "observed_source_snapshots" not in document
    observations = document["publisher_reported_observations"]
    assert observations["three_retained_output_sets_byte_identical"] is True
    assert observations["a_b_head_commit_tree_identity_observed"] is True
    assert all(value is False for value in document["claims"].values())


def test_live_checks_promote_only_retained_output_byte_identity(
    synthetic_case: SyntheticCase,
) -> None:
    report = checker.check_evidence(
        synthetic_case.evidence_path,
        output_directories=synthetic_case.output_directories,
        source_directories=synthetic_case.source_directories,
        require_retained_output_identity=True,
    )

    _assert_exact_report_schema(report)
    assert report["ok"] is True
    assert report["live_output_sets_checked"] == 3
    assert report["live_artifact_files_checked"] == 12
    assert report["live_output_roots_pairwise_distinct"] is True
    assert report["live_source_head_observations_checked"] == 3
    assert report["live_a_b_head_commit_tree_identity_observed"] is True
    assert report[checker.LIVE_RETAINED_OUTPUT_IDENTITY_FIELD] is True


def test_retained_output_identity_does_not_require_or_imply_source_provenance(
    synthetic_case: SyntheticCase,
) -> None:
    report = checker.check_evidence(
        synthetic_case.evidence_path,
        output_directories=synthetic_case.output_directories,
        require_retained_output_identity=True,
    )

    _assert_exact_report_schema(report)
    assert report["ok"] is True
    assert report[checker.LIVE_RETAINED_OUTPUT_IDENTITY_FIELD] is True
    assert report["live_source_head_observations_checked"] == 0
    assert report["live_a_b_head_commit_tree_identity_observed"] is False
    assert report["source_to_output_provenance_verified"] is False
    assert report["same_host_build_reproducibility_verified"] is False


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (
            lambda value: value["claims"].__setitem__(
                "cross_host_reproducibility_verified", True
            ),
            "claims.cross_host_reproducibility_verified must be exactly False",
        ),
        (
            lambda value: value["claims"].__setitem__(
                "same_host_build_reproducibility_verified", True
            ),
            "claims.same_host_build_reproducibility_verified must be exactly False",
        ),
        (
            lambda value: value["claims"].__setitem__(
                "source_to_output_provenance_verified", True
            ),
            "claims.source_to_output_provenance_verified must be exactly False",
        ),
        (
            lambda value: value["claims"].__setitem__("production_authority", 0),
            "claims.production_authority must be exactly False",
        ),
        (
            lambda value: value["comparison_profile"].__setitem__(
                "unreviewed", False
            ),
            "comparison_profile field set mismatch",
        ),
        (
            lambda value: value["publisher_reported_observations"][
                "source_head_commit_tree_observations"
            ][2].__setitem__(
                "repository_commit",
                value["publisher_reported_observations"][
                    "source_head_commit_tree_observations"
                ][0]["repository_commit"],
            ),
            r"source_head_commit_tree_observations\[2\].repository_commit mismatch",
        ),
        (
            lambda value: value["artifacts"][0].__setitem__("size_bytes", 1),
            r"artifacts\[0\] mismatch",
        ),
    ],
)
def test_validator_rejects_claim_schema_source_and_artifact_mutations(
    mutation,
    message: str,
) -> None:
    document, _ = checker.load_evidence(checker.DEFAULT_EVIDENCE)
    changed = copy.deepcopy(document)
    mutation(changed)

    with pytest.raises(checker.RetainedOutputEvidenceError, match=message):
        checker.validate_evidence(
            changed, checker.canonical_bytes(changed), require_anchor=False
        )


@pytest.mark.parametrize(
    "raw",
    [
        b'{"schema":"first","schema":"second"}\n',
        b'{"schema":1.0}\n',
        b'{"schema":NaN}\n',
        json.dumps({"nested": [[[[[[[[[[[[[1]]]]]]]]]]]]]}).encode("utf-8") + b"\n",
    ],
)
def test_loader_rejects_duplicate_floating_or_overdeep_json(
    tmp_path: Path, raw: bytes
) -> None:
    path = tmp_path / "evidence.json"
    path.write_bytes(raw)

    with pytest.raises(checker.RetainedOutputEvidenceError):
        checker.load_evidence(path)


def test_loader_rejects_equivalent_noncanonical_json(tmp_path: Path) -> None:
    document, _ = checker.load_evidence(checker.DEFAULT_EVIDENCE)
    path = tmp_path / "evidence.json"
    path.write_text(json.dumps(document), encoding="utf-8")

    with pytest.raises(checker.RetainedOutputEvidenceError, match="noncanonical"):
        checker.load_evidence(path)


@pytest.mark.parametrize(
    ("raw", "message"),
    [
        (b'{"value":' + (b"9" * 5_000) + b"}\n", "integer exceeds governed bound"),
        (b'{"value":"\\ud800"}\n', "contains invalid Unicode"),
    ],
)
def test_json_resource_and_unicode_failures_return_canonical_report(
    tmp_path: Path, raw: bytes, message: str
) -> None:
    path = tmp_path / "evidence.json"
    path.write_bytes(raw)

    report = checker.check_evidence(path)

    _assert_exact_report_schema(report)
    assert report["ok"] is False
    assert report["errors"] and message in report["errors"][0]
    assert report[checker.LIVE_RETAINED_OUTPUT_IDENTITY_FIELD] is False
    json.dumps(report, sort_keys=True, separators=(",", ":"))


def test_loader_rejects_symlink_and_fifo_without_following_or_blocking(
    tmp_path: Path,
) -> None:
    target = tmp_path / "target.json"
    target.write_bytes(b"{}\n")
    symlink = tmp_path / "symlink.json"
    symlink.symlink_to(target)
    fifo = tmp_path / "evidence.fifo"
    os.mkfifo(fifo)

    with pytest.raises(checker.RetainedOutputEvidenceError):
        checker.load_evidence(symlink)
    with pytest.raises(
        checker.RetainedOutputEvidenceError, match="must be a regular file"
    ):
        checker.load_evidence(fifo)


def test_live_output_content_mutation_rejects(
    synthetic_case: SyntheticCase,
) -> None:
    path = synthetic_case.output_directories["build_b"] / "spot_value_leaf_v6.bin"
    path.write_bytes(b"wrong-v6")

    with pytest.raises(checker.RetainedOutputEvidenceError, match="SHA-256 mismatch"):
        checker.validate_evidence(
            synthetic_case.document,
            synthetic_case.raw,
            output_directories=synthetic_case.output_directories,
        )


def test_final_global_output_recheck_detects_earlier_root_mutation(
    synthetic_case: SyntheticCase,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = checker._stable_artifact_bytes
    mutated = False

    def mutate_build_a_before_build_b_read(
        directory_fd: int, spec: checker.ArtifactSpec, label: str
    ) -> bytes:
        nonlocal mutated
        if label.startswith("output.build_b.") and not mutated:
            mutated = True
            target = (
                synthetic_case.output_directories["build_a"]
                / "spot_value_leaf_v6.bin"
            )
            target.write_bytes(b"changed\0")
        return original(directory_fd, spec, label)

    monkeypatch.setattr(
        checker, "_stable_artifact_bytes", mutate_build_a_before_build_b_read
    )

    with pytest.raises(checker.RetainedOutputEvidenceError, match="SHA-256 mismatch"):
        checker.validate_evidence(
            synthetic_case.document,
            synthetic_case.raw,
            output_directories=synthetic_case.output_directories,
        )


def test_live_output_extra_file_rejects(synthetic_case: SyntheticCase) -> None:
    (synthetic_case.output_directories["path4"] / "extra.bin").write_bytes(b"extra")

    with pytest.raises(
        checker.RetainedOutputEvidenceError,
        match="inventory exceeds governed bound",
    ):
        checker.validate_evidence(
            synthetic_case.document,
            synthetic_case.raw,
            output_directories=synthetic_case.output_directories,
        )


def test_output_inventory_stops_at_one_over_the_governed_bound(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class GuardedEntries:
        def __init__(self) -> None:
            self.requested = 0

        def __enter__(self) -> GuardedEntries:
            return self

        def __exit__(self, *_arguments: object) -> None:
            return None

        def __iter__(self) -> GuardedEntries:
            return self

        def __next__(self) -> Path:
            self.requested += 1
            if self.requested > 5:
                raise AssertionError("inventory reader crossed its one-over bound")
            return Path(f"entry-{self.requested}")

    entries = GuardedEntries()
    monkeypatch.setattr(checker.os, "scandir", lambda _descriptor: entries)

    with pytest.raises(
        checker.RetainedOutputEvidenceError,
        match="inventory exceeds governed bound",
    ):
        checker._bounded_directory_inventory(7, 4, "output.test")
    assert entries.requested == 5


def test_live_output_symlink_and_fifo_reject(
    synthetic_case: SyntheticCase,
) -> None:
    root = synthetic_case.output_directories["path4"]
    artifact = root / "spot_value_leaf_v6.bin"
    outside = root.parent / "outside.bin"
    outside.write_bytes(artifact.read_bytes())
    artifact.unlink()
    artifact.symlink_to(outside)

    with pytest.raises(checker.RetainedOutputEvidenceError, match="unavailable"):
        checker.validate_evidence(
            synthetic_case.document,
            synthetic_case.raw,
            output_directories=synthetic_case.output_directories,
        )

    artifact.unlink()
    os.mkfifo(artifact)
    with pytest.raises(
        checker.RetainedOutputEvidenceError, match="must be a regular file"
    ):
        checker.validate_evidence(
            synthetic_case.document,
            synthetic_case.raw,
            output_directories=synthetic_case.output_directories,
        )


def test_live_output_directory_alias_rejects(
    synthetic_case: SyntheticCase,
) -> None:
    aliased = dict(synthetic_case.output_directories)
    aliased["build_b"] = aliased["build_a"]

    with pytest.raises(checker.RetainedOutputEvidenceError, match="pairwise distinct"):
        checker.validate_evidence(
            synthetic_case.document,
            synthetic_case.raw,
            output_directories=aliased,
        )


@pytest.mark.parametrize("index_flag", ["--assume-unchanged", "--skip-worktree"])
def test_live_source_claim_is_head_only_with_hidden_worktree_change(
    synthetic_case: SyntheticCase,
    index_flag: str,
) -> None:
    source = synthetic_case.source_directories["build_b"]
    _git(source, "update-index", index_flag, "source.txt")
    (source / "source.txt").write_text("hidden dirty input\n", encoding="utf-8")

    report = checker.validate_evidence(
        synthetic_case.document,
        synthetic_case.raw,
        source_directories=synthetic_case.source_directories,
    )

    _assert_exact_report_schema(report)
    assert report["live_a_b_head_commit_tree_identity_observed"] is True
    assert report["complete_build_input_closure_verified"] is False
    assert any("working-tree contents" in item for item in report["nonclaims"])


def test_live_source_claim_is_head_only_with_core_worktree_redirect(
    synthetic_case: SyntheticCase,
    tmp_path: Path,
) -> None:
    source = synthetic_case.source_directories["build_b"]
    redirected = tmp_path / "redirected-worktree"
    redirected.mkdir()
    _git(source, "config", "core.worktree", str(redirected))

    report = checker.validate_evidence(
        synthetic_case.document,
        synthetic_case.raw,
        source_directories=synthetic_case.source_directories,
    )

    _assert_exact_report_schema(report)
    assert report["live_a_b_head_commit_tree_identity_observed"] is True
    assert report["complete_build_input_closure_verified"] is False


def test_final_global_source_recheck_detects_earlier_head_mutation(
    synthetic_case: SyntheticCase,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = checker._git_head_commit_tree_observation
    mutated = False

    def mutate_build_a_before_build_b_observation(
        directory_fd: int, label: str
    ) -> tuple[str, str]:
        nonlocal mutated
        if label == "source.build_b" and not mutated:
            mutated = True
            source = synthetic_case.source_directories["build_a"]
            _git(source, "config", "user.name", "ZRPF Test")
            _git(source, "config", "user.email", "zrpf-test@example.invalid")
            (source / "source.txt").write_text("later head\n", encoding="utf-8")
            _git(source, "add", "source.txt")
            _git(source, "commit", "--quiet", "-m", "later")
        return original(directory_fd, label)

    monkeypatch.setattr(
        checker,
        "_git_head_commit_tree_observation",
        mutate_build_a_before_build_b_observation,
    )

    with pytest.raises(
        checker.RetainedOutputEvidenceError,
        match="HEAD commit/tree changed after initial observation",
    ):
        checker.validate_evidence(
            synthetic_case.document,
            synthetic_case.raw,
            source_directories=synthetic_case.source_directories,
        )


def test_live_source_directory_alias_rejects(
    synthetic_case: SyntheticCase,
) -> None:
    aliased = dict(synthetic_case.source_directories)
    aliased["build_b"] = aliased["build_a"]

    with pytest.raises(checker.RetainedOutputEvidenceError, match="pairwise distinct"):
        checker.validate_evidence(
            synthetic_case.document,
            synthetic_case.raw,
            source_directories=aliased,
        )


def test_require_retained_output_identity_rejects_static_only_check() -> None:
    report = checker.check_evidence(require_retained_output_identity=True)

    _assert_exact_report_schema(report)
    assert report["ok"] is False
    assert report[checker.LIVE_RETAINED_OUTPUT_IDENTITY_FIELD] is False


def test_partial_cli_roots_emit_the_exact_fail_closed_report_schema(
    tmp_path: Path,
) -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(Path(checker.__file__)),
            "--build-a-output",
            str(tmp_path),
            "--json",
        ],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=20,
    )

    assert completed.returncode == 1
    assert completed.stderr == ""
    report = json.loads(completed.stdout)
    _assert_exact_report_schema(report)
    assert report["ok"] is False
    assert report[checker.LIVE_RETAINED_OUTPUT_IDENTITY_FIELD] is False
