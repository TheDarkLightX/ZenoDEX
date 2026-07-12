from __future__ import annotations

import contextlib
import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools import check_zrpf_v4_spot_value_leaf_local_evidence as checker
from tools import zrpf_v4_spot_value_leaf_evidence_support as support


def test_static_checker_authenticates_bytes_without_claiming_seal_execution() -> None:
    report = checker.check_manifest()

    assert report["ok"] is True
    assert report["mode"] == "static"
    assert report["facts"] == {
        "artifact_files_checked": 2,
        "canonical_receipts_checked": True,
        "exact_mutation_relation_checked": True,
        "execution_checked": False,
        "manifest_sha256": support.EXPECTED_MANIFEST_SHA256,
        "mutation_receipt_cryptographically_rejected": False,
        "native_verifier_source_anchor_checked": True,
        "positive_receipt_cryptographically_verified": False,
        "proof_source_anchor_checked": True,
        "scoped_native_replay_claim_allowed": False,
        "supporting_inputs_checked": 2,
    }


def test_isolated_cli_executes_the_static_checker_contract() -> None:
    completed = subprocess.run(
        [sys.executable, "-I", str(Path(checker.__file__)), "--json"],
        check=False,
        capture_output=True,
        cwd=support.REPO_ROOT,
        timeout=30,
    )

    assert completed.returncode == 0
    assert completed.stderr == b""
    report = json.loads(completed.stdout)
    assert report["ok"] is True
    assert report["mode"] == "static"
    assert report["facts"]["execution_checked"] is False


def test_manifest_bytes_equal_the_exact_governed_document() -> None:
    loaded = support.common.load_manifest(support.DEFAULT_MANIFEST)

    assert loaded.document == support.expected_manifest()
    assert support.common.sha256_bytes(loaded.raw) == support.EXPECTED_MANIFEST_SHA256


@pytest.mark.parametrize(
    ("raw", "message"),
    [
        (b'{"schema":"a","schema":"b"}\n', "duplicate JSON key"),
        (b'{"x":1.0}\n', "floating-point JSON number"),
    ],
)
def test_manifest_loader_rejects_ambiguous_json(
    tmp_path: Path,
    raw: bytes,
    message: str,
) -> None:
    path = tmp_path / "manifest.json"
    path.write_bytes(raw)

    document, errors = checker.load_manifest(path)

    assert document is None
    assert any(message in error for error in errors)


def test_manifest_loader_rejects_noncanonical_equivalent_json(tmp_path: Path) -> None:
    path = tmp_path / "manifest.json"
    path.write_text('{"x":1}\n', encoding="utf-8")

    document, errors = checker.load_manifest(path)

    assert document is None
    assert any("manifest JSON bytes are not canonical" in error for error in errors)


@pytest.mark.parametrize(
    ("label", "mutate", "expected_error"),
    [
        (
            "unknown nested field",
            lambda value: value["program"].__setitem__("unreviewed_authority", True),
            "manifest.program has unknown fields: unreviewed_authority",
        ),
        (
            "Boolean integer substitution",
            lambda value: value["claims"].__setitem__(
                "manifest_authorizes_production", 0
            ),
            "manifest.claims.manifest_authorizes_production type mismatch",
        ),
        (
            "claim promotion",
            lambda value: value["claims"].__setitem__(
                "manifest_authorizes_settlement", True
            ),
            "manifest.claims.manifest_authorizes_settlement value mismatch",
        ),
        (
            "mutation index drift",
            lambda value: value["mutation_control"].__setitem__(
                "seal_word_index", 2
            ),
            "manifest.mutation_control.seal_word_index value mismatch",
        ),
        (
            "supporting path escape",
            lambda value: value["native_replay"]["supporting_inputs"][0].__setitem__(
                "path", "../source.json"
            ),
            "manifest.native_replay.supporting_inputs[0].path value mismatch",
        ),
    ],
)
def test_static_checker_rejects_structure_preserving_manifest_mutations(
    label: str,
    mutate,
    expected_error: str,
) -> None:
    del label
    document = copy.deepcopy(support.expected_manifest())
    mutate(document)

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert expected_error in report["errors"]
    assert report["facts"]["execution_checked"] is False
    assert report["facts"]["scoped_native_replay_claim_allowed"] is False


def test_exact_mutation_helper_rejects_a_second_changed_seal_word() -> None:
    root = support.common.resolve_relative_directory(
        support.REPO_ROOT,
        support.EVIDENCE_ROOT_RELATIVE,
    )
    source = support.common.load_artifact(root, support.ARTIFACTS[0]).document
    candidate = support.common.load_artifact(root, support.ARTIFACTS[1]).document
    candidate = copy.deepcopy(candidate)
    candidate["inner"]["Succinct"]["seal"][2] ^= 1

    with pytest.raises(
        support.common.EvidenceInputError,
        match="must change exactly one word",
    ):
        support.common.exact_succinct_seal_word_one_xor_one(source, candidate)


def test_positive_report_contract_rejects_observed_elf_claim() -> None:
    document = copy.deepcopy(support.EXPECTED_POSITIVE_REPORT)
    document["guest_artifact"]["observed_elf_bytes"] = 499_312
    raw = support.canonical_compact_newline(document)

    with pytest.raises(RuntimeError, match="output contract mismatch"):
        checker._require_exact_json_output(raw, support.EXPECTED_POSITIVE_REPORT)


def test_typed_mutation_report_contract_rejects_outer_code_drift() -> None:
    document = copy.deepcopy(support.EXPECTED_REJECT_REPORT)
    document["reject"]["outer_code"] = "accepted"
    raw = support.canonical_compact_newline(document)

    with pytest.raises(RuntimeError, match="output contract mismatch"):
        checker._require_exact_json_output(raw, support.EXPECTED_REJECT_REPORT)


def test_typed_dev_mode_report_contract_rejects_boundary_drift() -> None:
    document = copy.deepcopy(support.EXPECTED_DEV_MODE_REJECT_REPORT)
    document["reject"]["boundary"] = "after_receipt_verification"
    raw = support.canonical_compact_newline(document)

    with pytest.raises(RuntimeError, match="output contract mismatch"):
        checker._require_exact_json_output(
            raw,
            support.EXPECTED_DEV_MODE_REJECT_REPORT,
        )


def test_receipt_controls_require_the_three_exact_process_outcomes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    outcomes = iter(
        (
            subprocess.CompletedProcess(
                args=(),
                returncode=0,
                stdout=support.canonical_compact_newline(
                    support.EXPECTED_POSITIVE_REPORT
                ),
                stderr=b"",
            ),
            subprocess.CompletedProcess(
                args=(),
                returncode=1,
                stdout=b"",
                stderr=support.canonical_compact_newline(
                    support.EXPECTED_DEV_MODE_REJECT_REPORT
                ),
            ),
            subprocess.CompletedProcess(
                args=(),
                returncode=1,
                stdout=b"",
                stderr=support.canonical_compact_newline(
                    support.EXPECTED_REJECT_REPORT
                ),
            ),
        )
    )
    monkeypatch.setattr(checker, "_run_verifier", lambda *_args, **_kwargs: next(outcomes))

    positive, dev_mode, mutation = checker._run_receipt_controls(
        object(),
        {},
        tmp_path,
    )

    assert support.common.sha256_bytes(positive) == (
        support.expected_manifest()["native_replay"]["expected_positive_report"][
            "sha256"
        ]
    )
    assert support.common.sha256_bytes(dev_mode) == (
        support.expected_manifest()["native_replay"][
            "expected_dev_mode_reject_report"
        ]["sha256"]
    )
    assert support.common.sha256_bytes(mutation) == (
        support.expected_manifest()["native_replay"][
            "expected_mutation_reject_report"
        ]["sha256"]
    )


def test_receipt_controls_reject_dev_mode_receipt_acceptance(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    positive = support.canonical_compact_newline(support.EXPECTED_POSITIVE_REPORT)
    outcomes = iter(
        (
            subprocess.CompletedProcess(
                args=(), returncode=0, stdout=positive, stderr=b""
            ),
            subprocess.CompletedProcess(
                args=(), returncode=0, stdout=positive, stderr=b""
            ),
        )
    )
    monkeypatch.setattr(checker, "_run_verifier", lambda *_args, **_kwargs: next(outcomes))

    with pytest.raises(RuntimeError, match="exact reject boundary"):
        checker._run_receipt_controls(object(), {}, tmp_path)


def test_live_mode_cannot_execute_after_static_failure(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = support.expected_manifest()
    document["claims"]["manifest_authorizes_production"] = True
    path = tmp_path / "manifest.json"
    path.write_bytes(support.common.canonical_manifest_bytes(document))

    def forbidden_build(*_args, **_kwargs):
        raise AssertionError("native build must not execute")

    monkeypatch.setattr(checker, "_build_and_replay", forbidden_build)
    report = checker.live_check(
        tmp_path,
        tmp_path / "target",
        manifest_path=path,
    )

    assert report["ok"] is False
    assert report["mode"] == "live"
    assert report["live"] == {"executed": False, "verified": False}
    assert report["facts"]["execution_checked"] is False


def test_live_build_rejects_ancestor_cargo_configuration_before_cargo(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    target = tmp_path / "target"
    target.mkdir(mode=0o700)
    source_root = target / "source"
    workspace = source_root / "zk/zrpf_risc0"
    workspace.mkdir(parents=True)
    cargo_config = target / ".cargo"
    cargo_config.mkdir()
    (cargo_config / "config.toml").write_text(
        '[build]\nrustc-wrapper = "untrusted-wrapper"\n',
        encoding="utf-8",
    )

    monkeypatch.setattr(
        checker.environment,
        "create_private_target",
        lambda _path: target,
    )
    monkeypatch.setattr(
        checker.source_snapshot,
        "SourceSnapshot",
        lambda *_args, **_kwargs: contextlib.nullcontext(source_root),
    )
    monkeypatch.setattr(
        checker.toolchain,
        "verify_toolchain",
        lambda *_args, **_kwargs: ({}, {}),
    )
    monkeypatch.setattr(
        checker,
        "_run_build",
        lambda *_args, **_kwargs: pytest.fail("Cargo build must not start"),
    )

    with pytest.raises(RuntimeError, match="unpinned Cargo config"):
        checker._build_and_replay(
            tmp_path / "risc0",
            tmp_path / "requested-target",
            repo_root,
        )


def test_exact_type_comparison_rejects_bool_integer_aliases() -> None:
    assert support.exact_type_and_value(False, 0) is False
    assert support.exact_type_and_value(True, 1) is False
    assert support.exact_type_and_value({"x": False}, {"x": False}) is True
