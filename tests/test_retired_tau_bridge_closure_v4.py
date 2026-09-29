"""Pure-data conformance tests for the bounded O-003B V4 successor core."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from tools import build_retired_tau_bridge_closure_v3 as acquisition
from tools import retired_tau_bridge_closure_v3 as legacy
from tools import retired_tau_bridge_closure_v4 as closure

ROOT = Path(__file__).resolve().parents[1]


def _adapter_source(*, widened: bool, body: str = "return value") -> bytes:
    balance_import = "NATIVE_ASSET, BalanceTable"
    nonce_import = "NonceTable"
    balance_annotation = "BalanceTable"
    nonce_annotation = "NonceTable"
    if widened:
        balance_import = "NATIVE_ASSET, BalanceSnapshot, BalanceTable"
        nonce_import = "NonceSnapshot, NonceTable"
        balance_annotation = "BalanceTable | BalanceSnapshot"
        nonce_annotation = "NonceTable | NonceSnapshot"
    return (
        "from ..state.balances import "
        f"{balance_import}\n"
        f"from ..state.nonces import {nonce_import}\n\n"
        f"def _copy_balance_table(value: {balance_annotation}) -> BalanceTable:\n"
        f"    {body}\n\n"
        f"def _copy_nonce_table(value: {nonce_annotation}) -> NonceTable:\n"
        f"    {body}\n"
    ).encode("utf-8")


def _source(path: str, data: bytes) -> legacy.SourceFileV3:
    return legacy.SourceFileV3(path=path, git_blob_sha=legacy._git_blob_sha(data), data=data)


def _git(*arguments: str) -> bytes:
    """Read immutable repository objects for an explicitly unqualified fixture."""

    return subprocess.check_output(
        ("git", *arguments),
        cwd=ROOT,
    )


def _git_text(*arguments: str) -> str:
    return _git(*arguments).decode("ascii").strip()


def _bare_snapshot() -> closure.QualificationSnapshotV4:
    source = legacy.SourceSnapshotV3(commit="1" * 40, tree="2" * 40, files=())
    current = legacy.SubjectSnapshotV3(
        captured_head="1" * 40,
        rechecked_head="1" * 40,
        baseline=source,
        subject=source,
        baseline_is_subject_ancestor=True,
        subject_is_current_ancestor=True,
    )
    return closure.QualificationSnapshotV4(
        current=current,
        predecessor=current,
        predecessor_artifact=b"not the immutable predecessor",
        extra_sources=(),
    )


@pytest.fixture(scope="module")
def unqualified_fixture_snapshot() -> closure.QualificationSnapshotV4:
    """Exercise pure derivation; this fixture never claims Stage-A/B qualification."""

    def historical(path: str) -> legacy.SourceFileV3:
        return _source(
            path,
            _git("show", f"{closure.PREDECESSOR_SUBJECT_V4}:{path}"),
        )

    baseline_discovery = acquisition._git_python_discovery_v3(ROOT, legacy.BASELINE_COMMIT_V3)
    predecessor_discovery = acquisition._git_python_discovery_v3(
        ROOT,
        closure.PREDECESSOR_SUBJECT_V4,
    )
    baseline = legacy.SourceSnapshotV3(
        commit=legacy.BASELINE_COMMIT_V3,
        tree=legacy.BASELINE_TREE_V3,
        files=tuple(
            _source(path, _git("show", f"{legacy.BASELINE_COMMIT_V3}:{path}"))
            for path in legacy.BASELINE_PIN_PATHS_V3
        ),
        discovery=baseline_discovery,
    )
    predecessor_subject = legacy.SourceSnapshotV3(
        commit=closure.PREDECESSOR_SUBJECT_V4,
        tree=_git_text("rev-parse", f"{closure.PREDECESSOR_SUBJECT_V4}^{{tree}}"),
        files=tuple(historical(path) for path in legacy.SUBJECT_PIN_PATHS_V3),
        discovery=predecessor_discovery,
    )
    predecessor = legacy.SubjectSnapshotV3(
        captured_head=closure.PREDECESSOR_SUBJECT_V4,
        rechecked_head=closure.PREDECESSOR_SUBJECT_V4,
        baseline=baseline,
        subject=predecessor_subject,
        baseline_is_subject_ancestor=True,
        subject_is_current_ancestor=True,
        current_discovery=predecessor_discovery,
    )
    current_discovery = acquisition._worktree_python_discovery_v3(ROOT)
    current_subject = legacy.SourceSnapshotV3(
        commit=_git_text("rev-parse", "HEAD"),
        tree=_git_text("rev-parse", "HEAD^{tree}"),
        files=tuple(
            _source(path, (ROOT / path).read_bytes())
            if path in closure.APPROVED_CHANGED_PINS_V4
            else historical(path)
            for path in legacy.SUBJECT_PIN_PATHS_V3
        ),
        discovery=current_discovery,
    )
    current = legacy.SubjectSnapshotV3(
        captured_head=current_subject.commit,
        rechecked_head=current_subject.commit,
        baseline=baseline,
        subject=current_subject,
        baseline_is_subject_ancestor=True,
        subject_is_current_ancestor=True,
        current_discovery=current_discovery,
    )
    return closure.QualificationSnapshotV4(
        current=current,
        predecessor=predecessor,
        predecessor_artifact=_git(
            "show",
            f"{closure.PREDECESSOR_COMMIT_V4}:{legacy.OUTPUT_PATH_V3}",
        ),
        extra_sources=tuple(
            _source(path, (ROOT / path).read_bytes()) for path in closure.EXTRA_PIN_PATHS_V4
        ),
    )


@pytest.mark.parametrize("path", sorted(closure._ADAPTER_SNAPSHOTS_V4))
def test_reviewed_snapshot_type_widening_normalizes_to_predecessor_ast(path: str) -> None:
    previous = _adapter_source(widened=False)
    current = _adapter_source(widened=True)

    closure._validate_adapter_delta_v4(previous, current, path)


@pytest.mark.parametrize("path", sorted(closure._ADAPTER_SNAPSHOTS_V4))
def test_adapter_normalization_rejects_a_body_change(path: str) -> None:
    previous = _adapter_source(widened=False)
    current = _adapter_source(widened=True, body="return altered")

    with pytest.raises(closure.ClosureRejectV4, match="ADAPTER_AST_DELTA"):
        closure._validate_adapter_delta_v4(previous, current, path)


def test_successor_configuration_is_closed_sorted_and_never_self_pins_receipt() -> None:
    closure._validate_configuration_v4()

    assert closure.EXTRA_PIN_PATHS_V4 == tuple(sorted(closure.EXTRA_PIN_PATHS_V4))
    assert closure.OUTPUT_PATH_V4 not in closure.EXTRA_PIN_PATHS_V4
    assert tuple(sorted(closure.APPROVED_CHANGED_PINS_V4)) == closure._APPROVED_CHANGED_PATHS_V4


def test_failure_report_is_authority_free_and_binds_the_known_predecessor() -> None:
    report = closure.failure_report_v4(
        closure.ClosureRejectV4("TEST_REJECT", "test", "ordinary conformance")
    )

    assert report == {
        "artifact_sha256": "",
        "classification_counts": {},
        "closed_value_movement_gates": 0,
        "current_only_import_edge_count": None,
        "dependency_count": 0,
        "findings": [
            {"code": "TEST_REJECT", "detail": "ordinary conformance", "path": "test"}
        ],
        "o003b_status": "OPEN",
        "ok": False,
        "predecessor_artifact_sha256": closure.PREDECESSOR_SHA256_V4,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": closure.CHECK_SCHEMA_V4,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


def test_stale_approved_legacy_digest_rejects_before_adapter_equivalence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    previous = {
        path: _source(path, f"previous:{path}".encode("utf-8"))
        for path in legacy.SUBJECT_PIN_PATHS_V3
    }
    current = dict(previous)
    for path in closure._APPROVED_CHANGED_PATHS_V4:
        current[path] = _source(path, f"current:{path}".encode("utf-8"))
    approved = {
        path: legacy._sha256(current[path].data) for path in closure._APPROVED_CHANGED_PATHS_V4
    }
    approved["docs/PRODUCTION_BOUNDARY_CLOSURE_AUDIT.md"] = "0" * 64
    monkeypatch.setattr(closure, "APPROVED_CHANGED_PINS_V4", approved)

    with pytest.raises(closure.ClosureRejectV4, match="APPROVED_PIN_SHA"):
        closure._change_records_v4(previous, current)


@pytest.mark.parametrize("sources", [(), "duplicate"])
def test_extra_pin_snapshot_rejects_missing_or_duplicate_rows(sources: object) -> None:
    snapshot = _bare_snapshot()
    rows = tuple(
        _source(path, f"extra:{path}".encode("utf-8")) for path in closure.EXTRA_PIN_PATHS_V4
    )
    if sources == "duplicate":
        rows = (*rows[:-1], rows[0])
    snapshot = closure.QualificationSnapshotV4(
        current=snapshot.current,
        predecessor=snapshot.predecessor,
        predecessor_artifact=snapshot.predecessor_artifact,
        extra_sources=rows if sources == "duplicate" else (),
    )

    with pytest.raises(closure.ClosureRejectV4, match="SOURCE_SCOPE"):
        closure._extra_source_map_v4(snapshot)


def test_wrong_predecessor_receipt_digest_rejects_before_replay() -> None:
    with pytest.raises(closure.ClosureRejectV4, match="PREDECESSOR_ARTIFACT_SHA"):
        closure._predecessor_template_v4(_bare_snapshot())


def test_noncanonical_artifact_bytes_reject_before_derivation() -> None:
    with pytest.raises(closure.ClosureRejectV4, match="NONCANONICAL_ARTIFACT"):
        closure.check_artifact_v4(b"{} \n", _bare_snapshot())


def test_unqualified_fixture_rebuilds_canonical_successor_and_rejects_drift(
    unqualified_fixture_snapshot: closure.QualificationSnapshotV4,
) -> None:
    """A configuration fixture exercises only pure representation, never acceptance topology."""

    raw = closure.build_artifact_v4(unqualified_fixture_snapshot)
    report = closure.check_artifact_v4(raw, unqualified_fixture_snapshot)
    artifact = json.loads(raw)
    unsigned = dict(artifact)
    unsigned["status"] = "UNQUALIFIED_FIXTURE_DRIFT"
    unsigned["certificate_root"] = legacy._sha256(
        legacy.canonical_json_bytes_v3(
            {key: value for key, value in unsigned.items() if key != "certificate_root"}
        )
    )

    assert report["ok"] is True
    assert report["predecessor_artifact_sha256"] == closure.PREDECESSOR_SHA256_V4
    with pytest.raises(closure.ClosureRejectV4, match="ARTIFACT_REPLAY_MISMATCH"):
        closure.check_artifact_v4(
            legacy.canonical_json_bytes_v3(unsigned),
            unqualified_fixture_snapshot,
        )
