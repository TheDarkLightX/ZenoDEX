#!/usr/bin/env python3
"""Build the bounded research-only O-005 requirements-floor certificate."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Final

try:
    from tools.build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _atomic_replace_regular_file_v1,
        _git_head_v1,
        _git_is_ancestor_v1,
        _git_tree_entry_v1,
        _git_tree_v1,
        _read_bounded_regular_file_v1,
        _require_inert_path_v1,
    )
    from tools.m6_o005_requirements_floor_completion_v1 import (
        ARTIFACT_SCHEMA_V1,
        EVIDENCE_FILE_PINS_V1,
        EVIDENCE_SUBJECT_COMMIT_V1,
        EVIDENCE_SUBJECT_TREE_V1,
        MAX_ARTIFACT_BYTES_V1,
        MAX_EVIDENCE_FILE_BYTES_V1,
        CompletionRejectV1,
        SubjectEvidenceSnapshotV1,
        build_requirements_floor_completion_artifact_v1,
    )
except ModuleNotFoundError:
    from build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _atomic_replace_regular_file_v1,
        _git_head_v1,
        _git_is_ancestor_v1,
        _git_tree_entry_v1,
        _git_tree_v1,
        _read_bounded_regular_file_v1,
        _require_inert_path_v1,
    )
    from m6_o005_requirements_floor_completion_v1 import (  # type: ignore[no-redef]
        ARTIFACT_SCHEMA_V1,
        EVIDENCE_FILE_PINS_V1,
        EVIDENCE_SUBJECT_COMMIT_V1,
        EVIDENCE_SUBJECT_TREE_V1,
        MAX_ARTIFACT_BYTES_V1,
        MAX_EVIDENCE_FILE_BYTES_V1,
        CompletionRejectV1,
        SubjectEvidenceSnapshotV1,
        build_requirements_floor_completion_artifact_v1,
    )


REPO_ROOT: Final = Path(__file__).resolve().parents[1]
JSON_OUTPUT: Final = Path("docs/research/M6_O005_REQUIREMENTS_FLOOR_COMPLETION_V1.json")


def load_subject_snapshot_v1(root: Path | str) -> SubjectEvidenceSnapshotV1:
    """Acquire one race-checked, current-subject snapshot for the pure core."""

    inert_root = _require_inert_path_v1(root, "O005 completion root")
    captured_head = _git_head_v1(inert_root)
    subject_tree = _git_tree_v1(inert_root, EVIDENCE_SUBJECT_COMMIT_V1)
    if subject_tree != EVIDENCE_SUBJECT_TREE_V1:
        raise CompletionRejectV1("SUBJECT_TREE", "Git", "immutable evidence subject tree drift")
    source_entries = tuple(
        _git_tree_entry_v1(inert_root, EVIDENCE_SUBJECT_COMMIT_V1, pin.path)
        for pin in EVIDENCE_FILE_PINS_V1
    )
    current_entries = tuple(
        _git_tree_entry_v1(inert_root, captured_head, pin.path) for pin in EVIDENCE_FILE_PINS_V1
    )
    subject_bytes = tuple(
        (
            pin.path,
            _read_bounded_regular_file_v1(
                inert_root / pin.path, MAX_EVIDENCE_FILE_BYTES_V1, f"O005 subject {pin.path}"
            ),
        )
        for pin in EVIDENCE_FILE_PINS_V1
    )
    rechecked_head = _git_head_v1(inert_root)
    return SubjectEvidenceSnapshotV1(
        captured_git_head=captured_head,
        rechecked_git_head=rechecked_head,
        evidence_subject_is_current_ancestor=_git_is_ancestor_v1(
            inert_root, EVIDENCE_SUBJECT_COMMIT_V1, captured_head
        ),
        evidence_subject_tree=subject_tree,
        source_subject_entries=source_entries,
        current_head_entries=current_entries,
        source_subject_bytes=subject_bytes,
        current_content_bytes=subject_bytes,
    )


def build_artifact_v1(root: Path | str) -> bytes:
    """Build certificate bytes from shell-acquired evidence only."""

    return build_requirements_floor_completion_artifact_v1(load_subject_snapshot_v1(root))


def _failure_report_v1(exc: CompletionRejectV1 | ShellRejectV1) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "closed_value_movement_gates": 0,
        "finding": {"code": exc.code, "detail": exc.detail, "path": exc.path},
        "manifest_complete": False,
        "ok": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "requirements_closed": False,
        "schema": "zenodex/m6-o005-requirements-floor-completion-build/v1",
        "semantic_closure_complete": False,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        expected = build_artifact_v1(args.root)
        output = args.root / JSON_OUTPUT
        if args.check:
            actual = _read_bounded_regular_file_v1(
                output, MAX_ARTIFACT_BYTES_V1, "O005 completion certificate"
            )
            ok = actual == expected
            print(
                json.dumps(
                    {
                        "artifact_sha256": hashlib.sha256(actual).hexdigest() if ok else "",
                        "manifest_complete": False,
                        "ok": ok,
                        "production_authority": "NONE",
                        "release_authority": "NONE",
                        "requirements_closed": False,
                        "schema": "zenodex/m6-o005-requirements-floor-completion-build/v1",
                        "settlement_authority": "NONE",
                        "value_movement_authority": "NONE",
                    },
                    sort_keys=True,
                )
            )
            return 0 if ok else 1
        _atomic_replace_regular_file_v1(output, expected)
        print(
            json.dumps(
                {
                    "artifact_sha256": hashlib.sha256(expected).hexdigest(),
                    "artifact_schema": ARTIFACT_SCHEMA_V1,
                    "manifest_complete": False,
                    "ok": True,
                    "production_authority": "NONE",
                    "release_authority": "NONE",
                    "requirements_closed": False,
                    "schema": "zenodex/m6-o005-requirements-floor-completion-build/v1",
                    "settlement_authority": "NONE",
                    "value_movement_authority": "NONE",
                },
                sort_keys=True,
            )
        )
        return 0
    except (CompletionRejectV1, ShellRejectV1) as exc:
        print(json.dumps(_failure_report_v1(exc), sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
