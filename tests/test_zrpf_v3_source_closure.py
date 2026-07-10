from __future__ import annotations

import copy
from pathlib import Path

from tools import zrpf_v3_source_closure as closure


REPO_ROOT = Path(__file__).resolve().parents[1]


def test_current_clean_checkout_matches_exact_source_inventory() -> None:
    document = closure.build_source_closure(REPO_ROOT)
    assert document["schema"] == closure.SCHEMA
    assert document["file_count"] == 37
    assert document["worktree_clean"] is True
    assert [row["path"] for row in document["files"]] == sorted(
        row["path"] for row in document["files"]
    )
    assert not closure.check_source_closure(document, REPO_ROOT)


def test_checker_rejects_a_rebound_source_digest() -> None:
    document = closure.build_source_closure(REPO_ROOT)
    rebound = copy.deepcopy(document)
    rebound["files"][0]["sha256"] = "0" * 64
    assert closure.check_source_closure(rebound, REPO_ROOT) == [
        "source closure differs from the current clean worktree"
    ]
