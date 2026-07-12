from __future__ import annotations

import copy
import os
from pathlib import Path

import pytest

from tools import zrpf_v3_source_closure as closure

REPO_ROOT = Path(__file__).resolve().parents[1]


def test_current_clean_checkout_matches_exact_source_inventory() -> None:
    document = closure.build_source_closure(REPO_ROOT)
    assert document["schema"] == closure.SCHEMA
    assert document["file_count"] == 65
    assert {
        (row["role"], row["path"])
        for row in document["files"]
        if row["role"].endswith("_v2")
    } == {
        (
            "semantic_mapping_v2",
            "zk/zrpf_risc0/semantic_shared/src/bind_v2.rs",
        ),
        (
            "semantic_mapping_v2",
            "zk/zrpf_risc0/semantic_shared/src/codec_v2.rs",
        ),
        (
            "semantic_mapping_v2",
            "zk/zrpf_risc0/semantic_shared/src/disclosure_v1.rs",
        ),
        (
            "semantic_mapping_v2",
            "zk/zrpf_risc0/semantic_shared/src/epoch_v2.rs",
        ),
        (
            "semantic_protocol_v2",
            "zk/zrpf_protocol/protocol/src/semantic_epoch_v2/hash.rs",
        ),
        (
            "semantic_protocol_v2",
            "zk/zrpf_protocol/protocol/src/semantic_epoch_v2/mod.rs",
        ),
        (
            "semantic_protocol_v2",
            "zk/zrpf_protocol/protocol/src/semantic_epoch_v2/proposal.rs",
        ),
        (
            "verification_harness_v2",
            "zk/zrpf_risc0/verifier/src/semantic_epoch_v2.rs",
        ),
    }
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


def test_source_reader_rejects_symlinked_parent_and_fifo(tmp_path: Path) -> None:
    real = tmp_path / "real"
    real.mkdir()
    (real / "source.rs").write_text("fn main() {}\n", encoding="utf-8")
    (tmp_path / "linked").symlink_to(real, target_is_directory=True)
    os.mkfifo(tmp_path / "source.fifo")

    with pytest.raises(closure.SourceClosureError, match="unavailable"):
        closure._read_source(tmp_path, "linked/source.rs")
    with pytest.raises(closure.SourceClosureError, match="bounded regular"):
        closure._read_source(tmp_path, "source.fifo")
