from __future__ import annotations

import copy
import os
import shutil
from pathlib import Path

import pytest

from tools import zrpf_v3_source_closure as closure

REPO_ROOT = Path(__file__).resolve().parents[1]


def test_current_clean_checkout_matches_exact_source_inventory() -> None:
    document = closure.build_source_closure(REPO_ROOT)
    assert document["schema"] == closure.SCHEMA
    assert document["file_count"] == 327
    semantic_v2_roles = {
        "semantic_mapping_v2",
        "semantic_protocol_v2",
        "verification_harness_v2",
    }
    assert {
        (row["role"], row["path"]) for row in document["files"] if row["role"] in semantic_v2_roles
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
    v4_paths = {row["path"] for row in document["files"] if row["role"].endswith("_v4")}
    assert v4_paths == {
        "zk/zrpf_protocol/protocol/src/value_node_v4/bounded.rs",
        "zk/zrpf_protocol/protocol/src/value_node_v4/error.rs",
        "zk/zrpf_protocol/protocol/src/value_node_v4/journal.rs",
        "zk/zrpf_protocol/protocol/src/value_node_v4/mod.rs",
        "zk/zrpf_protocol/protocol/src/value_node_v4/records.rs",
        "zk/zrpf_protocol/protocol/src/value_node_v4/subtree.rs",
        "zk/zrpf_protocol/protocol/src/value_node_v4/subtree/codec.rs",
        "zk/zrpf_protocol/protocol/src/value_node_v4/subtree/hash.rs",
        "zk/zrpf_protocol/protocol/src/value_node_v4/subtree/merge.rs",
        "zk/zrpf_protocol/protocol/src/value_node_v4/subtree/validate.rs",
        "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4.rs",
        "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4/artifact_io.rs",
        "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4/report.rs",
        "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4/source.rs",
        "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4/tests.rs",
        "zk/zrpf_risc0/methods/spot_value_leaf_v4/Cargo.toml",
        "zk/zrpf_risc0/methods/spot_value_leaf_v4/src/main.rs",
        "zk/zrpf_risc0/semantic_shared/src/value_v1.rs",
        "zk/zrpf_risc0/semantic_shared/src/value_v1/compose.rs",
        "zk/zrpf_risc0/semantic_shared/src/value_v1/error.rs",
        "zk/zrpf_risc0/semantic_shared/src/value_v1/expected.rs",
        "zk/zrpf_risc0/semantic_shared/src/value_v1/hash.rs",
        "zk/zrpf_risc0/semantic_shared/src/value_v1/validate.rs",
        "zk/zrpf_risc0/semantic_shared/src/value_v1/wire_v4.rs",
        "zk/zrpf_risc0/semantic_shared/src/value_v1/wire_v4/error.rs",
        "zk/zrpf_risc0/value_node_shared/Cargo.toml",
        "zk/zrpf_risc0/value_node_shared/src/cursor.rs",
        "zk/zrpf_risc0/value_node_shared/src/error.rs",
        "zk/zrpf_risc0/value_node_shared/src/leaf.rs",
        "zk/zrpf_risc0/value_node_shared/src/leaf_codec.rs",
        "zk/zrpf_risc0/value_node_shared/src/lib.rs",
        "zk/zrpf_risc0/value_node_shared/src/profile.rs",
        "zk/zrpf_risc0/verifier/src/spot_value_leaf_v4.rs",
        "zk/zrpf_risc0/verifier/src/spot_value_leaf_v4/tests.rs",
    }
    direct_v5_roles = {
        "value_aggregate_guest_v5",
        "value_aggregate_l2_policy_v5",
        "value_aggregate_root_policy_v5",
        "value_aggregate_mapping_v5",
    }
    assert {row["path"] for row in document["files"] if row["role"] in direct_v5_roles} == {
        "zk/zrpf_risc0/methods/ordinary_spot_settlement/Cargo.toml",
        "zk/zrpf_risc0/methods/value_aggregate_l1/Cargo.toml",
        "zk/zrpf_risc0/methods/value_aggregate_l1/src/main.rs",
        "zk/zrpf_risc0/methods/value_aggregate_l2/Cargo.toml",
        "zk/zrpf_risc0/methods/value_aggregate_l2/src/main.rs",
        "zk/zrpf_risc0/value_aggregate_l2_policy/Cargo.toml",
        "zk/zrpf_risc0/value_aggregate_l2_policy/src/lib.rs",
        "zk/zrpf_risc0/value_aggregate_root_policy/Cargo.toml",
        "zk/zrpf_risc0/value_aggregate_root_policy/src/lib.rs",
        "zk/zrpf_risc0/value_aggregate_shared/Cargo.toml",
        "zk/zrpf_risc0/value_aggregate_shared/src/child.rs",
        "zk/zrpf_risc0/value_aggregate_shared/src/error.rs",
        "zk/zrpf_risc0/value_aggregate_shared/src/guest_input.rs",
        "zk/zrpf_risc0/value_aggregate_shared/src/input.rs",
        "zk/zrpf_risc0/value_aggregate_shared/src/level_one.rs",
        "zk/zrpf_risc0/value_aggregate_shared/src/level_two.rs",
        "zk/zrpf_risc0/value_aggregate_shared/src/lib.rs",
        "zk/zrpf_risc0/value_aggregate_shared/src/policy.rs",
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


def test_workspace_inventory_rejects_automatic_cargo_build_script(tmp_path: Path) -> None:
    root = _copy_source_inventory(tmp_path)
    build_script = root / "zk/zrpf_risc0/harness/build.rs"
    build_script.write_text("fn main() {}\n", encoding="utf-8")

    with pytest.raises(closure.SourceClosureError, match="harness/build.rs"):
        closure._validate_governed_workspace_inventory(root)


@pytest.mark.parametrize(
    "relative",
    (
        ".cargo/config.toml",
        "zk/zrpf_protocol/.cargo/config.toml",
        "zk/state_proof_risc0/.cargo/config",
    ),
)
def test_workspace_inventory_rejects_unlisted_cargo_config(
    tmp_path: Path,
    relative: str,
) -> None:
    root = _copy_source_inventory(tmp_path)
    config = root / relative
    config.parent.mkdir(parents=True, exist_ok=True)
    config.write_text(
        '[build]\nrustflags = ["--cfg", "zrpf_adversarial_root_config"]\n',
        encoding="utf-8",
    )

    with pytest.raises(closure.SourceClosureError, match="Cargo compiler control inventory"):
        closure._validate_governed_workspace_inventory(root)


def test_workspace_inventory_rejects_custom_cargo_build_script(tmp_path: Path) -> None:
    root = _copy_source_inventory(tmp_path)
    manifest = root / "zk/zrpf_risc0/harness/Cargo.toml"
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace(
            "[package]\n",
            '[package]\nbuild = "custom-build.rs"\n',
            1,
        ),
        encoding="utf-8",
    )
    (manifest.parent / "custom-build.rs").write_text("fn main() {}\n", encoding="utf-8")

    with pytest.raises(closure.SourceClosureError, match="custom-build.rs"):
        closure._validate_governed_workspace_inventory(root)


@pytest.mark.parametrize(
    ("manifest_relative", "source_relative"),
    (
        (
            "zk/zrpf_risc0/methods/ordinary_spot_settlement/Cargo.toml",
            "zk/zrpf_risc0/methods/ordinary_spot_settlement/src/main.rs",
        ),
        (
            "zk/zrpf_protocol/protocol/Cargo.toml",
            "zk/zrpf_protocol/protocol/src/lib.rs",
        ),
        (
            "zk/state_proof_risc0/shared/Cargo.toml",
            "zk/state_proof_risc0/shared/src/lib.rs",
        ),
        (
            "zk/zrpf_risc0/aggregate_shared/Cargo.toml",
            "zk/zrpf_risc0/aggregate_shared/src/lib.rs",
        ),
        (
            "zk/zrpf_risc0/value_aggregate_l2_policy/Cargo.toml",
            "zk/zrpf_risc0/value_aggregate_l2_policy/src/lib.rs",
        ),
    ),
)
def test_workspace_inventory_rejects_unlisted_rust_even_with_build_false(
    tmp_path: Path,
    manifest_relative: str,
    source_relative: str,
) -> None:
    root = _copy_source_inventory(tmp_path)
    manifest = root / manifest_relative
    manifest_text = manifest.read_text(encoding="utf-8")
    if "build = false" not in manifest_text:
        manifest.write_text(
            manifest_text.replace(
                "[package]\n",
                "[package]\nbuild = false\n",
                1,
            ),
            encoding="utf-8",
        )
    disabled = manifest.parent / "build.rs"
    disabled.write_text("fn main() {}\n", encoding="utf-8")
    source = root / source_relative
    source.write_text(
        f'include!("../build.rs");\n{source.read_text(encoding="utf-8")}',
        encoding="utf-8",
    )

    with pytest.raises(closure.SourceClosureError, match="build.rs"):
        closure._validate_governed_workspace_inventory(root)


def test_workspace_inventory_rejects_symlinked_cargo_control(tmp_path: Path) -> None:
    root = _copy_source_inventory(tmp_path)
    target = root / "untrusted-build.rs"
    target.write_text("fn main() {}\n", encoding="utf-8")
    (root / "zk/zrpf_risc0/harness/build.rs").symlink_to(target)

    with pytest.raises(closure.SourceClosureError, match="symlinked"):
        closure._validate_governed_workspace_inventory(root)


def test_workspace_inventory_rejects_symlinked_source_directory(tmp_path: Path) -> None:
    root = _copy_source_inventory(tmp_path)
    untrusted = root / "untrusted-source"
    untrusted.mkdir()
    (untrusted / "evil.rs").write_text("pub const EVIL: bool = true;\n", encoding="utf-8")
    linked = root / "zk/zrpf_protocol/protocol/src/linked"
    linked.symlink_to(untrusted, target_is_directory=True)
    source = root / "zk/zrpf_protocol/protocol/src/lib.rs"
    source.write_text(
        f'#[path = "linked/evil.rs"] mod evil;\n{source.read_text(encoding="utf-8")}',
        encoding="utf-8",
    )

    with pytest.raises(closure.SourceClosureError, match="symlink"):
        closure._validate_governed_workspace_inventory(root)


def test_workspace_inventory_rejects_unlisted_include_bytes_payload(tmp_path: Path) -> None:
    root = _copy_source_inventory(tmp_path)
    source = root / "zk/zrpf_protocol/protocol/src/lib.rs"
    source.write_text(
        f'const OMITTED: &[u8] = include_bytes!("../../omitted_workspace_payload.bin");\n'
        f"{source.read_text(encoding='utf-8')}",
        encoding="utf-8",
    )
    (root / "zk/zrpf_protocol/omitted_workspace_payload.bin").write_bytes(b"compiler-visible")

    with pytest.raises(closure.SourceClosureError, match="omitted_workspace_payload.bin"):
        closure._validate_governed_workspace_inventory(root)


def _copy_source_inventory(tmp_path: Path) -> Path:
    root = tmp_path / "source"
    for _, relative in closure.SOURCE_ROWS:
        source = REPO_ROOT / relative
        destination = root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
    return root
