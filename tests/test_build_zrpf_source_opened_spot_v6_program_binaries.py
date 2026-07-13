from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "build_zrpf_source_opened_spot_v6_program_binaries.sh"


def _source() -> str:
    return SCRIPT.read_text(encoding="utf-8")


def test_recipe_pins_image_canonical_source_and_bounded_container() -> None:
    source = _source()

    assert source.startswith("#!/bin/bash -p\n")
    assert (
        "ubuntu@sha256:4fbb8e6a8395de5a7550b33509421a2bafbc0aab6c06ba2cef9ebffbc7092d90"
        in source
    )
    assert "readonly CANONICAL_SOURCE_ROOT=/src/zenodex" in source
    assert '"$DOCKER" image inspect "$BUILD_IMAGE"' in source
    assert "docker pull" not in source
    for required_option in (
        "--network none",
        "--read-only",
        "--cap-drop ALL",
        "--security-opt no-new-privileges",
        "--pids-limit 512",
        "--cpus 2",
        "--memory 6g",
        "--memory-swap 6g",
    ):
        assert required_option in source
    assert "--cpus 3" not in source
    assert "--cpus 4" not in source
    assert "/var/run/docker.sock" not in source
    assert "--privileged" not in source


def test_recipe_requires_one_exact_clean_committed_source_snapshot() -> None:
    source = _source()

    assert "^[0-9a-f]{40}$" in source
    assert "rev-parse --verify 'HEAD^{commit}'" in source
    assert '[[ $ACTUAL_SOURCE_COMMIT == "$source_commit" ]]' in source
    assert "status --porcelain=v1 --untracked-files=all" in source
    assert "archive --format=tar \"$source_commit\"" in source
    assert "--no-same-owner" in source
    assert "--no-same-permissions" in source
    assert 'target=$CANONICAL_SOURCE_ROOT,readonly"' in source
    assert "source worktree must be completely clean" in source


def test_recipe_mounts_only_pinned_inputs_read_only_and_writes_externally() -> None:
    source = _source()

    assert "--risc0-toolchain-dir" in source
    assert "--cargo-registry-dir" in source
    assert "v1.94.1-rust-x86_64-unknown-linux-gnu" in source
    assert "cargo 1.94.1-dev (29ea6fb6a 2026-03-24)" in source
    assert "rustc 1.94.1-dev (06e01cb0d 2026-04-09)" in source
    assert "target=/opt/risc0-toolchain,readonly" in source
    assert "target=/opt/cargo-registry,readonly" in source
    assert "target=$CONTAINER_TARGET_ROOT" in source
    assert "target=$CONTAINER_OUTPUT_ROOT" in source
    assert '"$HOME/.cargo' not in source
    assert '"$HOME/.risc0' not in source
    assert "CARGO_NET_OFFLINE=true" in source
    assert "RISC0_BUILD_LOCKED=1" in source
    assert "jobs = 2" in source
    assert (
        'linker = "/opt/risc0-toolchain/lib/rustlib/'
        'x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld"'
    ) in source
    assert 'linker = "/opt/risc0-toolchain/bin/lld-wrapper"' not in source


def test_recipe_builds_one_exact_package_with_locked_offline_cargo() -> None:
    source = _source()

    expected_command_fragments = (
        "/risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu/bin/cargo build",
        "--manifest-path /src/zenodex/zk/zrpf_risc0/Cargo.toml",
        "--package zenodex-zrpf-risc0-spot-v6-methods",
        "--release",
        "--locked",
        "--offline",
        "--jobs 2",
        "--target-dir /build/target",
    )
    for fragment in expected_command_fragments:
        assert fragment in source
    assert "RISC0_SKIP_BUILD" in source
    assert "unset RISC0_SKIP_BUILD RUSTUP_TOOLCHAIN" in source
    assert "cargo test" not in source
    assert "cargo clippy" not in source


def test_recipe_extracts_exact_r0bf_program_binary_inventory() -> None:
    source = _source()

    expected_outputs = {
        "spot_value_leaf_v6.bin",
        "spot_value_aggregate_l1_v6.bin",
        "spot_value_aggregate_l2_v6.bin",
        "source_opened_spot_settlement_v6.bin",
    }
    output_names = set(
        re.findall(r"(?:/build/output/|\$output_dir/)([a-z0-9_]+\.bin)", source)
    )
    assert output_names == expected_outputs
    assert "readonly PROGRAM_BINARY_MAGIC_HEX=52304246" in source
    assert "[[ $magic == 52304246 ]]" in source
    assert "-name '*.bin'" in source
    assert "discovered_program_binaries" in source
    assert "extracted program-binary inventory mismatch" in source
    for package in (
        "zenodex-zrpf-risc0-source-opened-spot-settlement-v6",
        "zenodex-zrpf-risc0-spot-value-aggregate-l1-v6",
        "zenodex-zrpf-risc0-spot-value-aggregate-l2-v6",
        "zenodex-zrpf-risc0-spot-value-leaf-v6",
    ):
        assert (
            f"$guest_root/{package}/riscv32im-risc0-zkvm-elf/release/{package}.bin"
            in source
        )
    assert "readelf" not in source
    assert ".elf.bin" not in source


def test_recipe_names_combined_outputs_program_binaries_not_elfs() -> None:
    source = _source().lower()

    assert "program binaries" in source
    assert "r0bf program binary" in source
    assert "guest elf" not in source
    assert "raw_elf" not in source
