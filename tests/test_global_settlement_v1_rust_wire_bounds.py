from __future__ import annotations

import os
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_cargo_test(manifest: str, *selectors: str) -> None:
    environment = os.environ.copy()
    environment["CARGO_NET_OFFLINE"] = "true"
    manifest_path = REPO_ROOT / manifest
    completed = subprocess.run(
        (
            "cargo",
            "test",
            "--manifest-path",
            "Cargo.toml",
            "--locked",
            *selectors,
        ),
        cwd=manifest_path.parent,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr


def test_rust_global_state_and_effect_wire_bounds() -> None:
    _run_cargo_test(
        "zk/global_settlement_abi_v1/Cargo.toml",
        "--lib",
        "--test",
        "wire_decode_resource_bounds",
    )


def test_mounted_initial_state_rejects_oversized_nested_state_during_decode() -> None:
    _run_cargo_test(
        "zk/economic_initial_state_risc0/shared/Cargo.toml",
        "--test",
        "initial_state_guest_contract",
        "canonical_wire_decoder_maps_oversized_nested_state_to_decode",
    )
