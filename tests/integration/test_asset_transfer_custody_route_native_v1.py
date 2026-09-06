"""Replay the custody route's native semantic controls through the Python gate.

Requires installed Rust 1.90.0 and the locked offline dependencies. This runs
only the ordinary-data shared target, with no guest or proof generation.
Set CARGO_TARGET_DIR to reuse an existing native cache.
"""

from __future__ import annotations

import os
import subprocess
from pathlib import Path


def test_native_custody_route_replays_semantics_and_resource_boundaries() -> None:
    root = Path(__file__).resolve().parents[2]
    manifest = root / "zk/asset_transfer_custody_route_risc0/Cargo.toml"
    environment = dict(os.environ)
    environment.update({
        "CARGO_INCREMENTAL": "0",
        "CARGO_PROFILE_DEV_DEBUG": "0",
        "CARGO_BUILD_JOBS": "2",
        "CARGO_NET_OFFLINE": "true",
    })
    # rustup run does not install a missing toolchain without --install.
    result = subprocess.run(
        [
            "rustup", "run", "1.90.0", "cargo", "test",
            "--manifest-path", str(manifest), "--offline", "--locked",
            "-p", "zenodex-asset-transfer-custody-route-risc0-shared",
            "--test", "custody_route_preflight",
        ],
        cwd=root,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout=180,
    )
    assert result.returncode == 0, result.stdout[-8_000:]
    for node in (
        "matching_roots_and_nonzero_custody_prepare_the_route_from_retained_components",
        "exact_selected_module_journal_ceiling_applies_to_all_route_entries",
        "resource_bounds::coherent_oversized_typed_route_rejects_at_the_same_outer_wire_ceiling",
    ):
        assert f"test {node} ... ok" in result.stdout, result.stdout[-8_000:]
