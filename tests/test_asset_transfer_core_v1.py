from __future__ import annotations

import os
import subprocess
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
ZRPF_PROTOCOL_ROOT = REPO_ROOT / "zk" / "zrpf_protocol"
RUST_RUNTIME_ROOT = REPO_ROOT / "rust-runtime"


def _run_cargo_test(
    *,
    cwd: Path,
    environment: dict[str, str],
    arguments: list[str],
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["cargo", "test", "--locked", *arguments],
        cwd=cwd,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
        timeout=240,
    )


def test_asset_transfer_shared_core_protocol_and_runtime_contract() -> None:
    # Arrange
    environment = os.environ.copy()

    # Act
    with tempfile.TemporaryDirectory(prefix="zenodex-asset-transfer-zrpf-v1-") as target_dir:
        environment["CARGO_TARGET_DIR"] = target_dir
        arithmetic = _run_cargo_test(
            cwd=ZRPF_PROTOCOL_ROOT,
            environment=environment,
            arguments=["-p", "zenodex-asset-transfer-core"],
        )
        protocol = _run_cargo_test(
            cwd=ZRPF_PROTOCOL_ROOT,
            environment=environment,
            arguments=[
                "-p",
                "zenodex-zrpf-protocol-v3",
                "--test",
                "asset_transfer_v1",
            ],
        )
    with tempfile.TemporaryDirectory(prefix="zenodex-asset-transfer-runtime-v1-") as target_dir:
        environment["CARGO_TARGET_DIR"] = target_dir
        runtime = _run_cargo_test(
            cwd=RUST_RUNTIME_ROOT,
            environment=environment,
            arguments=[
                "-p",
                "zenodex-runtime-core",
                "balance_kernel::tests",
            ],
        )

    # Assert
    assert arithmetic.returncode == 0, arithmetic.stdout + arithmetic.stderr
    assert "3 passed; 0 failed" in arithmetic.stdout
    assert protocol.returncode == 0, protocol.stdout + protocol.stderr
    assert "17 passed; 0 failed" in protocol.stdout
    assert runtime.returncode == 0, runtime.stdout + runtime.stderr
    assert "9 passed; 0 failed" in runtime.stdout
