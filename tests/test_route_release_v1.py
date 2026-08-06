from __future__ import annotations

import os
import subprocess
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
ZRPF_PROTOCOL_ROOT = REPO_ROOT / "zk" / "zrpf_protocol"


def test_route_release_rust_contract() -> None:
    # Arrange
    environment = os.environ.copy()

    # Act
    with tempfile.TemporaryDirectory(prefix="zenodex-route-release-v1-") as target_dir:
        environment["CARGO_TARGET_DIR"] = target_dir
        completed = subprocess.run(
            [
                "cargo",
                "test",
                "--locked",
                "-p",
                "zenodex-zrpf-protocol-v3",
                "--test",
                "route_release_v1",
            ],
            cwd=ZRPF_PROTOCOL_ROOT,
            env=environment,
            check=False,
            capture_output=True,
            text=True,
            timeout=180,
        )

    # Assert
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert "18 passed; 0 failed" in completed.stdout
