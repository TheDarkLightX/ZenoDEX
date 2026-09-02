from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CRATE = ROOT / "zk" / "global_settlement_abi_v1"


def test_rust_transition_resource_bound_totality_replay(tmp_path: Path) -> None:
    cargo = shutil.which("cargo")
    assert cargo is not None, "Rust transition totality replay requires cargo"

    env = os.environ.copy()
    env["CARGO_TARGET_DIR"] = str(tmp_path / "cargo-target")
    env["RUSTFLAGS"] = "-Dwarnings"
    result = subprocess.run(
        [
            cargo,
            "test",
            "--locked",
            "--test",
            "transition_resource_bound_totality",
            "--",
            "--nocapture",
        ],
        cwd=CRATE,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=600,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    output = result.stdout + result.stderr
    assert "test result: ok." in output
    assert "4 passed" in output
