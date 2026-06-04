from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def _lean_dir() -> Path:
    return Path(__file__).resolve().parents[2] / "lean-mathlib"


def test_lean_zenodex_nonces_builds_without_warnings() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    proc = subprocess.run(
        [
            lake,
            "env",
            "lean",
            "-DwarningAsError=true",
            "Proofs/ZenoDEXNonces.lean",
        ],
        cwd=_lean_dir(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_zenodex_nonces_exports_range_disjointness_theorem() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    lean_dir = _lean_dir()
    smoke = (
        "import Proofs.ZenoDEXNonces\n"
        "#check Proofs.ZenoDEX.acceptedBatchNonce\n"
        "#check Proofs.ZenoDEX.laterBatchNonce\n"
        "#check Proofs.ZenoDEX.acceptedBatchNonce_not_laterBatchNonce\n"
        "#check Proofs.ZenoDEX.acceptedBatchRange_disjoint_laterBatchRange\n"
        "#check Proofs.ZenoDEX.witness_accepted_later_ranges_disjoint\n"
    )
    smoke_path = lean_dir / ".tmp_zenodex_nonces_smoke.lean"
    smoke_path.write_text(smoke, encoding="utf-8")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", smoke_path.name],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    finally:
        smoke_path.unlink(missing_ok=True)

    assert proc.returncode == 0, proc.stdout + proc.stderr
