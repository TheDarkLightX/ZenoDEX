from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
TARGET = "Proofs/ZUSDProtocolFeeAccrualAllocation.lean"
AGGREGATE = LEAN_DIR / "Proofs.lean"
TOOLCHAIN_DIR = Path(os.environ.get("ZENODEX_LEAN_TOOLCHAIN_DIR", str(LEAN_DIR)))


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake is not installed")
def test_lean_zusd_protocol_fee_accrual_allocation_typechecks() -> None:
    if not (TOOLCHAIN_DIR / "lakefile.lean").exists():
        pytest.skip("Lean project toolchain is missing")
    result = subprocess.run(
        ["lake", "env", "lean", str(LEAN_DIR / TARGET)],
        cwd=str(TOOLCHAIN_DIR),
        capture_output=True,
        text=True,
        check=False,
        timeout=180,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_lean_zusd_protocol_fee_accrual_allocation_has_no_placeholders() -> None:
    source = (LEAN_DIR / TARGET).read_text(encoding="utf-8")
    forbidden = ("sorry", "admit", "axiom ", "unsafe ")
    assert not any(token in source for token in forbidden)


def test_lean_zusd_protocol_fee_accrual_allocation_is_in_default_aggregate() -> None:
    source = AGGREGATE.read_text(encoding="utf-8")
    assert "import Proofs.ZUSDProtocolFeeAccrualAllocation" in source.splitlines()
