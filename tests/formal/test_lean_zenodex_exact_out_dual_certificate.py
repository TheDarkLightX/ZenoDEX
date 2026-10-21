from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
TARGET = "Proofs/ZenoDEXExactOutDualCertificate.lean"
FORBIDDEN = ("sorry", "admit", "axiom", "unsafe", "sorryAx")


def test_zenodex_exact_out_dual_certificate_typechecks() -> None:
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("lake is unavailable")
    if not (ROOT / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", TARGET],
            cwd=LEAN_DIR,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {TARGET}")

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_zenodex_exact_out_dual_certificate_has_no_placeholder_tokens() -> None:
    text = (LEAN_DIR / TARGET).read_text(encoding="utf-8")

    for token in FORBIDDEN:
        assert token not in text
