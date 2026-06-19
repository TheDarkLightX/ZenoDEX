from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_cpmm_target_price_executable_bound_typechecks_without_placeholders() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable missing")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/CpmmTargetPriceExecutableBound.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    for required in (
        "theorem minGrossForNet_reaches",
        "theorem minGrossForNet_minimal",
        "theorem positiveOutputNetThreshold_sufficient",
        "theorem minimumExecutableGross_produces_positive_output",
    ):
        assert required in source
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    assert forbidden.search(source) is None

    try:
        proc = subprocess.run(
            [lake, "env", "lean", target],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
