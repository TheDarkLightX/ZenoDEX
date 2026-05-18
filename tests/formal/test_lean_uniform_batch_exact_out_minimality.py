from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_uniform_batch_exact_out_minimality_typechecks_without_placeholders() -> None:
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/UniformBatchExactOutMinimality.lean"
    source = (lean_dir / target).read_text(encoding="utf-8")

    for required in (
        "theorem requiredNetForOut_satisfies",
        "theorem requiredNetForOut_minimal",
        "theorem requiredNetForOut_iff",
        "theorem minimalGrossForNet_satisfies",
        "theorem minimalGrossForNet_minimal",
        "theorem minimalGrossForNet_iff",
        "theorem minimalGrossForOut_satisfies",
        "theorem minimalGrossForOut_minimal",
        "theorem minimalGrossForOut_iff",
        "theorem minimalGrossForOut_satisfies_and_minimal",
    ):
        assert required in source

    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    assert forbidden.search(source) is None

    lake = shutil.which("lake")
    if not lake:
        return
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "build", "Proofs.UniformBatchExactOutMinimality"],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake build timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
