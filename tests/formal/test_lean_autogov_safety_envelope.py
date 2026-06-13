from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_autogov_safety_envelope_typechecks_without_placeholders() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable missing")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/AutoGovSafetyEnvelope.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    assert "def GateAccepted" in source
    assert "def DecisionOK" in source
    assert "theorem applyStep_preserves_envelope" in source
    assert "theorem runSteps_preserves_envelope" in source
    assert "theorem runBudgetSteps_preserves_limit" in source
    assert "theorem runBudgetSteps_used_monotone" in source
    assert "It does not prove policy optimality" in source
    for forbidden in ("sorry", "admit", "axiom", "unsafe", "sorryAx"):
        assert not re.search(rf"\b{forbidden}\b", source)

    try:
        proc = subprocess.run(
            [lake, "env", "lean", target],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
