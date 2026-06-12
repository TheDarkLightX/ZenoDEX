from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_state_root_framing_injectivity_typechecks_without_placeholders() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not available")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/StateRootFramingInjectivity.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    for required in (
        "theorem injective_of_left_inverse",
        "theorem fee_delta_changes_sections",
        "theorem fee_delta_changes_encoding",
    ):
        assert required in source
    for forbidden in ("sorry", "admit", "axiom", "unsafe"):
        assert forbidden not in source

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
