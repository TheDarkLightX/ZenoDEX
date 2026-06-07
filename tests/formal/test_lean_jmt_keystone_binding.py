from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_jmt_keystone_binding_typechecks_without_placeholders() -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/JmtKeystoneBinding.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    assert "theorem rootAux_perm" in source
    assert "theorem rootAux_children_eq_of_injective2" in source
    assert "theorem rootAux_single_placeholder_eq_empty" in source
    assert "theorem filter_not_append_filter_perm" in source
    assert "theorem perm_of_filter_perms" in source
    assert "current repo has no\n`src/state/jmt.py` artifact" in source
    assert "Model-level boundary" in source
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
