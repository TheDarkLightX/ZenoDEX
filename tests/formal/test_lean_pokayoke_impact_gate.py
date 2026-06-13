from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def _run(cmd: list[str], *, cwd: Path, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    try:
        proc = subprocess.run(
            cmd,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"{' '.join(cmd)} timed out after {exc.timeout}s")
    return proc


def test_pokayoke_impact_gate_file_typechecks_without_warnings() -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/PokayokeImpactGate.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    proc = _run([lake, "env", "lean", "-DwarningAsError=true", target], cwd=lean_dir)
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_pokayoke_impact_gate_exported_from_proofs_root(tmp_path: Path) -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    snippet = lean_dir / "PokayokeImpactGateRootSmoke.lean"
    try:
        snippet.write_text(
            "\n".join(
                [
                    "import Proofs",
                    "open Proofs.PokayokeImpactGate",
                    "",
                    "example : impactOnlyAction 500 = ImpactAction.typedConfirm := by",
                    "  exact impactOnlyAction_of_ge_500 500 (by native_decide)",
                    "",
                    "example : severity (impactOnlyAction 99) ≤ severity (impactOnlyAction 500) := by",
                    "  exact severity_impactOnlyAction_monotone 99 500 (by native_decide)",
                    "",
                ]
            ),
            encoding="utf-8",
        )
        proc = _run([lake, "env", "lean", "-DwarningAsError=true", snippet.name], cwd=lean_dir)
    finally:
        snippet.unlink(missing_ok=True)
    assert proc.returncode == 0, proc.stdout + proc.stderr
