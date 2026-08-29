from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "GovernanceMigrationLifecycleV1.lean"


def _pinned_lean_executable() -> Path:
    toolchain = (LEAN_PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip()
    expected_version = toolchain.rsplit(":v", maxsplit=1)[-1]
    resolved = subprocess.run(
        ["elan", "which", "lean"],
        cwd=LEAN_PROJECT,
        check=True,
        capture_output=True,
        text=True,
    )
    lean = Path(resolved.stdout.strip())
    version = subprocess.run(
        [str(lean), "--version"],
        cwd=LEAN_PROJECT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    assert lean.is_file()
    assert f"version {expected_version}" in version
    return lean


def test_governance_migration_proof_has_required_surface() -> None:
    # Arrange / Act.
    source = PROOF.read_text(encoding="utf-8")

    # Assert.
    assert "import Mathlib" not in source
    assert re.search(r"\b(?:sorry|admit|axiom)\b", source) is None
    for declaration in (
        "inductive Phase",
        "inductive Step",
        "def transition",
        "theorem rejected_transition_is_exact_noop",
        "theorem transition_preserves_writer_safety",
        "theorem rollback_before_switch_restores_source_and_rotates_branch",
        "theorem rollback_after_switch_is_forbidden",
        "theorem post_switch_fail_stop_disables_both_writers",
        "theorem happy_path_disables_legacy_writer",
        "theorem legacy_disabled_cannot_restore_legacy_writer",
    ):
        assert declaration in source
    assert "Nonclaims:" in source


def test_governance_migration_proof_checks_with_pinned_lean() -> None:
    # Arrange.
    lean = _pinned_lean_executable()

    # Act / Assert.
    subprocess.run([str(lean), str(PROOF)], cwd=LEAN_PROJECT, check=True)
