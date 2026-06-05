from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def _lean_dir() -> Path:
    return Path(__file__).resolve().parents[2] / "lean-mathlib"


def test_lean_zenodex_nonce_batch_wrapper_builds_without_warnings() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    proc = subprocess.run(
        [
            lake,
            "env",
            "lean",
            "-DwarningAsError=true",
            "Proofs/ZenoDEXNonceBatchWrapper.lean",
        ],
        cwd=_lean_dir(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_zenodex_nonce_batch_wrapper_exports_decision_safety_theorem() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    lean_dir = _lean_dir()
    build = subprocess.run(
        [lake, "build", "Proofs.ZenoDEXNonceBatchWrapper"],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
    )
    assert build.returncode == 0, build.stdout + build.stderr

    smoke = (
        "import Proofs.ZenoDEXNonceBatchWrapper\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.batchAccepts\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.batchFinals\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.CanonicalBatch\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.canonicalBatchAccepts\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.successorRange\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.groupExactRange\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.acceptsSortedFold_eq_successorRange\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.acceptsSortedFold_final_eq_start_add_length\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.canonical_batch_accept_decision_implies_safety\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.canonical_batch_accept_decision_implies_exact_ranges\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.canonical_batch_sender_ids_nodup\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.batch_accept_decision_implies_safety\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.batch_accept_decision_implies_exact_ranges\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.batch_accept_decision_implies_group_nodup\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.group_accept_decision_implies_exact_range\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.witness_batch_accepts\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.witness_canonical_batch_accepts\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.witness_reject_gap\n"
        "#check Proofs.ZenoDEX.NonceBatchWrapper.witness_reject_is_noop_finals\n"
        "#print axioms Proofs.ZenoDEX.NonceBatchWrapper.canonical_batch_accept_decision_implies_exact_ranges\n"
    )
    smoke_path = lean_dir / ".tmp_zenodex_nonce_batch_wrapper_smoke.lean"
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

    output = proc.stdout + proc.stderr
    assert proc.returncode == 0, output
    assert "sorryAx" not in output, output
    assert "Lean.trustCompiler" not in output, output
    assert "Lean.ofReduceBool" not in output, output
