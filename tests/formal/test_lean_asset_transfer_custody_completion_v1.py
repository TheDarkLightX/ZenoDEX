"""Actual Std-only Lean compilation, axiom audit and executable mutants."""

import re
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PROOF = ROOT / "lean-mathlib/Proofs/AssetTransferCustodyCompletionV1.lean"
NAMESPACE = "Proofs.AssetTransferCustodyCompletionV1"
CLAIMS = (
    "completed_totals_preserve_supply",
    "checked_completion_accepts_valid_projection",
    "checked_success_is_u128",
    "maximum_total_accepts",
    "overflow_neighbor_rejects",
    "custody_frame_is_necessary",
)


def _lean(path):
    executable = shutil.which("lean")
    assert executable is not None
    assert (ROOT / "lean-mathlib/lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    return subprocess.run(
        [executable, "-DwarningAsError=true", str(path)],
        cwd=ROOT / "lean-mathlib",
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )


def test_custody_lift_compiles_and_exposes_only_standard_axioms(tmp_path):
    source = PROOF.read_text()
    assert tuple(re.findall(r"^theorem (\w+)", source, re.MULTILINE)) == CLAIMS
    assert re.search(r"\b(sorry|admit|axiom)\b", source) is None
    probe = tmp_path / "CustodyAxioms.lean"
    probe.write_text(
        source + "\n" + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in CLAIMS)
    )
    result = _lean(probe)
    assert result.returncode == 0, result.stdout + result.stderr
    for name in CLAIMS:
        assert f"'{NAMESPACE}.{name}'" in result.stdout
    axioms = {
        name.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        for name in group.split(",")
        if name.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


@pytest.mark.parametrize(
    "old,new,probe",
    (
        (
            "(before + custodyBefore, after + custodyAfter)",
            "(before, after + custodyAfter)",
            "(complete 115 115 1 1).1 == 115",
        ),
        (
            "totals.1 ≤ maxAtoms ∧ totals.2 ≤ maxAtoms",
            "True",
            "(completeChecked 115 115 (maxAtoms - 114) (maxAtoms - 114)).isSome",
        ),
    ),
)
def test_definition_mutants_fail_fixed_theorems_and_exhibit_bad_outcomes(tmp_path, old, new, probe):
    source = PROOF.read_text()
    split = source.index("\ntheorem ")
    definitions = source[:split]
    assert definitions.count(old) == 1
    mutated = definitions.replace(old, new, 1)
    path = tmp_path / "CustodyMutant.lean"
    # Omitting custody leaves a definition parameter unused. Disable only this
    # warning so a warning alone cannot serve as the negative proof oracle.
    mutated = mutated.replace(
        "import Std.Tactic", "import Std.Tactic\nset_option linter.unusedVariables false", 1
    )
    path.write_text(mutated + source[split:])
    failure = _lean(path)
    assert failure.returncode != 0, "mutant survived fixed theorem statements"
    path.write_text(mutated + f"\n#eval {probe}\nend {NAMESPACE}\n")
    observed = _lean(path)
    assert observed.returncode == 0, observed.stdout + observed.stderr
    assert observed.stdout.strip() == "true"
