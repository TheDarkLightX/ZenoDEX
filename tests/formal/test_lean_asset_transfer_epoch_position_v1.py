"""Pinned, dependency-free Lean checks for epoch height and prefix association.

These compile an abstract control-flow model and meaningful mutations. They do
not establish receipt verification, storage ancestry or full runtime refinement.
"""

import re
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PROOF = ROOT / "lean-mathlib/Proofs/AssetTransferEpochPositionV1.lean"
NAMESPACE = "Proofs.AssetTransferEpochPositionV1"
CLAIMS = (
    "accepted_step_binds_height_and_predecessor",
    "run_append",
    "accepted_prefix_has_exact_intermediate_state",
    "accepted_run_length_bound",
    "accepted_nonempty_run_height",
    "two_command_nonempty_control",
    "wrong_prefix_root_rejects",
    "hidden_intermediate_height_rejects",
)


def _lean(path):
    executable = shutil.which("lean")
    assert executable is not None, "pinned Lean compiler is required"
    assert (ROOT / "lean-mathlib/lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    return subprocess.run(
        [executable, "-DwarningAsError=true", str(path)],
        cwd=ROOT / "lean-mathlib",
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )


def test_epoch_position_theorems_compile_and_use_only_standard_axioms(tmp_path):
    source = PROOF.read_text()
    assert tuple(re.findall(r"^theorem (\w+)", source, re.MULTILINE)) == CLAIMS
    assert re.search(r"\b(sorry|admit|axiom)\b", source) is None
    probe = tmp_path / "EpochPositionAxioms.lean"
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
        ("cmd.preRoot = state.root ∧ ", "", "(run 7 0 ⟨7, 10⟩ [⟨8, 10, 11⟩, ⟨8, 10, 12⟩]).isSome"),
        (
            "some ⟨sourceHeight + 1, cmd.postRoot⟩",
            "some ⟨sourceHeight, cmd.postRoot⟩",
            "(step 7 0 ⟨7, 10⟩ ⟨8, 10, 11⟩).map (fun s => s.height == 7) == some true",
        ),
        (" ∧\n      index < 64", "", "(step 7 64 ⟨8, 10⟩ ⟨8, 10, 11⟩).isSome"),
    ),
)
def test_step_semantic_mutants_break_fixed_claims_and_expose_bad_outcome(tmp_path, old, new, probe):
    source = PROOF.read_text()
    start, stop = source.index("def step "), source.index("\ndef run ")
    target = source[start:stop]
    assert target.count(old) == 1
    mutated = source[:start] + target.replace(old, new, 1) + source[stop:]
    path = tmp_path / "EpochPositionMutant.lean"
    path.write_text(mutated)
    failure = _lean(path)
    assert failure.returncode != 0, "mutant survived the fixed theorem statements"
    # Independently execute the bad trace with only definitions, so a proof-term
    # type error alone is never the mutation oracle.
    definitions = mutated[: mutated.index("\ntheorem ")]
    path.write_text(definitions + f"\n#eval {probe}\nend {NAMESPACE}\n")
    observed = _lean(path)
    assert observed.returncode == 0, observed.stdout + observed.stderr
    assert observed.stdout.strip() == "true"
