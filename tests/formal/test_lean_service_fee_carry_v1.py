"""Compile the carry theorem and compare its definitions with exact references."""

import ast
import re
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path

from tools.tokenomics.lp_service_budget_v1 import fee_partition

ROOT = Path(__file__).resolve().parents[2]
PROOF = ROOT / "lean-mathlib/Proofs/ServiceFeeCarryV1.lean"
CLAIMS = (
    "quotient_remainder_identity", "remainders_lt_count", "payouts_le_fees",
    "owned_partition", "carry_scaled", "carry_lt_claimant_count",
    "payouts_monotone", "incremental_carry_identity", "incremental_payout_bound",
)


def _run_lean(path: Path) -> subprocess.CompletedProcess[str]:
    executable = shutil.which("lean")
    assert executable is not None
    assert (ROOT / "lean-mathlib/lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    return subprocess.run(
        [executable, "-DwarningAsError=true", str(path)], cwd=ROOT / "lean-mathlib",
        capture_output=True, text=True, timeout=30, check=False,
    )


def _lean(path: Path) -> str:
    result = _run_lean(path)
    assert result.returncode == 0, result.stdout + result.stderr
    return result.stdout


def test_actual_carry_theorems_compile_without_unproved_axioms(tmp_path):
    source = PROOF.read_text()
    assert tuple(re.findall(r"^theorem (\w+)", source, re.MULTILINE)) == CLAIMS
    assert re.search(r"\b(sorry|admit|axiom)\b", source) is None
    probe = tmp_path / "CarryAxioms.lean"
    probe.write_text(source + "\n" + "\n".join(
        f"#print axioms ServiceFeeCarryV1.{name}" for name in CLAIMS
    ))
    output = _lean(probe)
    for name in CLAIMS:
        assert f"'ServiceFeeCarryV1.{name}'" in output
    axioms = {
        name.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
        for name in group.split(",") if name.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


def test_lean_cumulative_definitions_match_rational_and_python_references(tmp_path):
    # Small policy shapes plus a large atom boundary; no adopted policy values.
    weights = ((1,), (1, 1), (1, 1, 1, 1), (0, 2, 1), (1, 1, 2), (3, 0, 5))
    expressions, expected = [], []
    for shares in weights:
        denominator = sum(shares)
        for fees in (0, 1, denominator - 1, denominator, denominator + 1, (1 << 128) - 1):
            for added in (0, 1, denominator):
                before = tuple(Fraction(fees * w, denominator).__floor__() for w in shares)
                after = tuple(Fraction((fees + added) * w, denominator).__floor__() for w in shares)
                old_carry, new_carry = fees - sum(before), fees + added - sum(after)
                assert fee_partition(fees, shares, denominator) == (*before, old_carry)
                increment = sum(after) - sum(before)
                assert increment + new_carry == added + old_carry
                assert increment <= added + len(shares) - 1
                expected.append((sum(before), old_carry, increment, new_carry))
                shape = "[" + ",".join(map(str, shares)) + "]"
                p = f"payouts {fees} {denominator} {shape}"
                q = f"payouts {fees + added} {denominator} {shape}"
                expressions.append(
                    f"({p}, carry {fees} {denominator} {shape}, {q} - {p}, "
                    f"carry {fees + added} {denominator} {shape})"
                )
    probe = tmp_path / "CarryReference.lean"
    probe.write_text(PROOF.read_text() + "\nopen ServiceFeeCarryV1\n#eval [\n"
                     + ",\n".join(expressions) + "\n]\n")
    assert ast.literal_eval(_lean(probe).strip()) == expected


def test_cumulative_carry_release_does_not_reassign_per_occurrence_residue():
    first = fee_partition(1, (1, 1), 2)
    second = fee_partition(1, (1, 1), 2)
    cumulative = fee_partition(2, (1, 1), 2)
    assert tuple(a + b for a, b in zip(first, second, strict=True)) == (0, 0, 2)
    assert cumulative == (1, 1, 0)
    # They account for the same two atoms under different ownership contracts.
    assert sum(first) + sum(second) == sum(cumulative) == 2
    tight_before = fee_partition(3, (1, 1, 1, 1), 4)
    tight_after = fee_partition(4, (1, 1, 1, 1), 4)
    assert sum(tight_after[:-1]) - sum(tight_before[:-1]) == 1 + 3


def test_discarded_carry_mutant_fails_unchanged_accounting_challenge(tmp_path):
    source = PROOF.read_text()
    original = "(ws : List Nat) : Nat := F - payouts F D ws"
    replacement = "(ws : List Nat) : Nat := 0 * (F - payouts F D ws)"
    assert source.count(original) == 1
    challenge = (
        "\nopen ServiceFeeCarryV1\n"
        "example : payouts 2 2 [1,1] - payouts 1 2 [1,1] + carry 2 2 [1,1]"
        " = 1 + carry 1 2 [1,1] := by decide\n"
    )
    probe = tmp_path / "CarryChallenge.lean"
    probe.write_text(source + challenge)
    _lean(probe)
    # Alter the definition only; retain arguments, theorem statements and challenge.
    probe.write_text(source.replace(original, replacement, 1) + challenge)
    result = _run_lean(probe)
    assert result.returncode != 0
    assert "decide" in result.stdout
    assert "unused variable" not in result.stdout + result.stderr
