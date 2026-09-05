"""Checked signed differences: universal Lean model and extracted Rust execution.

The Rust probe compiles the unchanged production function body with its exact
constant and a minimal Result/error shell. This is arithmetic differential
evidence; it does not execute the enclosing crate or establish compiler proof.
"""

import json
import re
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PROOF = ROOT / "lean-mathlib/Proofs/CheckedSignedDeltaRefinementV1.lean"
RUST = ROOT / "zk/global_settlement_abi_v1/src/global_economic_state_delta.rs"
NAMESPACE = "Proofs.CheckedSignedDeltaRefinementV1"
MIN_MAGNITUDE = 1 << 127
MAX_HOLDING = (1 << 128) - 1
ERROR = "ERR:economic refinement signed state delta"
CLAIMS = (
    "bounds_match_rust_widths",
    "subtraction_magnitudes_fit_u128",
    "checked_signed_delta_refines_specification",
    "success_iff_exact_representable",
    "rejection_iff_out_of_range",
    "unchanged_holdings_accept_zero",
    "minimum_signed_difference_accepts",
    "positive_overflow_neighbor_rejects",
    "negative_overflow_neighbor_rejects",
    "maximum_holdings_small_difference_accepts",
)


def _lean(path: Path) -> subprocess.CompletedProcess[str]:
    executable = shutil.which("lean")
    assert executable is not None, "installed pinned Lean is required"
    pin = (ROOT / "lean-mathlib/lean-toolchain").read_text().strip()
    assert pin == "leanprover/lean4:v4.27.0"
    version = subprocess.run(
        [executable, "--version"], cwd=ROOT / "lean-mathlib",
        capture_output=True, text=True, check=True,
    )
    assert "version 4.27.0," in version.stdout
    return subprocess.run(
        [executable, "-DwarningAsError=true", str(path)],
        cwd=ROOT / "lean-mathlib",
        capture_output=True,
        text=True,
        check=False,
        timeout=60,
    )


def _rust_source() -> str:
    source = RUST.read_text()
    marker = "pub(crate) fn checked_signed_delta_v1("
    assert source.count(marker) == 1
    start = source.index(marker)
    end = source.index("\n}\n", start) + 3
    constants = re.findall(r"^const I128_MIN_MAGNITUDE_V1:.*;$", source, re.MULTILINE)
    assert len(constants) == 1
    return constants[0] + "\n" + source[start:end]


def _rust_results(tmp_path: Path, function: str, cases: list[tuple[int, int]]) -> list[str]:
    rustup = shutil.which("rustup")
    assert rustup is not None
    # `which` locates an installed toolchain without installing or updating it.
    located = subprocess.run(
        [rustup, "which", "--toolchain", "1.90.0", "rustc"],
        capture_output=True, text=True, check=True,
    )
    compiler = located.stdout.strip()
    version = subprocess.run([compiler, "--version"], capture_output=True, text=True, check=True)
    assert version.stdout.startswith("rustc 1.90.0 ")
    path = tmp_path / "signed_delta.rs"
    binary = tmp_path / "signed_delta"
    path.write_text(
        "use std::io::{self, BufRead};\n"
        "#[derive(Debug)] enum AbiErrorV1 { InvalidBounds(&'static str) }\n"
        "type AbiResultV1<T> = Result<T, AbiErrorV1>;\n"
        + function
        + "\nfn main() {\n"
        '  for line in io::stdin().lock().lines() {\n'
        '    let line = line.unwrap();\n'
        '    let parts: Vec<u128> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();\n'
        '    match checked_signed_delta_v1(parts[0], parts[1]) {\n'
        '      Ok(value) => println!("OK:{}", value),\n'
        '      Err(AbiErrorV1::InvalidBounds(message)) => println!("ERR:{}", message),\n'
        '    }\n  }\n}\n'
    )
    compiled = subprocess.run(
        [compiler, "--edition=2021", "-C", "opt-level=0", str(path), "-o", str(binary)],
        capture_output=True, text=True, check=False, timeout=30,
    )
    assert compiled.returncode == 0, compiled.stdout + compiled.stderr
    result = subprocess.run(
        [str(binary)], input="".join(f"{post} {pre}\n" for post, pre in cases),
        capture_output=True, text=True, check=True, timeout=10,
    )
    return result.stdout.splitlines()


def _exact_oracle(post: int, pre: int) -> str:
    delta = post - pre
    return f"OK:{delta}" if -MIN_MAGNITUDE <= delta < MIN_MAGNITUDE else ERROR


def _lean_observations(source: str, cases: list[tuple[int, int]]) -> str:
    render = (
        f"\nopen {NAMESPACE}\n"
        "def renderDelta : Except Reject Int → String\n"
        '  | .ok value => "OK:" ++ toString value\n'
        f'  | .error .signedStateDeltaBounds => "{ERROR}"\n'
    )
    probes = "\n".join(
        f"#eval renderDelta (checkedSignedDelta ⟨{post}, by decide⟩ ⟨{pre}, by decide⟩)"
        for post, pre in cases
    )
    return source + render + probes + "\n"


def test_signed_delta_model_compiles_with_standard_axioms(tmp_path: Path) -> None:
    source = PROOF.read_text()
    assert tuple(re.findall(r"^theorem (\w+)", source, re.MULTILINE)) == CLAIMS
    assert re.search(r"\b(sorry|admit|axiom)\b", source) is None
    probe = tmp_path / "SignedDeltaAxioms.lean"
    probe.write_text(source + "\n" + "\n".join(f"#print axioms {NAMESPACE}.{n}" for n in CLAIMS))
    result = _lean(probe)
    assert result.returncode == 0, result.stdout + result.stderr
    for name in CLAIMS:
        assert f"'{NAMESPACE}.{name}'" in result.stdout
    axioms = {
        name.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        for name in group.split(",") if name.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


def test_actual_rust_body_and_lean_agree_with_exact_integer_oracle(tmp_path: Path) -> None:
    anchors = (0, 1, 2, 31, 32, MIN_MAGNITUDE - 1, MIN_MAGNITUDE,
               MIN_MAGNITUDE + 1, MAX_HOLDING - 32, MAX_HOLDING - 1, MAX_HOLDING)
    cases = [(post, pre) for post in anchors for pre in anchors]
    expected = [_exact_oracle(post, pre) for post, pre in cases]
    assert _rust_results(tmp_path, _rust_source(), cases) == expected
    probe = tmp_path / "SignedDeltaDifferential.lean"
    probe.write_text(_lean_observations(PROOF.read_text(), cases))
    result = _lean(probe)
    assert result.returncode == 0, result.stdout + result.stderr
    assert [json.loads(line) for line in result.stdout.splitlines()] == expected


@pytest.mark.parametrize("mutant", ("omit_minimum", "narrow_absolute_holdings"))
def test_definition_mutants_fail_fixed_theorems_and_actual_boundary_oracle(
    tmp_path: Path, mutant: str,
) -> None:
    source = PROOF.read_text()
    split = source.index("\ntheorem ")
    definitions, theorems = source[:split], source[split:]
    rust = _rust_source()
    if mutant == "omit_minimum":
        old, new = "if magnitude = minMagnitude then", "if False then"
        rust_old, rust_new = "if magnitude == I128_MIN_MAGNITUDE_V1 {", "if false {"
        case = (0, MIN_MAGNITUDE)
    else:
        old = "if post.val ≥ pre.val then"
        new = ("if post.val > signedMax ∨ pre.val > signedMax then\n"
               "    .error .signedStateDeltaBounds\n  else if post.val ≥ pre.val then")
        rust_old = "    if post_atoms >= pre_atoms {"
        rust_new = (
            "    if post_atoms > i128::MAX as u128 || pre_atoms > i128::MAX as u128 {\n"
            '        return Err(AbiErrorV1::InvalidBounds("economic refinement signed state delta"));\n'
            "    }\n" + rust_old
        )
        case = (MAX_HOLDING, MAX_HOLDING)
    assert definitions.count(old) == rust.count(rust_old) == 1
    definitions = definitions.replace(old, new, 1)
    probe = tmp_path / "SignedDeltaMutant.lean"
    probe.write_text(definitions + theorems)
    failed = _lean(probe)
    assert failed.returncode != 0, "definition mutant survived the unchanged theorem packet"
    # A failing proof script is not sufficient: both executable mutants must
    # compile and expose the specific wrong result against the arithmetic oracle.
    mutant_source = definitions + f"\nend {NAMESPACE}\n"
    probe.write_text(_lean_observations(mutant_source, [case]))
    observed = _lean(probe)
    assert observed.returncode == 0, observed.stdout + observed.stderr
    lean_result = [json.loads(line) for line in observed.stdout.splitlines()]
    rust_result = _rust_results(tmp_path, rust.replace(rust_old, rust_new, 1), [case])
    assert lean_result == rust_result == [ERROR]
    assert _exact_oracle(*case) != ERROR
