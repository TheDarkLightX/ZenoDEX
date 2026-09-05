"""Check actual model imports and compare custody composition with integer oracles.

Each dependency is freshly compiled with the pinned standalone Lean toolchain.
No Mathlib build or preexisting local proof object supplies acceptance.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = ROOT / "lean-mathlib"
MODULE = "AssetTransferCustodyCompositionV1"
PROOF = LEAN_ROOT / "Proofs" / f"{MODULE}.lean"
NAMESPACE = f"Proofs.{MODULE}"
DEPENDENCIES = (
    "AssetTransferRefinementV1",
    "AssetTransferCustodyCompletionV1",
    "CheckedSignedDeltaRefinementV1",
)


def _check(path: Path, library: Path, output: Path | None = None):
    environment = dict(os.environ)
    environment["LEAN_PATH"] = str(library)
    args = ["lean", "-DwarningAsError=true"]
    if output is not None:
        args += ["-R", str(LEAN_ROOT), "-o", str(output)]
    args.append(str(path))
    return subprocess.run(
        args,
        cwd=LEAN_ROOT,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
        timeout=60,
    )


@pytest.fixture(scope="module")
def lean_library(tmp_path_factory):
    assert shutil.which("lean") is not None, "pinned Lean installation required"
    assert (LEAN_ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    version = subprocess.run(
        ["lean", "--version"],
        cwd=LEAN_ROOT,
        capture_output=True,
        text=True,
        check=True,
        timeout=10,
    )
    assert "version 4.27.0," in version.stdout
    library = tmp_path_factory.mktemp("custody-composition-imports")
    (library / "Proofs").mkdir()
    for name in (*DEPENDENCIES, MODULE):
        source = LEAN_ROOT / "Proofs" / f"{name}.lean"
        result = _check(source, library, library / "Proofs" / f"{name}.olean")
        assert result.returncode == 0, result.stdout + result.stderr
    return library


def test_composition_theorems_compile_with_standard_axioms(lean_library, tmp_path):
    source = PROOF.read_text()
    declarations = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(sorry|admit|axiom)\b", declarations) is None
    names = re.findall(r"^theorem (\w+)", declarations, re.MULTILINE)
    assert {
        "accepted_account_signed_delta",
        "accepted_movement_row_signed_delta",
        "accepted_movement_sum_matches_state_delta",
        "movementRows_sum_eq_delta_mul_occ",
        "unchanged_custody_signed_delta",
        "accepted_complete_supply_with_common_custody",
    } <= set(names)
    probe = tmp_path / "CompositionAxioms.lean"
    probe.write_text(
        f"import {NAMESPACE}\n" + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in names)
    )
    result = _check(probe, lean_library)
    assert result.returncode == 0, result.stdout + result.stderr
    for name in names:
        assert f"'{NAMESPACE}.{name}'" in result.stdout
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


def _scenario(name, module_input):
    command = module_input["command"]
    state = module_input["pre_state"]
    asset = command["asset"]
    policy = next(row for row in state["policies"] if row["asset"] == asset)
    balances = {
        row["owner"]: row["amount_atoms"] for row in state["balances"] if row["asset"] == asset
    }
    supply = next(row["amount_atoms"] for row in state["supplies"] if row["asset"] == asset)
    rows = ", ".join(f"({json.dumps(owner)}, {atoms})" for owner, atoms in balances.items())
    text_fields = [module_input["context"]["subject_id"], command["sender"], command["recipient"]]
    subject, sender, recipient = map(json.dumps, text_fields)
    source = (
        f"def {name} := scenario {json.dumps(policy['fee_owner'])} {policy['transfer_fee_atoms']} "
        f"true [{rows}] {supply} releaseA {subject} assetTransferCommandKind usd "
        f"{sender} {recipient} {command['amount_atoms']} {command['max_fee_atoms']}\n"
    )
    return source, balances, policy


def test_lean_arithmetic_composition_matches_native_fixture_integer_oracles(lean_library, tmp_path):
    fixture = json.loads(
        (ROOT / "tests/data/asset_lane_custody_coordinator_v1_golden.json").read_text()
    )
    cases = fixture["cases"] + [event for event in fixture["history"] if "module_accepted" in event]
    assert len(cases) == 13
    source = (
        f"import {NAMESPACE}\n"
        "open Proofs.AssetTransferRefinementV1\n"
        f"open {NAMESPACE}\n"
        "def renderDelta : Except Proofs.CheckedSignedDeltaRefinementV1.Reject Int → String\n"
        '  | .ok value => "OK:" ++ toString value\n'
        '  | .error _ => "ERR"\n'
        "def renderTotals : Option (Nat × Nat) → String\n"
        '  | .some (before, after) => "OK:" ++ toString before ++ "," ++ toString after\n'
        '  | .none => "ERR"\n'
    )
    expected: list[bool | str | int] = []
    for index, case in enumerate(cases):
        module_input = case["input"]["module_input"]
        name = f"vector{index}"
        definition, balances, policy = _scenario(name, module_input)
        source += definition + f"#eval decide ({name}.run.verdict = .accepted)\n"
        expected.append(True)
        command = module_input["command"]
        principals = sorted(set(balances) | {"untouched"})
        for principal in principals:
            delta = (
                (
                    -(command["amount_atoms"] + policy["transfer_fee_atoms"])
                    if principal == command["sender"]
                    else 0
                )
                + (command["amount_atoms"] if principal == command["recipient"] else 0)
                + (policy["transfer_fee_atoms"] if principal == policy["fee_owner"] else 0)
            )
            p = json.dumps(principal)
            source += (
                f"#eval renderDelta (D.checkedSignedDelta "
                f"(holdingOf ({name}.run.post.balance {p}) (by decide)) "
                f"(holdingOf ({name}.pre.balance {p}) (by decide)))\n"
            )
            expected.append(f"OK:{delta}")
            source += f"#eval movementDeltaSum {p} {name}.run.effects.movements\n"
            expected.append(delta)
        custody = sum(
            row["amount_atoms"]
            for row in module_input["custody"]
            if row["asset"] == command["asset"]
        )
        supply = next(
            row["amount_atoms"]
            for row in module_input["pre_state"]["supplies"]
            if row["asset"] == command["asset"]
        )
        assert sum(balances.values()) + custody == supply
        enumerated = "[" + ", ".join(map(json.dumps, principals)) + "]"
        source += (
            f"#eval renderTotals (C.completeChecked (sumOver {name}.pre.balance {enumerated}).toNat "
            f"(sumOver {name}.run.post.balance {enumerated}).toNat {custody} {custody})\n"
        )
        expected.append(f"OK:{supply},{supply}")
        for row in module_input["custody"]:
            atoms = row["amount_atoms"]
            source += (
                f"#eval renderDelta (D.checkedSignedDelta ⟨{atoms}, by decide⟩ "
                f"⟨{atoms}, by decide⟩)\n"
            )
            expected.append("OK:0")
    probe = tmp_path / "CompositionDifferential.lean"
    probe.write_text(source)
    result = _check(probe, lean_library)
    assert result.returncode == 0, result.stdout + result.stderr
    assert [json.loads(line) for line in result.stdout.splitlines()] == expected


def test_accepted_bridge_has_a_well_formed_nonvacuous_instance(lean_library, tmp_path):
    probe = tmp_path / "CompositionNonvacuity.lean"
    probe.write_text(
        f"import {NAMESPACE}\n"
        "open Proofs.AssetTransferRefinementV1\n"
        f"open {NAMESPACE}\n"
        "def baseWellFormed : StateWellFormed acceptDistinct.pre := by\n"
        "  refine ⟨?_, by decide, by decide⟩\n"
        "  intro p\n"
        "  by_cases ha : p = alice <;> by_cases hb : p = bob <;> by_cases ht : p = treasury\n"
        "  all_goals simp_all [acceptDistinct, scenario, baseRows, ledger, IsU128, u128Max, alice, bob, treasury]\n"
        "example : D.checkedSignedDelta (holdingOf 68 (by decide))\n"
        "    (holdingOf 100 (by decide)) = .ok (-32) := by\n"
        "  exact accepted_account_signed_delta (ctx := acceptDistinct.ctx) (cmd := acceptDistinct.cmd) baseWellFormed (by decide) alice\n"
        "def custodyScenario : Scenario :=\n"
        "  { acceptDistinct with pre := { acceptDistinct.pre with supplyAtoms := 122 } }\n"
        "def custodyWellFormed : StateWellFormed custodyScenario.pre :=\n"
        "  ⟨baseWellFormed.balances, by decide, baseWellFormed.fee⟩\n"
        "example : C.completeChecked 115 115 7 7 = .some (122, 122) := by\n"
        "  exact (accepted_complete_supply_with_common_custody\n"
        "    (ctx := custodyScenario.ctx) (cmd := custodyScenario.cmd)\n"
        "    custodyWellFormed (by decide) [alice, bob, treasury]\n"
        "    (by decide) (by decide) (by decide) (custody := 7) (by decide)).2.1\n"
        "example : ¬(sumOver custodyScenario.pre.balance [alice, bob, treasury] + (8 : Int)\n"
        "    = custodyScenario.pre.supplyAtoms) := by decide\n"
    )
    result = _check(probe, lean_library)
    assert result.returncode == 0, result.stdout + result.stderr


def test_in_range_but_wrong_holding_representation_fails_fixed_composition_theorems(
    lean_library, tmp_path
):
    source = PROOF.read_text()
    start = source.index("def holdingOf ")
    end = source.index("\ntheorem exactDifference_holdingOf", start)
    # Complementing each unsigned holding preserves the width but reverses
    # every nonzero difference. Width checks alone cannot validate this view.
    mutant = (
        "def holdingOf (atoms : Int) (_h : T.IsU128 atoms) : D.Holding :=\n"
        "  ⟨(2 ^ 128 - 1) - atoms.toNat, by\n"
        "    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)⟩\n"
    )
    probe = tmp_path / "CompositionHoldingMutant.lean"
    probe.write_text(
        source[:start]
        + mutant
        + "\ndef renderMutant : Except Proofs.CheckedSignedDeltaRefinementV1.Reject Int → String\n"
        + '  | .ok value => "OK:" ++ toString value\n'
        + '  | .error _ => "ERR"\n'
        + "#eval renderMutant (D.checkedSignedDelta (holdingOf 68 (by decide)) "
        + "(holdingOf 100 (by decide)))\n"
        + f"end {NAMESPACE}\n"
    )
    observation = _check(probe, lean_library)
    assert observation.returncode == 0, observation.stdout + observation.stderr
    assert json.loads(observation.stdout.strip()) == "OK:32"  # Exact oracle is -32.
    probe.write_text(source[:start] + mutant + source[end:])
    failed = _check(probe, lean_library)
    assert failed.returncode != 0, "wrong holding view survived the fixed theorem packet"
    assert "error:" in failed.stdout + failed.stderr


def test_omitted_movement_map_fails_fixed_coverage_theorems(lean_library, tmp_path):
    source = PROOF.read_text()
    start = source.index("def movementDeltaSum ")
    end = source.index("\ntheorem movementRows_sum_eq_delta_mul_occ", start)
    mutant = "def movementDeltaSum (_p : T.Principal) (_rows : List T.MovementRow) : Int := 0\n"
    probe = tmp_path / "CompositionMovementMutant.lean"
    probe.write_text(
        source[:start]
        + mutant
        + '\n#eval movementDeltaSum "alice" [⟨"alice", -32⟩, ⟨"bob", 30⟩, ⟨"treasury", 2⟩]\n'
        + f"end {NAMESPACE}\n"
    )
    observation = _check(probe, lean_library)
    assert observation.returncode == 0, observation.stdout + observation.stderr
    assert observation.stdout.strip() == "0"  # Exact emitted Alice delta is -32.
    probe.write_text(source[:start] + mutant + source[end:])
    failed = _check(probe, lean_library)
    assert failed.returncode != 0, "empty movement map survived the fixed coverage theorems"
    assert "error:" in failed.stdout + failed.stderr
