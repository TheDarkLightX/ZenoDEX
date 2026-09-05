"""Kernel-checked accounting bridge, premise controls and bounded runtime parity.

The lift is an accounting projection with explicit representation/coverage
premises. These checks do not construct a V2 Verified outcome, authenticate a
context, establish snapshot provenance or prove Python/Rust refinement.
"""

from __future__ import annotations

import ast
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from src.core.asset_transfer_module_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferStateV1,
    transition_asset_transfer_v1,
)
from src.core.global_settlement_types_v1 import AssetSupplyV1, EconomicAmountV1

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
MODULE = "Proofs.AssetTransferGlobalPreservationV1"
PROOF = LEAN_DIR / "Proofs" / "AssetTransferGlobalPreservationV1.lean"
CLAIMS = (
    "balanceRows_total",
    "step_frame",
    "step_represents",
    "step_account_totals",
    "step_owned_supply",
    "step_exact_allocation",
    "step_claimant_backing",
    "step_rejection_is_noop",
    "accepted_sender_is_context_subject",
    "step_changes_only_for_context_subject",
    "run_preserves_accounting",
    "demo_represents",
    "demo_coverage",
    "demo_owned_supply",
    "demo_exact_allocation",
    "demo_claimant_backing",
    "demo_nonempty_accepted",
    "demo_derived_preservation",
    "fee_owner_alias_controls",
    "demo_trace_coverage",
    "demo_trace_has_rejection_and_two_transfers",
    "demo_trace_derived_preservation",
    "missing_principal_breaks_conservation",
    "extra_credit_breaks_owned_supply",
    "wrong_claimant_keeps_totals_but_breaks_terminal",
)


def _lake(*args: str) -> subprocess.CompletedProcess[str]:
    executable = shutil.which("lake")
    assert executable is not None, "formal gate requires pinned lake and Lean"
    return subprocess.run(
        [executable, *args], cwd=LEAN_DIR, capture_output=True, text=True,
        timeout=900, check=False,
    )


@pytest.fixture(scope="module")
def compiled() -> None:
    result = _lake("build", MODULE)
    assert result.returncode == 0, result.stdout + result.stderr


def _probe(tmp_path: Path, body: str) -> subprocess.CompletedProcess[str]:
    path = tmp_path / "TransferGlobalProbe.lean"
    path.write_text(f"import {MODULE}\nopen {MODULE}\n{body}\n")
    return _lake("env", "lean", "-DwarningAsError=true", str(path))


def test_new_target_compiles_without_warnings(compiled: None) -> None:
    result = _lake("env", "lean", "-DwarningAsError=true", str(PROOF))
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == result.stderr.strip() == ""


def test_all_declared_theorems_have_only_standard_kernel_axioms(
    compiled: None, tmp_path: Path,
) -> None:
    source = PROOF.read_text()
    assert set(re.findall(r"^theorem (\w+)", source, re.MULTILINE)) == set(CLAIMS)
    result = _probe(tmp_path, "\n".join(f"#print axioms {MODULE}.{name}" for name in CLAIMS))
    assert result.returncode == 0, result.stdout + result.stderr
    for name in CLAIMS:
        assert f"'{MODULE}.{name}'" in result.stdout
    dependencies = {
        entry.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        for entry in group.split(",") if entry.strip()
    }
    assert dependencies <= {"propext", "Quot.sound", "Classical.choice"}


def test_new_proof_has_no_placeholders() -> None:
    result = subprocess.run(
        [sys.executable, str(ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"),
         str(PROOF), "--json"],
        cwd=ROOT, capture_output=True, text=True, timeout=120, check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads(result.stdout)
    assert payload["blocked"] is False
    assert payload["match_count"] == 0


@pytest.mark.parametrize("owner,expected", [
    ("treasury", [68, 40, 7]), ("alice", [70, 40, 5]), ("bob", [68, 42, 5]),
])
def test_nonempty_global_projection_matches_python_transfer_for_each_fee_alias(
    owner: str, expected: list[int], compiled: None, tmp_path: Path,
) -> None:
    body = f'''def projected := step principals accountDomain T.acceptDistinct.ctx
  T.acceptDistinct.cmd (demoWithFeeOwner "{owner}")
#eval IO.println (repr [projected.localState.balance "alice",
  projected.localState.balance "bob", projected.localState.balance "treasury"])
'''
    result = _probe(tmp_path, body)
    assert result.returncode == 0, result.stdout + result.stderr
    lean_balances = ast.literal_eval(result.stdout.strip())
    root = "0x" + "01" * 32
    context = AssetTransferContextV1(
        chain_id="transfer-global-formal", deployment_root=root, profile_root=root,
        writer_epoch=0, module_release_id=root, command_occurrence_id=root,
        subject_id="alice", grant_root=root,
    )
    state = AssetTransferStateV1(
        module_release_id=root,
        policies=(AssetTransferPolicyV1("USD", owner, 2, True),),
        balances=tuple(EconomicAmountV1(p, "USD", ACCOUNT_CUSTODY_DOMAIN_V1, n)
                       for p, n in [("alice", 100), ("bob", 10), ("treasury", 5)]),
        supplies=(AssetSupplyV1("USD", 125),),
    )
    command = AssetTransferCommandV1(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1, asset="USD", sender="alice",
        recipient="bob", amount_atoms=30, max_fee_atoms=2,
    )
    accepted = transition_asset_transfer_v1(context, state, command)
    assert isinstance(accepted, AssetTransferAcceptedV1)
    assert lean_balances == expected
    assert [row.amount_atoms for row in accepted.post_state.balances] == expected
    assert sum(lean_balances) + 10 == 125


@pytest.mark.parametrize("false_statement", [
    'T.sumOver (T.transition T.acceptDistinct.ctx demoLocal T.acceptDistinct.cmd).post.balance '
    '[T.alice, T.bob] = T.sumOver demoLocal.balance [T.alice, T.bob]',
    'G.ownedFor extraCredit T.usd = 125',
    'G.openTerminalAmountFor wrongClaimant.terminalObligations T.alice T.usd claimDomain ≤ '
    'G.amountAt wrongClaimant.liabilities T.alice T.usd claimDomain',
    '(T.transition { T.acceptDistinct.ctx with subjectId := T.mallory } '
    'demoLocal T.acceptDistinct.cmd).verdict = .accepted',
], ids=["missing-principal", "extra-credit", "wrong-claimant", "unauthorized-subject"])
def test_false_strengthenings_are_refused_by_kernel(
    false_statement: str, compiled: None, tmp_path: Path,
) -> None:
    result = _probe(tmp_path, f"example : {false_statement} := by decide")
    assert result.returncode != 0
    assert "Tactic `decide` proved that the proposition" in result.stdout
    assert "is false" in result.stdout
    assert "Unknown" not in result.stdout, result.stdout + result.stderr


@pytest.mark.parametrize("before,after,failed_obligation,failed_control", [
    ("balances := balanceRows result.post.policy.asset domain result.post.balance ps",
     "balances := balanceRows result.post.policy.asset domain result.post.balance ps\n"
     "        liabilities := []", "step_frame", "demo_nonempty_accepted"),
    ("T.transition ctx s.localState cmd",
     "T.transition { ctx with subjectId := cmd.sender } s.localState cmd",
     "step_changes_only_for_context_subject", "demo_trace_has_rejection_and_two_transfers"),
], ids=["erase-claimant-table", "replace-authenticated-subject"])
def test_semantic_mutants_cannot_retain_preservation_theorems(
    before: str, after: str, failed_obligation: str, failed_control: str,
    compiled: None, tmp_path: Path,
) -> None:
    source = PROOF.read_text()
    start, stop = source.index("def step ("), source.index("theorem step_frame")
    assert source.count(before, start, stop) == 1
    assert source.index(before) >= start
    mutated = source[:start] + source[start:stop].replace(before, after, 1) + source[stop:]
    assert mutated[mutated.index("theorem step_frame"):] == source[stop:]
    path = tmp_path / "MutatedTransferGlobal.lean"
    path.write_text(mutated)
    result = _lake("env", "lean", "-DwarningAsError=true", str(path))
    assert result.returncode != 0
    error_lines = {
        int(line) for line in re.findall(rf"{re.escape(str(path))}:(\d+):\d+: error:", result.stdout)
    }
    lines = mutated.splitlines()
    for theorem in (failed_obligation, failed_control):
        first = next(i + 1 for i, line in enumerate(lines) if line.startswith(f"theorem {theorem} "))
        last = next((i + 1 for i, line in enumerate(lines[first:], first)
                     if re.match(r"^(?:theorem|def|abbrev|end) ", line)), len(lines) + 1)
        assert any(first <= line < last for line in error_lines), result.stdout + result.stderr
    assert "unexpected token" not in result.stdout
    assert "Unknown" not in result.stdout, result.stdout + result.stderr
