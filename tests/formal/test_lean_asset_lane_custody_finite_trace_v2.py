"""Finite policy selection and rejected steps preserve complete custody histories.

Lean checks the modeled finite leaf outcomes. Runtime histories separately
exercise the coordinator; outer binding/resource checks and publication remain
outside the universal theorem.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest

from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    custody_effect_plan_lean as custody_effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    effect_plan_lean as effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    lean as lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    outcome_lean as outcome_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    transfer_consumer_lean as transfer_consumer_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    transfer_effect_plan_lean as transfer_effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    transfer_outcome_lean as transfer_outcome_lean,
)
from tests.formal.test_lean_asset_lane_custody_trace_v2 import CONTROLS_SHA256
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

REPO = Path(__file__).resolve().parents[2]
MODULE = "AssetLaneCustodyFiniteTraceV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = REPO / "lean-mathlib/Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "5c603db143f8a981a3747a9f6501e53a9b27eea6e6be60fe378d2a673412465a"
CONTROLS_PATH = Path(__file__).with_name("asset_lane_custody_trace_v2_controls.lean")
FINITE_CONTROLS_PATH = Path(__file__).with_name("asset_lane_custody_finite_trace_v2_controls.lean")
FINITE_CONTROLS_SHA256 = "2a0e01f595d5e6813032205567d61948ad8e1d7b51ea6987708be8c1e23edeaa"
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
CONTRACTS = {
    "transfer_rejected_noop": """∀ {digest : B.Bytes → String} {pre : C.State}
      {context : T.Context} {command : T.Command} {code : FT.RejectCode},
      (FT.transition digest context (E.transferSource pre) command).verdict = .rejected code →
      step digest pre (.transfer context command) = pre""",
    "managed_rejected_noop": """∀ {digest : B.Bytes → String} {pre : C.State}
      {context : M.Context} {command : M.Command} {code : FM.RejectCode},
      (FM.transition digest context (E.managedSource pre) command).verdict = .rejected code →
      step digest pre (.managed context command) = pre""",
    "transfer_accepted_actual_post": """∀ {digest : B.Bytes → String} {pre : C.State}
      {context : T.Context} {command : T.Command},
      (FT.transition digest context (E.transferSource pre) command).verdict = .accepted →
      ∃ policy, FT.policyFor (E.transferSource pre) command.asset = some policy ∧
        policy ∈ pre.transferState.policies ∧
        step digest pre (.transfer context command) = E.transferPostFromLeaf pre
          (FT.transition digest context (E.transferSource pre) command).post ∧
        step digest pre (.transfer context command) = C.transferPost pre policy command""",
    "managed_accepted_actual_post": """∀ {digest : B.Bytes → String} {pre : C.State}
      {context : M.Context} {command : M.Command}, C.RowsRepresentable pre →
      (FM.transition digest context (E.managedSource pre) command).verdict = .accepted →
      ∃ policy, FM.policyFor (E.managedSource pre) command.asset = some policy ∧
        policy ∈ pre.managedPolicies ∧
        step digest pre (.managed context command) = E.managedPostFromLeaf pre
          (FM.transition digest context (E.managedSource pre) command).post ∧
        step digest pre (.managed context command) = R.recomposedPost pre command.asset
          command.accountOwner (M.signedAmount command) ∧
        step digest pre (.managed context command) = C.managedPost pre command.asset
          command.accountOwner (M.signedAmount command)""",
    "step_preserves_rows": """∀ (digest : B.Bytes → String) {pre : C.State} {action : Action},
      C.RowsRepresentable pre → StaticPolicyShape pre → CommandShape action →
      C.RowsRepresentable (step digest pre action)""",
    "step_fixed_frame": """∀ (digest : B.Bytes → String) (pre : C.State) (action : Action),
      FixedFrame pre (step digest pre action)""",
    "run_preserves_rows": """∀ (digest : B.Bytes → String) (actions : List Action)
      {pre : C.State}, C.RowsRepresentable pre → StaticPolicyShape pre →
      (∀ action ∈ actions, CommandShape action) → C.RowsRepresentable (run digest pre actions)""",
    "run_fixed_frame": """∀ (digest : B.Bytes → String) (actions : List Action) (pre : C.State),
      FixedFrame pre (run digest pre actions)""",
    "every_prefix_rows_and_frame": """∀ (digest : B.Bytes → String) (actions : List Action)
      {pre : C.State}, C.RowsRepresentable pre → StaticPolicyShape pre →
      (∀ action ∈ actions, CommandShape action) → ∀ length,
      C.RowsRepresentable (run digest pre (actions.take length)) ∧
        FixedFrame pre (run digest pre (actions.take length))""",
}


@pytest.fixture(scope="module")
def finite_trace_lean(custody_effect_plan_lean: LeanSubject) -> LeanSubject:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    target = custody_effect_plan_lean.source / "Proofs" / f"{MODULE}.lean"
    target.write_bytes(source)
    checked = _compile(
        custody_effect_plan_lean,
        target,
        custody_effect_plan_lean.library / "Proofs" / f"{MODULE}.olean",
    )
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stdout == checked.stderr == ""
    return custody_effect_plan_lean


def test_initial_only_admission_contracts_and_standard_axioms(finite_trace_lean: LeanSubject) -> None:
    source = SOURCE.read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert tuple(re.findall(r"^theorem\s+(\w+)", source, flags=re.MULTILINE)) == tuple(CONTRACTS)
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in CONTRACTS.items()
    )
    path = finite_trace_lean.source / "CustodyFiniteTraceContracts.lean"
    path.write_text(f"import {NAMESPACE}\nopen {NAMESPACE}\n{body}")
    checked = _compile(finite_trace_lean, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", checked.stdout)
    axioms = {item.strip() for group in groups for item in group.split(",") if item.strip()}
    assert axioms <= STANDARD_AXIOMS
    assert len(groups) + checked.stdout.count("does not depend on any axioms") == len(CONTRACTS)


def test_finite_policy_lookup_history_matches_independent_complete_tables(
    finite_trace_lean: LeanSubject,
) -> None:
    controls = CONTROLS_PATH.read_bytes()
    appendix = FINITE_CONTROLS_PATH.read_bytes()
    assert hashlib.sha256(controls).hexdigest() == CONTROLS_SHA256
    assert hashlib.sha256(appendix).hexdigest() == FINITE_CONTROLS_SHA256
    path = finite_trace_lean.source / "CustodyFiniteHistoryControls.lean"
    path.write_text(f"import {NAMESPACE}\n" + controls.decode() + appendix.decode())
    checked = _compile(finite_trace_lean, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""


@pytest.mark.parametrize(
    ("name", "original", "replacement"),
    (
        ("RejectedTransferDropsCustody", "| .rejected _ => pre",
         "| .rejected _ => { pre with custody := [] }"),
        ("AcceptedManagedDropsCustody", "| .accepted => E.managedPostFromLeaf pre result.post",
         "| .accepted => { E.managedPostFromLeaf pre result.post with custody := [] }"),
        ("AcceptedManagedSkipsUpdate", "| .accepted => E.managedPostFromLeaf pre result.post",
         "| .accepted => pre"),
    ),
)
def test_well_typed_state_mutants_fail_the_complete_history_contract(
    finite_trace_lean: LeanSubject, name: str, original: str, replacement: str,
) -> None:
    """A mutant must elaborate as a program before proof failure counts."""

    source = SOURCE.read_text()
    assert source.count(original) == (2 if name == "RejectedTransferDropsCustody" else 1)
    mutant = source.replace(original, replacement, 1)
    prefix, marker, _ = mutant.partition("\ntheorem transfer_rejected_noop")
    assert marker
    program = finite_trace_lean.source / f"{name}Program.lean"
    program.write_text(prefix + f"\nend {NAMESPACE}\n")
    elaborated = _compile(finite_trace_lean, program)
    assert elaborated.returncode == 0, elaborated.stdout + elaborated.stderr
    assert elaborated.stdout == elaborated.stderr == ""
    path = finite_trace_lean.source / f"{name}Mutant.lean"
    path.write_text(mutant)
    checked = _compile(finite_trace_lean, path)
    assert checked.returncode == 1, checked.stdout + checked.stderr
    assert "error:" in checked.stdout
    assert "unexpected token" not in checked.stdout
    assert "unknown identifier" not in checked.stdout.lower()
    assert "failed to synthesize" not in checked.stdout.lower()


def test_unknown_policy_attempts_do_not_change_the_following_valid_history() -> None:
    """Given custody and dormant assets, rejected requests leave the next input intact."""

    from src.core.asset_lane_coordinator_values_v2 import AssetLaneRejectedV2
    from src.core.asset_lane_custody_coordinator_v2 import (
        AssetLaneCustodyAcceptedV2,
        transition_asset_lane_custody_v2,
    )
    from src.core.asset_transfer_types_v2 import AssetTransferRejectCodeV2
    from src.core.global_settlement_types_v2 import (
        AssetSupplyV2,
        EconomicAmountV2,
        canonical_global_bytes_v2,
    )
    from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecycleRejectCodeV2
    from tests.core.test_asset_lane_coordinator_v2 import (
        _context,
        _managed_command,
        _transfer_command,
    )
    from tests.core.test_asset_lane_custody_v2 import multiasset_custody_state

    initial = multiasset_custody_state()
    state = initial
    issue = _managed_command(amount_atoms=2)
    transfer = _transfer_command(amount_atoms=1)
    burn = _managed_command(kind="managed_asset_burn", amount_atoms=1)
    history = (
        (issue, "issuer", None, (2, 0, 2)),
        (transfer, "alice", None, (1, 1, 2)),
        (replace(transfer, asset="UNKNOWN"), "alice",
         AssetTransferRejectCodeV2.UNKNOWN_ASSET, (1, 1, 2)),
        (replace(issue, asset="UNKNOWN"), "issuer",
         ManagedAssetLifecycleRejectCodeV2.UNKNOWN_ASSET, (1, 1, 2)),
        (replace(issue, asset="EUR"), "issuer",
         ManagedAssetLifecycleRejectCodeV2.UNKNOWN_ASSET, (1, 1, 2)),
        (burn, "mallory", ManagedAssetLifecycleRejectCodeV2.UNAUTHORIZED_SUBJECT, (1, 1, 2)),
        (burn, "alice", None, (0, 1, 1)),
    )
    for nonce, (command, subject, code, expected) in enumerate(history, start=1):
        captured = canonical_global_bytes_v2(state)
        root = state.state_root
        result = transition_asset_lane_custody_v2(
            _context(command, subject=subject, nonce=nonce), state, command
        )
        assert canonical_global_bytes_v2(state) == captured
        if code is not None:
            assert type(result) is AssetLaneRejectedV2
            rejected = cast(AssetLaneRejectedV2, result)
            assert rejected.code is code
            assert rejected.pre_state_root == rejected.post_state_root == root
            assert rejected.effects.is_empty
        else:
            assert type(result) is AssetLaneCustodyAcceptedV2
            state = result.post_state
        alice, bob, supply = expected
        selected = tuple(
            EconomicAmountV2(owner, "USD", "accounts", amount)
            for owner, amount in (("alice", alice), ("bob", bob)) if amount
        )
        assert state.transfer_state.balances == (
            *initial.transfer_state.balances[:3], *selected, initial.transfer_state.balances[3],
        )
        assert state.transfer_state.supplies == tuple(
            AssetSupplyV2(row.asset, supply) if row.asset == "USD" else row
            for row in initial.transfer_state.supplies
        )
        assert state.transfer_state.policies == initial.transfer_state.policies
        assert state.origin_registry == initial.origin_registry
        assert state.managed_policies == initial.managed_policies
        assert state.custody == initial.custody
