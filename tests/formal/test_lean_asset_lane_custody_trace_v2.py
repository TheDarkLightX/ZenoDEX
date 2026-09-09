"""Initial-state-only custody trace proof; finite runtime correspondence separately."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

import pytest

from tests.formal.test_lean_asset_lane_custody_refinement_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_refinement_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_lane_custody_refinement_v2 import (
    custody_lean as custody_lean,
)
from tests.formal.test_lean_asset_lane_custody_refinement_v2 import (
    lean as lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

MODULE = "AssetLaneCustodyTraceV2"
NAMESPACE = f"Proofs.{MODULE}"
PROOFS = Path(__file__).resolve().parents[2] / "lean-mathlib/Proofs"
SOURCE_SHA256 = "fda710c542059d5041afd36bfd96746e8f208f98b8c4a31c4b723c9e9c6b9940"
CONTROLS_SHA256 = "9131cfcd7c68e5ccc008d090341f17038d59729b41de4d8f4bd67f50c934688f"
OPEN = """open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1
open Proofs.AssetLaneCustodyRefinementV2 Proofs.AssetLaneCustodyTraceV2
namespace T
export Proofs.AssetTransferRefinementV2 (RootModel Context Policy Command transition IsU128)
end T
namespace M
export Proofs.ManagedAssetLifecycleRefinementV2 (RootModel Context Policy Command transition
  PolicyWellFormed CommandWellFormed signedAmount)
end M
"""


@pytest.fixture(scope="module")
def trace_lean(custody_lean: LeanSubject) -> LeanSubject:
    source = (PROOFS / f"{MODULE}.lean").read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    path = custody_lean.source / "Proofs" / f"{MODULE}.lean"
    path.write_bytes(source)
    checked = _compile(custody_lean, path, custody_lean.library / "Proofs" / f"{MODULE}.olean")
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stdout == checked.stderr == ""
    return custody_lean


def _probe(subject: LeanSubject, name: str, body: str):
    path = subject.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    return _compile(subject, path)


def _controls_probe(subject: LeanSubject, name: str, body: str = ""):
    source = Path(__file__).with_name("asset_lane_custody_trace_v2_controls.lean").read_bytes()
    assert hashlib.sha256(source).hexdigest() == CONTROLS_SHA256
    path = subject.source / f"{name}.lean"
    path.write_text(source.decode() + "\n" + body)
    return _compile(subject, path)


def test_exact_mixed_history_and_prefixes(trace_lean: LeanSubject):
    checked = _controls_probe(trace_lean, "MixedTraceControls")
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", checked.stdout)
    assert len(groups) + checked.stdout.count("does not depend on any axioms") == 3
    axioms = {item.strip() for group in groups for item in group.split(",") if item.strip()}
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


@pytest.mark.parametrize(("name", "body"), [
    ("ChangedFinalSupply", """example :
      supplyAt (run B.roots M.lifecycleRoots B.pre actions) "ORD" = 121 := by
      rw [exact_history]; decide"""),
    ("DroppedDormantKey", """example :
      (run B.roots M.lifecycleRoots B.pre actions).transferState.supplies =
        [⟨"EUR", 7⟩, ⟨"ORD", 120⟩] := by rw [exact_history]; decide"""),
    ("ChangedCustodyOwner", """example :
      (run B.roots M.lifecycleRoots B.pre actions).custody =
        [⟨"mallory", "ORD", "escrow", 5⟩] := by rw [history_custody]; decide"""),
    ("RejectedStateChanged", """example :
      (transferStep B.roots (T.baseContext "mallory") afterTransfer B.policy B.transfer).2 =
        afterBurn := by rw [unauthorized_result]; decide"""),
    ("LostFeeAtom", """example :
      (run B.roots M.lifecycleRoots B.pre actions).transferState.balances =
        [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 88⟩,
         ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 1⟩] := by
      rw [exact_history]; decide"""),
])
def test_kernel_refuses_false_history_laws(trace_lean: LeanSubject, name: str, body: str):
    """Check kernel refusal of false laws; these are not runtime code mutants."""
    checked = _controls_probe(trace_lean, name, body)
    assert checked.returncode == 1, checked.stdout + checked.stderr
    assert "Tactic `decide` proved that the proposition" in checked.stdout
    assert "is false" in checked.stdout


def test_initial_only_trace_contracts_and_standard_axioms(trace_lean: LeanSubject):
    contracts = {
        "supply_bounded": """∀ {pre : State}, RowsRepresentable pre →
          ∀ asset, FitsU128 (supplyAt pre asset)""",
        "transfer_preserves_rows": """∀ {roots : T.RootModel} {context : T.Context}
          {pre : State} {policy : T.Policy} {command : T.Command},
          RowsRepresentable pre → policy ∈ pre.transferState.policies →
          T.IsU128 policy.transferFeeAtoms → policy.atomDecimals = 8 →
          (T.transition roots context (transferView pre policy) command).verdict = .accepted →
          RowsRepresentable (transferPost pre policy command)""",
        "managed_preserves_rows": """∀ {roots : M.RootModel} {context : M.Context}
          {pre : State} {policy : M.Policy} {command : M.Command},
          RowsRepresentable pre → policy ∈ pre.managedPolicies → M.PolicyWellFormed policy →
          M.CommandWellFormed command →
          (M.transition roots context (managedView pre policy) command).verdict = .accepted →
          RowsRepresentable (managedPost pre command.asset command.accountOwner
            (M.signedAmount command))""",
        "run_preserves_rows": """∀ (transferRoots : T.RootModel) (managedRoots : M.RootModel)
          (actions : List Action) {pre : State}, RowsRepresentable pre →
          (∀ action ∈ actions, Ready pre action) →
          RowsRepresentable (run transferRoots managedRoots pre actions)""",
        "run_fixed_frame": """∀ (transferRoots : T.RootModel) (managedRoots : M.RootModel)
          (actions : List Action) (pre : State),
          let post := run transferRoots managedRoots pre actions
          post.transferState.moduleReleaseId = pre.transferState.moduleReleaseId ∧
          post.transferState.policies = pre.transferState.policies ∧
          post.originRegistry = pre.originRegistry ∧
          post.managedPolicies = pre.managedPolicies ∧ post.custody = pre.custody""",
        "every_prefix_preserves_rows": """∀ (transferRoots : T.RootModel) (managedRoots : M.RootModel)
          (actions : List Action) {pre : State}, RowsRepresentable pre →
          (∀ action ∈ actions, Ready pre action) → ∀ length,
          RowsRepresentable (run transferRoots managedRoots pre (actions.take length))""",
    }
    body = "\n".join(f"example : {signature} := @{NAMESPACE}.{name}" for name, signature in contracts.items())
    body += "\n" + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in contracts)
    checked = _probe(trace_lean, "IndependentTraceContracts", body)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    assert checked.stdout.count("depends on axioms") + checked.stdout.count(
        "does not depend on any axioms"
    ) == len(contracts)
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", checked.stdout)
        for item in group.split(",") if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    source = (PROOFS / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None


def test_runtime_mixed_trace_matches_the_complete_formal_rows_at_each_prefix():
    from dataclasses import replace

    from src.core.asset_lane_coordinator_values_v2 import AssetLaneRejectedV2
    from src.core.asset_lane_custody_coordinator_v2 import (
        AssetLaneCustodyAcceptedV2,
        transition_asset_lane_custody_v2,
    )
    from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
    from src.core.asset_transfer_types_v2 import AssetTransferRejectCodeV2, AssetTransferStateV2
    from src.core.global_settlement_types_v2 import (
        AssetSupplyV2,
        EconomicAmountV2,
        canonical_global_bytes_v2,
    )
    from tests.core import test_asset_lane_coordinator_v2 as fixture

    keys = ("AUD", "EUR", "ORD")
    policies = tuple(
        fixture._transfer_policy(asset=asset, fee_owner="m_treasury", fee_atoms=2)
        for asset in keys
    )
    managed = (fixture._managed_policy(asset="ORD"),)
    custody = (EconomicAmountV2("vault", "ORD", "escrow", 5),)
    state = AssetLaneCustodyStateV2(
        AssetTransferStateV2(
            fixture._root("module-release"), policies,
            (EconomicAmountV2("dave", "EUR", "accounts", 7),
             EconomicAmountV2("alice", "ORD", "accounts", 100),
             EconomicAmountV2("bob", "ORD", "accounts", 15)),
            (AssetSupplyV2("AUD", 0), AssetSupplyV2("EUR", 7), AssetSupplyV2("ORD", 120)),
        ), fixture._registry(policies, managed), managed, custody,
    )
    transfer = replace(
        fixture._transfer_command(amount_atoms=10),
        asset="ORD", asset_origin_root=fixture._root("origin:ORD"),
    )
    issue = replace(
        fixture._managed_command(amount_atoms=7), asset="ORD",
        asset_origin_root=fixture._root("origin:ORD"), authorization_root=fixture._root("issue:ORD"),
    )
    burn = replace(
        fixture._managed_command(kind="managed_asset_burn", amount_atoms=7), asset="ORD",
        asset_origin_root=fixture._root("origin:ORD"), authorization_root=fixture._root("burn:ORD"),
    )
    for nonce, (command, subject, expected) in enumerate((
        (issue, "issuer", (107, 15, 0, 127)),
        (transfer, "alice", (95, 25, 2, 127)),
        (transfer, "mallory", (95, 25, 2, 127)),
        (burn, "alice", (88, 25, 2, 120)),
    ), start=1):
        context = fixture._context(
            command, subject=subject, nonce=nonce,
            grant_root=getattr(command, "authorization_root", None),
        )
        captured = canonical_global_bytes_v2(state)
        result = transition_asset_lane_custody_v2(context, state, command)
        assert canonical_global_bytes_v2(state) == captured
        if subject == "mallory":
            assert type(result) is AssetLaneRejectedV2
            assert result.code is AssetTransferRejectCodeV2.UNAUTHORIZED_SUBJECT
            assert result.effects.is_empty
            assert result.pre_state_root == result.post_state_root == state.state_root
        else:
            assert type(result) is AssetLaneCustodyAcceptedV2
            state = result.post_state
        balances = {(row.asset, row.owner): row.amount_atoms for row in state.transfer_state.balances}
        assert tuple(balances.get(("ORD", owner), 0) for owner in ("alice", "bob", "m_treasury")) == expected[:3]
        assert balances[("EUR", "dave")] == 7
        assert state.physical_atoms("ORD") == state.transfer_state.supply_atoms("ORD") == expected[3]
        assert state.transfer_state.supply_atoms("AUD") == 0
        assert tuple(row.asset for row in state.origin_registry.assets) == keys
        assert state.custody == custody
