"""Fresh Lean replay of filtered custody steps and their complete mixed traces."""

from __future__ import annotations

import hashlib
import inspect
import re
from pathlib import Path

import pytest

from tests.formal.test_lean_asset_lane_custody_trace_v2 import (
    CONTROLS_SHA256,
    PROOFS,
)
from tests.formal.test_lean_asset_lane_custody_trace_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_trace_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_lane_custody_trace_v2 import (
    custody_lean as custody_lean,
)
from tests.formal.test_lean_asset_lane_custody_trace_v2 import (
    lean as lean,
)
from tests.formal.test_lean_asset_lane_custody_trace_v2 import (
    trace_lean as trace_lean,
)
from tests.formal.test_lean_asset_lane_finite_recomposition_v2 import (
    SOURCE_SHA256 as RECOMPOSITION_SHA,
)
from tests.formal.test_lean_asset_lane_shared_projection_v2 import SOURCE_SHA256 as SHARED_SHA
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

MODULE = "AssetLaneCustodyRecompositionV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE_SHA256 = "0ffbeb9fdc38e1bc3b9995e1b17582dd921bbab8ee0ee846d88d59587d0d42e3"
OPEN = f"""open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.AssetLaneCustodyRefinementV2
open {NAMESPACE}
"""


@pytest.fixture(scope="module")
def recomposed_lean(trace_lean: LeanSubject) -> LeanSubject:
    for name, pin in (
        ("AssetLaneSharedProjectionV2", SHARED_SHA),
        ("AssetLaneFiniteRecompositionV2", RECOMPOSITION_SHA),
        (MODULE, SOURCE_SHA256),
    ):
        source = (PROOFS / f"{name}.lean").read_bytes()
        assert hashlib.sha256(source).hexdigest() == pin
        path = trace_lean.source / "Proofs" / f"{name}.lean"
        path.write_bytes(source)
        checked = _compile(trace_lean, path, trace_lean.library / "Proofs" / f"{name}.olean")
        assert checked.returncode == 0, checked.stdout + checked.stderr
        assert checked.stdout == checked.stderr == ""
    return trace_lean


def test_complete_state_and_initial_only_trace_contracts(recomposed_lean: LeanSubject) -> None:
    contracts = {
        "selected_supply_numeric_rows": """∀ (assets : List Asset)
          (rows : List Proofs.RegisteredSupplySupportV1.V1SupplyRow),
          Proofs.RegisteredSupplySupportV1.numericRows (R.selectSupplies assets rows) =
            (Proofs.RegisteredSupplySupportV1.numericRows rows).filter
              (fun row => decide (row.asset ∈ assets))""",
        "filtered_view_eq": """∀ {pre : State} {policy : M.Policy},
          RowsRepresentable pre → policy ∈ pre.managedPolicies →
          filteredView pre policy = managedView pre policy""",
        "recomposed_post_eq": """∀ {pre : State} {asset owner : String} {deltaAtoms : Int},
          RowsRepresentable pre → asset ∈ managedAssets pre →
          recomposedPost pre asset owner deltaAtoms = managedPost pre asset owner deltaAtoms""",
        "managed_step_eq": f"""∀ {{roots : M.RootModel}} {{context : M.Context}} {{pre : State}}
          {{policy : M.Policy}} {{command : M.Command}}, RowsRepresentable pre →
          policy ∈ pre.managedPolicies →
          {NAMESPACE}.managedStep roots context pre policy command =
            Proofs.AssetLaneCustodyRefinementV2.managedStep roots context pre policy command""",
        "run_eq": """∀ (transferRoots : T.RootModel) (managedRoots : M.RootModel)
          (actions : List Trace.Action) {pre : State}, RowsRepresentable pre →
          (∀ action ∈ actions, Trace.Ready pre action) →
          run transferRoots managedRoots pre actions = Trace.run transferRoots managedRoots pre actions""",
        "run_preserves_rows": """∀ (transferRoots : T.RootModel) (managedRoots : M.RootModel)
          (actions : List Trace.Action) {pre : State}, RowsRepresentable pre →
          (∀ action ∈ actions, Trace.Ready pre action) →
          RowsRepresentable (run transferRoots managedRoots pre actions)""",
    }
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in contracts.items()
    )
    path = recomposed_lean.source / "RecomposedCustodyContracts.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    checked = _compile(recomposed_lean, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", checked.stdout)
    assert len(groups) + checked.stdout.count("does not depend on any axioms") == len(contracts)
    axioms = {item.strip() for group in groups for item in group.split(",") if item.strip()}
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    code = re.sub(r"/-.*?-/", "", (PROOFS / f"{MODULE}.lean").read_text(), flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None


def test_recomposed_history_has_the_independent_expected_complete_state(
    recomposed_lean: LeanSubject,
) -> None:
    controls = Path(__file__).with_name(
        "asset_lane_custody_trace_v2_controls.lean"
    ).read_bytes()
    assert hashlib.sha256(controls).hexdigest() == CONTROLS_SHA256
    path = recomposed_lean.source / "RecomposedCustodyHistory.lean"
    path.write_text(
        f"import {NAMESPACE}\n" + controls.decode() + f"""
example : {NAMESPACE}.run B.roots M.lifecycleRoots B.pre actions = afterBurn := by
  rw [{NAMESPACE}.run_eq B.roots M.lifecycleRoots actions
    Controls.legal_custody_state_representable inputs_ready]
  exact exact_history

example (length : Nat) :
    RowsRepresentable ({NAMESPACE}.run B.roots M.lifecycleRoots B.pre (actions.take length)) := by
  apply {NAMESPACE}.run_preserves_rows B.roots M.lifecycleRoots _
    Controls.legal_custody_state_representable
  intro action member
  exact inputs_ready action (List.mem_of_mem_take member)

def deniedContext : Proofs.ManagedAssetLifecycleRefinementV2.Context :=
  {{ M.issueContext with occurrence :=
      M.issueContext.occurrence.map (fun occurrence => {{ occurrence with subjectId := "mallory" }}) }}

example : {NAMESPACE}.managedStep M.lifecycleRoots deniedContext B.pre M.ordinaryPolicy B.issue =
    (.rejected .unauthorizedSubject, B.pre) := by
  rw [{NAMESPACE}.managed_step_eq Controls.legal_custody_state_representable (by decide)]
  decide
"""
    )
    checked = _compile(recomposed_lean, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""


@pytest.mark.parametrize(("name", "before", "after"), [
    (
        "DropDormantIdentities",
        "pre.transferState.supplies\n        asset deltaAtoms } }",
        "(pre.transferState.supplies.filter nonzeroRow)\n        asset deltaAtoms } }",
    ),
    (
        "DropUnmanagedBalances",
        "balances := R.recomposeBalances (managedAssets pre) pre.transferState.balances",
        "balances := A.updateRows (H.selectRows (managedAssets pre) pre.transferState.balances)",
    ),
    (
        "ChangeRejectedCustody",
        "| .rejected code => (.rejected code, pre)",
        "| .rejected code => (.rejected code, { pre with custody := [] })",
    ),
    (
        "ChangeAcceptedCustody",
        "{ pre with transferState := { pre.transferState with",
        "{ pre with custody := [], transferState := { pre.transferState with",
    ),
])
def test_kernel_refuses_semantically_changed_constructions(
    recomposed_lean: LeanSubject, name: str, before: str, after: str,
) -> None:
    """These alter the modeled construction, not the Python/Rust implementation."""
    source = (PROOFS / f"{MODULE}.lean").read_text()
    assert source.count(before) == 1
    path = recomposed_lean.source / f"{name}.lean"
    path.write_text(source.replace(before, after))
    checked = _compile(recomposed_lean, path)
    assert checked.returncode == 1, checked.stdout + checked.stderr
    assert "error:" in checked.stdout
    assert "unexpected token" not in checked.stdout
    assert "unknownIdentifier" not in checked.stdout


@pytest.mark.parametrize(("before", "after"), [
    ("*[r for r in old.balances if r.asset not in managed]", "*[]"),
    (
        "*[r for r in old.balances if r.asset not in managed]",
        "*([r for r in old.balances if r.asset not in managed] * 2)",
    ),
    ("*post.balances", '*[r for r in post.balances if r.asset != "GBP"]'),
    (
        "r.asset not in managed], *post.supplies",
        "r.asset not in managed and r.amount_atoms != 0], *post.supplies",
    ),
    (
        "*post.balances",
        '*[replace(r, owner="mallory") if r.asset == "USD" else r for r in post.balances]',
    ),
    ("pre.custody)", "())"),
    (
        "pre.custody)",
        'tuple(replace(r, owner="mallory") for r in pre.custody))',
    ),
], ids=[
    "lost-complement", "duplicate-complement", "lost-managed-sibling", "lost-dormant",
    "wrong-owner", "lost-custody", "custody-owner-substitution",
])
def test_runtime_history_detects_recomposition_faults(
    monkeypatch: pytest.MonkeyPatch, before: str, after: str,
) -> None:
    """The real history oracle must detect each mutated Python construction."""
    from src.core import asset_lane_custody_coordinator_v2 as coordinator
    from tests.core.test_asset_lane_custody_v2 import (
        test_managed_multiasset_history_keeps_complete_rows_and_rejects_unauthorized_burn as history,
    )

    history()
    source = inspect.getsource(coordinator._post_state)
    assert source.count(before) == 1
    namespace = vars(coordinator).copy()
    exec(compile(source.replace(before, after), "<custody-row-mutant>", "exec"), namespace)
    monkeypatch.setattr(coordinator, "_post_state", namespace["_post_state"])
    with pytest.raises((AssertionError, ValueError)):
        history()
