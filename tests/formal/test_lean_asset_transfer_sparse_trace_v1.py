"""Constructive transfer histories: checked Lean contract and finite Python parity.

The history omits rejected attempts and retains every accepted accounting row.
It has no receipt, metadata, policy activation or publication semantics. The
sender-fee-owner example is a leaf history and can fail global fee admission.
Definitions-only mutants execute in isolated Lean files; none supplies proof.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferStateV1,
)
from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicAmountV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import (
    PROJECT,
    LeanSubject,
    _compile,
)

MODULE = "AssetTransferSparseTraceV1"
NAMESPACE = f"Proofs.{MODULE}"
DEPENDENCIES = (
    "AssetTransferRefinementV1", "AssetTransferCustodyCompletionV1",
    "CheckedSignedDeltaRefinementV1", "AssetTransferCustodyCompositionV1",
    "CheckedEconomicAggregationV1", "GlobalSettlementCoreV2",
    "GlobalEconomicStateRefinementV2", "CheckedEpochEconomicTablesV1",
    "CanonicalEpochEconomicRowsV1", "AssetTransferSparseTablesV1",
)
ROOT = "0x" + "01" * 32
HISTORY = (("mallory", 1), ("alice", 3), ("alice", 0),
           ("alice", 100), ("alice", 5), ("alice", 5))


@pytest.fixture(scope="module")
def compiled(tmp_path_factory: pytest.TempPathFactory) -> LeanSubject:
    assert (PROJECT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    found = subprocess.run(["elan", "which", "lean"], cwd=PROJECT,
                           capture_output=True, text=True, check=True, timeout=30)
    executable = Path(found.stdout.strip())
    version = subprocess.run([str(executable), "--version"], capture_output=True,
                             text=True, check=True, timeout=30)
    assert "version 4.27.0," in version.stdout
    directory = tmp_path_factory.mktemp("sparse-transfer-trace")
    source, library = directory / "source", directory / "library"
    (source / "Proofs").mkdir(parents=True)
    (library / "Proofs").mkdir(parents=True)
    subject = LeanSubject(executable, source, library)
    for name in (*DEPENDENCIES, MODULE):
        captured = source / "Proofs" / f"{name}.lean"
        captured.write_bytes((PROJECT / "Proofs" / f"{name}.lean").read_bytes())
        result = _compile(subject, captured, library / "Proofs" / f"{name}.olean")
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""
    return subject


def _probe(subject: LeanSubject, name: str, text: str) -> str:
    path = subject.source / f"{name}.lean"
    path.write_text(text)
    result = _compile(subject, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert not result.stderr
    return result.stdout


def _fixture(owner: str) -> tuple[AssetTransferContextV1, AssetTransferStateV1]:
    context = AssetTransferContextV1("trace", ROOT, ROOT, 1, ROOT, ROOT, "alice", ROOT)
    state = AssetTransferStateV1(
        ROOT, (AssetTransferPolicyV1("USD", owner, 1, True),),
        (EconomicAmountV1("alice", "USD", "accounts", 10),),
        (AssetSupplyV1("USD", 10),),
    )
    return context, state


def _runtime(owner: str) -> list[list[str]]:
    context, state = _fixture(owner)
    plans = []
    rejects = []
    for subject, atoms in HISTORY:
        command = AssetTransferCommandV1("asset_transfer", "USD", "alice", "bob", atoms, 1)
        before = canonical_global_bytes_v1(state)
        outcome = transition_asset_transfer_v1(replace(context, subject_id=subject), state, command)
        assert canonical_global_bytes_v1(state) == before
        if isinstance(outcome, AssetTransferAcceptedV1):
            state = outcome.post_state
            plans.append(outcome.effects)
        else:
            rejects.append(outcome.code)
            assert outcome.effects.is_empty
            assert outcome.pre_state_root == outcome.post_state_root == state.state_root
    assert rejects == [AssetTransferRejectCodeV1.UNAUTHORIZED_SUBJECT,
                       AssetTransferRejectCodeV1.ZERO_AMOUNT,
                       AssetTransferRejectCodeV1.INSUFFICIENT_BALANCE,
                       AssetTransferRejectCodeV1.INSUFFICIENT_BALANCE]
    assert len(plans) == 2
    assert sum(row.amount_atoms for row in state.balances) == 10
    expected_balances = {
        "treasury": (("bob", 8), ("treasury", 2)),
        "bob": (("bob", 10),),
        "alice": (("alice", 2), ("bob", 8)),
    }
    assert tuple((row.owner, row.amount_atoms) for row in state.balances) == expected_balances[owner]
    return (
        [["COUNT", str(len(plans))]]
        + [["B", row.owner, row.asset, row.custody_domain, str(row.amount_atoms)]
           for row in state.balances]
        + [["E", str(index), row.kind.value, row.principal, row.asset,
            row.custody_domain, str(row.delta_atoms)]
           for index, plan in enumerate(plans) for row in plan.rows]
    )


def _observation(owner: str) -> str:
    requests = ",\n".join(
        f'⟨⟨{json.dumps(ROOT)}, {json.dumps(subject)}⟩, '
        f'⟨"asset_transfer", "USD", "alice", "bob", {atoms}, 1⟩⟩'
        for subject, atoms in HISTORY
    )
    return f'''
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.AssetTransferSparseTraceV1
def config : Config := ⟨{json.dumps(ROOT)}, ⟨"USD", {json.dumps(owner)}, 1, true⟩⟩
def initial : GlobalState := {{ staticGlobalState with
  balances := [⟨"alice", "USD", "accounts", 10⟩]
  supplies := [⟨"USD", 10⟩] }}
def requests : List Request := [{requests}]
def actual := run config requests initial
def observation : List (List String) :=
  [["COUNT", toString actual.acceptedPlans.length]] ++
  (actual.post.balances.map fun row =>
    ["B", row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]) ++
  (actual.acceptedPlans.zipIdx.flatMap fun pair => pair.1.rows.map fun row =>
    ["E", toString pair.2, row.kind.code, row.principal, row.asset,
      row.custodyDomain, toString row.deltaAtoms])
#eval IO.println (reprStr observation)
'''


def _positive_consumer() -> str:
    return '''
theorem initial_canonical : S.CanonicalBalances initial.balances := by
  constructor
  · unfold Proofs.AssetTransferSparseTablesV1.Unique
    decide
  constructor
  · intro row member
    simp only [initial, List.mem_singleton] at member
    subst row
    decide
  constructor
  · decide
  · exact List.pairwise_singleton _ _
example : Proofs.CheckedEpochEconomicTablesV1.TableChain initial
    actual.acceptedPlans actual.post :=
  (run_table_chain config requests initial initial_canonical).1
'''


def test_constructed_history_contract_and_transitive_axioms(compiled: LeanSubject) -> None:
    types = {
        "rejected_attempt_omitted": "∀ (c : Config) (r : Request) (rs : List Request) (pre : GlobalState) {code : Proofs.AssetTransferRefinementV1.RejectCode}, (S.step (inputFor c r pre)).verdict = .rejected code → run c (r :: rs) pre = run c rs pre ∧ (S.step (inputFor c r pre)).post = pre ∧ (S.step (inputFor c r pre)).plan = EffectPlan.empty",
        "run_table_chain": "∀ (c : Config) (rs : List Request) (pre : GlobalState), S.CanonicalBalances pre.balances → TableChain pre (run c rs pre).acceptedPlans (run c rs pre).post ∧ S.CanonicalBalances (run c rs pre).post.balances",
        "run_plan_count": "∀ (c : Config) (rs : List Request) (pre : GlobalState), (run c rs pre).acceptedPlans.length ≤ rs.length",
        "checked_history_exact_tables": "∀ (c : Config) (rs : List Request) (pre : GlobalState), S.CanonicalBalances pre.balances → ∀ out : Totals, checkedEpoch i128 (run c rs pre).acceptedPlans = .ok out → ∀ (table : Table) (owner asset domain : String), amountAt (tableRows table (run c rs pre).post) owner asset domain - amountAt (tableRows table pre) owner asset domain = out (encodeKey (tableKind table) owner asset domain)",
        "checked_history_iff_prefix_bounds": "∀ (c : Config) (rs : List Request) (pre : GlobalState), S.CanonicalBalances pre.balances → ((∃ out, checkedEpoch i128 (run c rs pre).acceptedPlans = .ok out ∧ ∀ (table : Table) (owner asset domain : String), amountAt (tableRows table (run c rs pre).post) owner asset domain - amountAt (tableRows table pre) owner asset domain = out (encodeKey (tableKind table) owner asset domain)) ↔ PrefixFits i128 empty (orderedRows (run c rs pre).acceptedPlans))",
    }
    text = f"import {NAMESPACE}\nopen {NAMESPACE}\n"
    text += "open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2\n"
    text += "open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1\n"
    for name, signature in types.items():
        text += f"example : {signature} := {NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}\n"
    result = _probe(compiled, "Contract", text)
    groups = re.findall(r"depends on axioms: \[(.*?)\]", result, re.S)
    assert len(groups) == len(types), result
    for group in groups:
        assert set(re.findall(r"[A-Za-z_.]+", group)) <= {"propext", "Classical.choice", "Quot.sound"}


@pytest.mark.parametrize("owner", ("treasury", "bob", "alice"))
def test_rejected_attempts_preserve_following_transfers_and_exact_rows(
    compiled: LeanSubject, owner: str,
) -> None:
    expected = _runtime(owner)
    actual = _probe(
        compiled, f"History_{owner}",
        f"import {NAMESPACE}\n" + _observation(owner) + _positive_consumer(),
    )
    assert json.loads(actual) == expected


@pytest.mark.parametrize(("needle", "replacement"), (
    ("| .rejected _ => run config requests pre", "| .rejected _ => ⟨pre, []⟩"),
    ("⟨tail.post, next.plan :: tail.acceptedPlans⟩", "⟨tail.post, tail.acceptedPlans⟩"),
    ("let tail := run config requests next.post", "let tail := run config requests pre"),
))
def test_executable_history_mutants_are_detected(
    compiled: LeanSubject, needle: str, replacement: str,
) -> None:
    source = (compiled.source / "Proofs" / f"{MODULE}.lean").read_text()
    definitions = source.split("theorem rejected_attempt_omitted", 1)[0]
    assert definitions.count(needle) == 1
    mutated = definitions.replace(needle, replacement) + f"\nend {NAMESPACE}\n"
    actual = _probe(compiled, "HistoryMutant", mutated + _observation("treasury"))
    assert json.loads(actual) != _runtime("treasury")
