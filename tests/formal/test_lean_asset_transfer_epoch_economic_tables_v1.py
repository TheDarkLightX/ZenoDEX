"""Input-derived custody transfer traces refine checked and canonical epoch tables.

Lean evidence compiles a fresh Std-only closure, checks every public theorem's
type and axioms, and applies the trace-to-table theorems to the same concrete
two-transfer inputs used by the actual custody module, coordinator and epoch
position checker. The Python composer and four-table delta checker supply a
separate finite correspondence lane. Ordered rows and signed-prefix rejection
are observed directly; equality of final sums cannot establish either property.

No aggregate Verified, authorization, authenticated roots, publication, mounted
multi-command support or universal Python/Rust refinement is claimed. Prospective
states are input-derived disclosures; their builder grants no authority. The
single-occurrence mounted guard and standalone adjacent-height rule are retained.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

import pytest

from src.core.epoch_effect_composition_v1 import compose_asset_lane_epoch_effect_plans_v1
from src.core.global_economic_state_delta_v1 import _require_amount_table_refinement_v1
from src.core.global_settlement_types_v1 import MAX_U64_V1
from tests.formal.test_lean_asset_transfer_epoch_state_closure_v1 import (
    LEAN_OPENS,
    SharedHeightPair,
    _assert_shared_height_runtime,
    _shared_height_body,
)
from tests.formal.test_lean_asset_transfer_epoch_state_closure_v1 import (
    SOURCE_PINS as PREFIX_SOURCE_PINS,
)
from tests.formal.test_lean_asset_transfer_global_successor_v1 import PROJECT, _compile, _normalise
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import LeanSubject

MODULE = "AssetTransferEpochEconomicTablesV1"
NAMESPACE = f"Proofs.{MODULE}"
OPENS = LEAN_OPENS + (
    "\nopen Proofs.CanonicalEpochEconomicRowsV1 "
    f"Proofs.CheckedEpochEconomicTablesV1 Proofs.CheckedEconomicAggregationV1 {NAMESPACE}\n"
)
INPUT = "Proofs.AssetTransferGlobalSuccessorV1.Input"
STATE = "Proofs.AssetTransferPolicySelectionV1.State"
TRACE_BINDERS = (
    f"{{source : {STATE}}} {{count : Nat}} {{inputs : List {INPUT}}} {{carried : {STATE}}}"
)
TRACE = "EpochInputTrace source count inputs carried"
CERTIFIED_TRACE = f"StateInvariant source → {TRACE} → "

THEOREM_TYPES = {
    "epochInputPlans_snoc": (
        f"∀ (inputs : List {INPUT}) (next : {INPUT}), "
        "epochInputPlans (inputs ++ [next]) = epochInputPlans inputs ++ [(result next).plan]"
    ),
    "epochInputOccurrences_snoc": (
        f"∀ (inputs : List {INPUT}) (next : {INPUT}), epochInputOccurrences (inputs ++ [next]) = "
        "epochInputOccurrences inputs ++ [next.occurrence]"
    ),
    "epochInputPlans_length": f"∀ inputs : List {INPUT}, (epochInputPlans inputs).length = inputs.length",
    "orderedRows_epochInputPlans_snoc": (
        f"∀ (inputs : List {INPUT}) (next : {INPUT}), orderedRows (epochInputPlans (inputs ++ [next])) = "
        "orderedRows (epochInputPlans inputs) ++ encodeRows (result next).plan.rows"
    ),
    "epochInputTrace_prefix": (
        f"∀ {TRACE_BINDERS}, {TRACE} → EpochPrefix source count (epochInputOccurrences inputs) carried"
    ),
    "epochInputTrace_length": f"∀ {TRACE_BINDERS}, {TRACE} → inputs.length = count ∧ count ≤ maxEpochCommands",
    "epochInputTrace_invariant": f"∀ {TRACE_BINDERS}, {CERTIFIED_TRACE}StateInvariant carried",
    "epochInputTrace_nonempty": (
        f"∀ {TRACE_BINDERS}, {TRACE} → count ≠ 0 → "
        "1 ≤ inputs.length ∧ inputs.length ≤ maxEpochCommands ∧ "
        "carried.economic.height = source.economic.height + 1"
    ),
    "epochInputTrace_consumptions": (
        f"∀ {TRACE_BINDERS}, {CERTIFIED_TRACE}"
        "((epochInputPlans inputs).map EffectPlan.occurrenceConsumptions).flatten = "
        "inputs.map (fun input => input.occurrence.occurrenceId)"
    ),
    "epochInputTrace_tableChain": (
        f"∀ {TRACE_BINDERS}, {CERTIFIED_TRACE}TableChain source.economic (epochInputPlans inputs) carried.economic"
    ),
    "epochInputTrace_checked_iff": (
        f"∀ (bounds : Bounds) {TRACE_BINDERS}, {CERTIFIED_TRACE}"
        "((∃ output, checkedEpoch bounds (epochInputPlans inputs) = .ok output ∧ "
        "∀ table owner asset domain, amountAt (tableRows table carried.economic) owner asset domain - "
        "amountAt (tableRows table source.economic) owner asset domain = "
        "output (encodeKey (tableKind table) owner asset domain)) ↔ "
        "PrefixFits bounds empty (orderedRows (epochInputPlans inputs)))"
    ),
    "epochInputTrace_exact_tables": (
        f"∀ {TRACE_BINDERS}, {CERTIFIED_TRACE}∀ output : Totals, "
        "checkedEpoch i128 (epochInputPlans inputs) = .ok output → "
        "∀ (table : Table) (owner : Principal) (asset : Asset) (domain : AccountingLocation), "
        "amountAt (tableRows table carried.economic) owner asset domain - "
        "amountAt (tableRows table source.economic) owner asset domain = "
        "output (encodeKey (tableKind table) owner asset domain)"
    ),
    "amountKey_nodup_of_permuted": (
        "∀ rows : List AmountRow, (rows.map (fun row => (row.asset, row.owner, row.custodyDomain))).Nodup → "
        "(rows.map amountKey).Nodup"
    ),
    "endpointKeysUnique_of_admitted": (
        "∀ {pre post : GlobalState}, StateQuantitiesAdmitted pre → StateQuantitiesAdmitted post → "
        "EndpointKeysUnique pre post"
    ),
    "epochInputTrace_quantities": (
        f"∀ {TRACE_BINDERS}, {CERTIFIED_TRACE}"
        "StateQuantitiesAdmitted source.economic ∧ StateQuantitiesAdmitted carried.economic"
    ),
    "epochInputTrace_endpointKeysUnique": (
        f"∀ {TRACE_BINDERS}, {CERTIFIED_TRACE}EndpointKeysUnique source.economic carried.economic"
    ),
    "epochInputTrace_canonical_rows": (
        f"∀ {TRACE_BINDERS}, {CERTIFIED_TRACE}∀ output : Totals, "
        "checkedEpoch i128 (epochInputPlans inputs) = .ok output → "
        "CanonicalEffectRows (emitRows (epochInputPlans inputs) output) ∧ "
        "(∀ row ∈ emitRows (epochInputPlans inputs) output, Fits i128 row.deltaAtoms) ∧ "
        "(∀ key, keyedSum key (encodeRows (emitRows (epochInputPlans inputs) output)) = output key) ∧ "
        "∀ table, checkedStateDeltaRows table (tableRows table source.economic) "
        "(tableRows table carried.economic) = "
        ".ok (projectDeltaRows table (emitRows (epochInputPlans inputs) output))"
    ),
    "epochInputTrace_zero": (
        f"∀ {{source : {STATE}}} {{inputs : List {INPUT}}} {{carried : {STATE}}}, "
        "EpochInputTrace source 0 inputs carried → inputs = [] ∧ carried = source"
    ),
    "epochInputTrace_snoc_inv": (
        f"∀ {{source : {STATE}}} {{count : Nat}} {{inputs : List {INPUT}}} "
        f"{{next : {INPUT}}} {{carried : {STATE}}}, "
        "EpochInputTrace source (count + 1) (inputs ++ [next]) carried → "
        "carried = epochContinuedState next ∧ ∃ prior, EpochInputTrace source count inputs prior ∧ "
        "EpochRequirements ⟨source.economic, count⟩ prior next ∧ "
        "(Proofs.AssetTransferPolicySelectionV1.step next.transfer).verdict = .accepted"
    ),
}

RUNTIME_PINS = {
    # This continuation consumes the reviewed pure epoch-preparation subject.
    # The predecessor tests retain their own historical source declarations.
    "src/core/global_economic_proof_v1.py":
        "b7d826ddabc4c140e1803ffa0aebca0642d0a9ecd69b94a00567894829bbf345",
    "src/core/epoch_effect_composition_v1.py":
        "a678e459c3d57462c20fb787160c5e1ef9ed0706e62c293449b21a978efdd045",
    "src/core/global_economic_state_delta_v1.py":
        "5b06120b14176985a2889b81cc784145339b7f72720d7b161c74b296cb4e5634",
}
STANDARD_IMPORTS = {
    "Init.Data.Int.Order", "Init.Data.Int.Pow", "Init.Data.List.Lemmas",
    "Init.Data.List.Sort", "Init.Data.Ord", "Lean.Elab.Tactic.Omega", "Std.Tactic",
}


def _dependency_order() -> tuple[str, ...]:
    result: list[str] = []

    def visit(name: str) -> None:
        if name in result:
            return
        source = (PROJECT / "Proofs" / f"{name}.lean").read_text()
        for dependency in re.findall(r"^import (\S+)", source, re.MULTILINE):
            assert dependency.startswith("Proofs.") or dependency in STANDARD_IMPORTS, dependency
            if dependency.startswith("Proofs."):
                visit(dependency.removeprefix("Proofs."))
        result.append(name)

    visit(MODULE)
    return tuple(result)


@pytest.fixture(scope="module")
def lean(tmp_path_factory: pytest.TempPathFactory) -> LeanSubject:
    """No .lake dependency, shared cache or prebuilt subject enters this closure."""
    assert (PROJECT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    located = subprocess.run(["elan", "which", "lean"], cwd=PROJECT, capture_output=True,
                             text=True, check=True, timeout=30)
    executable = Path(located.stdout.strip())
    version = subprocess.run([str(executable), "--version"], capture_output=True,
                             text=True, check=True, timeout=30)
    assert "version 4.27.0," in version.stdout
    root = tmp_path_factory.mktemp("transfer-epoch-economic-tables")
    source, library = root / "source", root / "library"
    (source / "Proofs").mkdir(parents=True)
    (library / "Proofs").mkdir(parents=True)
    subject = LeanSubject(executable, source, library)
    order = _dependency_order()
    assert len(order) == 23 and order[-1] == MODULE
    for name in order:
        captured = source / "Proofs" / f"{name}.lean"
        captured.write_bytes((PROJECT / "Proofs" / f"{name}.lean").read_bytes())
        result = _compile(subject, captured, library / "Proofs" / f"{name}.olean")
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""
    return subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPENS}\n{body}")
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def test_every_theorem_signature_axioms_input_maps_and_empty_trace(lean: LeanSubject) -> None:
    source_path = lean.source / "Proofs" / f"{MODULE}.lean"
    source = source_path.read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert tuple(re.findall(r"^theorem (\w+)", code, re.MULTILINE)) == tuple(THEOREM_TYPES)
    scanner = PROJECT.parent / "tools/scan_lean_proof_placeholders_v1.py"
    scan = subprocess.run([sys.executable, str(scanner), str(source_path), "--json"],
                          capture_output=True, text=True, check=False, timeout=120)
    assert scan.returncode == 0 and json.loads(scan.stdout)["blocked"] is False
    consumers = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    consumers += f"""
example : epochInputPlans = fun inputs => inputs.map (fun input => (result input).plan) := rfl
example : epochInputOccurrences = fun inputs => inputs.map (fun input => input.occurrence) := rfl
example : checkedEpoch i128 (epochInputPlans []) = .ok empty := rfl
example (source : {STATE}) : EpochInputTrace source 0 [] source := EpochInputTrace.nil
example (source : {STATE}) : TableChain source.economic (epochInputPlans []) source.economic :=
  TableChain.nil _
"""
    report = " ".join(_probe(lean, "TheoremConsumers", consumers).split())
    for name in THEOREM_TYPES:
        found = re.search(re.escape(f"'{NAMESPACE}.{name}' ") +
                          r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", report)
        assert found, (name, report)
        axioms = {x.strip() for x in (found.group(1) or "").split(",") if x.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)
    for path, digest in {**PREFIX_SOURCE_PINS, **RUNTIME_PINS}.items():
        assert hashlib.sha256((PROJECT.parent / path).read_bytes()).hexdigest() == digest, path


def _decode_observations(output: str) -> list[object]:
    values = [json.loads(line) for line in output.splitlines()]
    return [None if value == "ERR" else json.loads(value.removeprefix("OK:")) for value in values]


@pytest.mark.parametrize("height", [7, MAX_U64_V1 - 1])
def test_same_input_trace_derives_checked_rows_and_all_endpoint_tables(lean: LeanSubject, height: int) -> None:
    pair = SharedHeightPair(height=height)
    _assert_shared_height_runtime(pair)
    first = _normalise(pair.first, pair.first_accepted)
    second = pair.second_effects
    epoch = compose_asset_lane_epoch_effect_plans_v1((first, second))
    deltas = _require_amount_table_refinement_v1(pair.source, pair.second_post, epoch)
    body = _shared_height_body(pair) + ROW_LEMMAS + TRACE_CONSUMERS + OBSERVERS
    body += """
#eval observeRows ((checkedEpoch i128 tracePlans).map (emitRows tracePlans))
"""
    expected: list[object] = [[
        [row.kind.value, row.principal, row.asset, row.custody_domain, str(row.delta_atoms)]
        for row in epoch.rows
    ]]
    for table in ("balances", "custody", "liabilities", "reserves"):
        body += f"""
#eval observeDeltas (checkedStateDeltaRows .{table} (tableRows .{table} firstEconomic)
  (tableRows .{table} (epochContinuedState secondGlobal).economic))
#eval observeDeltas ((checkedEpoch i128 tracePlans).map
  (fun totals => projectDeltaRows .{table} (emitRows tracePlans totals)))
"""
        rows = [[row.table, row.owner, row.asset, row.custody_domain, str(row.delta_atoms)]
                for row in deltas if row.table == table]
        expected.extend([rows, rows])
    body += """
#eval observeOrdered (orderedRows tracePlans)
#eval observeOrdered (orderedRows (epochInputPlans [secondGlobal, firstGlobal]))
"""
    ordered = lambda plan: [  # noqa: E731 -- local observation has no authority.
        [row.kind.value, row.principal, row.asset, row.custody_domain, str(row.delta_atoms)]
        for row in plan.rows
    ]
    expected.extend([ordered(first) + ordered(second), ordered(second) + ordered(first)])
    assert expected[-1] != expected[-2]
    assert _decode_observations(_probe(lean, f"TraceTables{height}", body)) == expected


ROW_LEMMAS = r"""
/-- Rows of an accepted custody-complete plan are the projected rows of the selected sparse step. -/
theorem result_rows_of_accepted {input : Proofs.AssetTransferGlobalSuccessorV1.Input}
    (accepted : (Proofs.AssetTransferPolicySelectionV1.step input.transfer).verdict = .accepted) :
    ∃ policy, Proofs.AssetTransferPolicySelectionV1.policyFor input.transfer.pre.policies
        input.transfer.command.asset = some policy ∧
      (Proofs.AssetTransferGlobalSuccessorV1.result input).plan.rows =
        (Proofs.AssetTransferSparseTablesV1.projectedPlan
          (Proofs.AssetTransferPolicySelectionV1.selectedInput input.transfer policy)).rows := by
  obtain ⟨policy, selection, _, _, _, _⟩ :=
    Proofs.AssetTransferPolicySelectionV1.accepted_selected_step accepted
  refine ⟨policy, selection, ?_⟩
  unfold Proofs.AssetTransferGlobalSuccessorV1.result
  rw [(Proofs.AssetTransferCustodyEffectPlanV1.complete_preserves_other_plan_fields _ _).1,
    Proofs.AssetTransferEffectPlanV1.complete_accepted_plan accepted selection,
    Proofs.AssetTransferEffectPlanV1.selectedPlan_rows]

theorem second_rows : (result secondGlobal).plan.rows =
    [⟨.accountMovement, "alice", "USD", "accounts", (-3 : Int)⟩,
     ⟨.accountMovement, "bob", "USD", "accounts", (3 : Int)⟩,
     ⟨.feeAllocation, "bob", "USD", "accounts", (1 : Int)⟩] := by
  obtain ⟨policy, selection, rows⟩ := result_rows_of_accepted (input := secondGlobal) second_accepted
  change policyFor (epochContinuedState firstGlobal).policies "USD" = some policy at selection
  rw [(epochContinuedState_static_frame firstGlobal).2] at selection
  have chosen : policy = ⟨"USD", "bob", (1 : Int), true⟩ :=
    Option.some.inj (selection.symm.trans rfl)
  subst chosen
  rw [rows]
  change Proofs.CanonicalEpochEconomicRowsV1.sortOn Proofs.AssetTransferSparseTablesV1.effectWire
    [⟨.accountMovement, "alice", "USD", "accounts", (-3 : Int)⟩,
     ⟨.accountMovement, "bob", "USD", "accounts", (3 : Int)⟩,
     ⟨.feeAllocation, "bob", "USD", "accounts", (1 : Int)⟩] = _
  simp +decide [Proofs.CanonicalEpochEconomicRowsV1.sortOn, List.mergeSort,
    List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

theorem first_rows : (result firstGlobal).plan.rows =
    [⟨.accountMovement, "alice", "USD", "accounts", (-5 : Int)⟩,
     ⟨.accountMovement, "bob", "USD", "accounts", (5 : Int)⟩,
     ⟨.feeAllocation, "bob", "USD", "accounts", (1 : Int)⟩] := by
  obtain ⟨policy, selection, rows⟩ := result_rows_of_accepted (input := firstGlobal) first_accepted
  have chosen : policy = ⟨"USD", "bob", (1 : Int), true⟩ :=
    Option.some.inj (selection.symm.trans rfl)
  subst chosen
  rw [rows]
  change Proofs.CanonicalEpochEconomicRowsV1.sortOn Proofs.AssetTransferSparseTablesV1.effectWire
    [⟨.accountMovement, "alice", "USD", "accounts", (-5 : Int)⟩,
     ⟨.accountMovement, "bob", "USD", "accounts", (5 : Int)⟩,
     ⟨.feeAllocation, "bob", "USD", "accounts", (1 : Int)⟩] = _
  simp +decide [Proofs.CanonicalEpochEconomicRowsV1.sortOn, List.mergeSort,
    List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

def isOk {α : Type} : Except Reject α → Bool
  | .ok _ => true
  | .error _ => false

abbrev tracePlans : List EffectPlan := epochInputPlans [firstGlobal, secondGlobal]

theorem trace_checked_ok : isOk (checkedEpoch i128 tracePlans) = true := by
  simp only [tracePlans, checkedEpoch, epochInputPlans, List.map_cons, List.map_nil, orderedRows,
    first_rows, second_rows]
  decide

theorem trace_success : ∃ output, checkedEpoch i128 tracePlans = .ok output := by
  have ok := trace_checked_ok
  cases result : checkedEpoch i128 tracePlans with
  | ok output => exact ⟨output, rfl⟩
  | error reason => rw [result] at ok; cases ok
"""


TRACE_CONSUMERS = r"""
/-- The explicit input trace of the two actual accepted transfers, in command order. -/
theorem trace_one : EpochInputTrace firstTransfer.pre 1 [firstGlobal] (epochContinuedState firstGlobal) :=
  EpochInputTrace.snoc (source := firstTransfer.pre) (next := firstGlobal) EpochInputTrace.nil
    first_requirements first_accepted
theorem trace_two : EpochInputTrace firstTransfer.pre 2 [firstGlobal, secondGlobal]
    (epochContinuedState secondGlobal) :=
  EpochInputTrace.snoc (source := firstTransfer.pre) (next := secondGlobal) trace_one
    second_requirements second_accepted

example : EpochPrefix firstTransfer.pre 2 [firstOccurrence, secondOccurrence] (epochContinuedState secondGlobal) :=
  epochInputTrace_prefix trace_two
example : [firstGlobal, secondGlobal].length = 2 ∧ 2 ≤ maxEpochCommands := epochInputTrace_length trace_two
example : 1 ≤ [firstGlobal, secondGlobal].length ∧ [firstGlobal, secondGlobal].length ≤ maxEpochCommands ∧
    (epochContinuedState secondGlobal).economic.height = firstTransfer.pre.economic.height + 1 :=
  epochInputTrace_nonempty trace_two (by decide)
example : StateInvariant (epochContinuedState secondGlobal) := epochInputTrace_invariant first_invariant trace_two
theorem trace_chain : TableChain firstEconomic tracePlans (epochContinuedState secondGlobal).economic :=
  epochInputTrace_tableChain first_invariant trace_two
example : (tracePlans.map EffectPlan.occurrenceConsumptions).flatten =
    [firstOccurrence.occurrenceId, secondOccurrence.occurrenceId] :=
  epochInputTrace_consumptions first_invariant trace_two
example : EndpointKeysUnique firstEconomic (epochContinuedState secondGlobal).economic :=
  epochInputTrace_endpointKeysUnique first_invariant trace_two

theorem trace_prefix_fits : PrefixFits i128 empty (orderedRows tracePlans) :=
  (checkedEpoch_success_iff i128 tracePlans).mp trace_success

theorem trace_endpoints : ∃ output, checkedEpoch i128 tracePlans = .ok output ∧
    ∀ table owner asset domain,
      amountAt (tableRows table (epochContinuedState secondGlobal).economic) owner asset domain -
        amountAt (tableRows table firstEconomic) owner asset domain =
      output (encodeKey (tableKind table) owner asset domain) :=
  (epochInputTrace_checked_iff i128 first_invariant trace_two).mpr trace_prefix_fits

theorem trace_canonical : ∃ output, checkedEpoch i128 tracePlans = .ok output ∧
    CanonicalEffectRows (emitRows tracePlans output) ∧
    ∀ table, checkedStateDeltaRows table (tableRows table firstEconomic)
        (tableRows table (epochContinuedState secondGlobal).economic) =
      .ok (projectDeltaRows table (emitRows tracePlans output)) := by
  obtain ⟨output, accepted⟩ := trace_success
  have canonical := epochInputTrace_canonical_rows first_invariant trace_two output accepted
  exact ⟨output, accepted, canonical.1, canonical.2.2.2⟩

/-- Swapped history: no carried state admits the two inputs in the other order. -/
example : ¬ ∃ carried, EpochInputTrace firstTransfer.pre 2 [secondGlobal, firstGlobal] carried := by
  rintro ⟨carried, trace⟩
  obtain ⟨_, prior, swapped, _, _⟩ :=
    epochInputTrace_snoc_inv (inputs := [secondGlobal]) (next := firstGlobal) trace
  obtain ⟨_, base, zero, requirements, _⟩ :=
    epochInputTrace_snoc_inv (inputs := []) (next := secondGlobal) swapped
  obtain ⟨_, rfl⟩ := epochInputTrace_zero zero
  have heights : (epochContinuedState firstGlobal).economic.height = firstTransfer.pre.economic.height :=
    congrArg (fun state : Proofs.AssetTransferPolicySelectionV1.State => state.economic.height) requirements.pre
  rw [epochContinuedState_accepted first_accepted] at heights
  exact absurd heights (by decide)
"""


OBSERVERS = r"""
def observeTotals (keys : List Key) : Except Reject Totals → String
  | .ok totals => "OK:" ++ reprStr (keys.map totals)
  | .error .signedAggregationBounds => "ERR"
def observeRows : Except Reject (List EconomicEffectRow) → String
  | .error _ => "ERR"
  | .ok rows => "OK:" ++ reprStr (rows.map fun r =>
      [r.kind.code, r.principal, r.asset, r.custodyDomain, toString r.deltaAtoms])
def observeDeltas : Except Reject (List DeltaRow) → String
  | .error _ => "ERR"
  | .ok rows => "OK:" ++ reprStr (rows.map fun r =>
      [tableCode r.table, r.owner, r.asset, r.domain, toString r.delta])

def observeOrdered (rows : List Row) : String :=
  "OK:" ++ reprStr (rows.map fun row =>
    [(decodeKind row.key.kind).code, row.key.principal, row.key.asset, row.key.domain,
      toString row.delta])
"""


def test_input_plan_order_and_omission_mutants_change_observations_and_fail_theorems(
    lean: LeanSubject,
) -> None:
    """Observe defective definitions before requiring their ordinary law to fail."""
    pair = SharedHeightPair(height=7)
    fixture = lean.source / "MutationTransferPair.lean"
    fixture.write_text(f"import {NAMESPACE}\n{OPENS}\n" + _shared_height_body(pair) + OBSERVERS)
    built = _compile(lean, fixture, lean.library / "MutationTransferPair.olean")
    assert built.returncode == 0 and built.stdout == built.stderr == "", built.stdout + built.stderr
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    definition_prefix = source.split("theorem epochInputPlans_snoc", 1)[0]
    needle = "inputs.map fun input => (X.result input).plan"
    assert source.count(needle) == 1
    observed = []
    mutations = (
        ("Control", needle),
        ("Reversed", "inputs.reverse.map fun input => (X.result input).plan"),
        ("Omitted", "(inputs.drop 1).map fun input => (X.result input).plan"),
    )
    for name, replacement in mutations:
        namespace = f"InputPlans{name}V1"
        prefix = definition_prefix.replace(f"namespace {MODULE}", f"namespace {namespace}")
        prefix = prefix.replace(needle, replacement)
        path = lean.source / f"ObserveInputPlans{name}.lean"
        path.write_text(
            "import MutationTransferPair\n" + prefix + f"\nend {namespace}\nend Proofs\n" + OPENS
            + f"\n#eval observeOrdered (orderedRows (Proofs.{namespace}.epochInputPlans "
            "[firstGlobal, secondGlobal]))\n"
        )
        result = _compile(lean, path)
        assert result.returncode == 0 and result.stderr == "", result.stdout + result.stderr
        observed.append(_decode_observations(result.stdout)[0])
        if name == "Control":
            continue
        # Full proof failure must localize to the ordinary append-order theorem.
        mutated = source.replace(needle, replacement)
        full = lean.source / f"FullInputPlans{name}.lean"
        full.write_text(mutated)
        rejected = _compile(lean, full)
        assert rejected.returncode != 0 and "unsolved goals" in rejected.stdout
        first_error = re.search(r":(\d+):\d+: error:", rejected.stdout)
        assert first_error, rejected.stdout
        first_line = source[:source.index("theorem epochInputPlans_snoc")].count("\n") + 1
        last_line = source[:source.index("theorem epochInputOccurrences_snoc")].count("\n") + 1
        assert first_line <= int(first_error.group(1)) < last_line, rejected.stdout
    actual_plans = (_normalise(pair.first, pair.first_accepted), pair.second_effects)
    rows = [[[r.kind.value, r.principal, r.asset, r.custody_domain, str(r.delta_atoms)]
             for r in plan.rows] for plan in actual_plans]
    assert observed == [rows[0] + rows[1], rows[1] + rows[0], rows[1]]
    assert observed[0] != observed[1] and observed[0] != observed[2]
