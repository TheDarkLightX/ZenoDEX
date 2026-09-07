import Proofs.AssetTransferEpochStateClosureV1
import Proofs.CanonicalEpochEconomicRowsV1

/-!
# Checked and canonical epoch tables of a shared-height custody transfer trace

`AssetTransferEpochStateClosureV1.EpochPrefix` chains admitted accepted attempts by count,
occurrence list and carried state; it lives in `Prop` and carries no input or plan list.
`CheckedEpochEconomicTablesV1` composes an ordered plan list whose adjacent states satisfy
`ExactEconomicTables` (`TableChain`) and characterises the checked `i128` row fold by
`PrefixFits`; `CanonicalEpochEconomicRowsV1` emits the canonical four-table delta rows from a
successful fold and unique endpoint keys.

This file closes the seam between them with an input-indexed relation.  `EpochInputTrace`
keeps the explicit `List X.Input` in `Type` and admits each input with the existing
`EpochRequirements` and the actual accepted leaf verdict, appending at the end so that the
semantic order is visible:

```text
input[0], input[1], ...
  -> (X.result input[0]).plan, (X.result input[1]).plan, ...
  -> rows(plan[0]), rows(plan[1]), ...
```

`epochInputPlans` is definitionally the map of the actual custody-complete plans and
`epochInputOccurrences` the map of the occurrences, both in original command order.  No data is
eliminated from the old `Prop`-valued prefix and no plan list is chosen existentially.  The
trace-to-chain derivation assumes no desired post state, plan, table equation, table chain or
checked result.  Accepted-fold corollaries explicitly require the actual checked fold to succeed;
the central equivalence characterises that success by `PrefixFits`.

## What is proved

- a trace forgets to the old `EpochPrefix` on its occurrence map (one-way reuse), so the length
  bound `0..64`, the nonempty bound `1..64` with the shared target height and the carried
  `StateInvariant` are inherited rather than re-proved;
- the flattened per-plan occurrence consumptions are exactly the input occurrence identities in
  command order, from `SharedHeightVerified.occurrenceConsumptions`;
- `TableChain source.economic (epochInputPlans inputs) carried.economic`, by induction over the
  trace from the `economicTables` field of the existing shared-height obligations;
- the checked `checkedEpoch` fold succeeds with every four-table owner/asset/domain endpoint
  equation exactly when `PrefixFits` holds on the ordered plan rows, and a concrete successful
  `i128` fold yields every endpoint equation;
- `EndpointKeysUnique` of the source and carried states from `StateQuantitiesAdmitted`, which
  transports the `(asset, owner, domain)` no-duplicate keys to the canonical `(owner, asset,
  domain)` keys;
- the canonical four-table delta rows of the source/carried endpoint equal the projected emitted
  rows of the successful fold;
- the last input of a nonempty trace was admitted against its actual predecessor
  (`epochInputTrace_snoc_inv`); concrete reordered-history refusals are separate test witnesses.

## What is not proved

`PrefixFits` remains an explicit decision result: per-plan admission and representable endpoint
tables do not imply that every ordered signed prefix fits, and the existing checked model rejects
an overflowing intermediate prefix even when a later row cancels it.  The Python composer's final
tuple sorts its occurrence consumptions and rows; that normalised output has a different role
from the command order retained here.  Receipts, roots, authorisation, publication, the
single-occurrence mounted pipeline, the runtime dictionary or byte representation and any
Python/Rust refinement remain outside this file; Python correspondence is finite tested evidence.
-/

set_option warningAsError true

namespace Proofs
namespace AssetTransferEpochEconomicTablesV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open CheckedEconomicAggregationV1 CheckedEpochEconomicTablesV1 CanonicalEpochEconomicRowsV1
open AssetTransferEpochStateClosureV1

/-! ## Input-indexed accepted trace -/

/-- The actual custody-complete plans of an input list, in original command order. -/
def epochInputPlans (inputs : List X.Input) : List EffectPlan :=
  inputs.map fun input => (X.result input).plan

/-- The admitted occurrences of an input list, in original command order. -/
def epochInputOccurrences (inputs : List X.Input) : List G.CommandOccurrence :=
  inputs.map fun input => input.occurrence

/-- Ordered accepted attempts from a certified source with their inputs explicit.  Each input
is admitted against the carried state by the existing `EpochRequirements` at the position equal
to the number of earlier accepted attempts, accepted by the actual leaf verdict, and appended at
the end; the carried state is the actual continuation.  The relation stays in `Prop`; every
theorem below reads the explicit input list, never a proof. -/
inductive EpochInputTrace (source : K.State) : Nat → List X.Input → K.State → Prop
  | nil : EpochInputTrace source 0 [] source
  | snoc {count : Nat} {inputs : List X.Input} {carried : K.State} {next : X.Input}
      (trace : EpochInputTrace source count inputs carried)
      (requirements : EpochRequirements ⟨source.economic, count⟩ carried next)
      (accepted : (K.step next.transfer).verdict = .accepted) :
      EpochInputTrace source (count + 1) (inputs ++ [next]) (epochContinuedState next)

/-! ## Order of plans, occurrences and rows -/

theorem epochInputPlans_snoc (inputs : List X.Input) (next : X.Input) :
    epochInputPlans (inputs ++ [next]) = epochInputPlans inputs ++ [(X.result next).plan] := by
  simp only [epochInputPlans, List.map_append, List.map_cons, List.map_nil]

theorem epochInputOccurrences_snoc (inputs : List X.Input) (next : X.Input) :
    epochInputOccurrences (inputs ++ [next]) =
      epochInputOccurrences inputs ++ [next.occurrence] := by
  simp only [epochInputOccurrences, List.map_append, List.map_cons, List.map_nil]

theorem epochInputPlans_length (inputs : List X.Input) :
    (epochInputPlans inputs).length = inputs.length := by
  simp only [epochInputPlans, List.length_map]

/-- The checked row order: the rows of every earlier plan, then the rows of the appended plan. -/
theorem orderedRows_epochInputPlans_snoc (inputs : List X.Input) (next : X.Input) :
    orderedRows (epochInputPlans (inputs ++ [next])) =
      orderedRows (epochInputPlans inputs) ++ encodeRows (X.result next).plan.rows := by
  rw [epochInputPlans_snoc, orderedRows_append]
  simp only [orderedRows, List.append_nil]

/-! ## Forgetting to the retained prefix and inherited bounds -/

/-- One-way reuse bridge: a trace is an `EpochPrefix` on its occurrence map. -/
theorem epochInputTrace_prefix {source : K.State} {count : Nat} {inputs : List X.Input}
    {carried : K.State} (trace : EpochInputTrace source count inputs carried) :
    EpochPrefix source count (epochInputOccurrences inputs) carried := by
  induction trace with
  | nil => exact EpochPrefix.nil
  | snoc _ requirements accepted ih =>
      rw [epochInputOccurrences_snoc]
      exact EpochPrefix.cons ih requirements accepted

theorem epochInputTrace_length {source : K.State} {count : Nat} {inputs : List X.Input}
    {carried : K.State} (trace : EpochInputTrace source count inputs carried) :
    inputs.length = count ∧ count ≤ maxEpochCommands := by
  have bound := epochPrefix_length (epochInputTrace_prefix trace)
  simpa only [epochInputOccurrences, List.length_map] using bound

theorem epochInputTrace_invariant {source : K.State} {count : Nat} {inputs : List X.Input}
    {carried : K.State} (certified : Z.StateInvariant source)
    (trace : EpochInputTrace source count inputs carried) : Z.StateInvariant carried :=
  epochPrefix_invariant certified (epochInputTrace_prefix trace)

/-- A nonempty trace has between one and `maxEpochCommands` inputs and carries the shared
target height. -/
theorem epochInputTrace_nonempty {source : K.State} {count : Nat} {inputs : List X.Input}
    {carried : K.State} (trace : EpochInputTrace source count inputs carried)
    (nonempty : count ≠ 0) :
    1 ≤ inputs.length ∧ inputs.length ≤ maxEpochCommands ∧
      carried.economic.height = source.economic.height + 1 := by
  have length := epochInputTrace_length trace
  have bounds := epochPrefix_nonempty (epochInputTrace_prefix trace) nonempty
  exact ⟨by omega, by omega, bounds.2.2⟩

/-- Flattening the per-plan consumptions in plan order yields the input occurrence identities in
command order; each link is the existing shared-height consumption clause. -/
theorem epochInputTrace_consumptions {source : K.State} {count : Nat} {inputs : List X.Input}
    {carried : K.State} (certified : Z.StateInvariant source)
    (trace : EpochInputTrace source count inputs carried) :
    ((epochInputPlans inputs).map EffectPlan.occurrenceConsumptions).flatten =
      inputs.map fun input => input.occurrence.occurrenceId := by
  induction trace with
  | nil => rfl
  | snoc earlier requirements accepted ih =>
      have verified := epochContinuation_verified (epochInputTrace_invariant certified earlier)
        requirements accepted
      rw [epochInputPlans_snoc, List.map_append, List.flatten_append, ih, List.map_append]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, verified.occurrenceConsumptions]

/-! ## The actual table chain -/

/-- Every adjacent pair of carried states is linked by the exact four-table relation of the
actual completed plan, from the `economicTables` field of the existing shared-height
obligations.  No post state, plan, table equation or chain is assumed. -/
theorem epochInputTrace_tableChain {source : K.State} {count : Nat} {inputs : List X.Input}
    {carried : K.State} (certified : Z.StateInvariant source)
    (trace : EpochInputTrace source count inputs carried) :
    TableChain source.economic (epochInputPlans inputs) carried.economic := by
  induction trace with
  | nil => exact TableChain.nil _
  | @snoc _ _ carried next earlier requirements accepted ih =>
      have verified := epochContinuation_verified (epochInputTrace_invariant certified earlier)
        requirements accepted
      have preEq : X.pre next = carried.economic :=
        congrArg (fun state : K.State => state.economic) requirements.pre
      have link : G.ExactEconomicTables carried.economic (epochContinuedState next).economic
          (X.result next).plan := by
        rw [epochContinuedState_accepted accepted]
        show G.ExactEconomicTables carried.economic (epochSuccessor next) (X.result next).plan
        rw [← preEq]
        exact verified.economicTables
      rw [epochInputPlans_snoc]
      exact tableChain_append ih (TableChain.cons link (TableChain.nil _))

/-! ## Checked endpoint equations -/

/-- Checked composition with every four-table endpoint equation exists exactly when every
ordered row prefix fits; `PrefixFits` is the explicit decision result. -/
theorem epochInputTrace_checked_iff (bounds : Bounds) {source : K.State} {count : Nat}
    {inputs : List X.Input} {carried : K.State} (certified : Z.StateInvariant source)
    (trace : EpochInputTrace source count inputs carried) :
    (∃ output, checkedEpoch bounds (epochInputPlans inputs) = .ok output ∧
      ∀ table owner asset domain,
        amountAt (tableRows table carried.economic) owner asset domain -
            amountAt (tableRows table source.economic) owner asset domain =
          output (encodeKey (tableKind table) owner asset domain)) ↔
      PrefixFits bounds empty (orderedRows (epochInputPlans inputs)) :=
  checked_epoch_table_composition_iff bounds (epochInputTrace_tableChain certified trace)

/-- A concrete successful `i128` fold gives every owner/asset/domain endpoint equation of all
four tables. -/
theorem epochInputTrace_exact_tables {source : K.State} {count : Nat} {inputs : List X.Input}
    {carried : K.State} (certified : Z.StateInvariant source)
    (trace : EpochInputTrace source count inputs carried) (output : Totals)
    (accepted : checkedEpoch i128 (epochInputPlans inputs) = .ok output) (table : Table)
    (owner : Principal) (asset : Asset) (domain : AccountingLocation) :
    amountAt (tableRows table carried.economic) owner asset domain -
        amountAt (tableRows table source.economic) owner asset domain =
      output (encodeKey (tableKind table) owner asset domain) :=
  successful_epoch_exact_tables i128 output (epochInputTrace_tableChain certified trace) accepted
    table owner asset domain

/-! ## Endpoint keys from state admission -/

/-- Unique admitted `(asset, owner, domain)` keys give unique canonical
`(owner, asset, domain)` keys by the coordinate permutation. -/
theorem amountKey_nodup_of_permuted (rows : List AmountRow)
    (unique : (rows.map fun row => (row.asset, row.owner, row.custodyDomain)).Nodup) :
    (rows.map amountKey).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.pairwise_map.mp unique).imp
  intro a b different same
  apply different
  simp only [amountKey, Prod.mk.injEq] at same
  simp only [Prod.mk.injEq]
  exact ⟨same.2.1, same.1, same.2.2⟩

theorem endpointKeysUnique_of_admitted {pre post : G.GlobalState}
    (preAdmitted : G.StateQuantitiesAdmitted pre) (postAdmitted : G.StateQuantitiesAdmitted post) :
    EndpointKeysUnique pre post := by
  obtain ⟨_, _, _, _, _, _, _, preBalances, preCustody, preLiabilities, preReserves, _⟩ :=
    preAdmitted
  obtain ⟨_, _, _, _, _, _, _, postBalances, postCustody, postLiabilities, postReserves, _⟩ :=
    postAdmitted
  intro table
  cases table with
  | balances =>
      exact ⟨amountKey_nodup_of_permuted _ preBalances, amountKey_nodup_of_permuted _ postBalances⟩
  | custody =>
      exact ⟨amountKey_nodup_of_permuted _ preCustody, amountKey_nodup_of_permuted _ postCustody⟩
  | liabilities =>
      exact ⟨amountKey_nodup_of_permuted _ preLiabilities,
        amountKey_nodup_of_permuted _ postLiabilities⟩
  | reserves =>
      exact ⟨amountKey_nodup_of_permuted _ preReserves, amountKey_nodup_of_permuted _ postReserves⟩

theorem epochInputTrace_quantities {source : K.State} {count : Nat} {inputs : List X.Input}
    {carried : K.State} (certified : Z.StateInvariant source)
    (trace : EpochInputTrace source count inputs carried) :
    G.StateQuantitiesAdmitted source.economic ∧ G.StateQuantitiesAdmitted carried.economic :=
  ⟨certified.quantities, (epochInputTrace_invariant certified trace).quantities⟩

theorem epochInputTrace_endpointKeysUnique {source : K.State} {count : Nat}
    {inputs : List X.Input} {carried : K.State} (certified : Z.StateInvariant source)
    (trace : EpochInputTrace source count inputs carried) :
    EndpointKeysUnique source.economic carried.economic :=
  endpointKeysUnique_of_admitted (epochInputTrace_quantities certified trace).1
    (epochInputTrace_quantities certified trace).2

/-! ## Canonical four-table delta rows -/

/-- With the derived chain, the derived endpoint-key uniqueness and a successful `i128` fold,
each checked endpoint delta tuple of the four tables equals the projected emitted rows, which are
nonzero, bounded and canonically ordered. -/
theorem epochInputTrace_canonical_rows {source : K.State} {count : Nat} {inputs : List X.Input}
    {carried : K.State} (certified : Z.StateInvariant source)
    (trace : EpochInputTrace source count inputs carried) (output : Totals)
    (accepted : checkedEpoch i128 (epochInputPlans inputs) = .ok output) :
    CanonicalEffectRows (emitRows (epochInputPlans inputs) output) ∧
    (∀ row ∈ emitRows (epochInputPlans inputs) output, Fits i128 row.deltaAtoms) ∧
    (∀ key, keyedSum key (encodeRows (emitRows (epochInputPlans inputs) output)) = output key) ∧
    ∀ table, checkedStateDeltaRows table (tableRows table source.economic)
        (tableRows table carried.economic) =
      .ok (projectDeltaRows table (emitRows (epochInputPlans inputs) output)) :=
  checked_epoch_canonical_amount_delta_rows output (epochInputTrace_tableChain certified trace)
    (epochInputTrace_endpointKeysUnique certified trace) accepted

/-! ## Inversion: every input was admitted against its actual predecessor -/

theorem epochInputTrace_zero {source : K.State} {inputs : List X.Input} {carried : K.State}
    (trace : EpochInputTrace source 0 inputs carried) : inputs = [] ∧ carried = source := by
  generalize countEq : 0 = total at trace
  cases trace with
  | nil => exact ⟨rfl, rfl⟩
  | snoc => exact absurd countEq.symm (Nat.succ_ne_zero _)

/-- The last input of a nonempty trace is the last accepted step, admitted at the position of
the earlier inputs against the state those inputs carry. -/
theorem epochInputTrace_snoc_inv {source : K.State} {count : Nat} {inputs : List X.Input}
    {next : X.Input} {carried : K.State}
    (trace : EpochInputTrace source (count + 1) (inputs ++ [next]) carried) :
    carried = epochContinuedState next ∧
      ∃ prior, EpochInputTrace source count inputs prior ∧
        EpochRequirements ⟨source.economic, count⟩ prior next ∧
        (K.step next.transfer).verdict = .accepted := by
  generalize countEq : count + 1 = total at trace
  generalize listEq : inputs ++ [next] = list at trace
  cases trace with
  | nil => exact absurd countEq (Nat.succ_ne_zero _)
  | snoc earlier requirements accepted =>
      obtain rfl := Nat.add_right_cancel countEq
      obtain ⟨rfl, nextEq⟩ := List.append_inj' listEq rfl
      obtain ⟨rfl, _⟩ := List.cons.inj nextEq
      exact ⟨rfl, _, earlier, requirements, accepted⟩

end AssetTransferEpochEconomicTablesV1
end Proofs
