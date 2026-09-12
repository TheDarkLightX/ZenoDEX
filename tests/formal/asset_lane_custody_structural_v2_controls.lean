set_option warningAsError true
attribute [local instance] lexOrd
namespace CustodyStructuralControls
open Proofs.AssetLaneCustodyRefinementV2
namespace B
export Proofs.AssetLaneCustodyRefinementV2.Controls (pre legal_custody_state_representable)
end B
namespace E
export Proofs.AssetLaneCustodyEffectPlanV2 (transferSource managedSource)
end E
namespace FM
export Proofs.ManagedAssetFiniteOutcomeV2 (Structural)
end FM

/-- The older row invariant intentionally omits managed-policy uniqueness. -/
def duplicateManaged : State :=
  { B.pre with managedPolicies := B.pre.managedPolicies ++ B.pre.managedPolicies }

theorem duplicate_managed_rows : RowsRepresentable duplicateManaged := by
  have h := B.legal_custody_state_representable
  refine ⟨h.supplyUnique, h.supplyOrdered, h.supplyBounded, h.registryKeys,
    h.policyKeys, ?_, h.balanceUnique, h.balancePositive, h.custodyUnique,
    h.custodyShape, h.holdingsCovered, h.balanced⟩
  intro policy member
  rcases List.mem_append.mp member with member | member
  all_goals exact h.managedCovered policy member

theorem duplicate_managed_not_leaf_structural :
    ¬ FM.Structural (E.managedSource duplicateManaged) := by
  intro admitted
  have impossible : (["ORD", "ORD"] : List String).Nodup := admitted.policyUnique
  simp at impossible

/-- Physical accounting alone does not imply canonical balance order. -/
def unorderedBalances : State :=
  { B.pre with transferState := { B.pre.transferState with
    balances := [⟨"alice", "ORD", "accounts", 100⟩,
      ⟨"dave", "EUR", "accounts", 7⟩, ⟨"bob", "ORD", "accounts", 15⟩] } }

theorem unordered_balances_rows : RowsRepresentable unorderedBalances := by
  have h := B.legal_custody_state_representable
  refine ⟨h.supplyUnique, h.supplyOrdered, h.supplyBounded, h.registryKeys,
    h.policyKeys, h.managedCovered, ?_, ?_, h.custodyUnique,
    h.custodyShape, ?_, ?_⟩
  · unfold Proofs.AssetTransferSparseTablesV1.Unique; decide
  · simp [Proofs.AssetTransferSparseTablesV1.PositiveAccounts, unorderedBalances,
      Proofs.AssetTransferSparseTablesV1.accounts,
      Proofs.AssetTransferRefinementV1.IsU128, Proofs.AssetTransferRefinementV1.u128Max]
  · decide
  · intro asset
    by_cases ordinary : asset = "ORD"
    · subst asset; decide
    · by_cases euro : asset = "EUR"
      · subst asset; decide
      · simp [physicalFor, supplyAt, unorderedBalances, B.pre,
          Proofs.GlobalEconomicStateRefinementV2.amountForAsset,
          Proofs.RegisteredSupplySupportV1.numericRows,
          Proofs.RegisteredSupplySupportV1.nonzeroRow,
          Proofs.RegisteredSupplySupportV1.toNumericRow,
          Proofs.GlobalEconomicStateRefinementV2.supplyFor,
          Ne.symm ordinary, Ne.symm euro]

theorem unordered_balances_not_leaf_structural :
    ¬ Proofs.AssetTransferFiniteOutcomeV2.Structural (E.transferSource unorderedBalances) := by
  intro admitted
  have impossible := admitted.balanceOrdered
  have absent : ¬ (E.transferSource unorderedBalances).balances.Pairwise
      (fun l r => compare (Proofs.AssetTransferSparseTablesV1.balanceWire l)
        (Proofs.AssetTransferSparseTablesV1.balanceWire r) = .lt) := by decide
  exact absent impossible
end CustodyStructuralControls

namespace StructuralControls
namespace X
export Proofs.AssetLaneCustodyStructuralV2 (CompleteStructural ActionAdmission
  transfer_source_structural managed_source_structural every_prefix_complete_and_sources)
end X

local instance token_decidable (value : String) :
    Decidable (Proofs.AssetLaneFiniteByteAccountingV2.ValidToken value) := by
  unfold Proofs.AssetLaneFiniteByteAccountingV2.ValidToken
  infer_instance

theorem initial_complete : X.CompleteStructural B.pre := by
  refine {
    rows := Proofs.AssetLaneCustodyRefinementV2.Controls.legal_custody_state_representable
    policyShape := FiniteControls.static_policies
    managedPolicyOrdered := by decide
    balanceOrdered := by decide
    transferFeeOwnerTokens := ?_
    balanceTokens := ?_
    supplyTokens := ?_ }
  · intro policy member
    simp only [B.pre, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals decide
  · intro row member
    simp only [B.pre, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals decide
  · intro row member
    simp only [B.pre, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals decide

theorem initial_transfer_structure :
    Proofs.AssetTransferFiniteOutcomeV2.Structural
      (Proofs.AssetLaneCustodyEffectPlanV2.transferSource B.pre) :=
  X.transfer_source_structural initial_complete

theorem initial_managed_structure :
    Proofs.ManagedAssetFiniteOutcomeV2.Structural
      (Proofs.AssetLaneCustodyEffectPlanV2.managedSource B.pre) :=
  X.managed_source_structural initial_complete

theorem inputs_admitted :
    ∀ action ∈ FiniteControls.actions, X.ActionAdmission action := by
  intro action member
  simp only [FiniteControls.actions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [X.ActionAdmission, Proofs.AssetTransferFiniteOutcomeV2.CommandAdmission]
  all_goals repeat' constructor
  all_goals decide

theorem each_reached_leaf_has_structure (length : Nat) :
    let state := Proofs.AssetLaneCustodyFiniteTraceV2.run FiniteControls.digest B.pre
      (FiniteControls.actions.take length)
    X.CompleteStructural state ∧
      Proofs.AssetTransferFiniteOutcomeV2.Structural
        (Proofs.AssetLaneCustodyEffectPlanV2.transferSource state) ∧
      Proofs.ManagedAssetFiniteOutcomeV2.Structural
        (Proofs.AssetLaneCustodyEffectPlanV2.managedSource state) :=
  X.every_prefix_complete_and_sources FiniteControls.digest FiniteControls.actions
    initial_complete inputs_admitted length

-- The final state is the independently listed complete table, not only a scalar total.
theorem final_complete : X.CompleteStructural afterBurn := by
  have result := (each_reached_leaf_has_structure FiniteControls.actions.length).1
  simpa only [List.take_length, FiniteControls.exact_history] using result

/-- A dormant managed sibling surrounds an unmanaged asset in complete key order. -/
def twoManaged : State :=
  { B.pre with managedPolicies :=
      [{ Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy with asset := "AUD" },
        Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy] }

theorem two_managed_rows : RowsRepresentable twoManaged := by
  have h := initial_complete.rows
  exact ⟨h.supplyUnique, h.supplyOrdered, h.supplyBounded, h.registryKeys,
    h.policyKeys, by decide, h.balanceUnique, h.balancePositive, h.custodyUnique,
    h.custodyShape, h.holdingsCovered, h.balanced⟩

theorem two_managed_complete : X.CompleteStructural twoManaged := by
  refine {
    rows := two_managed_rows
    policyShape := ?_
    managedPolicyOrdered := by decide
    balanceOrdered := initial_complete.balanceOrdered
    transferFeeOwnerTokens := initial_complete.transferFeeOwnerTokens
    balanceTokens := initial_complete.balanceTokens
    supplyTokens := initial_complete.supplyTokens }
  constructor
  · exact FiniteControls.static_policies.1
  · intro policy member
    simp only [twoManaged, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals exact ⟨rfl, fun excluded => False.elim (excluded rfl)⟩

theorem managed_sibling_keys_and_rows_are_exact :
    (Proofs.AssetLaneCustodyEffectPlanV2.managedSource twoManaged).policies.map
        (fun policy => policy.asset) = ["AUD", "ORD"] ∧
      (Proofs.AssetLaneCustodyEffectPlanV2.managedSource twoManaged).supplies =
        [⟨"AUD", 0⟩, ⟨"ORD", 120⟩] ∧
      (Proofs.AssetLaneCustodyEffectPlanV2.managedSource twoManaged).balances =
        [⟨"alice", "ORD", "accounts", 100⟩, ⟨"bob", "ORD", "accounts", 15⟩] := by decide

theorem managed_siblings_structural :
    Proofs.ManagedAssetFiniteOutcomeV2.Structural
      (Proofs.AssetLaneCustodyEffectPlanV2.managedSource twoManaged) :=
  X.managed_source_structural two_managed_complete

def emptyRecipient := { B.transfer with recipient := "" }

theorem shape_alone_does_not_admit_empty_recipient :
    Proofs.AssetLaneCustodyFiniteTraceV2.CommandShape
      (.transfer (T.baseContext "alice") emptyRecipient) ∧
    ¬ X.ActionAdmission (.transfer (T.baseContext "alice") emptyRecipient) := by
  constructor
  · constructor <;> decide
  · intro admitted
    have emptyToken := admitted.2.2
    have impossible : ¬ Proofs.AssetLaneFiniteByteAccountingV2.ValidToken "" := by decide
    exact impossible emptyToken
end StructuralControls

namespace PrefixEffectConsumers
open Proofs
open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
namespace X
export AssetLaneCustodyStructuralV2 (CompleteStructural ActionAdmission
  every_prefix_complete_and_sources)
end X
namespace F
export AssetLaneCustodyFiniteTraceV2 (Action run transfer_accepted_actual_post
  managed_accepted_actual_post)
end F
namespace E
export AssetLaneCustodyEffectPlanV2 (transferSource managedSource transferEffectPlan
  managedEffectPlan transfer_accepted_plan_admitted managed_accepted_plan_admitted)
end E

/-- A reached prefix supplies the complete source premises for transfer plan completion. -/
theorem transfer_completion_at_prefix
    (digest : AssetLaneFiniteByteAccountingV2.Bytes → String) (actions : List F.Action)
    (length : Nat) {pre : AssetLaneCustodyRefinementV2.State}
    (initial : X.CompleteStructural pre)
    (inputs : ∀ action ∈ actions, X.ActionAdmission action)
    (roots : AssetTransferRefinementV2.RootModel)
    (ctx : AssetTransferRefinementV2.Context) (cmd : AssetTransferRefinementV2.Command)
    (preRoot postRoot : RootId)
    (accepted : (AssetTransferFiniteOutcomeV2.transition digest ctx
      (E.transferSource (F.run digest pre (actions.take length))) cmd).verdict = .accepted) :
    EffectPlanAdmitted (E.transferEffectPlan digest ctx
      (F.run digest pre (actions.take length)) cmd preRoot postRoot) := by
  have reached := X.every_prefix_complete_and_sources digest actions initial inputs length
  obtain ⟨_, selected, _, _, _⟩ := F.transfer_accepted_actual_post accepted
  exact E.transfer_accepted_plan_admitted roots reached.1.rows reached.2.1 selected accepted

/-- The same initial-only bridge supplies complete managed plan completion. -/
theorem managed_completion_at_prefix
    (digest : AssetLaneFiniteByteAccountingV2.Bytes → String) (actions : List F.Action)
    (length : Nat) {pre : AssetLaneCustodyRefinementV2.State}
    (initial : X.CompleteStructural pre)
    (inputs : ∀ action ∈ actions, X.ActionAdmission action)
    (ctx : ManagedAssetLifecycleRefinementV2.Context) (cmd : ManagedAssetLifecycleRefinementV2.Command)
    (commandAdmitted : X.ActionAdmission (.managed ctx cmd)) (preRoot postRoot : RootId)
    (accepted : (ManagedAssetFiniteOutcomeV2.transition digest ctx
      (E.managedSource (F.run digest pre (actions.take length))) cmd).verdict = .accepted) :
    EffectPlanAdmitted (E.managedEffectPlan digest ctx
      (F.run digest pre (actions.take length)) cmd preRoot postRoot) := by
  have reached := X.every_prefix_complete_and_sources digest actions initial inputs length
  obtain ⟨_, selected, _, _, _, _⟩ := F.managed_accepted_actual_post reached.1.rows accepted
  exact E.managed_accepted_plan_admitted reached.1.rows reached.2.2
    commandAdmitted.1 commandAdmitted.2 selected accepted

#print axioms transfer_completion_at_prefix
#print axioms managed_completion_at_prefix
end PrefixEffectConsumers
