import Proofs.AssetTransferSparseStateAdmissionV1
import Proofs.AssetTransferSparseAuthorizationV1

/-!
# Multi-asset ASSET_TRANSFER V1 policy selection

This bounded constructor-premise model adds the runtime's pre-state first-match
policy lookup around the existing sparse selected-policy transition.  A state
retains its module release, policy rows, and global economic rows; only the
economic balance table can change through the existing sparse step.

`StateAdmitted` models the quantitative parts of the Python state constructor:
canonical account rows, policy/supply key uniqueness and order, row ceilings,
u128 fees and supplies, equal policy/supply asset lists, and all-asset account
coverage.  Supply rows may carry zero atoms, matching the local runtime
constructor.  It deliberately omits token/root syntax, exact Python classes,
hashing, the other context coordinates, authentication, journals, receipts,
publication, and a Python/Rust/compiler refinement claim.  It is an input
constructor premise and is never supplied as a postcondition.
-/

set_option warningAsError true

namespace Proofs
namespace AssetTransferPolicySelectionV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open CheckedEconomicAggregationV1 CheckedEpochEconomicTablesV1

namespace S
export Proofs.AssetTransferSparseTablesV1 (Input Result step localState
  CanonicalBalances PositiveAccounts Unique accepted_sparse_transfer
  rejected_step_noop step_frame accounts accountKey)
end S

namespace P
export Proofs.AssetTransferSparseSupplyV1 (accepted_account_totals)
end P

namespace A
export Proofs.AssetTransferSparseStateAdmissionV1
  (step_preserves_state_quantities_admitted
   step_preserves_owned_supply_and_claimant_liabilities_backed)
end A

namespace Z
export Proofs.AssetTransferSparseAuthorizationV1 (accepted_decrease_authorized)
end Z

namespace T
export Proofs.AssetTransferRefinementV1 (Context Policy Command Verdict RejectCode
  TransferState StateWellFormed CommandWellFormed IsU128 assetTransferCommandKind)
end T

namespace G
export Proofs.GlobalEconomicStateRefinementV2 (GlobalState AmountRow SupplyRow
  amountForAsset supplyFor StateQuantitiesAdmitted OwnedMatchesSupply
  ClaimantLiabilitiesBacked)
end G

namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (AmountKey amountKey lookupLast)
end C

attribute [local instance] lexOrd

def maxPolicyRows : Nat := 256

def policyKey (policy : T.Policy) : String := policy.asset
def supplyKey (supply : G.SupplyRow) : String := supply.asset

def PoliciesAdmitted (policies : List T.Policy) : Prop :=
  (policies.map policyKey).Nodup ∧
  policies.Pairwise (fun left right => compare (policyKey left) (policyKey right) = .lt) ∧
  policies.length ≤ maxPolicyRows ∧
  ∀ policy ∈ policies, T.IsU128 policy.transferFeeAtoms

def SuppliesAdmitted (supplies : List G.SupplyRow) : Prop :=
  (supplies.map supplyKey).Nodup ∧
  supplies.Pairwise (fun left right => compare (supplyKey left) (supplyKey right) = .lt) ∧
  supplies.length ≤ maxPolicyRows ∧
  ∀ supply ∈ supplies, T.IsU128 supply.amountAtoms

structure State where
  moduleReleaseId : String
  policies : List T.Policy
  economic : G.GlobalState

structure Input where
  context : T.Context
  command : T.Command
  pre : State

structure Result where
  verdict : T.Verdict
  post : State
  plan : EffectPlan

/-- First matching policy row, as in `_policy_for`. -/
def policyFor (policies : List T.Policy) (asset : String) : Option T.Policy :=
  policies.find? fun policy => policy.asset == asset

def selectedInput (input : Input) (policy : T.Policy) : S.Input :=
  ⟨input.context, input.pre.moduleReleaseId, policy, input.command, input.pre.economic⟩

def reject (input : Input) (code : T.RejectCode) : Result :=
  ⟨.rejected code, input.pre, EffectPlan.empty⟩

def lift (input : Input) (result : S.Result) : Result :=
  ⟨result.verdict, ⟨input.pre.moduleReleaseId, input.pre.policies, result.post⟩, result.plan⟩

/-- The front door fixes the runtime order before invoking the selected leaf. -/
def step (input : Input) : Result :=
  if input.context.moduleReleaseId ≠ input.pre.moduleReleaseId then
    reject input .releaseMismatch
  else if input.command.commandKind ≠ T.assetTransferCommandKind then
    reject input .unknownCommand
  else match policyFor input.pre.policies input.command.asset with
    | none => reject input .unknownAsset
    | some policy => lift input (S.step (selectedInput input policy))

abbrev Request := Proofs.AssetTransferSparseTraceV1.Request

def inputFor (request : Request) (pre : State) : Input :=
  ⟨request.context, request.command, pre⟩

structure History where
  post : State
  acceptedPlans : List EffectPlan

/-- Each request selects from the current pre-state policy rows. -/
def run : List Request → State → History
  | [], pre => ⟨pre, []⟩
  | request :: requests, pre =>
      let next := step (inputFor request pre)
      match next.verdict with
      | .rejected _ => run requests pre
      | .accepted =>
          let tail := run requests next.post
          ⟨tail.post, next.plan :: tail.acceptedPlans⟩

/-- Quantitative constructor premises for the modelled state fields. -/
def StateAdmitted (state : State) : Prop :=
  S.CanonicalBalances state.economic.balances ∧
  PoliciesAdmitted state.policies ∧
  SuppliesAdmitted state.economic.supplies ∧
  state.policies.map policyKey = state.economic.supplies.map supplyKey ∧
  ∀ asset, G.amountForAsset state.economic.balances asset ≤
    G.supplyFor state.economic.supplies asset

theorem policyFor_some {policies : List T.Policy} {asset : String} {policy : T.Policy}
    (selected : policyFor policies asset = some policy) :
    policy ∈ policies ∧ policy.asset = asset := by
  change policies.find? (fun candidate => candidate.asset == asset) = some policy at selected
  refine ⟨List.mem_of_find?_eq_some selected, ?_⟩
  simpa using List.find?_some selected

theorem policyFor_none_iff (policies : List T.Policy) (asset : String) :
    policyFor policies asset = none ↔ ∀ policy ∈ policies, policy.asset ≠ asset := by
  change policies.find? (fun policy => policy.asset == asset) = none ↔ _
  simp

theorem policyFor_none_of_no_selection {policies : List T.Policy} {asset : String}
    (missing : ¬ ∃ policy, policyFor policies asset = some policy) :
    policyFor policies asset = none := by
  cases choice : policyFor policies asset with
  | none => rfl
  | some policy => exact False.elim (missing ⟨policy, choice⟩)

theorem policy_asset_unique {policies : List T.Policy} {left right : T.Policy}
    (keys : (policies.map policyKey).Nodup) (leftMember : left ∈ policies)
    (rightMember : right ∈ policies) (sameAsset : left.asset = right.asset) : left = right := by
  induction policies generalizing left right with
  | nil => simp at leftMember
  | cons head tail ih =>
      have parts := List.nodup_cons.mp keys
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with leftHead | leftTail
      · subst left
        rcases rightMember with rightHead | rightTail
        · exact rightHead.symm
        · exfalso
          apply parts.1
          exact List.mem_map.mpr ⟨right, rightTail, by simpa [policyKey] using sameAsset.symm⟩
      · rcases rightMember with rightHead | rightTail
        · subst right
          exfalso
          apply parts.1
          exact List.mem_map.mpr ⟨left, leftTail, by simpa [policyKey] using sameAsset⟩
        · exact ih parts.2 leftTail rightTail sameAsset

/-- Unique policy keys make the selected row the only member for its asset. -/
theorem policyFor_unique {policies : List T.Policy} {asset : String}
    {selected candidate : T.Policy} (admitted : PoliciesAdmitted policies)
    (selection : policyFor policies asset = some selected)
    (candidateMember : candidate ∈ policies) (candidateAsset : candidate.asset = asset) :
    selected = candidate := by
  exact policy_asset_unique admitted.1 (policyFor_some selection).1 candidateMember
    ((policyFor_some selection).2.trans candidateAsset.symm)

theorem supplyFor_zero_of_absent (supplies : List G.SupplyRow) (asset : String)
    (absent : ∀ supply ∈ supplies, supply.asset ≠ asset) :
    G.supplyFor supplies asset = 0 := by
  induction supplies with
  | nil => rfl
  | cons supply supplies ih =>
      change (if supply.asset = asset then supply.amountAtoms else 0) +
        G.supplyFor supplies asset = 0
      rw [if_neg (absent supply (by simp))]
      simpa using ih (fun next member => absent next (by simp [member]))

theorem amountForAsset_nonnegative (rows : List G.AmountRow)
    (bounded : ∀ row ∈ rows, T.IsU128 row.amountAtoms) (asset : String) :
    0 ≤ G.amountForAsset rows asset := by
  induction rows with
  | nil =>
      simp only [G.amountForAsset, List.map_nil, List.sum_nil]
      omega
  | cons row rows ih =>
      change 0 ≤ (if row.asset = asset then row.amountAtoms else 0) +
        G.amountForAsset rows asset
      have rowBound := bounded row (by simp)
      unfold T.IsU128 at rowBound
      have tailBound := ih (fun next member => bounded next (by simp [member]))
      split <;> omega

theorem amountForAsset_positive_of_member {rows : List G.AmountRow} {row : G.AmountRow}
    (positive : ∀ candidate ∈ rows,
      T.IsU128 candidate.amountAtoms ∧ candidate.amountAtoms ≠ 0)
    (member : row ∈ rows) : 0 < G.amountForAsset rows row.asset := by
  induction rows with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with same | member
      · subst row
        simp only [G.amountForAsset, List.map_cons, List.sum_cons]
        have headPositive : 0 < head.amountAtoms := by
          have bounds := (positive head (by simp)).1
          unfold T.IsU128 at bounds
          have nonzero := (positive head (by simp)).2
          omega
        have tailNonnegative := amountForAsset_nonnegative tail
          (fun candidate candidateMember => (positive candidate (by simp [candidateMember])).1)
          head.asset
        change 0 ≤ (tail.map fun candidate =>
          if candidate.asset = head.asset then candidate.amountAtoms else 0).sum at tailNonnegative
        exact Int.add_pos_of_pos_of_nonneg headPositive tailNonnegative
      · simp only [G.amountForAsset, List.map_cons, List.sum_cons]
        have headBounds := (positive head (by simp)).1
        unfold T.IsU128 at headBounds
        have headNonnegative : 0 ≤ head.amountAtoms := headBounds.1
        have tailPositive := ih
          (fun candidate candidateMember => positive candidate (by simp [candidateMember])) member
        change 0 < (tail.map fun candidate =>
          if candidate.asset = row.asset then candidate.amountAtoms else 0).sum at tailPositive
        split <;> omega

/-- All-asset coverage and positive sparse rows rule out unknown balance assets. -/
theorem admitted_balance_asset_has_policy {state : State} (admitted : StateAdmitted state)
    {row : G.AmountRow} (member : row ∈ state.economic.balances) :
    ∃ policy ∈ state.policies, policy.asset = row.asset := by
  rcases admitted with ⟨canonical, policies, supplies, equalAssets, coverage⟩
  classical
  apply Classical.byContradiction
  intro noPolicy
  have noPolicyRow : ∀ policy ∈ state.policies, policy.asset ≠ row.asset := by
    intro policy policyMember same
    exact noPolicy ⟨policy, policyMember, same⟩
  have policyAbsent : row.asset ∉ state.policies.map policyKey := by
    intro member
    obtain ⟨policy, policyMember, same⟩ := List.mem_map.mp member
    exact noPolicyRow policy policyMember (by simpa [policyKey] using same)
  have supplyAbsent : row.asset ∉ state.economic.supplies.map supplyKey := by
    rw [← equalAssets]
    exact policyAbsent
  have noSupplyRow : ∀ supply ∈ state.economic.supplies, supply.asset ≠ row.asset := by
    intro supply supplyMember same
    apply supplyAbsent
    exact List.mem_map.mpr ⟨supply, supplyMember, by simpa [supplyKey] using same⟩
  have balancePositive := amountForAsset_positive_of_member
    (fun candidate candidateMember => (canonical.2.1 candidate candidateMember).2) member
  have supplyZero := supplyFor_zero_of_absent state.economic.supplies row.asset noSupplyRow
  have covered := coverage row.asset
  rw [supplyZero] at covered
  omega

theorem amountForAsset_zero_of_absent (rows : List G.AmountRow) (asset : String)
    (absent : ∀ row ∈ rows, row.asset ≠ asset) :
    G.amountForAsset rows asset = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change (if row.asset = asset then row.amountAtoms else 0) +
        G.amountForAsset rows asset = 0
      rw [if_neg (absent row (by simp))]
      simpa using ih (fun next member => absent next (by simp [member]))

theorem supplyFor_nonnegative (supplies : List G.SupplyRow)
    (bounded : ∀ supply ∈ supplies, T.IsU128 supply.amountAtoms) (asset : String) :
    0 ≤ G.supplyFor supplies asset := by
  induction supplies with
  | nil =>
      simp only [G.supplyFor, List.map_nil, List.sum_nil]
      omega
  | cons supply supplies ih =>
      change 0 ≤ (if supply.asset = asset then supply.amountAtoms else 0) +
        G.supplyFor supplies asset
      have supplyBound := bounded supply (by simp)
      unfold T.IsU128 at supplyBound
      have tailBound := ih (fun next member => bounded next (by simp [member]))
      split <;> omega

theorem supplyFor_eq_member_amount {supplies : List G.SupplyRow} {supply : G.SupplyRow}
    (unique : (supplies.map supplyKey).Nodup) (member : supply ∈ supplies) :
    G.supplyFor supplies supply.asset = supply.amountAtoms := by
  induction supplies generalizing supply with
  | nil => simp at member
  | cons head tail ih =>
      have parts := List.nodup_cons.mp unique
      simp only [List.mem_cons] at member
      rcases member with same | member
      · subst supply
        have tailAbsent : ∀ supply ∈ tail, supply.asset ≠ head.asset := by
          intro supply supplyMember sameAsset
          apply parts.1
          exact List.mem_map.mpr ⟨supply, supplyMember,
            by simpa [supplyKey] using sameAsset⟩
        have tailZero := supplyFor_zero_of_absent tail head.asset tailAbsent
        change (if head.asset = head.asset then head.amountAtoms else 0) +
          G.supplyFor tail head.asset = head.amountAtoms
        rw [if_pos rfl, tailZero]
        omega
      · have headDifferent : head.asset ≠ supply.asset := by
          intro sameAsset
          apply parts.1
          exact List.mem_map.mpr ⟨supply, member,
            by simpa [supplyKey] using sameAsset.symm⟩
        change (if head.asset = supply.asset then head.amountAtoms else 0) +
          G.supplyFor tail supply.asset = supply.amountAtoms
        rw [if_neg headDifferent]
        simpa using ih parts.2 member

/-- The all-asset inequality is equivalent to the two local constructor clauses.
Zero supply rows remain admissible because their u128 lower bound supplies the
empty-balance direction. -/
theorem all_asset_coverage_iff_runtime_clauses {balances : List G.AmountRow}
    {supplies : List G.SupplyRow} (positive : S.PositiveAccounts balances)
    (supplyKeys : (supplies.map supplyKey).Nodup)
    (supplyBounds : ∀ supply ∈ supplies, T.IsU128 supply.amountAtoms) :
    (∀ asset, G.amountForAsset balances asset ≤ G.supplyFor supplies asset) ↔
      (∀ row ∈ balances, row.asset ∈ supplies.map supplyKey) ∧
        ∀ supply ∈ supplies,
          G.amountForAsset balances supply.asset ≤ supply.amountAtoms := by
  constructor
  · intro coverage
    constructor
    · intro row rowMember
      classical
      apply Classical.byContradiction
      intro absent
      have noSupply : ∀ supply ∈ supplies, supply.asset ≠ row.asset := by
        intro supply supplyMember sameAsset
        apply absent
        exact List.mem_map.mpr ⟨supply, supplyMember,
          by simpa [supplyKey] using sameAsset⟩
      have balancePositive := amountForAsset_positive_of_member
        (fun candidate candidateMember => (positive candidate candidateMember).2) rowMember
      have supplyZero := supplyFor_zero_of_absent supplies row.asset noSupply
      have covered := coverage row.asset
      rw [supplyZero] at covered
      omega
    · intro supply supplyMember
      have covered := coverage supply.asset
      rw [supplyFor_eq_member_amount supplyKeys supplyMember] at covered
      exact covered
  · rintro ⟨balanceAssets, supplyCoverage⟩ asset
    classical
    by_cases hasBalance : ∃ row ∈ balances, row.asset = asset
    · rcases hasBalance with ⟨row, rowMember, rowAsset⟩
      obtain ⟨supply, supplyMember, sameAsset⟩ :=
        List.mem_map.mp (balanceAssets row rowMember)
      have supplyAsset : supply.asset = asset := by
        simpa [supplyKey] using sameAsset.trans rowAsset
      calc
        G.amountForAsset balances asset = G.amountForAsset balances supply.asset := by
          rw [supplyAsset]
        _ ≤ supply.amountAtoms := supplyCoverage supply supplyMember
        _ = G.supplyFor supplies asset := by
          exact (supplyFor_eq_member_amount supplyKeys supplyMember).symm.trans
            (congrArg (G.supplyFor supplies) supplyAsset)
    · have noBalance : ∀ row ∈ balances, row.asset ≠ asset := by
        intro row rowMember sameAsset
        exact hasBalance ⟨row, rowMember, sameAsset⟩
      rw [amountForAsset_zero_of_absent balances asset noBalance]
      exact supplyFor_nonnegative supplies supplyBounds asset

theorem lookupLast_is_u128 (key : C.AmountKey) (rows : List G.AmountRow)
    (bounded : ∀ row ∈ rows, T.IsU128 row.amountAtoms) :
    T.IsU128 (C.lookupLast key rows) := by
  induction rows with
  | nil =>
      change T.IsU128 0
      decide
  | cons row rows ih =>
      simp only [C.lookupLast]
      split
      · exact ih (fun next member => bounded next (by simp [member]))
      · split
        · exact bounded row (by simp)
        · change T.IsU128 0
          decide

/-- Selection and admitted source rows construct every width premise used by
the existing selected-policy leaf. -/
theorem selectedInput_state_well_formed {input : Input} {policy : T.Policy}
    (admitted : StateAdmitted input.pre)
    (selection : policyFor input.pre.policies input.command.asset = some policy) :
    T.StateWellFormed (S.localState (selectedInput input policy)) := by
  rcases admitted with ⟨canonical, policies, supplies, equalAssets, coverage⟩
  have policyMember := (policyFor_some selection).1
  have policyAsset := (policyFor_some selection).2
  have assetInPolicies : policy.asset ∈ input.pre.policies.map policyKey :=
    List.mem_map.mpr ⟨policy, policyMember, rfl⟩
  have assetInSupplies : policy.asset ∈ input.pre.economic.supplies.map supplyKey := by
    rw [← equalAssets]
    exact assetInPolicies
  obtain ⟨supply, supplyMember, sameAsset⟩ := List.mem_map.mp assetInSupplies
  have supplyAsset : supply.asset = policy.asset := by
    simpa [supplyKey] using sameAsset
  refine ⟨?_, ?_, ?_⟩
  · intro owner
    change T.IsU128 (C.lookupLast (S.accountKey policy.asset owner)
      input.pre.economic.balances)
    exact lookupLast_is_u128 _ _
      (fun row member => (canonical.2.1 row member).2.1)
  · change T.IsU128 (G.supplyFor input.pre.economic.supplies policy.asset)
    rw [← supplyAsset, supplyFor_eq_member_amount supplies.1 supplyMember]
    exact supplies.2.2.2 supply supplyMember
  · exact policies.2.2.2 policy policyMember

theorem step_release_mismatch {input : Input}
    (mismatch : input.context.moduleReleaseId ≠ input.pre.moduleReleaseId) :
    step input = reject input .releaseMismatch := by
  simp [step, mismatch]

theorem step_unknown_command {input : Input}
    (releaseMatches : input.context.moduleReleaseId = input.pre.moduleReleaseId)
    (unknown : input.command.commandKind ≠ T.assetTransferCommandKind) :
    step input = reject input .unknownCommand := by
  simp [step, releaseMatches, unknown]

theorem step_unknown_asset {input : Input}
    (releaseMatches : input.context.moduleReleaseId = input.pre.moduleReleaseId)
    (commandMatches : input.command.commandKind = T.assetTransferCommandKind)
    (missing : policyFor input.pre.policies input.command.asset = none) :
    step input = reject input .unknownAsset := by
  simp [step, releaseMatches, commandMatches, missing]

theorem step_selected {input : Input} {policy : T.Policy}
    (releaseMatches : input.context.moduleReleaseId = input.pre.moduleReleaseId)
    (commandMatches : input.command.commandKind = T.assetTransferCommandKind)
    (selection : policyFor input.pre.policies input.command.asset = some policy) :
    step input = lift input (S.step (selectedInput input policy)) := by
  simp [step, releaseMatches, commandMatches, selection]

/-- An accepted front-door result identifies its first matching pre-state row
and the exact selected sparse step that accepted. -/
theorem accepted_selected_step {input : Input}
    (accepted : (step input).verdict = .accepted) :
    ∃ policy,
      policyFor input.pre.policies input.command.asset = some policy ∧
      (S.step (selectedInput input policy)).verdict = .accepted ∧
      step input = lift input (S.step (selectedInput input policy)) ∧
      policy ∈ input.pre.policies ∧ policy.asset = input.command.asset := by
  by_cases releaseMatches : input.context.moduleReleaseId = input.pre.moduleReleaseId
  · by_cases commandMatches : input.command.commandKind = T.assetTransferCommandKind
    · by_cases found : ∃ policy,
        policyFor input.pre.policies input.command.asset = some policy
      · obtain ⟨policy, selection⟩ := found
        refine ⟨policy, selection, ?_, step_selected releaseMatches commandMatches selection,
          (policyFor_some selection).1, (policyFor_some selection).2⟩
        rw [step_selected releaseMatches commandMatches selection] at accepted
        exact accepted
      · have missing : policyFor input.pre.policies input.command.asset = none :=
          policyFor_none_of_no_selection found
        rw [step_unknown_asset releaseMatches commandMatches missing] at accepted
        cases accepted
    · rw [step_unknown_command releaseMatches commandMatches] at accepted
      cases accepted
  · rw [step_release_mismatch releaseMatches] at accepted
    cases accepted

theorem rejected_step_noop {input : Input} {code : T.RejectCode}
    (rejected : (step input).verdict = .rejected code) :
    (step input).post = input.pre ∧ (step input).plan = EffectPlan.empty := by
  by_cases releaseMatches : input.context.moduleReleaseId = input.pre.moduleReleaseId
  · by_cases commandMatches : input.command.commandKind = T.assetTransferCommandKind
    · cases selection : policyFor input.pre.policies input.command.asset with
      | none =>
          rw [step_unknown_asset releaseMatches commandMatches selection]
          exact ⟨rfl, rfl⟩
      | some policy =>
          have innerRejected : (S.step (selectedInput input policy)).verdict = .rejected code :=
            by simpa [step, releaseMatches, commandMatches, selection] using rejected
          have innerNoop := S.rejected_step_noop innerRejected
          rw [step_selected releaseMatches commandMatches selection]
          simp only [lift]
          rw [innerNoop.1]
          exact ⟨rfl, innerNoop.2⟩
    · rw [step_unknown_command releaseMatches commandMatches]
      exact ⟨rfl, rfl⟩
  · rw [step_release_mismatch releaseMatches]
    exact ⟨rfl, rfl⟩

theorem lift_selected_step_preserves_state_admitted {input : Input} {policy : T.Policy}
    (admitted : StateAdmitted input.pre) :
    StateAdmitted (lift input (S.step (selectedInput input policy))).post := by
  rcases admitted with ⟨canonical, policies, supplies, equalAssets, coverage⟩
  unfold StateAdmitted
  simp only [lift]
  have suppliesFrame : (S.step (selectedInput input policy)).post.supplies =
      input.pre.economic.supplies := by
    rw [S.step_frame (selectedInput input policy)]
    rfl
  refine ⟨?_, policies, ?_, ?_, ?_⟩
  · cases verdict : (S.step (selectedInput input policy)).verdict with
    | rejected code =>
        rw [(S.rejected_step_noop verdict).1]
        exact canonical
    | accepted =>
        exact (S.accepted_sparse_transfer canonical.1 canonical.2.1 verdict).2.2.1
  · rw [suppliesFrame]
    exact supplies
  · rw [suppliesFrame]
    exact equalAssets
  · intro asset
    cases verdict : (S.step (selectedInput input policy)).verdict with
    | rejected code =>
        rw [(S.rejected_step_noop verdict).1]
        exact coverage asset
    | accepted =>
        rw [P.accepted_account_totals canonical.1 verdict asset,
          S.step_frame (selectedInput input policy)]
        exact coverage asset

theorem step_preserves_state_admitted {input : Input} (admitted : StateAdmitted input.pre) :
    StateAdmitted (step input).post := by
  unfold step
  split
  · simpa only [reject] using admitted
  · split
    · simpa only [reject] using admitted
    · split
      · simpa only [reject] using admitted
      · exact lift_selected_step_preserves_state_admitted admitted

/-- A strict front-door balance decrease is tied to the selected policy's
actual sparse transition, the command sender, and the selected context subject. -/
theorem accepted_decrease_authorized {input : Input}
    (admitted : StateAdmitted input.pre)
    (commandWellFormed : T.CommandWellFormed input.command)
    (accepted : (step input).verdict = .accepted) {owner asset domain : String}
    (decreased : amountAt (step input).post.economic.balances owner asset domain <
      amountAt input.pre.economic.balances owner asset domain) :
    owner = input.command.sender ∧ input.command.sender = input.context.subjectId ∧
      input.command.asset = asset ∧ S.accounts = domain := by
  obtain ⟨policy, selection, selectedAccepted, selectedStep, _, _⟩ :=
    accepted_selected_step accepted
  have localWellFormed := selectedInput_state_well_formed admitted selection
  have amountBounds := commandWellFormed.amount
  unfold T.IsU128 at amountBounds
  have feeBounds := localWellFormed.fee
  unfold T.IsU128 at feeBounds
  have selectedDecrease :
      amountAt (S.step (selectedInput input policy)).post.balances owner asset domain <
        amountAt (selectedInput input policy).pre.balances owner asset domain := by
    rw [selectedStep] at decreased
    simpa only [lift, selectedInput] using decreased
  exact Z.accepted_decrease_authorized admitted.1 amountBounds.1 feeBounds.1
    selectedAccepted selectedDecrease

/-- Policies are selected afresh for each request; admission is preserved from
the initial state without a fixed history policy premise. -/
theorem run_preserves_state_admitted (requests : List Request) (pre : State)
    (admitted : StateAdmitted pre) : StateAdmitted (run requests pre).post := by
  induction requests generalizing pre with
  | nil => exact admitted
  | cons request requests ih =>
      cases verdict : (step (inputFor request pre)).verdict with
      | rejected code =>
          simpa only [run, verdict] using ih pre admitted
      | accepted =>
          have nextAdmitted := step_preserves_state_admitted (input := inputFor request pre)
            admitted
          simpa only [run, verdict] using
            ih (step (inputFor request pre)).post nextAdmitted

/-- The selected sparse proof supplies each accepted link; no fixed policy is
carried across this history. -/
theorem run_table_chain (requests : List Request) (pre : State)
    (admitted : StateAdmitted pre) :
    TableChain pre.economic (run requests pre).acceptedPlans (run requests pre).post.economic ∧
      S.CanonicalBalances (run requests pre).post.economic.balances := by
  induction requests generalizing pre with
  | nil => exact ⟨.nil pre.economic, admitted.1⟩
  | cons request requests ih =>
      cases verdict : (step (inputFor request pre)).verdict with
      | rejected code =>
          simpa only [run, verdict] using ih pre admitted
      | accepted =>
          obtain ⟨policy, selection, selectedAccepted, selectedStep, _, _⟩ :=
            accepted_selected_step verdict
          have one := S.accepted_sparse_transfer admitted.1.1 admitted.1.2.1 selectedAccepted
          have nextAdmitted := step_preserves_state_admitted (input := inputFor request pre)
            admitted
          have tail := ih (step (inputFor request pre)).post nextAdmitted
          have route : ExactEconomicTables pre.economic
              (step (inputFor request pre)).post.economic
              (step (inputFor request pre)).plan := by
            rw [selectedStep]
            simpa only [lift, selectedInput] using one.1
          simpa only [run, verdict] using ⟨.cons route tail.1, tail.2⟩

/-- Global quantity admission is an additional initial premise because the
local state model intentionally allows zero supply rows. -/
theorem step_preserves_state_quantities_admitted {input : Input}
    (admitted : StateAdmitted input.pre)
    (quantities : G.StateQuantitiesAdmitted input.pre.economic) :
    G.StateQuantitiesAdmitted (step input).post.economic := by
  by_cases releaseMatches : input.context.moduleReleaseId = input.pre.moduleReleaseId
  · by_cases commandMatches : input.command.commandKind = T.assetTransferCommandKind
    · by_cases found : ∃ policy,
        policyFor input.pre.policies input.command.asset = some policy
      · obtain ⟨policy, selection⟩ := found
        rw [step_selected releaseMatches commandMatches selection]
        simpa only [lift] using A.step_preserves_state_quantities_admitted
          (input := selectedInput input policy) admitted.1 quantities
      · rw [step_unknown_asset releaseMatches commandMatches
          (policyFor_none_of_no_selection found)]
        exact quantities
    · rw [step_unknown_command releaseMatches commandMatches]
      exact quantities
  · rw [step_release_mismatch releaseMatches]
    exact quantities

theorem step_preserves_owned_supply_and_claimant_liabilities_backed {input : Input}
    (admitted : StateAdmitted input.pre) (owned : G.OwnedMatchesSupply input.pre.economic)
    (backed : G.ClaimantLiabilitiesBacked input.pre.economic) :
    G.OwnedMatchesSupply (step input).post.economic ∧
      G.ClaimantLiabilitiesBacked (step input).post.economic := by
  by_cases releaseMatches : input.context.moduleReleaseId = input.pre.moduleReleaseId
  · by_cases commandMatches : input.command.commandKind = T.assetTransferCommandKind
    · by_cases found : ∃ policy,
        policyFor input.pre.policies input.command.asset = some policy
      · obtain ⟨policy, selection⟩ := found
        rw [step_selected releaseMatches commandMatches selection]
        simpa only [lift] using
          A.step_preserves_owned_supply_and_claimant_liabilities_backed
            (input := selectedInput input policy) admitted.1 owned backed
      · rw [step_unknown_asset releaseMatches commandMatches
          (policyFor_none_of_no_selection found)]
        exact ⟨owned, backed⟩
    · rw [step_unknown_command releaseMatches commandMatches]
      exact ⟨owned, backed⟩
  · rw [step_release_mismatch releaseMatches]
    exact ⟨owned, backed⟩

theorem run_preserves_state_quantities_admitted (requests : List Request) (pre : State)
    (admitted : StateAdmitted pre) (quantities : G.StateQuantitiesAdmitted pre.economic) :
    G.StateQuantitiesAdmitted (run requests pre).post.economic := by
  induction requests generalizing pre with
  | nil => exact quantities
  | cons request requests ih =>
      cases verdict : (step (inputFor request pre)).verdict with
      | rejected code =>
          simpa only [run, verdict] using ih pre admitted quantities
      | accepted =>
          have nextAdmitted := step_preserves_state_admitted (input := inputFor request pre)
            admitted
          have nextQuantities := step_preserves_state_quantities_admitted
            (input := inputFor request pre) admitted quantities
          simpa only [run, verdict] using
            ih (step (inputFor request pre)).post nextAdmitted nextQuantities

theorem run_preserves_owned_supply_and_claimant_liabilities_backed
    (requests : List Request) (pre : State) (admitted : StateAdmitted pre)
    (owned : G.OwnedMatchesSupply pre.economic)
    (backed : G.ClaimantLiabilitiesBacked pre.economic) :
    G.OwnedMatchesSupply (run requests pre).post.economic ∧
      G.ClaimantLiabilitiesBacked (run requests pre).post.economic := by
  induction requests generalizing pre with
  | nil => exact ⟨owned, backed⟩
  | cons request requests ih =>
      cases verdict : (step (inputFor request pre)).verdict with
      | rejected code =>
          simpa only [run, verdict] using ih pre admitted owned backed
      | accepted =>
          have nextAdmitted := step_preserves_state_admitted (input := inputFor request pre)
            admitted
          have nextPreserved := step_preserves_owned_supply_and_claimant_liabilities_backed
            (input := inputFor request pre) admitted owned backed
          simpa only [run, verdict] using
            ih (step (inputFor request pre)).post nextAdmitted nextPreserved.1 nextPreserved.2

end AssetTransferPolicySelectionV1
end Proofs
