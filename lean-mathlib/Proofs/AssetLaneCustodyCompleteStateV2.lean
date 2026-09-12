import Proofs.AssetLaneCustodyStructuralV2
import Proofs.AssetOriginRegistryRefinementV2

/-!
# Complete owned state and bytes for the custody-capable asset lane

`FullState` retains the four runtime-owned payloads. Its finite projection
derives registry keys from the actual origin records, so there is no second
stored key list. The encoder follows the nested, sorted-key custody-state JSON
layout and reuses the existing finite transfer, managed-policy and row encoders.

`Resources` records only the concrete nested and complete-state count and byte
ceilings. It does not establish token validity, registry or policy binding,
canonical runtime construction, root authenticity, receipts or publication
authority. A finite leaf may be accepted while the materialized complete state
exceeds its outer byte ceiling; `step` does not claim resource preservation or
whole-coordinator acceptance. Exact Python/Rust byte correspondence remains a
differential-gate obligation on runtime-admitted values.
-/

set_option warningAsError true

namespace Proofs.AssetLaneCustodyCompleteStateV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace C
export AssetLaneCustodyRefinementV2 (State)
end C
namespace E
export AssetLaneCustodyEffectPlanV2 (transferSource)
end E
namespace F
export AssetLaneCustodyFiniteTraceV2 (Action FixedFrame step step_fixed_frame)
end F
namespace FT
export AssetTransferFiniteOutcomeV2 (State stateBytes)
end FT
namespace FM
export ManagedAssetFiniteOutcomeV2 (policyBytes)
end FM
namespace M
export ManagedAssetLifecycleRefinementV2 (Policy)
end M
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes raw quoted number amountRow array)
end B
namespace O
export AssetOriginRegistryRefinementV2 (OriginKind AssetClass Record RegistrationPolicy State)
end O

/-- The four owned payloads of `AssetLaneCustodyStateV2`. -/
structure FullState where
  transfer : FT.State
  originRegistry : O.State
  managedPolicies : List M.Policy
  custody : List AmountRow
  deriving DecidableEq, Repr

/-- Forget full registry records while deriving their actual ordered keys. -/
def erase (state : FullState) : C.State :=
  { transferState :=
      ⟨state.transfer.moduleReleaseId, state.transfer.policies,
        state.transfer.balances, state.transfer.supplies⟩
    originRegistry := state.originRegistry.assets.map (fun record => record.asset)
    managedPolicies := state.managedPolicies
    custody := state.custody }

def schema : String := "zenodex/asset-lane-custody-state/v2"

def originRegistrySchema : String := "zenodex/asset-origin-registry/v2"

def originKindCode : O.OriginKind → String
  | .native => "NATIVE"
  | .tauOriginated => "TAU_ORIGINATED"

def assetClassCode : O.AssetClass → String
  | .tauNativeCoin => "tau_native_coin"
  | .canonicalZusd => "canonical_zusd"
  | .lpShare => "lp_share"
  | .zdexProtocolToken => "zdex_protocol_token"
  | .sealedBidPaymentOrInventory => "sealed_bid_payment_or_inventory"
  | .registeredOrdinaryToken => "registered_ordinary_token"

/-- Sorted-key encoding of a complete origin-registry record. -/
def originRecordBytes (record : O.Record) : B.Bytes :=
  B.raw "{\"asset\":" ++ B.quoted record.asset ++
    B.raw ",\"asset_class\":" ++ B.quoted (assetClassCode record.assetClass) ++
    B.raw ",\"decimals\":" ++ B.number (Int.ofNat record.decimals) ++
    B.raw ",\"issue_policy_root\":" ++ B.quoted record.issuePolicyRoot ++
    B.raw ",\"origin_kind\":" ++ B.quoted (originKindCode record.originKind) ++
    B.raw ",\"origin_root\":" ++ B.quoted record.originRoot ++
    B.raw ",\"transfer_policy_root\":" ++ B.quoted record.transferPolicyRoot ++ B.raw "}"

/-- Sorted-key encoding of the origin-registration policy. -/
def registrationPolicyBytes (policy : O.RegistrationPolicy) : B.Bytes :=
  B.raw "{\"allow_native\":" ++ (if policy.allowNative then B.raw "true" else B.raw "false") ++
    B.raw ",\"allow_tau_originated\":" ++
      (if policy.allowTauOriginated then B.raw "true" else B.raw "false") ++
    B.raw ",\"authority_grant_root\":" ++ B.quoted policy.authorityGrantRoot ++
    B.raw ",\"authority_subject\":" ++ B.quoted policy.authoritySubject ++ B.raw "}"

/-- Sorted-key encoding of the complete origin registry, including its schema. -/
def originRegistryBytes (registry : O.State) : B.Bytes :=
  B.raw "{\"assets\":" ++ B.array originRecordBytes registry.assets ++
    B.raw ",\"module_release_id\":" ++ B.quoted registry.moduleReleaseId ++
    B.raw ",\"policy\":" ++ registrationPolicyBytes registry.policy ++
    B.raw ",\"schema\":" ++ B.quoted originRegistrySchema ++ B.raw "}"

/-- The actual five-field, sorted-key custody-state encoding. -/
def stateBytes (state : FullState) : B.Bytes :=
  B.raw "{\"custody\":" ++ B.array B.amountRow state.custody ++
    B.raw ",\"managed_policies\":" ++ B.array FM.policyBytes state.managedPolicies ++
    B.raw ",\"origin_registry\":" ++ originRegistryBytes state.originRegistry ++
    B.raw ",\"schema\":" ++ B.quoted schema ++
    B.raw ",\"transfer_state\":" ++ FT.stateBytes state.transfer ++ B.raw "}"

/-- Concrete nested-state and complete-state resource ceilings. -/
def Resources (state : FullState) : Prop :=
  state.transfer.policies.length ≤ 256 ∧
    state.transfer.balances.length ≤ 4096 ∧
    state.transfer.supplies.length ≤ 256 ∧
    (FT.stateBytes state.transfer).length ≤ 1048576 ∧
    state.originRegistry.assets.length ≤ 256 ∧
    (originRegistryBytes state.originRegistry).length ≤ 1048576 ∧
    state.managedPolicies.length ≤ 256 ∧
    state.custody.length ≤ 4096 ∧
    (stateBytes state).length ≤ 1048576

instance (state : FullState) : Decidable (Resources state) := by
  unfold Resources
  infer_instance

/-- Run the actual finite mixed step on the erased state and retain every full
metadata payload while materializing the resulting transfer fields. -/
def step (digest : B.Bytes → String) (pre : FullState) (action : F.Action) : FullState :=
  { transfer := E.transferSource (F.step digest (erase pre) action)
    originRegistry := pre.originRegistry
    managedPolicies := pre.managedPolicies
    custody := pre.custody }

/-- Erasure exposes exactly the owned transfer leaf. -/
theorem erase_transfer_source (state : FullState) :
    E.transferSource (erase state) = state.transfer := by
  cases state with
  | mk transfer originRegistry managedPolicies custody =>
      cases transfer
      rfl

/-- The complete wrapper commutes with the actual finite mixed transition. -/
theorem erase_step (digest : B.Bytes → String) (pre : FullState) (action : F.Action) :
    erase (step digest pre action) = F.step digest (erase pre) action := by
  have frame := F.step_fixed_frame digest (erase pre) action
  unfold step
  generalize postEq : F.step digest (erase pre) action = post at frame ⊢
  cases post with
  | mk transferState originRegistry managedPolicies custody =>
      cases transferState
      simp_all [F.FixedFrame, erase, E.transferSource]

/-- A complete step preserves every payload omitted by finite erasure. -/
theorem step_metadata (digest : B.Bytes → String) (pre : FullState) (action : F.Action) :
    (step digest pre action).originRegistry = pre.originRegistry ∧
      (step digest pre action).managedPolicies = pre.managedPolicies ∧
      (step digest pre action).custody = pre.custody := by
  exact ⟨rfl, rfl, rfl⟩

/-- The finite fixed frame also retains transfer release and policy metadata. -/
theorem step_transfer_metadata (digest : B.Bytes → String)
    (pre : FullState) (action : F.Action) :
    (step digest pre action).transfer.moduleReleaseId = pre.transfer.moduleReleaseId ∧
      (step digest pre action).transfer.policies = pre.transfer.policies := by
  have frame := F.step_fixed_frame digest (erase pre) action
  simpa only [step, E.transferSource, erase] using And.intro frame.1 frame.2.1

/-- Since outer metadata is unchanged, the full serialization changes in byte
length by exactly the same amount as its embedded transfer serialization. -/
theorem step_state_bytes_length_relation (digest : B.Bytes → String)
    (pre : FullState) (action : F.Action) :
    (stateBytes (step digest pre action)).length + (FT.stateBytes pre.transfer).length =
      (stateBytes pre).length + (FT.stateBytes (step digest pre action).transfer).length := by
  simp only [stateBytes, step, List.length_append]
  omega

end Proofs.AssetLaneCustodyCompleteStateV2
