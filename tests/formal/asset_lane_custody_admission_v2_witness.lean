import Proofs.AssetLaneCustodyAdmissionV2

set_option warningAsError true
set_option maxRecDepth 100000

namespace AdmissionWitness

namespace A
export Proofs.AssetLaneCustodyAdmissionV2 (ConstructorAdmission ConstructorMetadata
  RecordSyntax RegistrationPolicySyntax CustodyOrdered PolicyOriginBindings
  step_preserves_constructor_admission policy_origin_bindings_preserved
  transfer_accepted_full_projection managed_accepted_full_projection)
end A
namespace D
export Proofs.AssetLaneCustodyCompleteStateV2 (FullState erase Resources step step_metadata)
end D
namespace X
export Proofs.AssetLaneCustodyStructuralV2 (CompleteStructural ActionAdmission)
end X
namespace C
export Proofs.AssetLaneCustodyRefinementV2 (RowsRepresentable physicalFor supplyAt)
end C
namespace F
export Proofs.AssetLaneCustodyFiniteTraceV2 (StaticPolicyShape Action)
end F
namespace FT
export Proofs.AssetTransferFiniteOutcomeV2 (MetadataAdmission transition accepted_iff
  accepted_post_effects policyFor project candidate candidateFor Resources)
end FT
namespace FM
export Proofs.ManagedAssetFiniteOutcomeV2 (MetadataAdmission PolicySyntax transition)
end FM
namespace B
export Proofs.AssetLaneFiniteByteAccountingV2 (Bytes ValidToken BalanceTokens SupplyTokens raw)
end B
namespace O
export Proofs.AssetOriginRegistryRefinementV2 (ValidState zeroRoot)
end O
namespace S
export Proofs.AssetTransferSparseTablesV1 (Unique PositiveAccounts accounts balanceWire)
end S
namespace E
export Proofs.AssetLaneCustodyEffectPlanV2 (managedSource)
end E
namespace FA
export Proofs.AssetTransferFiniteAccountingV2 (transferRows)
end FA
namespace MA
export Proofs.ManagedAssetFiniteAccountingV2 (updateRows)
end MA
namespace K
export Proofs.CanonicalEpochEconomicRowsV1 (sortOn)
end K
namespace T
export Proofs.AssetTransferRefinementV2 (Policy Context Command)
end T
namespace M
export Proofs.ManagedAssetLifecycleRefinementV2 (Policy Context Command)
end M

open Proofs.GlobalEconomicStateRefinementV2
open Proofs.GlobalSettlementCoreV2
open Proofs.RegisteredSupplySupportV1
open Proofs.RegisteredSupplyUpdateV1
open Proofs.AssetTransferRefinementV1

attribute [local instance] lexOrd

local instance tokenDecidable (value : String) : Decidable (B.ValidToken value) := by
  unfold B.ValidToken
  infer_instance

/-- This bounded witness uses the runtime-shaped nonzero printable-root predicate.
It makes no claim that this predicate is the full Python root parser. -/
def rootSyntax (value : String) : Prop := B.ValidToken value ∧ value ≠ O.zeroRoot

local instance rootSyntaxDecidable (value : String) : Decidable (rootSyntax value) := by
  unfold rootSyntax
  infer_instance

def namespaceSyntax (_ : String) (_ : Proofs.AssetTransferRefinementV2.AssetClass) : Prop := True

local instance namespaceSyntaxDecidable (asset : String)
    (assetClass : Proofs.AssetTransferRefinementV2.AssetClass) :
    Decidable (namespaceSyntax asset assetClass) := by
  unfold namespaceSyntax
  infer_instance

/-- Exact `_full_state(custody_state())` output from the frozen complete-state
Python test generator. It has a positive account balance, positive custody and a
nonzero managed supply policy. -/
def pre : D.FullState :=
  ⟨⟨"0x2e33c221765009e5181427a67296d9a5c6f61d9483a4235b9bf5e7e2d282252f",
      [⟨"USD", "treasury", 2, true, .registeredOrdinaryToken,
        some "0x6d1f2f086dbcdda2adc8e9378930c2ffa775fdf4bba023dded9c0efa8f6ab8d5", 8⟩],
      [⟨"alice", "USD", "accounts", 80⟩], [⟨"USD", 100⟩]⟩,
    ⟨"0x2e33c221765009e5181427a67296d9a5c6f61d9483a4235b9bf5e7e2d282252f",
      ⟨"governance", "0x9c90b49f6987f4ef6bde9eb5e3314a5888f6c0508d1f443c30cbb77f0a24b0db",
        true, true⟩,
      [⟨"USD", .tauOriginated,
        "0x6d1f2f086dbcdda2adc8e9378930c2ffa775fdf4bba023dded9c0efa8f6ab8d5",
        "0x3d240afe1af329f16393ab220ebd82b54a123c5dba9707a40bc30ba20b46d9ad",
        "0x35a239da6b6e311403381c36b2aae0fa85b7fe29f7a9ccacfb6a13947c03ced2",
        8, .registeredOrdinaryToken⟩]⟩,
    [⟨"USD", .registeredOrdinaryToken,
      some "0x6d1f2f086dbcdda2adc8e9378930c2ffa775fdf4bba023dded9c0efa8f6ab8d5", 8,
      some ⟨"issuer", "0x77ccb1ef8f45585115747b028ab360d97ea778dad6a91ee9d594af063a197992"⟩,
      some "0x0201f8339ccc0115df4502f4b321c0b077bad10e2adeff118582b054c27fd0d0",
      true⟩],
    [⟨"vault", "USD", "escrow", 20⟩]⟩

theorem rows : C.RowsRepresentable (D.erase pre) := by
  constructor
  · unfold SourceAssetKeysUnique
    decide
  · unfold SourceAssetKeysOrdered
    decide
  · simp [SourceRowsU128, D.erase, pre, FitsU128, maxU128]
  · rfl
  · rfl
  · decide
  · unfold S.Unique
    decide
  · simp [S.PositiveAccounts, D.erase, pre, S.accounts, IsU128, u128Max]
  · unfold S.Unique
    decide
  · simp [D.erase, pre, S.accounts, FitsU128, maxU128]
  · decide
  · intro asset
    by_cases usd : asset = "USD"
    · subst asset
      decide
    · simp [C.physicalFor, C.supplyAt, D.erase, pre, amountForAsset, numericRows,
        nonzeroRow, toNumericRow, supplyFor, Ne.symm usd]

theorem complete : X.CompleteStructural (D.erase pre) := by
  refine {
    rows := rows
    policyShape := ?_
    managedPolicyOrdered := by decide
    balanceOrdered := by decide
    transferFeeOwnerTokens := ?_
    balanceTokens := ?_
    supplyTokens := ?_ }
  · unfold F.StaticPolicyShape
    constructor
    · intro policy member
      simp only [D.erase, pre, List.mem_cons, List.not_mem_nil, or_false] at member
      subst policy
      decide
    · intro policy member
      simp only [D.erase, pre, List.mem_cons, List.not_mem_nil, or_false] at member
      subst policy
      constructor
      · rfl
      · intro protocol
        exact False.elim (protocol rfl)
  · intro policy member
    simp only [D.erase, pre, List.mem_cons, List.not_mem_nil, or_false] at member
    subst policy
    decide
  · intro row member
    simp only [D.erase, pre, List.mem_cons, List.not_mem_nil, or_false] at member
    subst row
    decide
  · intro row member
    simp only [D.erase, pre, List.mem_cons, List.not_mem_nil, or_false] at member
    subst row
    decide

theorem metadata : A.ConstructorMetadata rootSyntax namespaceSyntax pre := by
  unfold A.ConstructorMetadata
  refine ⟨by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro policy member
    simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at member
    subst policy
    refine ⟨_, List.mem_singleton.mpr rfl, rfl, rfl, rfl, rfl⟩
  · unfold FT.MetadataAdmission
    simp [pre, rootSyntax, namespaceSyntax]
    decide
  · unfold FM.MetadataAdmission FM.PolicySyntax
    simp [Proofs.AssetLaneCustodyEffectPlanV2.managedSource, D.erase, pre,
      rootSyntax, namespaceSyntax]
    decide
  · intro record member
    simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at member
    subst record
    simp [A.RecordSyntax, rootSyntax, namespaceSyntax]
    decide
  · simp [A.RegistrationPolicySyntax, pre, rootSyntax]
    decide
  · intro row member
    simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at member
    subst row
    decide
  · unfold A.CustodyOrdered
    decide

/-- Nonvacuity witness for the complete modeled constructor predicate on one
actual positive-custody Python fixture. -/
theorem constructor_admission_witness :
    A.ConstructorAdmission rootSyntax namespaceSyntax pre := by
  exact ⟨complete, metadata, by decide⟩

/- The following context and command literals are emitted by the current
Python runtime fixture serializers. Each action starts from `pre`; these are
three independent accepted applications, not a chained outer-coordinator run. -/
def digest (_ : B.Bytes) : String := "admission-digest"

def transferContext : T.Context :=
  ⟨"0x2e33c221765009e5181427a67296d9a5c6f61d9483a4235b9bf5e7e2d282252f",
    "0x6060059efda0970b74febc94290f2136da569b1f92fe0e5523e40853ea3d298d",
    some ⟨"0x6060059efda0970b74febc94290f2136da569b1f92fe0e5523e40853ea3d298d", [],
      "asset_transfer",
      "0x710bbad757091ca84ee045597b3b304fc830d87fb3d95f578239972baea04bf7",
      "alice", "0xf852a7446e411be0320924844fd1940c3a81d83aa8aae97703886ea26a642693",
      "0xc6c1d5ddb07287ae20ca4af8eba9732aa3bcbb47005559d0124f755b96dfd30b"⟩⟩

def transferCommand : T.Command :=
  ⟨"asset_transfer",
    "0x710bbad757091ca84ee045597b3b304fc830d87fb3d95f578239972baea04bf7",
    "USD", "alice", "bob", 10, 2,
    some "0x6d1f2f086dbcdda2adc8e9378930c2ffa775fdf4bba023dded9c0efa8f6ab8d5"⟩

def issueContext : M.Context :=
  ⟨"0x2e33c221765009e5181427a67296d9a5c6f61d9483a4235b9bf5e7e2d282252f",
    "0x6060059efda0970b74febc94290f2136da569b1f92fe0e5523e40853ea3d298d",
    some ⟨"0x6060059efda0970b74febc94290f2136da569b1f92fe0e5523e40853ea3d298d", [],
      "managed_asset_issue",
      "0xcf643d4fc3965f2876ba190f60eff404cc8ed3a879a40002d6adc2943c657a47",
      "issuer", "0x77ccb1ef8f45585115747b028ab360d97ea778dad6a91ee9d594af063a197992",
      "0x4ee8ec9417ce4725edc12891224e46822de320c3f754c2c7fd4b5d994c6a6b50"⟩⟩

def issueCommand : M.Command :=
  ⟨"managed_asset_issue",
    "0xcf643d4fc3965f2876ba190f60eff404cc8ed3a879a40002d6adc2943c657a47",
    "USD", .registeredOrdinaryToken,
    some "0x6d1f2f086dbcdda2adc8e9378930c2ffa775fdf4bba023dded9c0efa8f6ab8d5", 8,
    some "0x77ccb1ef8f45585115747b028ab360d97ea778dad6a91ee9d594af063a197992",
    "alice", 2⟩

def burnContext : M.Context :=
  ⟨"0x2e33c221765009e5181427a67296d9a5c6f61d9483a4235b9bf5e7e2d282252f",
    "0x1ceab0a890a287ca675384624b8f1bb7c02383bb074a0b6e0c76570590c18c7d",
    some ⟨"0x1ceab0a890a287ca675384624b8f1bb7c02383bb074a0b6e0c76570590c18c7d", [],
      "managed_asset_burn",
      "0xae630b2ba09e2b7d1d423e8ed06e3a1be1e25a709a912361a673e6016d338a71",
      "alice", "0x0201f8339ccc0115df4502f4b321c0b077bad10e2adeff118582b054c27fd0d0",
      "0x99e839ed9096385b2e7e88d3b92f368d2be0362c987f3e74d5b851d332b6147e"⟩⟩

def burnCommand : M.Command :=
  ⟨"managed_asset_burn",
    "0xae630b2ba09e2b7d1d423e8ed06e3a1be1e25a709a912361a673e6016d338a71",
    "USD", .registeredOrdinaryToken,
    some "0x6d1f2f086dbcdda2adc8e9378930c2ffa775fdf4bba023dded9c0efa8f6ab8d5", 8,
    some "0x0201f8339ccc0115df4502f4b321c0b077bad10e2adeff118582b054c27fd0d0",
    "alice", 2⟩

def transferAction : F.Action := .transfer transferContext transferCommand
def issueAction : F.Action := .managed issueContext issueCommand
def burnAction : F.Action := .managed burnContext burnCommand

def transferPolicy : T.Policy :=
  ⟨"USD", "treasury", 2, true, .registeredOrdinaryToken,
    some "0x6d1f2f086dbcdda2adc8e9378930c2ffa775fdf4bba023dded9c0efa8f6ab8d5", 8⟩

theorem transfer_selected : FT.policyFor pre.transfer transferCommand.asset = some transferPolicy := by
  decide

theorem transfer_candidate_rows :
    FA.transferRows (FT.project pre.transfer transferPolicy) transferCommand pre.transfer.balances =
      [⟨"alice", "USD", "accounts", 68⟩, ⟨"bob", "USD", "accounts", 10⟩,
        ⟨"treasury", "USD", "accounts", 2⟩] := by
  have feeRows :
      MA.updateRows [⟨"alice", "USD", "accounts", 80⟩] "USD" "treasury" 2 =
        [⟨"alice", "USD", "accounts", 80⟩,
          ⟨"treasury", "USD", "accounts", 2⟩] := by
    simp only [MA.updateRows, Proofs.CanonicalEpochEconomicRowsV1.lookupLast,
      Proofs.AssetTransferSparseTablesV1.accountKey,
      Proofs.AssetTransferSparseTablesV1.putAmount,
      Proofs.AssetTransferSparseTablesV1.eraseKey,
      Proofs.AssetTransferSparseTablesV1.makeAmount,
      Proofs.CanonicalEpochEconomicRowsV1.amountKey,
      Proofs.AssetTransferSparseTablesV1.accounts, List.map_nil, List.not_mem_nil,
      Prod.mk.injEq, String.reduceEq, and_true, bne_iff_ne, ne_eq,
      not_false_eq_true, List.filter_cons_of_pos, List.filter_nil]
    apply Proofs.AssetLaneFiniteRecompositionV2.sortOn_eq_of_perm_keys
    · exact List.Perm.swap _ _ []
    · decide
    · decide
  have recipientRows :
      MA.updateRows
          [⟨"alice", "USD", "accounts", 80⟩,
            ⟨"treasury", "USD", "accounts", 2⟩]
          "USD" "bob" 10 =
        [⟨"alice", "USD", "accounts", 80⟩,
          ⟨"bob", "USD", "accounts", 10⟩,
          ⟨"treasury", "USD", "accounts", 2⟩] := by
    change K.sortOn S.balanceWire
      [⟨"bob", "USD", "accounts", 10⟩,
        ⟨"alice", "USD", "accounts", 80⟩,
        ⟨"treasury", "USD", "accounts", 2⟩] = _
    simp (disch := decide) [K.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  have senderRows :
      MA.updateRows
          [⟨"alice", "USD", "accounts", 80⟩,
            ⟨"bob", "USD", "accounts", 10⟩,
            ⟨"treasury", "USD", "accounts", 2⟩]
          "USD" "alice" (-12) =
        [⟨"alice", "USD", "accounts", 68⟩,
          ⟨"bob", "USD", "accounts", 10⟩,
          ⟨"treasury", "USD", "accounts", 2⟩] := by
    change K.sortOn S.balanceWire
      [⟨"alice", "USD", "accounts", 68⟩,
        ⟨"bob", "USD", "accounts", 10⟩,
        ⟨"treasury", "USD", "accounts", 2⟩] = _
    simp (disch := decide) [K.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  change MA.updateRows
    (MA.updateRows (MA.updateRows pre.transfer.balances "USD" "treasury" 2)
      "USD" "bob" 10) "USD" "alice" (-12) = _
  simp only [pre]
  rw [feeRows, recipientRows, senderRows]

theorem transfer_leaf_accepted :
    (FT.transition digest transferContext pre.transfer transferCommand).verdict = .accepted := by
  apply (FT.accepted_iff _ _ _ _).2
  constructor
  · decide
  · unfold FT.Resources
    simp only [FT.candidate, transfer_selected, FT.candidateFor]
    rw [transfer_candidate_rows]
    decide

theorem issue_leaf_accepted :
    (FM.transition digest issueContext (E.managedSource (D.erase pre)) issueCommand).verdict =
      .accepted := by
  decide +kernel

theorem burn_leaf_accepted :
    (FM.transition digest burnContext (E.managedSource (D.erase pre)) burnCommand).verdict =
      .accepted := by
  decide +kernel

theorem transfer_action_admitted : X.ActionAdmission transferAction := by
  simp only [transferAction, X.ActionAdmission]
  unfold Proofs.AssetTransferFiniteOutcomeV2.CommandAdmission
  exact ⟨⟨by decide, by decide⟩, by decide, by decide⟩

theorem issue_action_admitted : X.ActionAdmission issueAction := by
  simp only [issueAction, X.ActionAdmission]
  exact ⟨⟨by decide, rfl⟩, by decide⟩

theorem burn_action_admitted : X.ActionAdmission burnAction := by
  simp only [burnAction, X.ActionAdmission]
  exact ⟨⟨by decide, rfl⟩, by decide⟩

theorem transfer_post_resources : D.Resources (D.step digest pre transferAction) := by
  simp only [transferAction]
  unfold D.Resources Proofs.AssetLaneCustodyCompleteStateV2.stateBytes
  have frame := D.step_metadata digest pre (.transfer transferContext transferCommand)
  rw [A.transfer_accepted_full_projection transfer_leaf_accepted,
    frame.1, frame.2.1, frame.2.2]
  rw [(FT.accepted_post_effects transfer_leaf_accepted).1]
  simp only [FT.candidate, transfer_selected, FT.candidateFor]
  rw [transfer_candidate_rows]
  simp [pre]
  decide
theorem issue_post_resources : D.Resources (D.step digest pre issueAction) := by
  decide +kernel
theorem burn_post_resources : D.Resources (D.step digest pre burnAction) := by
  decide +kernel

/-- Each accepted actual leaf materialization retains complete constructor
admission; no post state is supplied as a premise. -/
theorem transfer_post_admitted :
    A.ConstructorAdmission rootSyntax namespaceSyntax (D.step digest pre transferAction) :=
  A.step_preserves_constructor_admission digest constructor_admission_witness
    transfer_action_admitted transfer_post_resources

theorem issue_post_admitted :
    A.ConstructorAdmission rootSyntax namespaceSyntax (D.step digest pre issueAction) :=
  A.step_preserves_constructor_admission digest constructor_admission_witness
    issue_action_admitted issue_post_resources

theorem burn_post_admitted :
    A.ConstructorAdmission rootSyntax namespaceSyntax (D.step digest pre burnAction) :=
  A.step_preserves_constructor_admission digest constructor_admission_witness
    burn_action_admitted burn_post_resources

theorem transfer_full_projection :
    (D.step digest pre transferAction).transfer =
      (FT.transition digest transferContext pre.transfer transferCommand).post :=
  A.transfer_accepted_full_projection transfer_leaf_accepted

theorem issue_full_projection :
    E.managedSource (D.erase (D.step digest pre issueAction)) =
      (FM.transition digest issueContext (E.managedSource (D.erase pre)) issueCommand).post :=
  A.managed_accepted_full_projection complete issue_action_admitted issue_leaf_accepted

theorem burn_full_projection :
    E.managedSource (D.erase (D.step digest pre burnAction)) =
      (FM.transition digest burnContext (E.managedSource (D.erase pre)) burnCommand).post :=
  A.managed_accepted_full_projection complete burn_action_admitted burn_leaf_accepted

/-- Exact finite post rows independently match the runtime fixture results. -/
theorem transfer_post_rows :
    (D.step digest pre transferAction).transfer.balances =
        [⟨"alice", "USD", "accounts", 68⟩, ⟨"bob", "USD", "accounts", 10⟩,
          ⟨"treasury", "USD", "accounts", 2⟩] ∧
      (D.step digest pre transferAction).transfer.supplies = [⟨"USD", 100⟩] := by
  simp only [transferAction]
  rw [A.transfer_accepted_full_projection transfer_leaf_accepted]
  rw [(FT.accepted_post_effects transfer_leaf_accepted).1]
  simp only [FT.candidate, transfer_selected, FT.candidateFor]
  rw [transfer_candidate_rows]
  simp [pre]

theorem issue_post_rows :
    (D.step digest pre issueAction).transfer.balances = [⟨"alice", "USD", "accounts", 82⟩] ∧
      (D.step digest pre issueAction).transfer.supplies = [⟨"USD", 102⟩] := by
  decide +kernel

theorem burn_post_rows :
    (D.step digest pre burnAction).transfer.balances = [⟨"alice", "USD", "accounts", 78⟩] ∧
      (D.step digest pre burnAction).transfer.supplies = [⟨"USD", 98⟩] := by
  decide +kernel

def managedPolicy : M.Policy :=
  ⟨"USD", .registeredOrdinaryToken,
    some "0x6d1f2f086dbcdda2adc8e9378930c2ffa775fdf4bba023dded9c0efa8f6ab8d5", 8,
    some ⟨"issuer", "0x77ccb1ef8f45585115747b028ab360d97ea778dad6a91ee9d594af063a197992"⟩,
    some "0x0201f8339ccc0115df4502f4b321c0b077bad10e2adeff118582b054c27fd0d0", true⟩

def transferCommit (policy : T.Policy) : String :=
  if policy = transferPolicy then
    "0x3d240afe1af329f16393ab220ebd82b54a123c5dba9707a40bc30ba20b46d9ad"
  else "unbound"

def managedCommit (policy : M.Policy) : String :=
  if policy = managedPolicy then
    "0x35a239da6b6e311403381c36b2aae0fa85b7fe29f7a9ccacfb6a13947c03ced2"
  else "unbound"

theorem initial_policy_origin_bindings :
    A.PolicyOriginBindings transferCommit managedCommit pre := by
  simp [A.PolicyOriginBindings, pre, transferCommit, managedCommit, transferPolicy, managedPolicy,
    Proofs.AssetLaneCustodyAdmissionV2.assetClassOf, O.zeroRoot]

theorem transfer_policy_origin_bindings :
    A.PolicyOriginBindings transferCommit managedCommit (D.step digest pre transferAction) :=
  A.policy_origin_bindings_preserved digest pre transferAction initial_policy_origin_bindings

theorem issue_policy_origin_bindings :
    A.PolicyOriginBindings transferCommit managedCommit (D.step digest pre issueAction) :=
  A.policy_origin_bindings_preserved digest pre issueAction initial_policy_origin_bindings

theorem burn_policy_origin_bindings :
    A.PolicyOriginBindings transferCommit managedCommit (D.step digest pre burnAction) :=
  A.policy_origin_bindings_preserved digest pre burnAction initial_policy_origin_bindings

end AdmissionWitness
