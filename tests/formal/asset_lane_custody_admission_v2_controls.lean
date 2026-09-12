import Proofs.AssetLaneCustodyAdmissionV2

set_option maxRecDepth 10000

namespace AdmissionSemanticControls

open Proofs GlobalEconomicStateRefinementV2

namespace A
export AssetLaneCustodyAdmissionV2
  (ConstructorAdmission ConstructorMetadata CustodyOrdered RecordSyntax
    RegistrationPolicySyntax)
end A
namespace B
export AssetLaneFiniteByteAccountingV2 (BalanceTokens SupplyTokens ValidToken)
end B
namespace C
export AssetLaneCustodyCompleteStateV2 (FullState Resources erase)
end C
namespace R
export AssetLaneCustodyRefinementV2 (RowsRepresentable physicalFor supplyAt)
end R
namespace X
export AssetLaneCustodyStructuralV2 (CompleteStructural)
end X
namespace FT
export AssetTransferFiniteOutcomeV2 (MetadataAdmission State)
end FT
namespace FM
export ManagedAssetFiniteOutcomeV2 (MetadataAdmission State)
end FM
namespace O
export AssetOriginRegistryRefinementV2
  (AssetClass Record RegistrationPolicy State opaqueRootA zeroRoot)
end O
namespace T
export AssetTransferRefinementV2 (AssetClass Policy)
end T

def rootSyntax (value : String) : Prop := value ≠ O.zeroRoot

def namespaceSyntax (_asset : String) (_assetClass : T.AssetClass) : Prop := True

instance rootSyntaxDecidable (value : String) : Decidable (rootSyntax value) := by
  unfold rootSyntax
  infer_instance

instance namespaceSyntaxDecidable (asset : String) (assetClass : T.AssetClass) :
    Decidable (namespaceSyntax asset assetClass) := by
  unfold namespaceSyntax
  infer_instance

instance validTokenDecidable (value : String) : Decidable (B.ValidToken value) := by
  unfold B.ValidToken
  infer_instance

instance balanceTokensDecidable (rows : List AmountRow) : Decidable (B.BalanceTokens rows) := by
  unfold B.BalanceTokens
  infer_instance

instance transferMetadataDecidable (state : FT.State) :
    Decidable (FT.MetadataAdmission rootSyntax namespaceSyntax state) := by
  unfold FT.MetadataAdmission
  infer_instance

instance managedMetadataDecidable (state : FM.State) :
    Decidable (FM.MetadataAdmission rootSyntax namespaceSyntax state) := by
  unfold FM.MetadataAdmission ManagedAssetFiniteOutcomeV2.PolicySyntax
  infer_instance

instance registrationPolicySyntaxDecidable (policy : O.RegistrationPolicy) :
    Decidable (A.RegistrationPolicySyntax rootSyntax policy) := by
  unfold A.RegistrationPolicySyntax
  infer_instance

instance custodyOrderedDecidable (state : C.FullState) : Decidable (A.CustodyOrdered state) := by
  unfold A.CustodyOrdered
  infer_instance

instance recordSyntaxDecidable (record : O.Record) :
    Decidable (A.RecordSyntax rootSyntax namespaceSyntax record) := by
  unfold A.RecordSyntax
  infer_instance

instance constructorMetadataDecidable (state : C.FullState) :
    Decidable (A.ConstructorMetadata rootSyntax namespaceSyntax state) := by
  unfold A.ConstructorMetadata
  infer_instance

def moduleRoot : String :=
  "0x2e33c221765009e5181427a67296d9a5c6f61d9483a4235b9bf5e7e2d282252f"

def originRoot : String :=
  "0x6d1f2f086dbcdda2adc8e9378930c2ffa775fdf4bba023dded9c0efa8f6ab8d5"

def transferPolicyRoot : String :=
  "0xaf0dd4470211b8f9b3f8cfbac520f84c632321f2e58ee34865dac6629928a54a"

def governanceGrantRoot : String :=
  "0x9c90b49f6987f4ef6bde9eb5e3314a5888f6c0508d1f443c30cbb77f0a24b0db"

def transferPolicy : T.Policy :=
  { asset := "USD"
    feeOwner := "treasury"
    transferFeeAtoms := 0
    enabled := true
    assetClass := .registeredOrdinaryToken
    assetOriginRoot := some originRoot
    atomDecimals := 8 }

def transfer : FT.State :=
  { moduleReleaseId := moduleRoot
    policies := [transferPolicy]
    balances := []
    supplies := [⟨"USD", 2⟩] }

def registry : O.State :=
  { moduleReleaseId := moduleRoot
    policy :=
      { authoritySubject := "governance"
        authorityGrantRoot := governanceGrantRoot
        allowNative := true
        allowTauOriginated := true }
    assets :=
      [{ asset := "USD"
         originKind := .tauOriginated
         originRoot := originRoot
         transferPolicyRoot := transferPolicyRoot
         issuePolicyRoot := O.zeroRoot
         decimals := 8
         assetClass := .registeredOrdinaryToken }] }

def custodyA : AmountRow :=
  { owner := "alice"
    asset := "USD"
    custodyDomain := "escrow"
    amountAtoms := 1 }

def custodyZ : AmountRow :=
  { owner := "zoe"
    asset := "USD"
    custodyDomain := "escrow"
    amountAtoms := 1 }

def sortedCustodyState : C.FullState :=
  { transfer := transfer
    originRegistry := registry
    managedPolicies := []
    custody := [custodyA, custodyZ] }

def reverseCustodyState : C.FullState :=
  { sortedCustodyState with custody := [custodyZ, custodyA] }

def nativeUnmanagedRecord : O.Record :=
  { asset := "TAU"
    originKind := .native
    originRoot := O.opaqueRootA
    transferPolicyRoot := O.opaqueRootA
    issuePolicyRoot := O.zeroRoot
    decimals := 8
    assetClass := .tauNativeCoin }

theorem sortedRows : R.RowsRepresentable (C.erase sortedCustodyState) := by
  refine {
    supplyUnique := ?_
    supplyOrdered := ?_
    supplyBounded := ?_
    registryKeys := rfl
    policyKeys := rfl
    managedCovered := ?_
    balanceUnique := ?_
    balancePositive := ?_
    custodyUnique := ?_
    custodyShape := ?_
    holdingsCovered := ?_
    balanced := ?_ }
  · unfold RegisteredSupplySupportV1.SourceAssetKeysUnique
    decide
  · unfold RegisteredSupplyUpdateV1.SourceAssetKeysOrdered
    decide
  · unfold RegisteredSupplySupportV1.SourceRowsU128 GlobalSettlementCoreV2.FitsU128
    decide
  · simp [C.erase, sortedCustodyState]
  · unfold AssetTransferSparseTablesV1.Unique
    decide
  · unfold AssetTransferSparseTablesV1.PositiveAccounts
    simp [C.erase, sortedCustodyState, transfer]
  · unfold AssetTransferSparseTablesV1.Unique
    decide
  · intro row member
    simp only [C.erase, sortedCustodyState, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    all_goals simp [custodyA, custodyZ, AssetTransferSparseTablesV1.accounts,
      GlobalSettlementCoreV2.FitsU128, GlobalSettlementCoreV2.maxU128]
  · intro row member
    simp only [C.erase, sortedCustodyState, transfer, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals decide
  · intro asset
    by_cases selected : asset = "USD"
    · subst asset
      decide
    · simp [R.physicalFor, R.supplyAt, C.erase, sortedCustodyState, transfer,
        custodyA, custodyZ,
        GlobalEconomicStateRefinementV2.amountForAsset,
        RegisteredSupplySupportV1.numericRows,
        RegisteredSupplySupportV1.nonzeroRow,
        RegisteredSupplySupportV1.toNumericRow,
        GlobalEconomicStateRefinementV2.supplyFor, Ne.symm selected]

theorem sortedComplete : X.CompleteStructural (C.erase sortedCustodyState) := by
  refine {
    rows := sortedRows
    policyShape := ?_
    managedPolicyOrdered := by decide
    balanceOrdered := by decide
    transferFeeOwnerTokens := ?_
    balanceTokens := ?_
    supplyTokens := ?_ }
  · constructor
    · intro policy member
      simp only [C.erase, sortedCustodyState, transfer, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst policy
      constructor
      · unfold AssetTransferRefinementV2.IsU128 transferPolicy
        decide
      · rfl
    · intro policy member
      simp only [C.erase, sortedCustodyState, List.not_mem_nil] at member
  · intro policy member
    simp only [C.erase, sortedCustodyState, transfer, List.mem_cons,
      List.not_mem_nil, or_false] at member
    subst policy
    decide
  · unfold B.BalanceTokens
    simp [C.erase, sortedCustodyState, transfer]
  · intro row member
    simp only [C.erase, sortedCustodyState, transfer, List.mem_cons,
      List.not_mem_nil, or_false] at member
    subst row
    decide

theorem reverseRows : R.RowsRepresentable (C.erase reverseCustodyState) := by
  refine {
    supplyUnique := ?_
    supplyOrdered := ?_
    supplyBounded := ?_
    registryKeys := rfl
    policyKeys := rfl
    managedCovered := ?_
    balanceUnique := ?_
    balancePositive := ?_
    custodyUnique := ?_
    custodyShape := ?_
    holdingsCovered := ?_
    balanced := ?_ }
  · unfold RegisteredSupplySupportV1.SourceAssetKeysUnique
    decide
  · unfold RegisteredSupplyUpdateV1.SourceAssetKeysOrdered
    decide
  · unfold RegisteredSupplySupportV1.SourceRowsU128 GlobalSettlementCoreV2.FitsU128
    decide
  · simp [C.erase, reverseCustodyState, sortedCustodyState]
  · unfold AssetTransferSparseTablesV1.Unique
    decide
  · unfold AssetTransferSparseTablesV1.PositiveAccounts
    simp [C.erase, reverseCustodyState, sortedCustodyState, transfer]
  · unfold AssetTransferSparseTablesV1.Unique
    decide
  · intro row member
    simp only [C.erase, reverseCustodyState, sortedCustodyState, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals simp [custodyA, custodyZ, AssetTransferSparseTablesV1.accounts,
      GlobalSettlementCoreV2.FitsU128, GlobalSettlementCoreV2.maxU128]
  · intro row member
    simp only [C.erase, reverseCustodyState, sortedCustodyState, transfer,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals decide
  · intro asset
    by_cases selected : asset = "USD"
    · subst asset
      decide
    · simp [R.physicalFor, R.supplyAt, C.erase, reverseCustodyState,
        sortedCustodyState, transfer, custodyA, custodyZ,
        GlobalEconomicStateRefinementV2.amountForAsset,
        RegisteredSupplySupportV1.numericRows,
        RegisteredSupplySupportV1.nonzeroRow,
        RegisteredSupplySupportV1.toNumericRow,
        GlobalEconomicStateRefinementV2.supplyFor, Ne.symm selected]

theorem reverseComplete : X.CompleteStructural (C.erase reverseCustodyState) := by
  refine {
    rows := reverseRows
    policyShape := sortedComplete.policyShape
    managedPolicyOrdered := sortedComplete.managedPolicyOrdered
    balanceOrdered := sortedComplete.balanceOrdered
    transferFeeOwnerTokens := sortedComplete.transferFeeOwnerTokens
    balanceTokens := sortedComplete.balanceTokens
    supplyTokens := sortedComplete.supplyTokens }

theorem sortedAdmission : A.ConstructorAdmission rootSyntax namespaceSyntax sortedCustodyState :=
  ⟨sortedComplete, by decide, by decide⟩

theorem reverseStructuralAndResources :
    X.CompleteStructural (C.erase reverseCustodyState) ∧ C.Resources reverseCustodyState :=
  ⟨reverseComplete, by decide⟩

example : A.ConstructorMetadata rootSyntax namespaceSyntax sortedCustodyState := by
  decide

example : ¬ A.CustodyOrdered reverseCustodyState := by
  decide

example : ¬ A.ConstructorMetadata rootSyntax namespaceSyntax reverseCustodyState := by
  decide

example : ¬ A.ConstructorAdmission rootSyntax namespaceSyntax reverseCustodyState := by
  intro admitted
  have rejected : ¬ A.ConstructorMetadata rootSyntax namespaceSyntax reverseCustodyState := by
    decide
  exact rejected admitted.2.1

example : ¬ rootSyntax O.zeroRoot := by
  decide

example : A.RecordSyntax rootSyntax namespaceSyntax nativeUnmanagedRecord := by
  decide

end AdmissionSemanticControls
