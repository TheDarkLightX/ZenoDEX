import Proofs.AssetLaneCustodyCompleteStateV2
import Proofs.AssetLaneCustodyExactProjectionV2

/-!
# Constructor and policy-origin admission over the complete custody state

This layer adds only predicates over fields `FullState` already owns. It stores
no second state, registry or key list, and has no acceptance Boolean.

`ConstructorMetadata` carries exactly the complete-state constructor conditions
that finite erasure cannot see: origin-registry validity, registry/transfer
release agreement, managed coverage by the assets of the registry records whose
issue root is not the zero root, transfer/managed identity agreement, the
existing transfer and managed leaf metadata admissions, registry record and
registration-policy syntax, and custody row tokens and canonical order.
Registry/transfer key agreement, row uniqueness, coverage and physical balance stay in
`CompleteStructural (erase state)`; the nine count and byte ceilings stay in
`Resources`.

`PolicyOriginBindings` is the separate coordinator guard over the same records
and policies. Its two commitment functions stay parameters, so no Lean
implementation of the runtime content hash is claimed; `rootSyntax`,
`namespaceSyntax` and `digest` are likewise uninterpreted parameters and
establish nothing about Python exact-type decoding, canonical bytes or root
authenticity. Root equality authenticates no registry and implies no preimage
equality.

Dormant zero-valued supplies and null optional policy origins remain admissible
exactly where the existing constructors permit them: the constructor conditions
relate optional origins only to each other, while the origin bindings require a
present origin, as the two runtime validators do.

Post-state resources are an explicit premise, never a consequence of pre-state
resources or leaf acceptance. These results reach the post-construction and
exact reprojection boundary only. They do not establish source journal/effect
binding, the account-conservation projection, journal or receipt construction,
hashing, publication or production authority.
-/

set_option warningAsError true

namespace Proofs.AssetLaneCustodyAdmissionV2

attribute [local instance] lexOrd

open AssetLaneCustodyCompleteStateV2 (FullState erase step Resources erase_step
  erase_transfer_source step_metadata step_transfer_metadata)

namespace E
export AssetLaneCustodyEffectPlanV2 (transferSource managedSource)
end E
namespace F
export AssetLaneCustodyFiniteTraceV2 (Action)
end F
namespace X
export AssetLaneCustodyStructuralV2 (CompleteStructural ActionAdmission
  step_preserves_complete)
end X
namespace P
export AssetLaneCustodyExactProjectionV2 (transfer_accepted_step_exact
  managed_accepted_step_exact)
end P
namespace FT
export AssetTransferFiniteOutcomeV2 (State MetadataAdmission transition)
end FT
namespace FM
export ManagedAssetFiniteOutcomeV2 (State MetadataAdmission transition)
end FM
namespace T
export AssetTransferRefinementV2 (AssetClass Policy Context Command)
end T
namespace M
export ManagedAssetLifecycleRefinementV2 (Policy Context Command)
end M
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes ValidToken BalanceTokens)
end B
namespace O
export AssetOriginRegistryRefinementV2 (AssetClass Record RegistrationPolicy ValidState
  zeroRoot)
end O

/-- The six registry asset classes as the shared transfer/managed policy
classes. This conversion is the only class glue this layer adds. -/
def assetClassOf : O.AssetClass → T.AssetClass
  | .tauNativeCoin => .tauNativeCoin
  | .canonicalZusd => .canonicalZusd
  | .lpShare => .lpShare
  | .zdexProtocolToken => .zdexProtocolToken
  | .sealedBidPaymentOrInventory => .sealedBidPaymentOrInventory
  | .registeredOrdinaryToken => .registeredOrdinaryToken

/-- Registry-record syntax under the nonzero root syntax used by the leaf
metadata predicates. The issue root separately permits the runtime zero sentinel. -/
def RecordSyntax (rootSyntax : String → Prop)
    (namespaceSyntax : String → T.AssetClass → Prop) (record : O.Record) : Prop :=
  B.ValidToken record.asset ∧ namespaceSyntax record.asset (assetClassOf record.assetClass) ∧
    B.ValidToken record.originRoot ∧ rootSyntax record.originRoot ∧
    B.ValidToken record.transferPolicyRoot ∧ rootSyntax record.transferPolicyRoot ∧
    B.ValidToken record.issuePolicyRoot ∧
    (record.issuePolicyRoot = O.zeroRoot ∨ rootSyntax record.issuePolicyRoot)

/-- Runtime custody keys are ordered by asset, owner, then custody domain. -/
def CustodyOrdered (state : FullState) : Prop :=
  state.custody.Pairwise (fun left right =>
    compare (left.asset, left.owner, left.custodyDomain)
      (right.asset, right.owner, right.custodyDomain) = .lt)

/-- Registration-policy subject and grant-root syntax. -/
def RegistrationPolicySyntax (rootSyntax : String → Prop)
    (policy : O.RegistrationPolicy) : Prop :=
  B.ValidToken policy.authoritySubject ∧ B.ValidToken policy.authorityGrantRoot ∧
    rootSyntax policy.authorityGrantRoot

/-- The complete-state constructor conditions omitted by finite erasure. The
managed/transfer identity condition compares optional origins to each other, so
a pair of null origins is admitted. -/
def ConstructorMetadata (rootSyntax : String → Prop)
    (namespaceSyntax : String → T.AssetClass → Prop) (state : FullState) : Prop :=
  O.ValidState state.originRegistry ∧
    state.originRegistry.moduleReleaseId = state.transfer.moduleReleaseId ∧
    state.managedPolicies.map (fun policy => policy.asset) =
      (state.originRegistry.assets.filter
        (fun record => record.issuePolicyRoot != O.zeroRoot)).map (fun record => record.asset) ∧
    (∀ policy ∈ state.managedPolicies, ∃ leaf ∈ state.transfer.policies,
      leaf.asset = policy.asset ∧ leaf.assetClass = policy.assetClass ∧
        leaf.assetOriginRoot = policy.assetOriginRoot ∧
        leaf.atomDecimals = policy.atomDecimals) ∧
    FT.MetadataAdmission rootSyntax namespaceSyntax state.transfer ∧
    FM.MetadataAdmission rootSyntax namespaceSyntax (E.managedSource (erase state)) ∧
    (∀ record ∈ state.originRegistry.assets,
      RecordSyntax rootSyntax namespaceSyntax record) ∧
    RegistrationPolicySyntax rootSyntax state.originRegistry.policy ∧
    B.BalanceTokens state.custody ∧ CustodyOrdered state

/-- Structural policy-origin membership for both owned policy lists against the
existing registry records. The two commitment functions are parameters: this
claims no Lean recomputation of the runtime policy roots, and root equality
carries no authentication. A present origin is required, as the runtime
validators require. Runtime lookup equivalence also uses the unique registry
assets supplied by `ConstructorAdmission`; membership alone on an arbitrary
`FullState` does not establish that equivalence. -/
def PolicyOriginBindings (transferCommit : T.Policy → String)
    (managedCommit : M.Policy → String) (state : FullState) : Prop :=
  (∀ policy ∈ state.transfer.policies, ∃ record ∈ state.originRegistry.assets,
      record.asset = policy.asset ∧ assetClassOf record.assetClass = policy.assetClass ∧
        policy.assetOriginRoot = some record.originRoot ∧
        record.decimals = policy.atomDecimals ∧
        record.transferPolicyRoot = transferCommit policy) ∧
    (∀ policy ∈ state.managedPolicies, ∃ record ∈ state.originRegistry.assets,
      record.asset = policy.asset ∧ assetClassOf record.assetClass = policy.assetClass ∧
        policy.assetOriginRoot = some record.originRoot ∧
        record.decimals = policy.atomDecimals ∧
        record.issuePolicyRoot ≠ O.zeroRoot ∧
        record.issuePolicyRoot = managedCommit policy)

/-- Complete constructor admission is exactly the existing structural predicate,
the added constructor metadata, and the existing resource ceilings. -/
def ConstructorAdmission (rootSyntax : String → Prop)
    (namespaceSyntax : String → T.AssetClass → Prop) (state : FullState) : Prop :=
  X.CompleteStructural (erase state) ∧
    ConstructorMetadata rootSyntax namespaceSyntax state ∧ Resources state

private theorem transfer_metadata_of_frame {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} {pre post : FT.State}
    (release : post.moduleReleaseId = pre.moduleReleaseId)
    (policies : post.policies = pre.policies)
    (metadata : FT.MetadataAdmission rootSyntax namespaceSyntax pre) :
    FT.MetadataAdmission rootSyntax namespaceSyntax post := by
  unfold FT.MetadataAdmission at metadata ⊢
  rw [release, policies]
  exact metadata

private theorem managed_metadata_of_frame {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} {pre post : FM.State}
    (release : post.moduleReleaseId = pre.moduleReleaseId)
    (policies : post.policies = pre.policies)
    (metadata : FM.MetadataAdmission rootSyntax namespaceSyntax pre) :
    FM.MetadataAdmission rootSyntax namespaceSyntax post := by
  unfold FM.MetadataAdmission at metadata ⊢
  rw [release, policies]
  exact metadata

/-- Constructor metadata reads only the immutable custody frame: transfer
release and policies, the registry, the managed policies and the custody rows. -/
private theorem metadata_of_frame {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} {pre post : FullState}
    (release : post.transfer.moduleReleaseId = pre.transfer.moduleReleaseId)
    (policies : post.transfer.policies = pre.transfer.policies)
    (registry : post.originRegistry = pre.originRegistry)
    (managed : post.managedPolicies = pre.managedPolicies)
    (custody : post.custody = pre.custody)
    (metadata : ConstructorMetadata rootSyntax namespaceSyntax pre) :
    ConstructorMetadata rootSyntax namespaceSyntax post := by
  unfold ConstructorMetadata at metadata ⊢
  obtain ⟨valid, releases, coverage, identities, transferSyntax, managedSyntax,
    recordSyntax, policySyntax, custodyTokens, custodyOrder⟩ := metadata
  refine ⟨?_, ?_, ?_, ?_,
    transfer_metadata_of_frame (pre := pre.transfer) release policies transferSyntax,
    managed_metadata_of_frame (pre := E.managedSource (erase pre)) release managed
      managedSyntax, ?_, ?_, ?_, ?_⟩
  · rw [registry]
    exact valid
  · rw [registry, release]
    exact releases
  · rw [managed, registry]
    exact coverage
  · rw [managed, policies]
    exact identities
  · rw [registry]
    exact recordSyntax
  · rw [registry]
    exact policySyntax
  · rw [custody]
    exact custodyTokens
  · simpa only [CustodyOrdered, custody] using custodyOrder

/-- The coordinator policy-origin guard quantifies only over the immutable
registry records and policy lists, so one actual finite step preserves it. It
neither follows from nor implies constructor admission. -/
theorem policy_origin_bindings_preserved {transferCommit : T.Policy → String}
    {managedCommit : M.Policy → String} (digest : B.Bytes → String) (pre : FullState)
    (action : F.Action) (h : PolicyOriginBindings transferCommit managedCommit pre) :
    PolicyOriginBindings transferCommit managedCommit (step digest pre action) := by
  have frame := step_metadata digest pre action
  unfold PolicyOriginBindings at h ⊢
  rw [(step_transfer_metadata digest pre action).2, frame.1, frame.2.1]
  exact h

/-- One actual finite step preserves complete constructor admission. Structure
comes from the existing preservation theorem and metadata from the fixed frame,
while the post-state resource decision stays an explicit outer premise because
pre-state resources and leaf acceptance do not imply it. -/
theorem step_preserves_constructor_admission {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → String)
    {pre : FullState} {action : F.Action}
    (h : ConstructorAdmission rootSyntax namespaceSyntax pre)
    (input : X.ActionAdmission action)
    (postFits : Resources (step digest pre action)) :
    ConstructorAdmission rootSyntax namespaceSyntax (step digest pre action) := by
  have transferFrame := step_transfer_metadata digest pre action
  have frame := step_metadata digest pre action
  refine ⟨?_, metadata_of_frame (pre := pre) transferFrame.1 transferFrame.2 frame.1
    frame.2.1 frame.2.2 h.2.1, postFits⟩
  rw [erase_step]
  exact X.step_preserves_complete digest h.1 input

/-- An accepted transfer leaf is reprojected exactly by the retained complete
transfer payload, rather than by an independently supplied successor. -/
theorem transfer_accepted_full_projection {digest : B.Bytes → String} {pre : FullState}
    {context : T.Context} {command : T.Command}
    (accepted : (FT.transition digest context pre.transfer command).verdict = .accepted) :
    (step digest pre (.transfer context command)).transfer =
      (FT.transition digest context pre.transfer command).post := by
  have source : (FT.transition digest context (E.transferSource (erase pre)) command).verdict =
      .accepted := by
    rw [erase_transfer_source]
    exact accepted
  have projected := P.transfer_accepted_step_exact source
  rw [erase_transfer_source] at projected
  exact projected

/-- An accepted managed leaf is recovered exactly from the complete post,
including every managed sibling and dormant zero-valued supply row. -/
theorem managed_accepted_full_projection {digest : B.Bytes → String} {pre : FullState}
    {context : M.Context} {command : M.Command}
    (structural : X.CompleteStructural (erase pre))
    (input : X.ActionAdmission (.managed context command))
    (accepted : (FM.transition digest context (E.managedSource (erase pre)) command).verdict =
      .accepted) :
    E.managedSource (erase (step digest pre (.managed context command))) =
      (FM.transition digest context (E.managedSource (erase pre)) command).post := by
  rw [erase_step]
  exact P.managed_accepted_step_exact structural input accepted

end Proofs.AssetLaneCustodyAdmissionV2
