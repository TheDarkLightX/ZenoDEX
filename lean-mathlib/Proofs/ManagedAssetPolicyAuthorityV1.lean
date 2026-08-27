/-!
# Managed ordinary-token issue and self-burn — authority core V1

A machine-checked model of the *authorization decision* for the two generic
managed-asset commands of `transition_managed_asset_lifecycle_v1` in
`src/core/managed_asset_lifecycle_module_v1.py` (mirrored by
`zk/global_settlement_abi_v1/src/managed_asset_lifecycle.rs`), together with the
policy-registry-root binding that `src/core/asset_lane_coordinator_v1.py` checks
on the lane projection. Everything here is an abstraction chosen to be provable;
the gap to the runtime is spelled out below rather than left implicit.

## The modeled surface

Exactly one decision: *may this context act on this command against this state
under this active profile*. Eight things are modeled and nothing else:

* the **exact command kind**, as a two-element closed enumeration plus a parser
  from the raw wire string. `MANAGED_ASSET_ISSUE_COMMAND_KIND_V1` and
  `MANAGED_ASSET_BURN_COMMAND_KIND_V1` are the only two accepted strings;
* the **active profile policy binding**: the profile snapshot must be `ACTIVE`,
  the context must name that profile, and the presented policy-registry root
  must be the root the profile governs (`EconomicProfileSnapshotV1.status`,
  `.profile_id`, `.policy_registry_root`);
* the **typed managed policy registry root**: the registry value carried by the
  module state declares a root, and that declared root must equal the presented
  root (the lane input's `asset_policy_registry_root`, compared by the
  coordinator's `POLICY_ROOT_MISMATCH` check);
* the **unique asset member**: the policy used must be a member of that registry
  and the *only* member naming the command's asset. The Python constructor
  enforces this with `_require_ordered_objects(..., key="asset")`; here it is a
  typed witness (`UniqueMember`) that the deterministic lookup produces from an
  explicit no-duplicate premise;
* the **module release**: `ManagedAssetLifecycleContextV1.module_release_id` must
  equal `ManagedAssetLifecycleStateV1.module_release_id`;
* the **subject**: `ManagedAssetLifecycleContextV1.subject_id`;
* the **owner**: `ManagedAssetLifecycleCommandV1.account_owner`;
* the **grant**: `ManagedAssetLifecycleContextV1.grant_root`.

The kind-specific rule is the point of the file. For issue, the subject must be
the policy's named issue-authority subject and the grant must be the policy's
issue policy root. For self-burn, the subject must be the command's own account
owner and the grant must be the policy's self-burn policy root.

These obligations are an **unordered conjunction**. The runtime spreads the
corresponding checks across three layers — profile activation in the commit
path, the profile and policy-registry roots in the asset lane coordinator, and
the release, kind, member, class, subject, and grant in the lifecycle module —
and it returns the *first* failing check as a typed code. Neither that layering
nor that precedence is modeled here, and no theorem below says which layer
enforces which obligation.

## Making the paired authority unrepresentable

`ManagedAssetLifecyclePolicyV1` stores `issue_authority_subject` and
`issue_policy_root` as two independent `str | None` fields and repairs the
pairing with a runtime cross-field check (`_require_optional_authority`). Here
the pair is one typed value, `Option IssueAuthority`, so a policy naming a
subject without a root, or a root without a subject, cannot be written down.
`IssueAuthorityMatches` is then a single equality against
`some ⟨ctx.subject, ctx.grantRoot⟩`: a check that matched the subject while
ignoring the root is not expressible as a weakening of that equality.

## Deterministic checker and typed witness

`authorizes` is a total `Bool` checker over the modeled fields. `Authorized` is
the typed witness with one field per modeled obligation.
`authorizes_eq_true_iff` proves the checker decides exactly the witness, under
the state well-formedness premise `NoDuplicateAssets`. The checker owns
promotion; every pinning theorem below reads the witness.

## Roots are opaque identifiers

`Root` is `String`. Roots are compared by equality and nothing else. No hash is
computed, and **no cryptographic property is claimed**: not preimage
resistance, not collision resistance, and not injectivity from a root to the
registry contents it names. Two distinct registries may carry the same declared
`registryRoot` in this model. Every theorem that "pins the registry" pins the
registry *value the checker consulted* together with the equality of its
declared root to the profile-governed root. Recovering the registry contents
from the root is exactly the step this file does not take, and
`staleRegistrySharingRoot` in the challenge module is the concrete reason the
module-release check stays load-bearing.

## Not modeled at all

No amounts, balances, supplies, or supply/balance ceilings; no `u128` or `i128`
width discipline; no conservation, effect rows, or asset conservation rows; no
canonical ordering, deduplication, or byte encoding; no state roots, effect plan
roots, private ports, journals, or receipts; no `chain_id`, `deployment_root`,
`writer_epoch`, `command_occurrence_id`, or replay and occurrence discipline; no
fee policy registry; no signature or authentication derivation; no cross-layer
composition of the commit path, the lane coordinator, and the lifecycle module;
and no `ManagedAssetLifecycleRejectCodeV1` enumeration, wire strings, or
rejection precedence. Rejection here is the *absence* of a witness, stated as
the implications in section 9, not a code.

## Accounting wording

`accountsLocation` is the accounting-location label the managed-asset rows carry
(`ACCOUNT_CUSTODY_DOMAIN_V1`, value `"accounts"`). It is an accounting location
and an accounting control domain label only. Nothing in this file asserts
custody, possession, title, control, key control, or any enforceable claim over
any asset by any party. Practical control of an asset follows key control, which
is outside this file entirely; `accountsLocation` is read by no theorem here.

## What is NOT claimed

No cryptographic injectivity of any root or identifier; no refinement between
this model and the Python or Rust runtime; no settlement, conservation, or
replay safety; no economic-policy correctness; no release, migration,
publication, or value-moving authority; and no production readiness. This is
research-only structural evidence about one authorization predicate.
-/

namespace Proofs
namespace ManagedAssetPolicyAuthorityV1

/-! ## 1. Opaque identifiers

Uninterpreted tokens. The runtime's token syntax (`_require_token`) and root
syntax (`_require_root`, 66-character lowercase `0x`-prefixed hex) are not
modeled: a `String` here may be empty, oversized, or non-ASCII. -/

abbrev Root := String
abbrev Subject := String
abbrev Asset := String
abbrev AccountingLocation := String

/-- The accounting-location label managed-asset rows carry
(`ACCOUNT_CUSTODY_DOMAIN_V1`). Accounting label only; no theorem reads it and
nothing here asserts custody, possession, title, control, or key control. -/
def accountsLocation : AccountingLocation := "accounts"

/-! ## 2. Exact command kind

The closed pair `{MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
MANAGED_ASSET_BURN_COMMAND_KIND_V1}`, plus the parser from the raw wire string
carried by `ManagedAssetLifecycleCommandV1.command_kind`. -/

/-- The two generic managed-asset command kinds. -/
inductive CommandKind where
  | issue
  | burn
  deriving DecidableEq, Repr

/-- The stable wire string for each kind. -/
def CommandKind.code : CommandKind → String
  | .issue => "managed_asset_issue"
  | .burn => "managed_asset_burn"

def allCommandKinds : List CommandKind := [.issue, .burn]

theorem allCommandKinds_length : allCommandKinds.length = 2 := rfl

theorem allCommandKinds_codes :
    allCommandKinds.map CommandKind.code =
      ["managed_asset_issue", "managed_asset_burn"] := rfl

/-- The enumeration is complete: there is no third generic kind. -/
theorem allCommandKinds_complete (k : CommandKind) : k ∈ allCommandKinds := by
  cases k <;> decide

theorem issue_ne_burn : CommandKind.issue ≠ CommandKind.burn := by decide

theorem issue_code_ne_burn_code :
    CommandKind.issue.code ≠ CommandKind.burn.code := by decide

theorem CommandKind.code_injective {a b : CommandKind} (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h (by decide)

/-- The wire-kind parser. Only the two exact strings are accepted. -/
def parseCommandKind (s : String) : Option CommandKind :=
  if s = CommandKind.issue.code then some CommandKind.issue
  else if s = CommandKind.burn.code then some CommandKind.burn
  else none

theorem parseCommandKind_code (k : CommandKind) : parseCommandKind k.code = some k := by
  cases k <;> decide

/-- Exactness of the kind: a wire string parses to a kind iff it *is* that
kind's code. -/
theorem parseCommandKind_eq_some_iff {s : String} {k : CommandKind} :
    parseCommandKind s = some k ↔ s = k.code := by
  constructor
  · intro h
    unfold parseCommandKind at h
    by_cases h1 : s = CommandKind.issue.code
    · rw [if_pos h1, Option.some.injEq] at h
      rw [← h]
      exact h1
    · rw [if_neg h1] at h
      by_cases h2 : s = CommandKind.burn.code
      · rw [if_pos h2, Option.some.injEq] at h
        rw [← h]
        exact h2
      · rw [if_neg h2] at h
        simp at h
  · intro h
    subst h
    exact parseCommandKind_code k

/-- One wire string never names both kinds. This is the wire-level half of the
issue-versus-burn confusion exclusion. -/
theorem parseCommandKind_no_kind_confusion (s : String) :
    ¬ (parseCommandKind s = some CommandKind.issue ∧
       parseCommandKind s = some CommandKind.burn) := by
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ## 3. Asset class

`ManagedAssetClassV1`. Only `REGISTERED_ORDINARY_TOKEN` may carry the generic
issue and self-burn authority; every other class must route supply changes
through its own named economic transition. -/

inductive AssetClass where
  | tauNativeCoin
  | canonicalZusd
  | lpShare
  | zdexProtocolToken
  | sealedBidPaymentOrInventory
  | registeredOrdinaryToken
  deriving DecidableEq, Repr

def AssetClass.code : AssetClass → String
  | .tauNativeCoin => "tau_native_coin"
  | .canonicalZusd => "canonical_zusd"
  | .lpShare => "lp_share"
  | .zdexProtocolToken => "zdex_protocol_token"
  | .sealedBidPaymentOrInventory => "sealed_bid_payment_or_inventory"
  | .registeredOrdinaryToken => "registered_ordinary_token"

def allAssetClasses : List AssetClass :=
  [ .tauNativeCoin, .canonicalZusd, .lpShare, .zdexProtocolToken,
    .sealedBidPaymentOrInventory, .registeredOrdinaryToken ]

theorem allAssetClasses_length : allAssetClasses.length = 6 := rfl

theorem allAssetClasses_codes :
    allAssetClasses.map AssetClass.code =
      [ "tau_native_coin", "canonical_zusd", "lp_share", "zdex_protocol_token",
        "sealed_bid_payment_or_inventory", "registered_ordinary_token" ] := rfl

theorem allAssetClasses_complete (c : AssetClass) : c ∈ allAssetClasses := by
  cases c <;> decide

/-! ## 4. Policies and the typed registry

The generic issue authority is one typed value, so the runtime's cross-field
"subject and policy root must be present together" invariant is unrepresentable
here rather than checked. -/

/-- The paired generic issue authority: a named subject *and* the policy root
that subject must present. Neither half exists without the other. -/
structure IssueAuthority where
  subject : Subject
  policyRoot : Root
  deriving DecidableEq, Repr

/-- One `ManagedAssetLifecyclePolicyV1`, restricted to the authority fields. -/
structure ManagedPolicy where
  asset : Asset
  assetClass : AssetClass
  issueAuthority : Option IssueAuthority
  selfBurnPolicyRoot : Option Root
  enabled : Bool
  deriving DecidableEq, Repr

/-- A managed policy registry: a declared root and its members. The root is an
opaque identifier; it is *not* computed from `members` and does not determine
them. See the header. -/
structure ManagedPolicyRegistry where
  registryRoot : Root
  members : List ManagedPolicy
  deriving DecidableEq, Repr

/-- The state well-formedness the Python constructor establishes with
`_require_ordered_objects(..., key="asset")`: at most one policy per asset. -/
def NoDuplicateAssets (ps : List ManagedPolicy) : Prop :=
  ∀ p ∈ ps, ∀ q ∈ ps, p.asset = q.asset → p = q

instance decidableNoDuplicateAssets (ps : List ManagedPolicy) :
    Decidable (NoDuplicateAssets ps) :=
  inferInstanceAs (Decidable (∀ p ∈ ps, ∀ q ∈ ps, p.asset = q.asset → p = q))

/-- The deterministic member lookup, mirroring the runtime's first-match scan
over `state.policies`. -/
def lookupPolicy (asset : Asset) : List ManagedPolicy → Option ManagedPolicy
  | [] => none
  | p :: rest => if p.asset = asset then some p else lookupPolicy asset rest

/-- The typed unique-member witness: `p` is a member of the registry, it names
the asset, and it is the only member that does. -/
structure UniqueMember (r : ManagedPolicyRegistry) (a : Asset) (p : ManagedPolicy) : Prop where
  mem : p ∈ r.members
  asset : p.asset = a
  unique : ∀ q ∈ r.members, q.asset = a → q = p

theorem lookupPolicy_mem {a : Asset} :
    ∀ {ps : List ManagedPolicy} {p : ManagedPolicy}, lookupPolicy a ps = some p → p ∈ ps
  | [], _, h => by simp [lookupPolicy] at h
  | q :: rest, p, h => by
      simp only [lookupPolicy] at h
      split at h
      · rw [Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem q (lookupPolicy_mem h)

theorem lookupPolicy_asset {a : Asset} :
    ∀ {ps : List ManagedPolicy} {p : ManagedPolicy}, lookupPolicy a ps = some p → p.asset = a
  | [], _, h => by simp [lookupPolicy] at h
  | q :: rest, p, h => by
      simp only [lookupPolicy] at h
      split at h
      · next hq =>
          rw [Option.some.injEq] at h
          subst h
          exact hq
      · exact lookupPolicy_asset h

theorem lookupPolicy_ne_none_of_mem {a : Asset} :
    ∀ {ps : List ManagedPolicy} {p : ManagedPolicy}, p ∈ ps → p.asset = a →
      lookupPolicy a ps ≠ none
  | [], _, h, _ => by simp at h
  | q :: rest, p, hmem, hasset => by
      simp only [lookupPolicy]
      by_cases hq : q.asset = a
      · rw [if_pos hq]
        simp
      · rw [if_neg hq]
        rcases List.mem_cons.mp hmem with rfl | h
        · exact absurd hasset hq
        · exact lookupPolicy_ne_none_of_mem h hasset

/-- Under the no-duplicate premise the deterministic lookup produces the typed
unique-member witness. -/
theorem uniqueMember_of_lookup {r : ManagedPolicyRegistry} {a : Asset} {p : ManagedPolicy}
    (hnd : NoDuplicateAssets r.members) (hl : lookupPolicy a r.members = some p) :
    UniqueMember r a p :=
  { mem := lookupPolicy_mem hl
    asset := lookupPolicy_asset hl
    unique := fun q hq hqa =>
      hnd q hq p (lookupPolicy_mem hl) (hqa.trans (lookupPolicy_asset hl).symm) }

/-- Conversely the witness pins the lookup result exactly. -/
theorem lookupPolicy_eq_some_of_uniqueMember {r : ManagedPolicyRegistry} {a : Asset}
    {p : ManagedPolicy} (h : UniqueMember r a p) : lookupPolicy a r.members = some p := by
  cases hl : lookupPolicy a r.members with
  | none => exact absurd hl (lookupPolicy_ne_none_of_mem h.mem h.asset)
  | some q =>
      rw [h.unique q (lookupPolicy_mem hl) (lookupPolicy_asset hl)]

/-- The unique-member witness is unique. -/
theorem uniqueMember_unique {r : ManagedPolicyRegistry} {a : Asset} {p q : ManagedPolicy}
    (hp : UniqueMember r a p) (hq : UniqueMember r a q) : p = q :=
  hq.unique p hp.mem hp.asset

/-! ## 5. Profile, state, context, command

The deciding fields only. `EconomicProfileSnapshotV1`'s lane, coordinator,
route, verifier, migration, and terminal registries, its proof shape root, root
image id, and authority epoch are not modeled, and `profile_id` is *not* proved
here to be the exact content-derived id. -/

/-- `ProfileStatusV1`. -/
inductive ProfileStatus where
  | candidate
  | shadow
  | active
  | retired
  | revoked
  deriving DecidableEq, Repr

def ProfileStatus.code : ProfileStatus → String
  | .candidate => "CANDIDATE"
  | .shadow => "SHADOW"
  | .active => "ACTIVE"
  | .retired => "RETIRED"
  | .revoked => "REVOKED"

def allProfileStatuses : List ProfileStatus :=
  [ .candidate, .shadow, .active, .retired, .revoked ]

theorem allProfileStatuses_codes :
    allProfileStatuses.map ProfileStatus.code =
      ["CANDIDATE", "SHADOW", "ACTIVE", "RETIRED", "REVOKED"] := rfl

theorem allProfileStatuses_complete (s : ProfileStatus) : s ∈ allProfileStatuses := by
  cases s <;> decide

/-- The governance side: which profile is active and which managed policy
registry root it governs. -/
structure ProfileSnapshot where
  profileRoot : Root
  managedPolicyRegistryRoot : Root
  status : ProfileStatus
  deriving DecidableEq, Repr

/-- The authority projection of `ManagedAssetLifecycleStateV1`: the module
release and the typed policy registry. Balances and supplies are out of scope. -/
structure ModuleState where
  moduleReleaseId : Root
  registry : ManagedPolicyRegistry
  deriving DecidableEq, Repr

/-- The deciding fields of `ManagedAssetLifecycleContextV1` together with the
lane input's `asset_policy_registry_root`. -/
structure Context where
  profileRoot : Root
  policyRegistryRoot : Root
  moduleReleaseId : Root
  subject : Subject
  grantRoot : Root
  deriving DecidableEq, Repr

/-- The authority projection of `ManagedAssetLifecycleCommandV1`. The raw wire
kind is kept unparsed so that "unknown command" stays representable. -/
structure Command where
  commandKind : String
  asset : Asset
  accountOwner : Subject
  deriving DecidableEq, Repr

/-! ## 6. The kind-specific grant rule

The whole point of the pairing in `IssueAuthority`: the issue rule is a *single*
equality binding the subject and the grant together. -/

/-- Issue: the policy's paired authority is exactly the subject and grant the
context presents. -/
def IssueAuthorityMatches (ctx : Context) (policy : ManagedPolicy) : Prop :=
  policy.issueAuthority = some ⟨ctx.subject, ctx.grantRoot⟩

/-- Self-burn: the subject is the command's own account owner and the grant is
the policy's self-burn policy root. -/
def SelfBurnGrantMatches (ctx : Context) (cmd : Command) (policy : ManagedPolicy) : Prop :=
  ctx.subject = cmd.accountOwner ∧ policy.selfBurnPolicyRoot = some ctx.grantRoot

instance decidableIssueAuthorityMatches (ctx : Context) (policy : ManagedPolicy) :
    Decidable (IssueAuthorityMatches ctx policy) :=
  inferInstanceAs (Decidable (policy.issueAuthority = some ⟨ctx.subject, ctx.grantRoot⟩))

instance decidableSelfBurnGrantMatches (ctx : Context) (cmd : Command) (policy : ManagedPolicy) :
    Decidable (SelfBurnGrantMatches ctx cmd policy) :=
  inferInstanceAs
    (Decidable (ctx.subject = cmd.accountOwner ∧ policy.selfBurnPolicyRoot = some ctx.grantRoot))

/-- The grant rule selected by the exact command kind. -/
def GrantMatches (ctx : Context) (cmd : Command) (kind : CommandKind)
    (policy : ManagedPolicy) : Prop :=
  match kind with
  | .issue => IssueAuthorityMatches ctx policy
  | .burn => SelfBurnGrantMatches ctx cmd policy

instance decidableGrantMatches (ctx : Context) (cmd : Command) (kind : CommandKind)
    (policy : ManagedPolicy) : Decidable (GrantMatches ctx cmd kind policy) :=
  match kind with
  | .issue => decidableIssueAuthorityMatches ctx policy
  | .burn => decidableSelfBurnGrantMatches ctx cmd policy

theorem grantMatches_issue (ctx : Context) (cmd : Command) (policy : ManagedPolicy) :
    GrantMatches ctx cmd CommandKind.issue policy = IssueAuthorityMatches ctx policy := rfl

theorem grantMatches_burn (ctx : Context) (cmd : Command) (policy : ManagedPolicy) :
    GrantMatches ctx cmd CommandKind.burn policy = SelfBurnGrantMatches ctx cmd policy := rfl

/-! ## 7. The typed authorization witness and the deterministic checker -/

/-- One obligation per modeled field. There is no other constructor, so an
authorization that skipped any of these is not expressible. -/
structure Authorized (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context)
    (cmd : Command) (kind : CommandKind) (policy : ManagedPolicy) : Prop where
  profileActive : profile.status = ProfileStatus.active
  profileNamed : ctx.profileRoot = profile.profileRoot
  registryRootGoverned : ctx.policyRegistryRoot = profile.managedPolicyRegistryRoot
  registryRootBound : st.registry.registryRoot = ctx.policyRegistryRoot
  releaseMatched : ctx.moduleReleaseId = st.moduleReleaseId
  kindExact : parseCommandKind cmd.commandKind = some kind
  member : UniqueMember st.registry cmd.asset policy
  ordinaryClass : policy.assetClass = AssetClass.registeredOrdinaryToken
  enabled : policy.enabled = true
  grantMatched : GrantMatches ctx cmd kind policy

/-- The context-and-policy half of the checker, once the kind has parsed and the
member has been found. -/
def contextAuthorizes (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context)
    (cmd : Command) (kind : CommandKind) (policy : ManagedPolicy) : Bool :=
  decide (profile.status = ProfileStatus.active) &&
  decide (ctx.profileRoot = profile.profileRoot) &&
  decide (ctx.policyRegistryRoot = profile.managedPolicyRegistryRoot) &&
  decide (st.registry.registryRoot = ctx.policyRegistryRoot) &&
  decide (ctx.moduleReleaseId = st.moduleReleaseId) &&
  decide (policy.assetClass = AssetClass.registeredOrdinaryToken) &&
  policy.enabled &&
  decide (GrantMatches ctx cmd kind policy)

/-- The total deterministic authorization checker. -/
def authorizes (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context)
    (cmd : Command) : Bool :=
  match parseCommandKind cmd.commandKind with
  | none => false
  | some kind =>
    match lookupPolicy cmd.asset st.registry.members with
    | none => false
    | some policy => contextAuthorizes profile st ctx cmd kind policy

theorem contextAuthorizes_eq_true_iff (profile : ProfileSnapshot) (st : ModuleState)
    (ctx : Context) (cmd : Command) (kind : CommandKind) (policy : ManagedPolicy) :
    contextAuthorizes profile st ctx cmd kind policy = true ↔
      profile.status = ProfileStatus.active ∧
      ctx.profileRoot = profile.profileRoot ∧
      ctx.policyRegistryRoot = profile.managedPolicyRegistryRoot ∧
      st.registry.registryRoot = ctx.policyRegistryRoot ∧
      ctx.moduleReleaseId = st.moduleReleaseId ∧
      policy.assetClass = AssetClass.registeredOrdinaryToken ∧
      policy.enabled = true ∧
      GrantMatches ctx cmd kind policy := by
  simp only [contextAuthorizes, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- The checker decides exactly the typed witness. `NoDuplicateAssets` is the
state well-formedness premise the runtime constructor establishes; without it a
registry could carry two policies for one asset and the lookup would silently
pick the first. -/
theorem authorizes_eq_true_iff (profile : ProfileSnapshot) (st : ModuleState)
    (ctx : Context) (cmd : Command) (hnd : NoDuplicateAssets st.registry.members) :
    authorizes profile st ctx cmd = true ↔
      ∃ (kind : CommandKind) (policy : ManagedPolicy),
        Authorized profile st ctx cmd kind policy := by
  cases hk : parseCommandKind cmd.commandKind with
  | none =>
      constructor
      · intro h
        simp [authorizes, hk] at h
      · rintro ⟨kind, policy, hA⟩
        rw [hA.kindExact] at hk
        simp at hk
  | some kind =>
      cases hl : lookupPolicy cmd.asset st.registry.members with
      | none =>
          constructor
          · intro h
            simp [authorizes, hk, hl] at h
          · rintro ⟨kind', policy, hA⟩
            rw [lookupPolicy_eq_some_of_uniqueMember hA.member] at hl
            simp at hl
      | some policy =>
          have hunfold : authorizes profile st ctx cmd
              = contextAuthorizes profile st ctx cmd kind policy := by
            simp [authorizes, hk, hl]
          rw [hunfold, contextAuthorizes_eq_true_iff]
          constructor
          · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
            exact ⟨kind, policy,
              { profileActive := h1
                profileNamed := h2
                registryRootGoverned := h3
                registryRootBound := h4
                releaseMatched := h5
                kindExact := hk
                member := uniqueMember_of_lookup hnd hl
                ordinaryClass := h6
                enabled := h7
                grantMatched := h8 }⟩
          · rintro ⟨kind', policy', hA⟩
            have hkind : kind' = kind := by
              rw [hA.kindExact] at hk
              exact Option.some.injEq _ _ ▸ hk
            have hpolicy : policy' = policy := by
              rw [lookupPolicy_eq_some_of_uniqueMember hA.member] at hl
              exact Option.some.injEq _ _ ▸ hl
            subst hkind
            subst hpolicy
            exact ⟨hA.profileActive, hA.profileNamed, hA.registryRootGoverned,
              hA.registryRootBound, hA.releaseMatched, hA.ordinaryClass, hA.enabled,
              hA.grantMatched⟩

/-! ## 8. Authorization pins the governed registry, the member, the release, and
the kind-specific grant -/

/-- The active-profile policy binding, pinned. The registry the checker
consulted declares exactly the root the active profile governs, and the context
presented that same root. -/
theorem authorized_pins_governed_registry_root {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd kind policy) :
    profile.status = ProfileStatus.active ∧
    ctx.profileRoot = profile.profileRoot ∧
    ctx.policyRegistryRoot = profile.managedPolicyRegistryRoot ∧
    st.registry.registryRoot = profile.managedPolicyRegistryRoot :=
  ⟨h.profileActive, h.profileNamed, h.registryRootGoverned,
    h.registryRootBound.trans h.registryRootGoverned⟩

/-- The unique asset member, pinned: the policy is a member of the governed
registry, it names the command's asset, and no other member does. -/
theorem authorized_pins_unique_member {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd kind policy) :
    policy ∈ st.registry.members ∧
    policy.asset = cmd.asset ∧
    (∀ q ∈ st.registry.members, q.asset = cmd.asset → q = policy) :=
  ⟨h.member.mem, h.member.asset, h.member.unique⟩

/-- Any registry member naming the command's asset *is* the authorized policy. -/
theorem authorized_member_eq {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy q : ManagedPolicy}
    (h : Authorized profile st ctx cmd kind policy)
    (hq : q ∈ st.registry.members) (hqa : q.asset = cmd.asset) : q = policy :=
  h.member.unique q hq hqa

/-- The authorized policy is unique. -/
theorem authorized_policy_unique {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {k₁ k₂ : CommandKind} {p₁ p₂ : ManagedPolicy}
    (h₁ : Authorized profile st ctx cmd k₁ p₁) (h₂ : Authorized profile st ctx cmd k₂ p₂) :
    p₁ = p₂ :=
  uniqueMember_unique h₁.member h₂.member

/-- The authorized kind is unique, because the wire kind parses deterministically. -/
theorem authorized_kind_unique {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {k₁ k₂ : CommandKind} {p₁ p₂ : ManagedPolicy}
    (h₁ : Authorized profile st ctx cmd k₁ p₁) (h₂ : Authorized profile st ctx cmd k₂ p₂) :
    k₁ = k₂ := by
  have h := h₁.kindExact.symm.trans h₂.kindExact
  exact (Option.some.injEq _ _ ▸ h)

/-- The module release, pinned. -/
theorem authorized_pins_module_release {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd kind policy) :
    ctx.moduleReleaseId = st.moduleReleaseId :=
  h.releaseMatched

/-- The exact wire command kind, pinned. -/
theorem authorized_pins_command_kind {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd kind policy) :
    cmd.commandKind = kind.code :=
  parseCommandKind_eq_some_iff.mp h.kindExact

/-- Generic authority is confined to registered ordinary tokens. -/
theorem authorized_requires_ordinary_class {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd kind policy) :
    policy.assetClass = AssetClass.registeredOrdinaryToken ∧ policy.enabled = true :=
  ⟨h.ordinaryClass, h.enabled⟩

/-- Issue: the subject is the policy's named issue-authority subject and the
grant is that authority's policy root, as one paired value. -/
theorem authorized_issue_pins_authority {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd CommandKind.issue policy) :
    policy.issueAuthority = some ⟨ctx.subject, ctx.grantRoot⟩ ∧
    ∃ ia : IssueAuthority,
      policy.issueAuthority = some ia ∧
      ctx.subject = ia.subject ∧ ctx.grantRoot = ia.policyRoot :=
  ⟨h.grantMatched, ⟨⟨ctx.subject, ctx.grantRoot⟩, h.grantMatched, rfl, rfl⟩⟩

/-- Self-burn: the subject is the command's own account owner and the grant is
the policy's self-burn policy root. -/
theorem authorized_burn_pins_owner_and_grant {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd CommandKind.burn policy) :
    ctx.subject = cmd.accountOwner ∧
    policy.selfBurnPolicyRoot = some ctx.grantRoot ∧
    ∃ root : Root,
      policy.selfBurnPolicyRoot = some root ∧
      ctx.subject = cmd.accountOwner ∧ ctx.grantRoot = root :=
  ⟨h.grantMatched.1, h.grantMatched.2, ⟨ctx.grantRoot, h.grantMatched.2, h.grantMatched.1, rfl⟩⟩

/-- The full pin, as one citable statement. -/
theorem authorized_pins_everything {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd kind policy) :
    profile.status = ProfileStatus.active ∧
    ctx.profileRoot = profile.profileRoot ∧
    st.registry.registryRoot = profile.managedPolicyRegistryRoot ∧
    (policy ∈ st.registry.members ∧ policy.asset = cmd.asset ∧
      ∀ q ∈ st.registry.members, q.asset = cmd.asset → q = policy) ∧
    ctx.moduleReleaseId = st.moduleReleaseId ∧
    cmd.commandKind = kind.code ∧
    policy.assetClass = AssetClass.registeredOrdinaryToken ∧
    (kind = CommandKind.issue →
      policy.issueAuthority = some ⟨ctx.subject, ctx.grantRoot⟩) ∧
    (kind = CommandKind.burn →
      ctx.subject = cmd.accountOwner ∧ policy.selfBurnPolicyRoot = some ctx.grantRoot) := by
  refine ⟨h.profileActive, h.profileNamed,
    h.registryRootBound.trans h.registryRootGoverned,
    ⟨h.member.mem, h.member.asset, h.member.unique⟩,
    h.releaseMatched, authorized_pins_command_kind h, h.ordinaryClass, ?_, ?_⟩
  · intro hk
    subst hk
    exact h.grantMatched
  · intro hk
    subst hk
    exact h.grantMatched

/-! ## 9. Rejection implications

Rejection is the absence of a witness. Each statement is the contrapositive of
one modeled obligation. -/

/-- Wrong root, presented: a context that presents a policy-registry root other
than the one the active profile governs is not authorized, for any kind and any
policy. -/
theorem wrong_presented_registry_root_not_authorized {profile : ProfileSnapshot}
    {st : ModuleState} {ctx : Context} {cmd : Command} {kind : CommandKind}
    {policy : ManagedPolicy}
    (hne : ctx.policyRegistryRoot ≠ profile.managedPolicyRegistryRoot) :
    ¬ Authorized profile st ctx cmd kind policy :=
  fun h => hne h.registryRootGoverned

/-- Wrong root, carried: a module state whose registry declares a root other
than the one the active profile governs is not authorized. -/
theorem wrong_registry_root_not_authorized {profile : ProfileSnapshot}
    {st : ModuleState} {ctx : Context} {cmd : Command} {kind : CommandKind}
    {policy : ManagedPolicy}
    (hne : st.registry.registryRoot ≠ profile.managedPolicyRegistryRoot) :
    ¬ Authorized profile st ctx cmd kind policy :=
  fun h => hne (h.registryRootBound.trans h.registryRootGoverned)

/-- Wrong release: a context naming a module release other than the state's is
not authorized. -/
theorem wrong_release_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (hne : ctx.moduleReleaseId ≠ st.moduleReleaseId) :
    ¬ Authorized profile st ctx cmd kind policy :=
  fun h => hne h.releaseMatched

/-- Wrong profile: a context naming a profile other than the active one is not
authorized. -/
theorem wrong_profile_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (hne : ctx.profileRoot ≠ profile.profileRoot) :
    ¬ Authorized profile st ctx cmd kind policy :=
  fun h => hne h.profileNamed

/-- A profile that is not `ACTIVE` authorizes nothing. -/
theorem inactive_profile_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (hne : profile.status ≠ ProfileStatus.active) :
    ¬ Authorized profile st ctx cmd kind policy :=
  fun h => hne h.profileActive

/-- An unparseable wire kind authorizes nothing. -/
theorem unknown_command_kind_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (hnone : parseCommandKind cmd.commandKind = none) :
    ¬ Authorized profile st ctx cmd kind policy := by
  intro h
  rw [h.kindExact] at hnone
  simp at hnone

/-- An asset with no member in the governed registry authorizes nothing. -/
theorem foreign_asset_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (hnone : ∀ q ∈ st.registry.members, q.asset ≠ cmd.asset) :
    ¬ Authorized profile st ctx cmd kind policy :=
  fun h => hnone policy h.member.mem h.member.asset

/-- A protocol-managed class authorizes nothing through this generic path. -/
theorem non_ordinary_class_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {kind : CommandKind} {policy : ManagedPolicy}
    (hne : policy.assetClass ≠ AssetClass.registeredOrdinaryToken) :
    ¬ Authorized profile st ctx cmd kind policy :=
  fun h => hne h.ordinaryClass

/-- Wrong grant, issue: a grant root other than the policy's issue policy root
is not authorized, even from the named authority subject. -/
theorem wrong_issue_grant_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy} {ia : IssueAuthority}
    (hia : policy.issueAuthority = some ia) (hne : ctx.grantRoot ≠ ia.policyRoot) :
    ¬ Authorized profile st ctx cmd CommandKind.issue policy := by
  intro h
  have hg : policy.issueAuthority = some ⟨ctx.subject, ctx.grantRoot⟩ := h.grantMatched
  rw [hia, Option.some.injEq] at hg
  exact hne (by rw [hg])

/-- Wrong subject, issue: a subject other than the policy's named issue
authority subject is not authorized, even holding the right grant root. -/
theorem wrong_issue_subject_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy} {ia : IssueAuthority}
    (hia : policy.issueAuthority = some ia) (hne : ctx.subject ≠ ia.subject) :
    ¬ Authorized profile st ctx cmd CommandKind.issue policy := by
  intro h
  have hg : policy.issueAuthority = some ⟨ctx.subject, ctx.grantRoot⟩ := h.grantMatched
  rw [hia, Option.some.injEq] at hg
  exact hne (by rw [hg])

/-- Issue with no configured authority is not authorized. -/
theorem issue_disabled_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy}
    (hnone : policy.issueAuthority = none) :
    ¬ Authorized profile st ctx cmd CommandKind.issue policy := by
  intro h
  have hg : policy.issueAuthority = some ⟨ctx.subject, ctx.grantRoot⟩ := h.grantMatched
  rw [hnone] at hg
  simp at hg

/-- Wrong grant, self-burn: a grant root other than the policy's self-burn
policy root is not authorized, even from the account owner. -/
theorem wrong_selfBurn_grant_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy} {root : Root}
    (hroot : policy.selfBurnPolicyRoot = some root) (hne : ctx.grantRoot ≠ root) :
    ¬ Authorized profile st ctx cmd CommandKind.burn policy := by
  intro h
  have hg : policy.selfBurnPolicyRoot = some ctx.grantRoot := h.grantMatched.2
  rw [hroot, Option.some.injEq] at hg
  exact hne hg.symm

/-- A self-burn from an account the subject does not own is not authorized. -/
theorem foreign_owner_selfBurn_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy}
    (hne : ctx.subject ≠ cmd.accountOwner) :
    ¬ Authorized profile st ctx cmd CommandKind.burn policy :=
  fun h => hne h.grantMatched.1

/-- Self-burn with no configured policy root is not authorized. -/
theorem burn_disabled_not_authorized {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy}
    (hnone : policy.selfBurnPolicyRoot = none) :
    ¬ Authorized profile st ctx cmd CommandKind.burn policy := by
  intro h
  have hg : policy.selfBurnPolicyRoot = some ctx.grantRoot := h.grantMatched.2
  rw [hnone] at hg
  simp at hg

/-! ## 10. Issue-versus-burn confusion exclusion

Three separate exclusions: at the wire kind, at the grant root, and at the
subject-versus-owner rule. -/

/-- If one context authorizes both an issue and a self-burn against the same
policy, then the policy's issue policy root and self-burn policy root coincide
and the issue-authority subject is the burned account's owner. Equivalently, a
policy that separates those roots cannot have both authorized from one context. -/
theorem issue_and_burn_from_one_context_forces_shared_grant {profile : ProfileSnapshot}
    {st : ModuleState} {ctx : Context} {cmdI cmdB : Command} {policy : ManagedPolicy}
    {ia : IssueAuthority} {root : Root}
    (hia : policy.issueAuthority = some ia) (hroot : policy.selfBurnPolicyRoot = some root)
    (hI : Authorized profile st ctx cmdI CommandKind.issue policy)
    (hB : Authorized profile st ctx cmdB CommandKind.burn policy) :
    ia.policyRoot = root ∧ ia.subject = cmdB.accountOwner := by
  have hgI : policy.issueAuthority = some ⟨ctx.subject, ctx.grantRoot⟩ := hI.grantMatched
  rw [hia, Option.some.injEq] at hgI
  have hgB : policy.selfBurnPolicyRoot = some ctx.grantRoot := hB.grantMatched.2
  rw [hroot, Option.some.injEq] at hgB
  have hsub : ctx.subject = cmdB.accountOwner := hB.grantMatched.1
  constructor
  · rw [hgI, ← hgB]
  · rw [hgI, ← hsub]

/-- Grant-root exclusion: when the issue and self-burn policy roots differ, one
context never authorizes both kinds against the same policy. -/
theorem distinct_grant_roots_exclude_kind_confusion {profile : ProfileSnapshot}
    {st : ModuleState} {ctx : Context} {cmdI cmdB : Command} {policy : ManagedPolicy}
    {ia : IssueAuthority} {root : Root}
    (hia : policy.issueAuthority = some ia) (hroot : policy.selfBurnPolicyRoot = some root)
    (hne : ia.policyRoot ≠ root) :
    ¬ (Authorized profile st ctx cmdI CommandKind.issue policy ∧
       Authorized profile st ctx cmdB CommandKind.burn policy) := by
  rintro ⟨hI, hB⟩
  exact hne (issue_and_burn_from_one_context_forces_shared_grant hia hroot hI hB).1

/-- Subject-versus-owner exclusion: an issue-authorized context cannot self-burn
an account the policy's issue-authority subject does not own. -/
theorem issue_context_cannot_selfBurn_foreign_account {profile : ProfileSnapshot}
    {st : ModuleState} {ctx : Context} {cmdI cmdB : Command} {policy : ManagedPolicy}
    {ia : IssueAuthority} (hia : policy.issueAuthority = some ia)
    (hI : Authorized profile st ctx cmdI CommandKind.issue policy)
    (hne : ia.subject ≠ cmdB.accountOwner) :
    ¬ Authorized profile st ctx cmdB CommandKind.burn policy := by
  intro hB
  exact hne (issue_and_burn_from_one_context_forces_shared_grant hia
    (by
      have hg : policy.selfBurnPolicyRoot = some ctx.grantRoot := hB.grantMatched.2
      exact hg)
    hI hB).2

/-- Wire-kind exclusion: one command never carries both kinds, so an
authorization is for exactly one of issue and self-burn. -/
theorem authorized_kind_is_exclusive {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {p₁ p₂ : ManagedPolicy}
    (h₁ : Authorized profile st ctx cmd CommandKind.issue p₁)
    (h₂ : Authorized profile st ctx cmd CommandKind.burn p₂) : False := by
  exact parseCommandKind_no_kind_confusion cmd.commandKind ⟨h₁.kindExact, h₂.kindExact⟩

/-! ## 11. The supply-effect kind the authorization selects

The runtime picks `EconomicEffectKindV1.ISSUE` or `.BURN` from the command kind.
Only that selection is modeled; no delta, amount, row, or conservation claim is
made here. -/

inductive SupplyEffectKind where
  | issue
  | burn
  deriving DecidableEq, Repr

def SupplyEffectKind.code : SupplyEffectKind → String
  | .issue => "ISSUE"
  | .burn => "BURN"

def authorizedSupplyEffectKind : CommandKind → SupplyEffectKind
  | .issue => .issue
  | .burn => .burn

theorem authorizedSupplyEffectKind_injective {a b : CommandKind}
    (h : authorizedSupplyEffectKind a = authorizedSupplyEffectKind b) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h (by decide)

/-- An issue authorization selects the `ISSUE` supply effect and the exact issue
wire kind. -/
theorem authorized_issue_selects_issue_effect {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd CommandKind.issue policy) :
    (authorizedSupplyEffectKind CommandKind.issue).code = "ISSUE" ∧
    cmd.commandKind = "managed_asset_issue" :=
  ⟨rfl, authorized_pins_command_kind h⟩

/-- A self-burn authorization selects the `BURN` supply effect and the exact
burn wire kind. -/
theorem authorized_burn_selects_burn_effect {profile : ProfileSnapshot} {st : ModuleState}
    {ctx : Context} {cmd : Command} {policy : ManagedPolicy}
    (h : Authorized profile st ctx cmd CommandKind.burn policy) :
    (authorizedSupplyEffectKind CommandKind.burn).code = "BURN" ∧
    cmd.commandKind = "managed_asset_burn" :=
  ⟨rfl, authorized_pins_command_kind h⟩

theorem supplyEffectKind_codes_differ :
    (authorizedSupplyEffectKind CommandKind.issue).code ≠
      (authorizedSupplyEffectKind CommandKind.burn).code := by decide

/-! ## 12. Source comparison

The forged-authorization counterexamples live in
`Proofs.ManagedAssetPolicyAuthorityV1Challenge`, which binds selected theorem
signatures and exhibits, for each of the registry-root, module-release, and
grant checks, a concrete input that the checker with that check removed accepts
and that this file's checker and witness both reject. -/

end ManagedAssetPolicyAuthorityV1
end Proofs
