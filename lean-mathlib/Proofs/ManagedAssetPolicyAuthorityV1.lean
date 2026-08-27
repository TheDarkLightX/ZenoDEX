/-!
# Managed ordinary-token issue and self-burn — bounded policy-helper authority V1

A machine-checked model of one *bounded* authorization predicate: the four
governed-policy helper functions plus the lifecycle authorization core, and one
named binder check. The runtime candidate read for this file is exact commit
`da979883f61648b1a2698f47794b27f5946b2cdb`.

## Exactly what is abstracted

Four functions and one check, named so the boundary is checkable:

* `require_governed_managed_asset_policy_registry_v1`,
  `require_managed_asset_policy_membership_v1`, and
  `require_managed_asset_route_policy_root_v1` in
  `src/core/managed_asset_policy_registry_v1.py`;
* `_authorize` in `src/core/managed_asset_lifecycle_module_v1.py`, up to and
  excluding its `ZERO_AMOUNT` check;
* the single check `candidate.actual_command_kind != occurrence.command_kind`
  from `_bind_candidate_v1` in
  `src/core/lane_module_release_route_binding_v1.py`, imported because without
  it this model would authorize a query whose outer binding and route are
  selected for one command kind while the lifecycle grant rule runs for the
  other. It is imported as the `commandKindAgrees` obligation and is the *only*
  binder check modeled.

**This is a bounded policy-helper claim. It is not the controlled release-route
admission path.** See "The rest of the binder is not modeled" below.

## The two-level binding

Governance is not one root. It is an outer registry bound to the profile, whose
*per-command-kind* binding names the inner registry:

```text
profile.policy_registry_root
  = EconomicPolicyRegistryV1.registry_root                       -- outer
      .require_binding("managed_asset_policy_v1", occurrence.command_kind)
        .policy_root
          = ManagedAssetPolicyRegistryV1.registry_root           -- inner
              = digest{schema, module_release_id, policies}
```

The lane input's `asset_policy_registry_root` and the governed route's
`RouteReleaseV1.issue_burn_policy_root` must equal that same inner root. The
inner registry *selects* the `ASSET_TRANSFER` module release, which both
`ManagedAssetLifecycleContextV1.module_release_id` and
`ManagedAssetLifecycleStateV1.module_release_id` must equal.

Because the outer binding key is `(policy_kind, command_kind)`, the runtime
**permits** issue and self-burn to name different inner registries. Nothing here
requires them to be equal, and `bundle_pins_each_kind_separately` is stated so
that one per-query witness is never read as pinning both kinds.

## Two policy rows, not one

This is the correction that matters most. `require_managed_asset_policy_membership_v1`
requires the command asset to have a *governed registry* member and requires
every carried pre-state row to equal its registry counterpart. But `_authorize`
then reads `_policy_for(pre_state, command.asset)` — the **pre-state** row — and
evaluates class, enabled, subject, and grant from it.

So the model carries both `Query.registryMember` and `Query.stateMember`,
requires each to exist, and evaluates every downstream rule from the *state*
member exactly as `_authorize` does.
`authorized_state_member_is_governed` then derives that the two coincide, from
state conformance rather than by assumption. Without the state-side membership
obligation an empty pre-state policy list would satisfy conformance vacuously
while `_authorize` returns `UNKNOWN_ASSET`; the challenge module rejects that
query.

## Roots are digests of content, with a narrow pairwise premise

`ManagedAssetPolicyRegistryV1.registry_root` is `hash_global_v1` over
`{schema, module_release_id, policies}`, so `Digests` carries an uninterpreted
content-to-root function. Equal content gives equal roots, for free and
truthfully.

The converse is not free, and this file does **not** assume any global
injectivity. `NoCollisionOn d r₁ r₂` is a premise about *one specific pair of
canonical preimages*: it says those two do not collide under that digest.
`noCollision_pins_registry` is the only place a registry value is recovered from
a root, and it carries that pairwise premise. Nothing here claims, implies, or
requires that `hash_global_v1` or SHA-256 is injective; `authorized_pins_root_not_value`
is the unconditional conclusion available without any such premise.

## The rest of the binder is not modeled

`_bind_candidate_v1` performs several checks beyond the one imported above, and
**none of them is modeled, abstracted, replaced, or discharged here**:

* the active-profile requirement (`profile.status is ProfileStatusV1.ACTIVE`);
* the command body hash equality
  (`candidate.command_body_hash != occurrence.command_body_hash`);
* the exact context binding (`_require_exact_context_binding`);
* the exact journal binding (`_require_exact_journal_binding`: chain id,
  deployment root, journal profile root against `profile.profile_id`, journal
  occurrence id, and writer epoch against `profile.authority_epoch`);
* the release checks, meaning the route ordered-lane index, the lane registry
  release, the agreement of `journal.module_release_id`,
  `route.module_release_ids[index]`, and `context.module_release_id` with that
  release, and `command_variants` membership;
* the statement root and the release witness it returns.

Consequently `EconomicProfileSnapshotV1.status` is deliberately **not** an
obligation below: no function this file abstracts inspects it, and adding it
would be an invented gate. A query being `Authorized` here means the bounded
policy-helper predicate holds, and nothing more.

## Scope: what is NOT modeled

No amount, balance, supply, or width; no `ZERO_AMOUNT`, `EFFECT_DELTA_OVERFLOW`,
`INSUFFICIENT_BALANCE`, `BALANCE_OVERFLOW`, or `SUPPLY_OVERFLOW`; no
conservation, effect rows, or asset conservation rows; no post-state and no
state transition at all. No receipts, journals, private ports, effect-plan
roots, or state roots. No canonical byte encoding, ordering, or deduplication.
No replay, nonce, or occurrence consumption. No signature or authentication
derivation. No fee policy registry. No rejection codes:
`ManagedAssetLifecycleRejectCodeV1`, its wire strings, and its precedence are
absent, and rejection here is the absence of a witness. No runtime refinement:
no theorem below relates this model to the Python or Rust sources, and none can,
because nothing here executes them.

The obligations are an **unordered conjunction**. The runtime raises on the
first failing check and spreads these checks across several functions. Neither
that ordering nor that layering is modeled.

## Accounting wording

`accountsLocation` is the accounting-location label the managed-asset rows carry
(`ACCOUNT_CUSTODY_DOMAIN_V1`, value `"accounts"`). It is an accounting location
and an accounting control domain label only. Nothing in this file asserts
custody, possession, title, control, or key control over any asset by any party.
Practical control of an asset follows key control, which is outside this file
entirely, and no theorem here reads `accountsLocation`.

## What is NOT claimed

No cryptographic property of any digest; no refinement between this model and
any runtime; no settlement, conservation, or replay safety; no economic-policy
correctness; no release, migration, publication, or value-moving authority; and
no production readiness. This is research-only structural evidence about one
bounded authorization predicate.
-/

namespace Proofs
namespace ManagedAssetPolicyAuthorityV1

/-! ## 1. Opaque identifiers

Uninterpreted tokens. The runtime's `_require_token` and `_require_root` shape
discipline is not modeled: a `String` here may be empty, oversized, or
non-ASCII. -/

abbrev Root := String
abbrev Subject := String
abbrev Asset := String
abbrev Token := String
abbrev AccountingLocation := String

/-- `ACCOUNT_CUSTODY_DOMAIN_V1`. Accounting label only; read by no theorem. -/
def accountsLocation : AccountingLocation := "accounts"

/-- `MANAGED_ASSET_POLICY_KIND_V1`, the outer binding's policy kind. -/
def managedAssetPolicyKind : Token := "managed_asset_policy_v1"

/-! ## 2. Exact command kind -/

inductive CommandKind where
  | issue
  | burn
  deriving DecidableEq, Repr

/-- `MANAGED_ASSET_ISSUE_COMMAND_KIND_V1` and
`MANAGED_ASSET_BURN_COMMAND_KIND_V1`. -/
def CommandKind.code : CommandKind → String
  | .issue => "managed_asset_issue"
  | .burn => "managed_asset_burn"

def allCommandKinds : List CommandKind := [.issue, .burn]

theorem allCommandKinds_codes :
    allCommandKinds.map CommandKind.code =
      ["managed_asset_issue", "managed_asset_burn"] := rfl

theorem allCommandKinds_complete (k : CommandKind) : k ∈ allCommandKinds := by
  cases k <;> decide

theorem issue_code_ne_burn_code :
    CommandKind.issue.code ≠ CommandKind.burn.code := by decide

theorem CommandKind.code_injective {a b : CommandKind} (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h (by decide)

/-- The wire-kind parser. Only the two exact strings are accepted; this is also
`_MANAGED_ASSET_ROUTE_COMMAND_KINDS_V1` membership. -/
def parseCommandKind (s : String) : Option CommandKind :=
  if s = CommandKind.issue.code then some CommandKind.issue
  else if s = CommandKind.burn.code then some CommandKind.burn
  else none

theorem parseCommandKind_code (k : CommandKind) : parseCommandKind k.code = some k := by
  cases k <;> decide

/-- Exactness: a wire string parses to a kind iff it *is* that kind's code. -/
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

/-- One wire string never names both kinds. This is a statement about a single
string, not about a governance registry. -/
theorem parseCommandKind_no_kind_confusion (s : String) :
    ¬ (parseCommandKind s = some CommandKind.issue ∧
       parseCommandKind s = some CommandKind.burn) := by
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ## 3. Asset class and release status -/

/-- `ManagedAssetClassV1`. Only `REGISTERED_ORDINARY_TOKEN` may carry the generic
issue and self-burn authority. -/
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

theorem allAssetClasses_codes :
    allAssetClasses.map AssetClass.code =
      [ "tau_native_coin", "canonical_zusd", "lp_share", "zdex_protocol_token",
        "sealed_bid_payment_or_inventory", "registered_ordinary_token" ] := rfl

theorem allAssetClasses_complete (c : AssetClass) : c ∈ allAssetClasses := by
  cases c <;> decide

/-- `ReleaseStatusV1`. Only `ACTIVE_NEW` yields a route for new objects. -/
inductive ReleaseStatus where
  | candidate
  | shadow
  | activeNew
  | drainOnly
  | verifyOnly
  | retired
  | revoked
  deriving DecidableEq, Repr

def ReleaseStatus.code : ReleaseStatus → String
  | .candidate => "CANDIDATE"
  | .shadow => "SHADOW"
  | .activeNew => "ACTIVE_NEW"
  | .drainOnly => "DRAIN_ONLY"
  | .verifyOnly => "VERIFY_ONLY"
  | .retired => "RETIRED"
  | .revoked => "REVOKED"

def allReleaseStatuses : List ReleaseStatus :=
  [ .candidate, .shadow, .activeNew, .drainOnly, .verifyOnly, .retired, .revoked ]

theorem allReleaseStatuses_codes :
    allReleaseStatuses.map ReleaseStatus.code =
      [ "CANDIDATE", "SHADOW", "ACTIVE_NEW", "DRAIN_ONLY", "VERIFY_ONLY",
        "RETIRED", "REVOKED" ] := rfl

theorem allReleaseStatuses_complete (s : ReleaseStatus) : s ∈ allReleaseStatuses := by
  cases s <;> decide

/-! ## 4. Policies, the inner registry, and the outer registry

The generic issue authority is one typed value, so the runtime's cross-field
"subject and policy root must be present together" invariant
(`_require_optional_authority`) is unrepresentable here rather than checked. -/

/-- The paired generic issue authority. Neither half exists without the other. -/
structure IssueAuthority where
  subject : Subject
  policyRoot : Root
  deriving DecidableEq, Repr

/-- One `ManagedAssetLifecyclePolicyV1`, authority fields only. -/
structure ManagedPolicy where
  asset : Asset
  assetClass : AssetClass
  issueAuthority : Option IssueAuthority
  selfBurnPolicyRoot : Option Root
  enabled : Bool
  deriving DecidableEq, Repr

/-- `ManagedAssetPolicyRegistryV1`: the canonical preimage whose digest is the
inner registry root. It selects the `ASSET_TRANSFER` module release. -/
structure ManagedPolicyRegistry where
  moduleReleaseId : Root
  policies : List ManagedPolicy
  deriving DecidableEq, Repr

/-- `EconomicPolicyBindingV1`. -/
structure PolicyBinding where
  policyKind : Token
  commandKind : Token
  policyRoot : Root
  deriving DecidableEq, Repr

/-- `EconomicPolicyRegistryV1`: the outer governed registry. -/
structure EconomicPolicyRegistry where
  bindings : List PolicyBinding
  deriving DecidableEq, Repr

/-- `RouteReleaseV1`, authority fields only. The lane list, module release ids,
port schemas, image id, budgets, and evidence statuses are not modeled. -/
structure RouteRelease where
  routeReleaseId : Root
  commandKind : Token
  issueBurnPolicyRoot : Root
  status : ReleaseStatus
  acceptsNewObjects : Bool
  deriving DecidableEq, Repr

/-- `RouteRegistryV1`, restricted to its route list. -/
structure RouteRegistry where
  routes : List RouteRelease
  deriving DecidableEq, Repr

/-- `EconomicProfileSnapshotV1`, authority fields only. `profile_id` is not
proved here to be the exact content-derived id, and `status`, the lane and
coordinator registries, proof shape root, image id, verifier, migration, and
terminal registry roots, and the authority epoch are not modeled. -/
structure Profile where
  profileId : Root
  policyRegistryRoot : Root
  routeRegistry : RouteRegistry
  deriving DecidableEq, Repr

/-- `EconomicCommandOccurrenceV1`, restricted to the two fields the governed
policy helpers read. -/
structure Occurrence where
  commandKind : Token
  routeReleaseId : Root
  deriving DecidableEq, Repr

/-- `ManagedAssetLifecycleContextV1` deciding fields, together with the lane
input's `asset_policy_registry_root`. -/
structure Context where
  policyRegistryRoot : Root
  moduleReleaseId : Root
  subject : Subject
  grantRoot : Root
  deriving DecidableEq, Repr

/-- The authority projection of `ManagedAssetLifecycleStateV1`: the release it
executes under and the policy rows it carries. Balances and supplies are out of
scope. -/
structure ModuleState where
  moduleReleaseId : Root
  policies : List ManagedPolicy
  deriving DecidableEq, Repr

/-- The authority projection of `ManagedAssetLifecycleCommandV1`. The raw wire
kind is kept unparsed so "unknown command" stays representable, and the amount
is absent because this file decides authority only. -/
structure Command where
  commandKind : String
  asset : Asset
  accountOwner : Subject
  deriving DecidableEq, Repr

/-! ## 5. The content digest and the narrow no-collision premise -/

/-- An uninterpreted content-to-root function standing in for `hash_global_v1`
on the two canonical preimages this model hashes. -/
structure Digests where
  outer : EconomicPolicyRegistry → Root
  managed : ManagedPolicyRegistry → Root

/-- The narrow premise this model actually needs: *these two* canonical
preimages do not collide under this digest. It is a hypothesis about one
specific pair. It is never discharged here, and it is emphatically **not** a
claim that `hash_global_v1` or SHA-256 is injective. -/
def NoCollisionOn (d : Digests) (r₁ r₂ : ManagedPolicyRegistry) : Prop :=
  d.managed r₁ = d.managed r₂ → r₁ = r₂

instance decidableNoCollisionOn (d : Digests) (r₁ r₂ : ManagedPolicyRegistry) :
    Decidable (NoCollisionOn d r₁ r₂) :=
  inferInstanceAs (Decidable (d.managed r₁ = d.managed r₂ → r₁ = r₂))

/-- The free direction: equal registry content gives equal roots. -/
theorem managed_root_of_eq (d : Digests) {r₁ r₂ : ManagedPolicyRegistry} (h : r₁ = r₂) :
    d.managed r₁ = d.managed r₂ := congrArg d.managed h

theorem outer_root_of_eq (d : Digests) {r₁ r₂ : EconomicPolicyRegistry} (h : r₁ = r₂) :
    d.outer r₁ = d.outer r₂ := congrArg d.outer h

/-! ## 6. Deterministic lookups

Each mirrors a runtime first-match scan whose uniqueness the constructor
establishes (`_require_ordered_objects`, sorted-unique registry keys). -/

/-- `ManagedAssetPolicyRegistryV1.policy_for`, and also the lifecycle module's
`_policy_for` over the pre-state rows. -/
def lookupPolicy (asset : Asset) : List ManagedPolicy → Option ManagedPolicy
  | [] => none
  | p :: rest => if p.asset = asset then some p else lookupPolicy asset rest

/-- `EconomicPolicyRegistryV1.require_binding`, as a total lookup. -/
def lookupBinding (policyKind commandKind : Token) : List PolicyBinding → Option PolicyBinding
  | [] => none
  | b :: rest =>
      if b.policyKind = policyKind ∧ b.commandKind = commandKind then some b
      else lookupBinding policyKind commandKind rest

/-- `RouteRegistryV1.route_for_command`. The runtime takes the *first* route
whose command kind matches and raises if that route is not `ACTIVE_NEW`, does
not accept new objects, or does not match the caller's claimed route release id;
it does not fall through to a later matching route. `none` models the raise. -/
def routeForCommand (commandKind : Token) (claimedRouteReleaseId : Root) :
    List RouteRelease → Option RouteRelease
  | [] => none
  | r :: rest =>
      if r.commandKind = commandKind then
        (if r.status = ReleaseStatus.activeNew ∧ r.acceptsNewObjects = true ∧
            r.routeReleaseId = claimedRouteReleaseId then some r else none)
      else routeForCommand commandKind claimedRouteReleaseId rest

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

theorem lookupBinding_spec {pk ck : Token} :
    ∀ {bs : List PolicyBinding} {b : PolicyBinding},
      lookupBinding pk ck bs = some b → b ∈ bs ∧ b.policyKind = pk ∧ b.commandKind = ck
  | [], _, h => by simp [lookupBinding] at h
  | c :: rest, b, h => by
      simp only [lookupBinding] at h
      split at h
      · next hc =>
          rw [Option.some.injEq] at h
          subst h
          exact ⟨List.mem_cons_self, hc.1, hc.2⟩
      · obtain ⟨hm, h1, h2⟩ := lookupBinding_spec h
        exact ⟨List.mem_cons_of_mem c hm, h1, h2⟩

theorem routeForCommand_spec {ck : Token} {rid : Root} :
    ∀ {rs : List RouteRelease} {r : RouteRelease},
      routeForCommand ck rid rs = some r →
        r ∈ rs ∧ r.commandKind = ck ∧ r.status = ReleaseStatus.activeNew ∧
        r.acceptsNewObjects = true ∧ r.routeReleaseId = rid
  | [], _, h => by simp [routeForCommand] at h
  | s :: rest, r, h => by
      simp only [routeForCommand] at h
      split at h
      · next hck =>
          split at h
          · next hok =>
              rw [Option.some.injEq] at h
              subst h
              exact ⟨List.mem_cons_self, hck, hok.1, hok.2.1, hok.2.2⟩
          · simp at h
      · obtain ⟨hm, h1, h2, h3, h4⟩ := routeForCommand_spec h
        exact ⟨List.mem_cons_of_mem s hm, h1, h2, h3, h4⟩

/-! ## 7. The authorization query -/

structure Query where
  digests : Digests
  profile : Profile
  outerRegistry : EconomicPolicyRegistry
  managedRegistry : ManagedPolicyRegistry
  occurrence : Occurrence
  ctx : Context
  state : ModuleState
  cmd : Command

/-- The inner registry root: the digest of the governed registry content. -/
def Query.managedRoot (q : Query) : Root := q.digests.managed q.managedRegistry

/-- The **governed registry** row for the command's asset, if any. This is what
`require_managed_asset_policy_membership_v1` requires to exist. -/
def Query.registryMember (q : Query) : Option ManagedPolicy :=
  lookupPolicy q.cmd.asset q.managedRegistry.policies

/-- The **pre-state** row for the command's asset, if any. This is the row
`_authorize` actually reads, and every class, enabled, subject, and grant rule
below is evaluated from it. -/
def Query.stateMember (q : Query) : Option ManagedPolicy :=
  lookupPolicy q.cmd.asset q.state.policies

/-- The parsed lifecycle command kind, if any. -/
def Query.kind (q : Query) : Option CommandKind := parseCommandKind q.cmd.commandKind

/-- The outer binding the profile-governed registry supplies for this
occurrence's command kind, if any. -/
def Query.outerBinding (q : Query) : Option PolicyBinding :=
  lookupBinding managedAssetPolicyKind q.occurrence.commandKind q.outerRegistry.bindings

/-- The governed route for this occurrence, if any. -/
def Query.route (q : Query) : Option RouteRelease :=
  routeForCommand q.occurrence.commandKind q.occurrence.routeReleaseId
    q.profile.routeRegistry.routes

/-! ## 8. The obligation registry

A closed enumeration and one total `Bool` checker per obligation. Adding a
constructor strengthens every witness and forces every fixture to be
re-decided. -/

inductive Obligation where
  /-- The outer registry is the one the profile governs. -/
  | outerProfileRoot
  /-- The outer binding for this command kind names the inner registry root. -/
  | outerBindingRoot
  /-- The governed route's `issue_burn_policy_root` is the inner registry root. -/
  | routePolicyRoot
  /-- The lane input's `asset_policy_registry_root` is the inner registry root. -/
  | laneRegistryRoot
  /-- The inner registry selects the release the context and pre-state execute under. -/
  | moduleRelease
  /-- Every carried pre-state policy is exactly its governed registry member. -/
  | stateConformance
  /-- The lifecycle wire kind is one of the two exact codes. -/
  | commandKindExact
  /-- The occurrence's command kind is the lifecycle command kind. Imported from
  `_bind_candidate_v1`; the only binder check modeled. -/
  | commandKindAgrees
  /-- The command's asset has a governed registry member. -/
  | registryAssetMember
  /-- The command's asset has a pre-state policy row, which is the row
  `_authorize` reads. -/
  | stateAssetMember
  /-- That pre-state row is a registered ordinary token. -/
  | ordinaryClass
  /-- That pre-state row is enabled. -/
  | enabled
  /-- The kind-specific subject rule, evaluated from the pre-state row. -/
  | subject
  /-- The kind-specific grant rule, evaluated from the pre-state row. -/
  | grant
  deriving DecidableEq, Repr

def allObligations : List Obligation :=
  [ .outerProfileRoot, .outerBindingRoot, .routePolicyRoot, .laneRegistryRoot,
    .moduleRelease, .stateConformance, .commandKindExact, .commandKindAgrees,
    .registryAssetMember, .stateAssetMember, .ordinaryClass, .enabled,
    .subject, .grant ]

theorem allObligations_length : allObligations.length = 14 := rfl

theorem allObligations_complete (o : Obligation) : o ∈ allObligations := by
  cases o <;> decide

/-- The deterministic per-obligation checker. -/
def obligationHolds (q : Query) : Obligation → Bool
  | .outerProfileRoot => decide (q.digests.outer q.outerRegistry = q.profile.policyRegistryRoot)
  | .outerBindingRoot =>
      match q.outerBinding with
      | none => false
      | some b => decide (b.policyRoot = q.managedRoot)
  | .routePolicyRoot =>
      match parseCommandKind q.occurrence.commandKind with
      | none => false
      | some _ =>
        match q.route with
        | none => false
        | some r => decide (r.issueBurnPolicyRoot = q.managedRoot)
  | .laneRegistryRoot => decide (q.ctx.policyRegistryRoot = q.managedRoot)
  | .moduleRelease =>
      decide (q.managedRegistry.moduleReleaseId = q.ctx.moduleReleaseId) &&
      decide (q.managedRegistry.moduleReleaseId = q.state.moduleReleaseId)
  | .stateConformance =>
      q.state.policies.all fun p =>
        decide (lookupPolicy p.asset q.managedRegistry.policies = some p)
  | .commandKindExact => decide (q.kind ≠ none)
  | .commandKindAgrees => decide (q.occurrence.commandKind = q.cmd.commandKind)
  | .registryAssetMember => decide (q.registryMember ≠ none)
  | .stateAssetMember => decide (q.stateMember ≠ none)
  | .ordinaryClass =>
      match q.stateMember with
      | none => false
      | some p => decide (p.assetClass = AssetClass.registeredOrdinaryToken)
  | .enabled =>
      match q.stateMember with
      | none => false
      | some p => p.enabled
  | .subject =>
      match q.kind with
      | none => false
      | some k =>
        match q.stateMember with
        | none => false
        | some p =>
          match k with
          | .issue =>
            match p.issueAuthority with
            | none => false
            | some ia => decide (q.ctx.subject = ia.subject)
          | .burn =>
            match p.selfBurnPolicyRoot with
            | none => false
            | some _ => decide (q.ctx.subject = q.cmd.accountOwner)
  | .grant =>
      match q.kind with
      | none => false
      | some k =>
        match q.stateMember with
        | none => false
        | some p =>
          match k with
          | .issue =>
            match p.issueAuthority with
            | none => false
            | some ia => decide (q.ctx.grantRoot = ia.policyRoot)
          | .burn =>
            match p.selfBurnPolicyRoot with
            | none => false
            | some root => decide (q.ctx.grantRoot = root)

/-- The typed witness: every obligation in the closed registry holds. This is
the bounded policy-helper predicate, not release-route admission. -/
def Authorized (q : Query) : Prop := ∀ o : Obligation, obligationHolds q o = true

/-- The total deterministic authorization checker. -/
def authorizes (q : Query) : Bool := allObligations.all (obligationHolds q)

/-- The same checker with a set of obligations removed. One definition covers
every omission counterexample. -/
def authorizesExcept (q : Query) (skip : Obligation → Bool) : Bool :=
  allObligations.all fun o => skip o || obligationHolds q o

/-- The single-obligation omission. Only the independently omissible
obligations have a counterexample of this shape. -/
def authorizesOmitting (q : Query) (skipped : Obligation) : Bool :=
  authorizesExcept q fun o => decide (o = skipped)

/-- The coupled-set omission, needed for the three obligations whose failure
forces other obligations to fail with them. -/
def authorizesOmittingAll (q : Query) (skipped : List Obligation) : Bool :=
  authorizesExcept q fun o => skipped.contains o

theorem authorizes_eq_true_iff (q : Query) : authorizes q = true ↔ Authorized q := by
  simp only [authorizes, List.all_eq_true]
  constructor
  · intro h o
    exact h o (allObligations_complete o)
  · intro h o _
    exact h o

/-- Rejection is the absence of a witness: one failing obligation is enough. -/
theorem not_authorized_of_obligation_false {q : Query} {o : Obligation}
    (h : obligationHolds q o = false) : ¬ Authorized q := by
  intro hA
  rw [hA o] at h
  exact absurd h (by decide)

theorem authorizes_eq_false_of_obligation_false {q : Query} {o : Obligation}
    (h : obligationHolds q o = false) : authorizes q = false := by
  cases hb : authorizes q with
  | false => rfl
  | true =>
      exact absurd ((authorizes_eq_true_iff q).mp hb o) (by rw [h]; decide)

/-- Omitting obligations only ever weakens the checker. -/
theorem authorizesExcept_of_authorizes {q : Query} (skip : Obligation → Bool)
    (h : authorizes q = true) : authorizesExcept q skip = true := by
  simp only [authorizes, List.all_eq_true] at h
  simp only [authorizesExcept, List.all_eq_true]
  intro x hx
  rw [h x hx, Bool.or_true]

theorem authorizesOmitting_of_authorizes {q : Query} (o : Obligation)
    (h : authorizes q = true) : authorizesOmitting q o = true :=
  authorizesExcept_of_authorizes _ h

/-! ## 9. The omission-counterexample shape -/

/-- The weakened checker accepts, the real checker rejects, and no witness
exists. `skip` may remove one obligation or a coupled set; the name of each
instance in the challenge module says which. -/
def OmissionCounterexampleFor (q : Query) (skip : Obligation → Bool) : Prop :=
  authorizesExcept q skip = true ∧ authorizes q = false ∧ ¬ Authorized q

/-- The single-obligation form. Only the independently omissible obligations
have a counterexample of this shape. -/
def SingleOmissionCounterexample (q : Query) (o : Obligation) : Prop :=
  OmissionCounterexampleFor q fun x => decide (x = o)

/-- The coupled-set form. -/
def CoupledOmissionCounterexample (q : Query) (os : List Obligation) : Prop :=
  OmissionCounterexampleFor q fun x => os.contains x

theorem omissionCounterexampleFor_of {q : Query} {skip : Obligation → Bool}
    {o : Obligation} (hweak : authorizesExcept q skip = true)
    (hfail : obligationHolds q o = false) : OmissionCounterexampleFor q skip :=
  ⟨hweak, authorizes_eq_false_of_obligation_false hfail,
    not_authorized_of_obligation_false hfail⟩

theorem singleOmission_of {q : Query} {o : Obligation}
    (hweak : authorizesOmitting q o = true) (hfail : obligationHolds q o = false) :
    SingleOmissionCounterexample q o :=
  omissionCounterexampleFor_of hweak hfail

theorem coupledOmission_of {q : Query} {os : List Obligation} {o : Obligation}
    (hweak : authorizesOmittingAll q os = true) (hfail : obligationHolds q o = false) :
    CoupledOmissionCounterexample q os :=
  omissionCounterexampleFor_of hweak hfail

/-- A counterexample witnesses that dropping those obligations is a strict
weakening of the checker. -/
theorem strictly_weaker_of_omission {q : Query} {skip : Obligation → Bool}
    (h : OmissionCounterexampleFor q skip) :
    ¬ (∀ r : Query, authorizesExcept r skip = authorizes r) := by
  intro hall
  have := hall q
  rw [h.1, h.2.1] at this
  exact absurd this (by decide)

/-! ## 10. Authorization pins the two-level binding -/

theorem authorized_pins_outer_profile_root {q : Query} (h : Authorized q) :
    q.digests.outer q.outerRegistry = q.profile.policyRegistryRoot := by
  have hb := h .outerProfileRoot
  simpa only [obligationHolds, decide_eq_true_eq] using hb

theorem authorized_pins_outer_binding {q : Query} (h : Authorized q) :
    ∃ b : PolicyBinding, q.outerBinding = some b ∧
      b.policyKind = managedAssetPolicyKind ∧
      b.commandKind = q.occurrence.commandKind ∧
      b.policyRoot = q.managedRoot := by
  have hb := h .outerBindingRoot
  simp only [obligationHolds] at hb
  split at hb
  · exact absurd hb (by simp)
  · next b hl =>
      have hspec := lookupBinding_spec hl
      refine ⟨b, hl, hspec.2.1, hspec.2.2, ?_⟩
      simpa only [decide_eq_true_eq] using hb

theorem authorized_pins_route_policy_root {q : Query} (h : Authorized q) :
    ∃ r : RouteRelease, q.route = some r ∧
      r.commandKind = q.occurrence.commandKind ∧
      r.status = ReleaseStatus.activeNew ∧
      r.acceptsNewObjects = true ∧
      r.routeReleaseId = q.occurrence.routeReleaseId ∧
      r.issueBurnPolicyRoot = q.managedRoot := by
  have hb := h .routePolicyRoot
  simp only [obligationHolds] at hb
  split at hb
  · exact absurd hb (by simp)
  · split at hb
    · exact absurd hb (by simp)
    · next r hr =>
        have hspec := routeForCommand_spec hr
        refine ⟨r, hr, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2, ?_⟩
        simpa only [decide_eq_true_eq] using hb

theorem authorized_pins_lane_registry_root {q : Query} (h : Authorized q) :
    q.ctx.policyRegistryRoot = q.managedRoot := by
  have hb := h .laneRegistryRoot
  simpa only [obligationHolds, decide_eq_true_eq] using hb

/-- The occurrence's command kind is one of the two exact managed kinds, which
is the `_MANAGED_ASSET_ROUTE_COMMAND_KINDS_V1` guard. -/
theorem authorized_occurrence_kind_is_managed {q : Query} (h : Authorized q) :
    ∃ k : CommandKind, parseCommandKind q.occurrence.commandKind = some k := by
  have hb := h .routePolicyRoot
  simp only [obligationHolds] at hb
  split at hb
  · exact absurd hb (by simp)
  · next k hk => exact ⟨k, hk⟩

/-- The imported binder check: the occurrence's command kind *is* the lifecycle
command kind, so the outer binding and the route are selected for the same kind
the grant rule runs for. -/
theorem authorized_command_kinds_agree {q : Query} (h : Authorized q) :
    q.occurrence.commandKind = q.cmd.commandKind := by
  have hb := h .commandKindAgrees
  simpa only [obligationHolds, decide_eq_true_eq] using hb

/-- The full two-level binding for **this query's one command kind**: the outer
registry is the profile's, its binding for that kind names the inner root, and
the lane input and the governed route name that same inner root. This says
nothing about the other command kind's binding or route. -/
theorem authorized_pins_two_level_binding {q : Query} (h : Authorized q) :
    q.digests.outer q.outerRegistry = q.profile.policyRegistryRoot ∧
    (∃ b : PolicyBinding, q.outerBinding = some b ∧
      b.commandKind = q.cmd.commandKind ∧ b.policyRoot = q.managedRoot) ∧
    (∃ r : RouteRelease, q.route = some r ∧
      r.commandKind = q.cmd.commandKind ∧ r.issueBurnPolicyRoot = q.managedRoot) ∧
    q.ctx.policyRegistryRoot = q.managedRoot := by
  have hk := authorized_command_kinds_agree h
  obtain ⟨b, hb, -, hbk, hbr⟩ := authorized_pins_outer_binding h
  obtain ⟨r, hr, hrk, -, -, -, hrr⟩ := authorized_pins_route_policy_root h
  exact ⟨authorized_pins_outer_profile_root h, ⟨b, hb, hbk.trans hk, hbr⟩,
    ⟨r, hr, hrk.trans hk, hrr⟩, authorized_pins_lane_registry_root h⟩

/-- All three root observations for this query's kind agree, so an adversary
must move every one of them together. -/
theorem authorized_roots_agree {q : Query} (h : Authorized q)
    {b : PolicyBinding} (hb : q.outerBinding = some b)
    {r : RouteRelease} (hr : q.route = some r) :
    q.ctx.policyRegistryRoot = b.policyRoot ∧
    b.policyRoot = r.issueBurnPolicyRoot := by
  obtain ⟨b', hb', -, -, hbr⟩ := authorized_pins_outer_binding h
  obtain ⟨r', hr', -, -, -, -, hrr⟩ := authorized_pins_route_policy_root h
  rw [hb] at hb'
  rw [hr] at hr'
  rw [Option.some.injEq] at hb' hr'
  subst hb'
  subst hr'
  exact ⟨(authorized_pins_lane_registry_root h).trans hbr.symm, hbr.trans hrr.symm⟩

/-! ## 11. Governance binds each command kind separately

The outer binding key is `(policy_kind, command_kind)` and routes are per
command kind, so the runtime **permits** issue and self-burn to name different
inner registries. Nothing in this file requires them to be equal. -/

/-- Two authorized queries, one issue and one self-burn, each pin *their own*
binding and route. No conclusion relates the issue inner root to the burn inner
root, and none is available: the challenge module exhibits a governance bundle
authorizing both kinds against different inner registries. -/
theorem bundle_pins_each_kind_separately {qI qB : Query}
    (hI : Authorized qI) (hB : Authorized qB)
    (hkI : qI.cmd.commandKind = CommandKind.issue.code)
    (hkB : qB.cmd.commandKind = CommandKind.burn.code) :
    (∃ b : PolicyBinding, qI.outerBinding = some b ∧
      b.commandKind = CommandKind.issue.code ∧ b.policyRoot = qI.managedRoot) ∧
    (∃ b : PolicyBinding, qB.outerBinding = some b ∧
      b.commandKind = CommandKind.burn.code ∧ b.policyRoot = qB.managedRoot) ∧
    (∃ r : RouteRelease, qI.route = some r ∧
      r.commandKind = CommandKind.issue.code ∧ r.issueBurnPolicyRoot = qI.managedRoot) ∧
    (∃ r : RouteRelease, qB.route = some r ∧
      r.commandKind = CommandKind.burn.code ∧ r.issueBurnPolicyRoot = qB.managedRoot) := by
  obtain ⟨-, ⟨bI, hbI, hbIk, hbIr⟩, ⟨rI, hrI, hrIk, hrIr⟩, -⟩ :=
    authorized_pins_two_level_binding hI
  obtain ⟨-, ⟨bB, hbB, hbBk, hbBr⟩, ⟨rB, hrB, hrBk, hrBr⟩, -⟩ :=
    authorized_pins_two_level_binding hB
  exact ⟨⟨bI, hbI, hbIk.trans hkI, hbIr⟩, ⟨bB, hbB, hbBk.trans hkB, hbBr⟩,
    ⟨rI, hrI, hrIk.trans hkI, hrIr⟩, ⟨rB, hrB, hrBk.trans hkB, hrBr⟩⟩

/-- Within **one** command kind and one outer registry the binding is the same,
so the inner root is the same. This is the only agreement available, and it is
deliberately not stated across kinds. -/
theorem outer_binding_root_agrees_within_one_kind {q₁ q₂ : Query}
    (h₁ : Authorized q₁) (h₂ : Authorized q₂)
    (hkind : q₁.cmd.commandKind = q₂.cmd.commandKind)
    (hreg : q₁.outerRegistry = q₂.outerRegistry) :
    q₁.managedRoot = q₂.managedRoot := by
  have e₁ := authorized_command_kinds_agree h₁
  have e₂ := authorized_command_kinds_agree h₂
  have hsame : q₁.outerBinding = q₂.outerBinding := by
    simp only [Query.outerBinding, e₁, e₂, hkind, hreg]
  obtain ⟨b₁, hb₁, -, -, hr₁⟩ := authorized_pins_outer_binding h₁
  obtain ⟨b₂, hb₂, -, -, hr₂⟩ := authorized_pins_outer_binding h₂
  rw [hsame, hb₂, Option.some.injEq] at hb₁
  subst hb₁
  rw [← hr₁, ← hr₂]

/-! ## 12. Module release, state conformance, and the two policy rows -/

/-- The inner registry selects the release, and both the context and the
pre-state execute under exactly that release. -/
theorem authorized_pins_module_release {q : Query} (h : Authorized q) :
    q.managedRegistry.moduleReleaseId = q.ctx.moduleReleaseId ∧
    q.managedRegistry.moduleReleaseId = q.state.moduleReleaseId ∧
    q.ctx.moduleReleaseId = q.state.moduleReleaseId := by
  have hb := h .moduleRelease
  simp only [obligationHolds, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨hb.1, hb.2, hb.1.symm.trans hb.2⟩

/-- Every policy row the pre-state carries is exactly its governed member. -/
theorem authorized_pins_state_conformance {q : Query} (h : Authorized q) :
    ∀ p ∈ q.state.policies, lookupPolicy p.asset q.managedRegistry.policies = some p := by
  have hb := h .stateConformance
  simp only [obligationHolds, List.all_eq_true, decide_eq_true_eq] at hb
  exact hb

theorem authorized_registryMember_exists {q : Query} (h : Authorized q) :
    ∃ p : ManagedPolicy, q.registryMember = some p := by
  have hb := h .registryAssetMember
  simp only [obligationHolds, decide_eq_true_eq, ne_eq] at hb
  cases hp : q.registryMember with
  | none => exact absurd hp hb
  | some p => exact ⟨p, rfl⟩

/-- The pre-state row `_authorize` reads exists. Without this obligation an
empty pre-state policy list would satisfy conformance vacuously. -/
theorem authorized_stateMember_exists {q : Query} (h : Authorized q) :
    ∃ p : ManagedPolicy, q.stateMember = some p := by
  have hb := h .stateAssetMember
  simp only [obligationHolds, decide_eq_true_eq, ne_eq] at hb
  cases hp : q.stateMember with
  | none => exact absurd hp hb
  | some p => exact ⟨p, rfl⟩

theorem authorized_kind_exists {q : Query} (h : Authorized q) :
    ∃ k : CommandKind, q.kind = some k := by
  have hb := h .commandKindExact
  simp only [obligationHolds, decide_eq_true_eq, ne_eq] at hb
  cases hk : q.kind with
  | none => exact absurd hk hb
  | some k => exact ⟨k, rfl⟩

/-- The row `_authorize` reads **is** the governed registry member. Derived from
state conformance, not assumed. -/
theorem authorized_state_member_is_governed {q : Query} (h : Authorized q)
    {p : ManagedPolicy} (hp : q.stateMember = some p) : q.registryMember = some p := by
  have hc := authorized_pins_state_conformance h p (lookupPolicy_mem hp)
  rw [lookupPolicy_asset hp] at hc
  exact hc

/-- The pre-state row is a member of both lists, names the command's asset, and
is a governed, enabled, registered ordinary token. -/
theorem authorized_pins_member {q : Query} (h : Authorized q) {p : ManagedPolicy}
    (hp : q.stateMember = some p) :
    p ∈ q.state.policies ∧ p ∈ q.managedRegistry.policies ∧ p.asset = q.cmd.asset ∧
    q.registryMember = some p ∧
    p.assetClass = AssetClass.registeredOrdinaryToken ∧ p.enabled = true := by
  have hgov := authorized_state_member_is_governed h hp
  have h1 := h .ordinaryClass
  have h2 := h .enabled
  simp only [obligationHolds, hp, decide_eq_true_eq] at h1 h2
  exact ⟨lookupPolicy_mem hp, lookupPolicy_mem hgov, lookupPolicy_asset hp, hgov, h1, h2⟩

/-- `ManagedAssetLifecyclePolicyV1.__post_init__` forbids generic authority on
any class other than `REGISTERED_ORDINARY_TOKEN`. This model does not enforce
that at construction; the predicate is named so its consequence below is
visible. -/
def PolicyClassDisciplined (p : ManagedPolicy) : Prop :=
  p.assetClass ≠ AssetClass.registeredOrdinaryToken →
    p.issueAuthority = none ∧ p.selfBurnPolicyRoot = none

/-- Under the constructor's class discipline the `ordinaryClass` obligation is
already implied by the subject rule: a non-ordinary policy carries no issue
authority and no self-burn root, so no subject matches. The obligation is
therefore defence in depth against a policy row the Python constructor would
already reject. -/
theorem ordinaryClass_redundant_under_class_discipline {q : Query} {p : ManagedPolicy}
    (hp : q.stateMember = some p) (hdisc : PolicyClassDisciplined p)
    (hkind : obligationHolds q .commandKindExact = true)
    (hsubject : obligationHolds q .subject = true) :
    p.assetClass = AssetClass.registeredOrdinaryToken := by
  by_cases hcls : p.assetClass = AssetClass.registeredOrdinaryToken
  · exact hcls
  · exfalso
    obtain ⟨hia, hsb⟩ := hdisc hcls
    simp only [obligationHolds, decide_eq_true_eq, ne_eq] at hkind
    cases hk : q.kind with
    | none => exact hkind hk
    | some k =>
        cases k with
        | issue => simp [obligationHolds, hk, hp, hia] at hsubject
        | burn => simp [obligationHolds, hk, hp, hsb] at hsubject

/-- Issue: the pre-state row's paired issue authority is exactly the subject and
grant the context presents. -/
theorem authorized_issue_pins_authority {q : Query} (h : Authorized q) {p : ManagedPolicy}
    (hk : q.kind = some CommandKind.issue) (hp : q.stateMember = some p) :
    p.issueAuthority = some ⟨q.ctx.subject, q.ctx.grantRoot⟩ := by
  cases hia : p.issueAuthority with
  | none =>
      have hs := h .subject
      simp [obligationHolds, hk, hp, hia] at hs
  | some ia =>
      have hs := h .subject
      have hg := h .grant
      simp only [obligationHolds, hk, hp, hia, decide_eq_true_eq] at hs hg
      rw [hs, hg]

/-- Self-burn: the subject is the command's own account owner and the grant is
the pre-state row's self-burn policy root. -/
theorem authorized_burn_pins_owner_and_grant {q : Query} (h : Authorized q)
    {p : ManagedPolicy} (hk : q.kind = some CommandKind.burn) (hp : q.stateMember = some p) :
    q.ctx.subject = q.cmd.accountOwner ∧
    p.selfBurnPolicyRoot = some q.ctx.grantRoot := by
  cases hr : p.selfBurnPolicyRoot with
  | none =>
      have hs := h .subject
      simp [obligationHolds, hk, hp, hr] at hs
  | some root =>
      have hs := h .subject
      have hg := h .grant
      simp only [obligationHolds, hk, hp, hr, decide_eq_true_eq] at hs hg
      exact ⟨hs, by rw [hg]⟩

/-- The exact lifecycle wire kind. -/
theorem authorized_pins_command_kind {q : Query} (h : Authorized q) :
    ∃ k : CommandKind, q.kind = some k ∧ q.cmd.commandKind = k.code := by
  obtain ⟨k, hk⟩ := authorized_kind_exists h
  exact ⟨k, hk, parseCommandKind_eq_some_iff.mp hk⟩

/-! ## 13. Recovering a registry value needs the pairwise no-collision premise

The lane input carries a root, not a registry. Root equality recovers registry
equality exactly when *those two* preimages do not collide, and that is a
hypothesis about the pair, never a global injectivity claim. -/

/-- Under the pairwise no-collision premise for the two compared canonical
preimages, two authorized queries sharing a digest and presenting the same lane
registry root use the same governed registry, hence the same selected module
release and the same policy rows. -/
theorem noCollision_pins_registry {d : Digests} {q₁ q₂ : Query}
    (hnc : NoCollisionOn d q₁.managedRegistry q₂.managedRegistry)
    (h₁ : Authorized q₁) (h₂ : Authorized q₂)
    (hd₁ : q₁.digests = d) (hd₂ : q₂.digests = d)
    (hroot : q₁.ctx.policyRegistryRoot = q₂.ctx.policyRegistryRoot) :
    q₁.managedRegistry = q₂.managedRegistry ∧
    q₁.managedRegistry.moduleReleaseId = q₂.managedRegistry.moduleReleaseId ∧
    q₁.managedRegistry.policies = q₂.managedRegistry.policies := by
  have e₁ := authorized_pins_lane_registry_root h₁
  have e₂ := authorized_pins_lane_registry_root h₂
  simp only [Query.managedRoot, hd₁] at e₁
  simp only [Query.managedRoot, hd₂] at e₂
  have hreg : q₁.managedRegistry = q₂.managedRegistry :=
    hnc (by rw [← e₁, ← e₂, hroot])
  exact ⟨hreg, congrArg ManagedPolicyRegistry.moduleReleaseId hreg,
    congrArg ManagedPolicyRegistry.policies hreg⟩

/-- Without any premise, only root equality is available. This is the
unconditional conclusion, and the challenge module exhibits a colliding pair
that realizes the gap between it and the previous theorem. -/
theorem authorized_pins_root_not_value {q₁ q₂ : Query} (h₁ : Authorized q₁)
    (h₂ : Authorized q₂) (hd : q₁.digests.managed = q₂.digests.managed)
    (hroot : q₁.ctx.policyRegistryRoot = q₂.ctx.policyRegistryRoot) :
    q₁.digests.managed q₁.managedRegistry = q₁.digests.managed q₂.managedRegistry := by
  have e₁ := authorized_pins_lane_registry_root h₁
  have e₂ := authorized_pins_lane_registry_root h₂
  simp only [Query.managedRoot] at e₁ e₂
  rw [← e₁, hroot, e₂, hd]

/-! ## 14. Issue-versus-burn separation

Two narrow statements only. Neither says a governance registry must bind the
two kinds to one inner registry, because the runtime does not require that. -/

/-- One lifecycle command never carries both kinds. This is a statement about a
single command's wire string. -/
theorem lifecycle_kind_is_exclusive {q : Query}
    (h₁ : q.kind = some CommandKind.issue) (h₂ : q.kind = some CommandKind.burn) : False :=
  parseCommandKind_no_kind_confusion q.cmd.commandKind ⟨h₁, h₂⟩

/-- If one context authorizes both an issue and a self-burn against the same
pre-state row, that row's issue policy root and self-burn policy root coincide
and the issue-authority subject is the burned account's owner. This is about one
policy row under one context; it is not a claim about governance bindings. -/
theorem issue_and_burn_from_one_context_forces_shared_grant {q₁ q₂ : Query}
    {p : ManagedPolicy} {ia : IssueAuthority} {root : Root}
    (hia : p.issueAuthority = some ia) (hroot : p.selfBurnPolicyRoot = some root)
    (hctx : q₁.ctx = q₂.ctx)
    (h₁ : Authorized q₁) (hk₁ : q₁.kind = some CommandKind.issue)
    (hp₁ : q₁.stateMember = some p)
    (h₂ : Authorized q₂) (hk₂ : q₂.kind = some CommandKind.burn)
    (hp₂ : q₂.stateMember = some p) :
    ia.policyRoot = root ∧ ia.subject = q₂.cmd.accountOwner := by
  have hI := authorized_issue_pins_authority h₁ hk₁ hp₁
  obtain ⟨hsub, hburn⟩ := authorized_burn_pins_owner_and_grant h₂ hk₂ hp₂
  rw [hia, Option.some.injEq] at hI
  rw [hroot, Option.some.injEq] at hburn
  subst hI
  exact ⟨by simp [hctx, hburn], by simp [hctx, hsub]⟩

/-- Grant-root separation: a policy row that separates its issue and self-burn
policy roots is never authorized for both kinds from one context. -/
theorem distinct_grant_roots_separate_the_two_kinds {q₁ q₂ : Query}
    {p : ManagedPolicy} {ia : IssueAuthority} {root : Root}
    (hia : p.issueAuthority = some ia) (hroot : p.selfBurnPolicyRoot = some root)
    (hne : ia.policyRoot ≠ root) (hctx : q₁.ctx = q₂.ctx)
    (hk₁ : q₁.kind = some CommandKind.issue) (hp₁ : q₁.stateMember = some p)
    (hk₂ : q₂.kind = some CommandKind.burn) (hp₂ : q₂.stateMember = some p) :
    ¬ (Authorized q₁ ∧ Authorized q₂) := by
  rintro ⟨h₁, h₂⟩
  exact hne (issue_and_burn_from_one_context_forces_shared_grant hia hroot hctx
    h₁ hk₁ hp₁ h₂ hk₂ hp₂).1

/-! ## 15. The supply-effect kind the authorization selects

The runtime picks `EconomicEffectKindV1.ISSUE` or `.BURN` from the command kind.
Only that selection is modeled: no delta, amount, row, plan, or conservation
claim is made. -/

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

theorem supplyEffectKind_codes_differ :
    (authorizedSupplyEffectKind CommandKind.issue).code ≠
      (authorizedSupplyEffectKind CommandKind.burn).code := by decide

/-! ## 16. Source comparison

The omission counterexamples, the empty pre-state rejection, the
issue-occurrence-with-burn-command rejection, the split-kind bundle, and the
colliding-pair fixture live in
`Proofs.ManagedAssetPolicyAuthorityV1Challenge`. -/

end ManagedAssetPolicyAuthorityV1
end Proofs
