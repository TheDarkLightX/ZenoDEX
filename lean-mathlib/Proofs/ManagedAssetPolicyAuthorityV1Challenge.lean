import Proofs.ManagedAssetPolicyAuthorityV1

/-!
# Managed ordinary-token issue and self-burn — bounded authority challenge

The admission challenge for `Proofs.ManagedAssetPolicyAuthorityV1`.

## What the counterexample family actually is

The core defines one `authorizesExcept`, so every counterexample here is one
application of `singleOmission_of` or `coupledOmission_of` with two `decide`s.
Of the fourteen obligations, **eleven are independently omissible** and get a
`SingleOmissionCounterexample`; **three are not**, and each of those gets a
`CoupledOmissionCounterexample` naming the exact set its failure drags with it:

* `commandKindExact` drags `outerBindingRoot`, `routePolicyRoot`, `subject`,
  and `grant`, because an unparseable wire kind has no governance binding, no
  route, and no kind-specific rule to run;
* `registryAssetMember` drags `stateConformance`, because a pre-state row for an
  asset the governed registry does not carry is itself non-conforming;
* `stateAssetMember` drags `ordinaryClass`, `enabled`, `subject`, and `grant`,
  because all four read the pre-state row.

Nothing here is called a single omission unless exactly one obligation fails.

## The two policy rows

`require_managed_asset_policy_membership_v1` checks the *governed registry*
member and pre-state conformance; `_authorize` then reads
`_policy_for(pre_state, command.asset)` and evaluates class, enabled, subject,
and grant from that **pre-state** row. `forgeEmptyState` is the negative
challenge for the gap between them: an empty pre-state policy list satisfies
conformance vacuously and has a governed registry member, yet `_authorize`
returns `UNKNOWN_ASSET`. The authoritative checker rejects it.

## Kind agreement

`forgeCommandKindAgrees` carries an **issue occurrence with a burn command**.
Every root, route, release, membership, subject, and grant obligation passes;
only `commandKindAgrees` fails. That obligation is the one binder check this
model imports, and this is its evidence.

## Per-kind bindings are permitted to differ

`splitIssue` and `splitBurn` are both `Authorized` under one profile and one
outer registry that binds issue and self-burn to **different** inner
registries. The runtime permits that, so no theorem requires the two inner
roots to be equal, and `bundle_pins_each_kind_separately` is what a single
witness buys: its own kind's binding and route, and nothing about the other.

## The no-collision premise is pairwise

`collidingDigests` collides on exactly the pair
`(governedManagedRegistry, supersededManagedRegistry)`. Under it two queries are
both `Authorized`, present the same lane registry root, and carry different
registries selecting different module releases. `honestDigests` discharges
`NoCollisionOn` for that same pair by evaluation — a fact about two fixture
values, not a claim that `hash_global_v1` or SHA-256 is injective.

## Bounded structural comparison only

`challengeReportV1` exists so this model's obligations can be compared, on a
fixed table, against exact runtime candidate commit
`da979883f61648b1a2698f47794b27f5946b2cdb`:
`require_governed_managed_asset_policy_registry_v1`,
`require_managed_asset_policy_membership_v1`, and
`require_managed_asset_route_policy_root_v1` in
`src/core/managed_asset_policy_registry_v1.py`, `_authorize` in
`src/core/managed_asset_lifecycle_module_v1.py` up to its `ZERO_AMOUNT` check,
and the single `actual_command_kind` equality from `_bind_candidate_v1`.
**No such comparison is performed or claimed by this module**; it emits the
string and nothing more.

**This is a bounded policy-helper claim, not the controlled release-route
admission path.** The rest of `_bind_candidate_v1` is not modeled: the
active-profile requirement, the command body hash equality, the exact context
and journal bindings, the route ordered-lane index, the governed module release
and command-variant checks, the statement root, and the release witness. A
`false` entry in the matrix below is a statement about this model's fourteen
obligations only, and never evidence that any runtime path is missing a check.

Amounts, balances, supplies, widths, effect rows, post-states, receipts,
journals, digest preimage or collision resistance, check ordering, and the
runtime reject-code enumeration are likewise outside the model. Nothing here
asserts custody, possession, title, control, or key control over any asset, and
nothing here confers settlement, release, publication, or value-moving
authority.
-/

namespace Proofs
namespace ManagedAssetPolicyAuthorityV1Challenge

open Proofs.ManagedAssetPolicyAuthorityV1

/-! ## 1. Bound signatures -/

theorem challenge_checker_decides_witness :
    ∀ q : Query, authorizes q = true ↔ Authorized q :=
  authorizes_eq_true_iff

/-- The two-level binding, for this query's one command kind. -/
theorem challenge_pins_two_level_binding :
    ∀ q : Query, Authorized q →
      q.digests.outer q.outerRegistry = q.profile.policyRegistryRoot ∧
      (∃ b : PolicyBinding, q.outerBinding = some b ∧
        b.commandKind = q.cmd.commandKind ∧ b.policyRoot = q.managedRoot) ∧
      (∃ r : RouteRelease, q.route = some r ∧
        r.commandKind = q.cmd.commandKind ∧ r.issueBurnPolicyRoot = q.managedRoot) ∧
      q.ctx.policyRegistryRoot = q.managedRoot :=
  fun _ h => authorized_pins_two_level_binding h

/-- Each command kind is bound separately; one witness never pins both. -/
theorem challenge_bundle_pins_each_kind_separately :
    ∀ qI qB : Query, Authorized qI → Authorized qB →
      qI.cmd.commandKind = CommandKind.issue.code →
      qB.cmd.commandKind = CommandKind.burn.code →
        (∃ b : PolicyBinding, qI.outerBinding = some b ∧
          b.commandKind = CommandKind.issue.code ∧ b.policyRoot = qI.managedRoot) ∧
        (∃ b : PolicyBinding, qB.outerBinding = some b ∧
          b.commandKind = CommandKind.burn.code ∧ b.policyRoot = qB.managedRoot) ∧
        (∃ r : RouteRelease, qI.route = some r ∧
          r.commandKind = CommandKind.issue.code ∧
          r.issueBurnPolicyRoot = qI.managedRoot) ∧
        (∃ r : RouteRelease, qB.route = some r ∧
          r.commandKind = CommandKind.burn.code ∧
          r.issueBurnPolicyRoot = qB.managedRoot) :=
  fun _ _ hI hB hkI hkB => bundle_pins_each_kind_separately hI hB hkI hkB

/-- The imported binder check. -/
theorem challenge_command_kinds_agree :
    ∀ q : Query, Authorized q → q.occurrence.commandKind = q.cmd.commandKind :=
  fun _ h => authorized_command_kinds_agree h

/-- The inner registry selects the release both the context and the pre-state
execute under. -/
theorem challenge_pins_module_release :
    ∀ q : Query, Authorized q →
      q.managedRegistry.moduleReleaseId = q.ctx.moduleReleaseId ∧
      q.managedRegistry.moduleReleaseId = q.state.moduleReleaseId :=
  fun _ h => ⟨(authorized_pins_module_release h).1, (authorized_pins_module_release h).2.1⟩

/-- Both policy rows exist and coincide: the row `_authorize` reads is the
governed registry member. -/
theorem challenge_state_row_is_governed_row :
    ∀ q : Query, Authorized q →
      ∃ p : ManagedPolicy, q.stateMember = some p ∧ q.registryMember = some p ∧
        p.assetClass = AssetClass.registeredOrdinaryToken ∧ p.enabled = true :=
  fun _ h => by
    obtain ⟨p, hp⟩ := authorized_stateMember_exists h
    obtain ⟨-, -, -, hgov, hcls, hen⟩ := authorized_pins_member h hp
    exact ⟨p, hp, hgov, hcls, hen⟩

/-- Issue pins the pre-state row's paired issue authority. -/
theorem challenge_issue_pins_authority :
    ∀ (q : Query) (p : ManagedPolicy), Authorized q →
      q.kind = some CommandKind.issue → q.stateMember = some p →
        p.issueAuthority = some ⟨q.ctx.subject, q.ctx.grantRoot⟩ :=
  fun _ _ h hk hp => authorized_issue_pins_authority h hk hp

/-- Self-burn pins the account owner and the self-burn grant. -/
theorem challenge_burn_pins_owner_and_grant :
    ∀ (q : Query) (p : ManagedPolicy), Authorized q →
      q.kind = some CommandKind.burn → q.stateMember = some p →
        q.ctx.subject = q.cmd.accountOwner ∧
        p.selfBurnPolicyRoot = some q.ctx.grantRoot :=
  fun _ _ h hk hp => authorized_burn_pins_owner_and_grant h hk hp

/-- Recovering a registry value from a root needs the *pairwise* premise. -/
theorem challenge_no_collision_pins_registry :
    ∀ (d : Digests) (q₁ q₂ : Query),
      NoCollisionOn d q₁.managedRegistry q₂.managedRegistry →
      Authorized q₁ → Authorized q₂ → q₁.digests = d → q₂.digests = d →
        q₁.ctx.policyRegistryRoot = q₂.ctx.policyRegistryRoot →
          q₁.managedRegistry = q₂.managedRegistry :=
  fun _ _ _ hnc h₁ h₂ hd₁ hd₂ hr =>
    (noCollision_pins_registry hnc h₁ h₂ hd₁ hd₂ hr).1

theorem challenge_rejection_is_absence :
    ∀ (q : Query) (o : Obligation), obligationHolds q o = false →
      authorizes q = false ∧ ¬ Authorized q :=
  fun _ _ h =>
    ⟨authorizes_eq_false_of_obligation_false h, not_authorized_of_obligation_false h⟩

/-- Kind separation, at the single command's wire string and at one policy row's
two grant roots. Neither statement constrains a governance registry. -/
theorem challenge_kind_separation :
    (∀ q : Query, q.kind = some CommandKind.issue →
        q.kind = some CommandKind.burn → False) ∧
    (∀ (q₁ q₂ : Query) (p : ManagedPolicy) (ia : IssueAuthority) (root : Root),
        p.issueAuthority = some ia → p.selfBurnPolicyRoot = some root →
        ia.policyRoot ≠ root → q₁.ctx = q₂.ctx →
        q₁.kind = some CommandKind.issue → q₁.stateMember = some p →
        q₂.kind = some CommandKind.burn → q₂.stateMember = some p →
          ¬ (Authorized q₁ ∧ Authorized q₂)) :=
  ⟨fun _ h₁ h₂ => lifecycle_kind_is_exclusive h₁ h₂,
    fun _ _ _ _ _ hia hroot hne hctx hk₁ hp₁ hk₂ hp₂ =>
      distinct_grant_roots_separate_the_two_kinds hia hroot hne hctx hk₁ hp₁ hk₂ hp₂⟩

/-! ## 2. Fixture identifiers -/

def currentRelease : Root := "root:asset-transfer-module-release-4"
def staleRelease : Root := "root:asset-transfer-module-release-3"

def governedManagedRoot : Root := "root:managed-policy-registry-7"
def supersededManagedRoot : Root := "root:managed-policy-registry-6"
def altBurnManagedRoot : Root := "root:managed-policy-registry-burn-lane"
def noOrdManagedRoot : Root := "root:managed-policy-registry-no-ord"
def strayManagedRoot : Root := "root:managed-policy-registry-stray"
def unlistedManagedRoot : Root := "root:managed-policy-registry-unlisted"

def governedOuterRoot : Root := "root:economic-policy-registry-7"
def supersededOuterRoot : Root := "root:economic-policy-registry-6"
def splitKindOuterRoot : Root := "root:economic-policy-registry-split"
def noOrdOuterRoot : Root := "root:economic-policy-registry-no-ord"
def strayOuterRoot : Root := "root:economic-policy-registry-stray"
def unlistedOuterRoot : Root := "root:economic-policy-registry-unlisted"

def issuePolicyRoot : Root := "root:ordinary-issue-policy"
def selfBurnRoot : Root := "root:ordinary-self-burn-policy"
def malloryGrantRoot : Root := "root:mallory-grant"

def routeReleaseIssue : Root := "root:route-managed-issue-2"
def routeReleaseBurn : Root := "root:route-managed-burn-2"

def disabledToken : Asset := "DIS"
def ordinaryToken : Asset := "ORD"
def undisciplinedToken : Asset := "UND"
def protocolToken : Asset := "ZUSD"
def absentToken : Asset := "GHOST"

def issuerSubject : Subject := "ordinary-token-issuer"
def alice : Subject := "alice"
def mallory : Subject := "mallory"

theorem fixture_identifiers_distinct :
    governedManagedRoot ≠ supersededManagedRoot ∧
    governedManagedRoot ≠ altBurnManagedRoot ∧
    governedManagedRoot ≠ noOrdManagedRoot ∧
    currentRelease ≠ staleRelease ∧
    issuePolicyRoot ≠ selfBurnRoot ∧
    issuePolicyRoot ≠ malloryGrantRoot ∧
    issuerSubject ≠ mallory ∧ alice ≠ mallory := by decide

/-! ## 3. Governed policy rows -/

def ordinaryPolicy : ManagedPolicy where
  asset := ordinaryToken
  assetClass := AssetClass.registeredOrdinaryToken
  issueAuthority := some ⟨issuerSubject, issuePolicyRoot⟩
  selfBurnPolicyRoot := some selfBurnRoot
  enabled := true

/-- A governed but disabled ordinary token. Fully constructible at runtime. -/
def disabledPolicy : ManagedPolicy :=
  { ordinaryPolicy with asset := disabledToken, enabled := false }

/-- A row carrying generic authority on a non-ordinary class.
`ManagedAssetLifecyclePolicyV1.__post_init__` rejects exactly this combination,
so the row is **not constructible in the runtime**; this model does not encode
that constructor check. It exists only to make the `ordinaryClass` obligation's
counterexample concrete, and
`ordinaryClass_redundant_under_class_discipline` states why no *disciplined* row
can serve. -/
def undisciplinedPolicy : ManagedPolicy :=
  { ordinaryPolicy with asset := undisciplinedToken, assetClass := AssetClass.canonicalZusd }

def zusdPolicy : ManagedPolicy where
  asset := protocolToken
  assetClass := AssetClass.canonicalZusd
  issueAuthority := none
  selfBurnPolicyRoot := none
  enabled := true

/-- A pre-state row that differs from its governed counterpart. -/
def tamperedZusdPolicy : ManagedPolicy := { zusdPolicy with enabled := false }

theorem disciplined_rows_are_disciplined :
    PolicyClassDisciplined ordinaryPolicy ∧
    PolicyClassDisciplined disabledPolicy ∧
    PolicyClassDisciplined zusdPolicy ∧
    ¬ PolicyClassDisciplined undisciplinedPolicy := by
  refine ⟨fun h => absurd rfl h, fun h => absurd rfl h, fun _ => ⟨rfl, rfl⟩, ?_⟩
  intro h
  obtain ⟨hia, -⟩ := h (by decide)
  exact absurd hia (by decide)

/-! ## 4. Registries, routes, profiles, digests -/

def governedPolicyRows : List ManagedPolicy :=
  [disabledPolicy, ordinaryPolicy, undisciplinedPolicy, zusdPolicy]

def governedManagedRegistry : ManagedPolicyRegistry where
  moduleReleaseId := currentRelease
  policies := governedPolicyRows

/-- The same policy rows, selecting a superseded module release. -/
def supersededManagedRegistry : ManagedPolicyRegistry :=
  { governedManagedRegistry with moduleReleaseId := staleRelease }

/-- A second governed inner registry, used for the self-burn lane in the
split-kind bundle. -/
def altBurnManagedRegistry : ManagedPolicyRegistry where
  moduleReleaseId := currentRelease
  policies := [ordinaryPolicy]

/-- A governed registry that does not carry the ordinary token at all. -/
def noOrdManagedRegistry : ManagedPolicyRegistry where
  moduleReleaseId := currentRelease
  policies := [zusdPolicy]

def governedOuterRegistry : EconomicPolicyRegistry where
  bindings :=
    [ ⟨managedAssetPolicyKind, CommandKind.burn.code, governedManagedRoot⟩,
      ⟨managedAssetPolicyKind, CommandKind.issue.code, governedManagedRoot⟩ ]

def supersededOuterRegistry : EconomicPolicyRegistry where
  bindings :=
    [ ⟨managedAssetPolicyKind, CommandKind.burn.code, supersededManagedRoot⟩,
      ⟨managedAssetPolicyKind, CommandKind.issue.code, supersededManagedRoot⟩ ]

/-- Issue and self-burn bound to **different** inner registries. The runtime
permits this; the binding key is `(policy_kind, command_kind)`. -/
def splitKindOuterRegistry : EconomicPolicyRegistry where
  bindings :=
    [ ⟨managedAssetPolicyKind, CommandKind.burn.code, altBurnManagedRoot⟩,
      ⟨managedAssetPolicyKind, CommandKind.issue.code, governedManagedRoot⟩ ]

def noOrdOuterRegistry : EconomicPolicyRegistry where
  bindings :=
    [ ⟨managedAssetPolicyKind, CommandKind.burn.code, noOrdManagedRoot⟩,
      ⟨managedAssetPolicyKind, CommandKind.issue.code, noOrdManagedRoot⟩ ]

def issueRoute : RouteRelease where
  routeReleaseId := routeReleaseIssue
  commandKind := CommandKind.issue.code
  issueBurnPolicyRoot := governedManagedRoot
  status := ReleaseStatus.activeNew
  acceptsNewObjects := true

def burnRoute : RouteRelease where
  routeReleaseId := routeReleaseBurn
  commandKind := CommandKind.burn.code
  issueBurnPolicyRoot := governedManagedRoot
  status := ReleaseStatus.activeNew
  acceptsNewObjects := true

def governedRouteRegistry : RouteRegistry where
  routes := [issueRoute, burnRoute]

def strayRouteRegistry : RouteRegistry where
  routes := [{ issueRoute with issueBurnPolicyRoot := altBurnManagedRoot }, burnRoute]

def retiredRouteRegistry : RouteRegistry where
  routes := [{ issueRoute with status := ReleaseStatus.retired }, burnRoute]

def drainOnlyRouteRegistry : RouteRegistry where
  routes := [{ issueRoute with acceptsNewObjects := false }, burnRoute]

def supersededRouteRegistry : RouteRegistry where
  routes :=
    [ { issueRoute with issueBurnPolicyRoot := supersededManagedRoot },
      { burnRoute with issueBurnPolicyRoot := supersededManagedRoot } ]

def splitKindRouteRegistry : RouteRegistry where
  routes := [issueRoute, { burnRoute with issueBurnPolicyRoot := altBurnManagedRoot }]

def noOrdRouteRegistry : RouteRegistry where
  routes :=
    [ { issueRoute with issueBurnPolicyRoot := noOrdManagedRoot },
      { burnRoute with issueBurnPolicyRoot := noOrdManagedRoot } ]

def activeProfile : Profile where
  profileId := "root:profile-7"
  policyRegistryRoot := governedOuterRoot
  routeRegistry := governedRouteRegistry

/-- A content digest for the inner registry: a total function of registry
content, standing in for `hash_global_v1`. -/
def managedRootOf : ManagedPolicyRegistry → Root := fun r =>
  if r = governedManagedRegistry then governedManagedRoot
  else if r = supersededManagedRegistry then supersededManagedRoot
  else if r = altBurnManagedRegistry then altBurnManagedRoot
  else if r = noOrdManagedRegistry then noOrdManagedRoot
  else unlistedManagedRoot

def outerRootOf : EconomicPolicyRegistry → Root := fun r =>
  if r = governedOuterRegistry then governedOuterRoot
  else if r = supersededOuterRegistry then supersededOuterRoot
  else if r = splitKindOuterRegistry then splitKindOuterRoot
  else if r = noOrdOuterRegistry then noOrdOuterRoot
  else unlistedOuterRoot

def honestDigests : Digests where
  outer := outerRootOf
  managed := managedRootOf

/-! ## 5. Occurrences, contexts, state, commands -/

def issueOccurrence : Occurrence where
  commandKind := CommandKind.issue.code
  routeReleaseId := routeReleaseIssue

def burnOccurrence : Occurrence where
  commandKind := CommandKind.burn.code
  routeReleaseId := routeReleaseBurn

def issueContext : Context where
  policyRegistryRoot := governedManagedRoot
  moduleReleaseId := currentRelease
  subject := issuerSubject
  grantRoot := issuePolicyRoot

def burnContext : Context where
  policyRegistryRoot := governedManagedRoot
  moduleReleaseId := currentRelease
  subject := alice
  grantRoot := selfBurnRoot

/-- The pre-state carries exactly the governed rows, so conformance holds. -/
def governedState : ModuleState where
  moduleReleaseId := currentRelease
  policies := governedPolicyRows

def issueCommand : Command where
  commandKind := CommandKind.issue.code
  asset := ordinaryToken
  accountOwner := alice

def burnCommand : Command where
  commandKind := CommandKind.burn.code
  asset := ordinaryToken
  accountOwner := alice

/-! ## 6. The two honest queries -/

def honestIssue : Query where
  digests := honestDigests
  profile := activeProfile
  outerRegistry := governedOuterRegistry
  managedRegistry := governedManagedRegistry
  occurrence := issueOccurrence
  ctx := issueContext
  state := governedState
  cmd := issueCommand

def honestBurn : Query :=
  { honestIssue with occurrence := burnOccurrence, ctx := burnContext, cmd := burnCommand }

theorem honest_queries_authorize :
    authorizes honestIssue = true ∧ authorizes honestBurn = true := by decide

theorem honestIssue_authorized : Authorized honestIssue :=
  (authorizes_eq_true_iff honestIssue).mp honest_queries_authorize.1

theorem honestBurn_authorized : Authorized honestBurn :=
  (authorizes_eq_true_iff honestBurn).mp honest_queries_authorize.2

/-- Non-vacuity: both policy rows resolve, and they coincide. -/
theorem honestIssue_pins :
    honestIssue.stateMember = some ordinaryPolicy ∧
    honestIssue.registryMember = some ordinaryPolicy ∧
    honestIssue.kind = some CommandKind.issue ∧
    honestIssue.managedRoot = governedManagedRoot ∧
    honestIssue.managedRegistry.moduleReleaseId = currentRelease := by decide

theorem honestIssue_issue_authority :
    ordinaryPolicy.issueAuthority =
      some ⟨honestIssue.ctx.subject, honestIssue.ctx.grantRoot⟩ :=
  authorized_issue_pins_authority honestIssue_authorized (by decide) (by decide)

theorem honestBurn_owner_and_grant :
    honestBurn.ctx.subject = honestBurn.cmd.accountOwner ∧
    ordinaryPolicy.selfBurnPolicyRoot = some honestBurn.ctx.grantRoot :=
  authorized_burn_pins_owner_and_grant honestBurn_authorized (by decide) (by decide)

/-! ## 7. Eleven independently omissible obligations

Each query below breaks exactly **one** obligation. There are twelve theorems
for eleven obligations: `grant` carries two witnesses, one on the issue lane
(`singleOmission_grant`) and one on the self-burn lane
(`singleOmission_grant_selfBurn`). The distinct-obligation count is eleven, and
`eleven_single_omissions_are_strictly_weaker` enumerates exactly those eleven. -/

def forgeOuterProfileRoot : Query :=
  { honestIssue with profile := { activeProfile with policyRegistryRoot := strayOuterRoot } }

theorem singleOmission_outerProfileRoot :
    SingleOmissionCounterexample forgeOuterProfileRoot Obligation.outerProfileRoot :=
  singleOmission_of (by decide) (by decide)

/-- The outer registry binds `managed_asset_burn` to a different inner registry
than the one this self-burn executes against. -/
def forgeOuterBindingRoot : Query :=
  { honestBurn with
      outerRegistry := splitKindOuterRegistry
      profile := { activeProfile with policyRegistryRoot := splitKindOuterRoot } }

theorem singleOmission_outerBindingRoot :
    SingleOmissionCounterexample forgeOuterBindingRoot Obligation.outerBindingRoot :=
  singleOmission_of (by decide) (by decide)

def forgeRoutePolicyRoot : Query :=
  { honestIssue with profile := { activeProfile with routeRegistry := strayRouteRegistry } }

theorem singleOmission_routePolicyRoot :
    SingleOmissionCounterexample forgeRoutePolicyRoot Obligation.routePolicyRoot :=
  singleOmission_of (by decide) (by decide)

def forgeLaneRegistryRoot : Query :=
  { honestIssue with ctx := { issueContext with policyRegistryRoot := strayManagedRoot } }

theorem singleOmission_laneRegistryRoot :
    SingleOmissionCounterexample forgeLaneRegistryRoot Obligation.laneRegistryRoot :=
  singleOmission_of (by decide) (by decide)

/-- A **consistent** superseded governance bundle: profile, outer registry,
route, and lane input all name the superseded inner registry, so every root
check passes. Only the release that registry selects differs from the release
the context and the live pre-state execute under. -/
def forgeModuleRelease : Query :=
  { honestIssue with
      profile :=
        { activeProfile with
            policyRegistryRoot := supersededOuterRoot
            routeRegistry := supersededRouteRegistry }
      outerRegistry := supersededOuterRegistry
      managedRegistry := supersededManagedRegistry
      ctx := { issueContext with policyRegistryRoot := supersededManagedRoot } }

theorem forgeModuleRelease_passes_every_root_check :
    obligationHolds forgeModuleRelease Obligation.outerProfileRoot = true ∧
    obligationHolds forgeModuleRelease Obligation.outerBindingRoot = true ∧
    obligationHolds forgeModuleRelease Obligation.routePolicyRoot = true ∧
    obligationHolds forgeModuleRelease Obligation.laneRegistryRoot = true ∧
    obligationHolds forgeModuleRelease Obligation.moduleRelease = false := by decide

theorem singleOmission_moduleRelease :
    SingleOmissionCounterexample forgeModuleRelease Obligation.moduleRelease :=
  singleOmission_of (by decide) (by decide)

/-- A pre-state row for a *non-command* asset that differs from its governed
counterpart. Conformance covers the whole carried list, not only the command's
row. -/
def forgeStateConformance : Query :=
  { honestIssue with
      state :=
        { governedState with
            policies := [disabledPolicy, ordinaryPolicy, undisciplinedPolicy,
                         tamperedZusdPolicy] } }

theorem forgeStateConformance_is_material :
    lookupPolicy protocolToken forgeStateConformance.managedRegistry.policies
      = some zusdPolicy ∧
    lookupPolicy protocolToken forgeStateConformance.state.policies
      = some tamperedZusdPolicy ∧
    tamperedZusdPolicy ≠ zusdPolicy := by decide

theorem singleOmission_stateConformance :
    SingleOmissionCounterexample forgeStateConformance Obligation.stateConformance :=
  singleOmission_of (by decide) (by decide)

/-- **An issue occurrence carrying a burn command.** Every root, route, release,
membership, class, enabled, subject, and grant obligation passes; the outer
binding and the route are selected for issue while the lifecycle grant rule runs
for self-burn. Only `commandKindAgrees` catches it. -/
def forgeCommandKindAgrees : Query :=
  { honestIssue with ctx := burnContext, cmd := burnCommand }

theorem forgeCommandKindAgrees_is_the_kind_split :
    forgeCommandKindAgrees.occurrence.commandKind = CommandKind.issue.code ∧
    forgeCommandKindAgrees.cmd.commandKind = CommandKind.burn.code ∧
    obligationHolds forgeCommandKindAgrees Obligation.outerBindingRoot = true ∧
    obligationHolds forgeCommandKindAgrees Obligation.routePolicyRoot = true ∧
    obligationHolds forgeCommandKindAgrees Obligation.subject = true ∧
    obligationHolds forgeCommandKindAgrees Obligation.grant = true ∧
    obligationHolds forgeCommandKindAgrees Obligation.commandKindAgrees = false := by
  decide

/-- The former counterexample, compiled as a rejection: the authoritative
checker refuses an issue occurrence carrying a burn command, and no witness
exists. -/
theorem kindSplit_is_rejected :
    authorizes forgeCommandKindAgrees = false ∧ ¬ Authorized forgeCommandKindAgrees :=
  ⟨by decide,
    not_authorized_of_obligation_false
      (o := Obligation.commandKindAgrees) (by decide)⟩

theorem singleOmission_commandKindAgrees :
    SingleOmissionCounterexample forgeCommandKindAgrees Obligation.commandKindAgrees :=
  singleOmission_of (by decide) (by decide)

/-- A pre-state row on a non-ordinary class that still carries generic
authority. The runtime constructor rejects this row, so the obligation is
defence in depth. -/
def forgeOrdinaryClass : Query :=
  { honestIssue with cmd := { issueCommand with asset := undisciplinedToken } }

theorem singleOmission_ordinaryClass :
    SingleOmissionCounterexample forgeOrdinaryClass Obligation.ordinaryClass :=
  singleOmission_of (by decide) (by decide)

def forgeEnabled : Query :=
  { honestIssue with cmd := { issueCommand with asset := disabledToken } }

theorem singleOmission_enabled :
    SingleOmissionCounterexample forgeEnabled Obligation.enabled :=
  singleOmission_of (by decide) (by decide)

def forgeSubject : Query :=
  { honestIssue with ctx := { issueContext with subject := mallory } }

theorem singleOmission_subject :
    SingleOmissionCounterexample forgeSubject Obligation.subject :=
  singleOmission_of (by decide) (by decide)

def forgeGrant : Query :=
  { honestIssue with ctx := { issueContext with grantRoot := malloryGrantRoot } }

theorem singleOmission_grant :
    SingleOmissionCounterexample forgeGrant Obligation.grant :=
  singleOmission_of (by decide) (by decide)

/-- The account owner self-burns while presenting the *issue* lane's policy root
as her grant. The subject rule passes; only the grant rule catches it. -/
def forgeCrossGrantBurn : Query :=
  { honestBurn with ctx := { burnContext with grantRoot := issuePolicyRoot } }

theorem singleOmission_grant_selfBurn :
    SingleOmissionCounterexample forgeCrossGrantBurn Obligation.grant :=
  singleOmission_of (by decide) (by decide)

theorem forgeCrossGrantBurn_subject_rule_passes :
    obligationHolds forgeCrossGrantBurn Obligation.subject = true ∧
    obligationHolds forgeCrossGrantBurn Obligation.grant = false := by decide

/-! ## 8. Three coupled obligations

Each of these cannot fail alone. The counterexample removes the whole coupled
set, and the accompanying theorem names exactly what the failure drags with
it. -/

/-- An unparseable wire kind, carried consistently by the occurrence so that
`commandKindAgrees` still passes. -/
def forgeUnknownKind : Query :=
  { honestIssue with
      occurrence := { issueOccurrence with commandKind := "managed_asset_mint" }
      cmd := { issueCommand with commandKind := "managed_asset_mint" } }

theorem unknownKind_coupled_set :
    obligationHolds forgeUnknownKind Obligation.commandKindExact = false ∧
    obligationHolds forgeUnknownKind Obligation.outerBindingRoot = false ∧
    obligationHolds forgeUnknownKind Obligation.routePolicyRoot = false ∧
    obligationHolds forgeUnknownKind Obligation.subject = false ∧
    obligationHolds forgeUnknownKind Obligation.grant = false ∧
    obligationHolds forgeUnknownKind Obligation.commandKindAgrees = true ∧
    authorizesOmitting forgeUnknownKind Obligation.commandKindExact = false := by decide

theorem coupledOmission_commandKindExact :
    CoupledOmissionCounterexample forgeUnknownKind
      [Obligation.commandKindExact, Obligation.outerBindingRoot,
       Obligation.routePolicyRoot, Obligation.subject, Obligation.grant] :=
  coupledOmission_of (o := Obligation.commandKindExact) (by decide) (by decide)

/-- A consistent governance bundle whose inner registry does not carry the
ordinary token, while the pre-state does. -/
def forgeRegistryAssetMember : Query :=
  { honestIssue with
      profile :=
        { activeProfile with
            policyRegistryRoot := noOrdOuterRoot
            routeRegistry := noOrdRouteRegistry }
      outerRegistry := noOrdOuterRegistry
      managedRegistry := noOrdManagedRegistry
      ctx := { issueContext with policyRegistryRoot := noOrdManagedRoot }
      state := { governedState with policies := [ordinaryPolicy, zusdPolicy] } }

theorem registryAssetMember_coupled_set :
    obligationHolds forgeRegistryAssetMember Obligation.registryAssetMember = false ∧
    obligationHolds forgeRegistryAssetMember Obligation.stateConformance = false ∧
    obligationHolds forgeRegistryAssetMember Obligation.stateAssetMember = true ∧
    obligationHolds forgeRegistryAssetMember Obligation.subject = true ∧
    obligationHolds forgeRegistryAssetMember Obligation.grant = true ∧
    authorizesOmitting forgeRegistryAssetMember Obligation.registryAssetMember = false := by
  decide

theorem coupledOmission_registryAssetMember :
    CoupledOmissionCounterexample forgeRegistryAssetMember
      [Obligation.registryAssetMember, Obligation.stateConformance] :=
  coupledOmission_of (o := Obligation.registryAssetMember) (by decide) (by decide)

/-- **The empty pre-state policy list.** Conformance holds vacuously and the
governed registry member exists, yet `_authorize` reads
`_policy_for(pre_state, asset)` and returns `UNKNOWN_ASSET`. The authoritative
checker rejects this query. -/
def forgeEmptyState : Query :=
  { honestIssue with state := { governedState with policies := [] } }

theorem emptyState_is_rejected :
    obligationHolds forgeEmptyState Obligation.stateConformance = true ∧
    obligationHolds forgeEmptyState Obligation.registryAssetMember = true ∧
    obligationHolds forgeEmptyState Obligation.stateAssetMember = false ∧
    obligationHolds forgeEmptyState Obligation.ordinaryClass = false ∧
    obligationHolds forgeEmptyState Obligation.enabled = false ∧
    obligationHolds forgeEmptyState Obligation.subject = false ∧
    obligationHolds forgeEmptyState Obligation.grant = false ∧
    authorizes forgeEmptyState = false ∧
    ¬ Authorized forgeEmptyState := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  exact not_authorized_of_obligation_false
    (o := Obligation.stateAssetMember) (by decide)

theorem coupledOmission_stateAssetMember :
    CoupledOmissionCounterexample forgeEmptyState
      [Obligation.stateAssetMember, Obligation.ordinaryClass, Obligation.enabled,
       Obligation.subject, Obligation.grant] :=
  coupledOmission_of (o := Obligation.stateAssetMember) (by decide) (by decide)

/-! ## 9. Cardinality of the omission family

Eleven single omissions and three coupled sets, totalling the fourteen
obligations. -/

theorem eleven_single_omissions_are_strictly_weaker :
    (¬ ∀ r : Query, authorizesOmitting r Obligation.outerProfileRoot = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.outerBindingRoot = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.routePolicyRoot = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.laneRegistryRoot = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.moduleRelease = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.stateConformance = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.commandKindAgrees = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.ordinaryClass = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.enabled = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.subject = authorizes r) ∧
    (¬ ∀ r : Query, authorizesOmitting r Obligation.grant = authorizes r) :=
  ⟨strictly_weaker_of_omission singleOmission_outerProfileRoot,
    strictly_weaker_of_omission singleOmission_outerBindingRoot,
    strictly_weaker_of_omission singleOmission_routePolicyRoot,
    strictly_weaker_of_omission singleOmission_laneRegistryRoot,
    strictly_weaker_of_omission singleOmission_moduleRelease,
    strictly_weaker_of_omission singleOmission_stateConformance,
    strictly_weaker_of_omission singleOmission_commandKindAgrees,
    strictly_weaker_of_omission singleOmission_ordinaryClass,
    strictly_weaker_of_omission singleOmission_enabled,
    strictly_weaker_of_omission singleOmission_subject,
    strictly_weaker_of_omission singleOmission_grant⟩

theorem three_coupled_omissions_are_strictly_weaker :
    (¬ ∀ r : Query, authorizesExcept r
        (fun o => [Obligation.commandKindExact, Obligation.outerBindingRoot,
                   Obligation.routePolicyRoot, Obligation.subject,
                   Obligation.grant].contains o) = authorizes r) ∧
    (¬ ∀ r : Query, authorizesExcept r
        (fun o => [Obligation.registryAssetMember,
                   Obligation.stateConformance].contains o) = authorizes r) ∧
    (¬ ∀ r : Query, authorizesExcept r
        (fun o => [Obligation.stateAssetMember, Obligation.ordinaryClass,
                   Obligation.enabled, Obligation.subject,
                   Obligation.grant].contains o) = authorizes r) :=
  ⟨strictly_weaker_of_omission coupledOmission_commandKindExact,
    strictly_weaker_of_omission coupledOmission_registryAssetMember,
    strictly_weaker_of_omission coupledOmission_stateAssetMember⟩

/-- The eleven single omissions and the three coupled heads exhaust the closed
obligation registry. -/
theorem omission_family_covers_all_obligations :
    ([Obligation.outerProfileRoot, Obligation.outerBindingRoot,
      Obligation.routePolicyRoot, Obligation.laneRegistryRoot,
      Obligation.moduleRelease, Obligation.stateConformance,
      Obligation.commandKindAgrees, Obligation.ordinaryClass, Obligation.enabled,
      Obligation.subject, Obligation.grant] ++
     [Obligation.commandKindExact, Obligation.registryAssetMember,
      Obligation.stateAssetMember]).length = allObligations.length ∧
    ∀ o : Obligation,
      o ∈ ([Obligation.outerProfileRoot, Obligation.outerBindingRoot,
            Obligation.routePolicyRoot, Obligation.laneRegistryRoot,
            Obligation.moduleRelease, Obligation.stateConformance,
            Obligation.commandKindAgrees, Obligation.ordinaryClass,
            Obligation.enabled, Obligation.subject, Obligation.grant] ++
           [Obligation.commandKindExact, Obligation.registryAssetMember,
            Obligation.stateAssetMember]) := by
  refine ⟨rfl, ?_⟩
  intro o
  cases o <;> decide

/-! ## 10. Route status and claimed-release rejections -/

theorem route_status_and_claim_rejections :
    obligationHolds
      { honestIssue with profile := { activeProfile with routeRegistry := retiredRouteRegistry } }
      Obligation.routePolicyRoot = false ∧
    obligationHolds
      { honestIssue with profile := { activeProfile with routeRegistry := drainOnlyRouteRegistry } }
      Obligation.routePolicyRoot = false ∧
    obligationHolds
      { honestIssue with occurrence := { issueOccurrence with routeReleaseId := routeReleaseBurn } }
      Obligation.routePolicyRoot = false := by decide

/-! ## 11. Per-kind bindings may name different inner registries

One profile, one outer registry, two inner registries. Both queries are
authorized. This is why no theorem requires the issue and self-burn inner roots
to coincide. -/

def splitKindProfile : Profile where
  profileId := "root:profile-7"
  policyRegistryRoot := splitKindOuterRoot
  routeRegistry := splitKindRouteRegistry

def splitIssue : Query :=
  { honestIssue with profile := splitKindProfile, outerRegistry := splitKindOuterRegistry }

def splitBurn : Query :=
  { honestIssue with
      profile := splitKindProfile
      outerRegistry := splitKindOuterRegistry
      managedRegistry := altBurnManagedRegistry
      occurrence := burnOccurrence
      ctx := { burnContext with policyRegistryRoot := altBurnManagedRoot }
      state := { governedState with policies := [ordinaryPolicy] }
      cmd := burnCommand }

theorem splitKind_bundle_authorizes_both_kinds :
    authorizes splitIssue = true ∧ authorizes splitBurn = true := by decide

theorem splitKind_inner_registries_differ :
    splitIssue.managedRegistry ≠ splitBurn.managedRegistry ∧
    splitIssue.managedRoot ≠ splitBurn.managedRoot ∧
    splitIssue.profile = splitBurn.profile ∧
    splitIssue.outerRegistry = splitBurn.outerRegistry := by decide

/-- The bundle theorem applied to the split fixture: each kind pins its own
binding and route, and nothing ties the two inner roots together. -/
theorem splitKind_each_kind_pins_its_own :
    (∃ b : PolicyBinding, splitIssue.outerBinding = some b ∧
      b.commandKind = CommandKind.issue.code ∧ b.policyRoot = splitIssue.managedRoot) ∧
    (∃ b : PolicyBinding, splitBurn.outerBinding = some b ∧
      b.commandKind = CommandKind.burn.code ∧ b.policyRoot = splitBurn.managedRoot) ∧
    (∃ r : RouteRelease, splitIssue.route = some r ∧
      r.commandKind = CommandKind.issue.code ∧
      r.issueBurnPolicyRoot = splitIssue.managedRoot) ∧
    (∃ r : RouteRelease, splitBurn.route = some r ∧
      r.commandKind = CommandKind.burn.code ∧
      r.issueBurnPolicyRoot = splitBurn.managedRoot) :=
  bundle_pins_each_kind_separately
    ((authorizes_eq_true_iff _).mp splitKind_bundle_authorizes_both_kinds.1)
    ((authorizes_eq_true_iff _).mp splitKind_bundle_authorizes_both_kinds.2)
    rfl rfl

/-! ## 12. Kind separation on the fixtures -/

theorem governedPolicy_separates_the_two_kinds (q₁ q₂ : Query) (hctx : q₁.ctx = q₂.ctx)
    (hk₁ : q₁.kind = some CommandKind.issue) (hp₁ : q₁.stateMember = some ordinaryPolicy)
    (hk₂ : q₂.kind = some CommandKind.burn) (hp₂ : q₂.stateMember = some ordinaryPolicy) :
    ¬ (Authorized q₁ ∧ Authorized q₂) :=
  distinct_grant_roots_separate_the_two_kinds
    (ia := ⟨issuerSubject, issuePolicyRoot⟩) (root := selfBurnRoot)
    rfl rfl (by decide) hctx hk₁ hp₁ hk₂ hp₂

/-! ## 13. The no-collision premise is pairwise and load-bearing -/

def collidingManagedRootOf : ManagedPolicyRegistry → Root := fun r =>
  if r = supersededManagedRegistry then governedManagedRoot else managedRootOf r

def collidingDigests : Digests where
  outer := outerRootOf
  managed := collidingManagedRootOf

/-- The honest fixture digest discharges the pairwise premise for this one pair
by evaluation. This is a fact about two fixture values and says nothing about
`hash_global_v1` or SHA-256. -/
theorem honestDigests_noCollision_on_the_pair :
    NoCollisionOn honestDigests governedManagedRegistry supersededManagedRegistry := by
  decide

theorem collidingDigests_collide_on_the_pair :
    ¬ NoCollisionOn collidingDigests governedManagedRegistry supersededManagedRegistry := by
  intro h
  exact absurd (h (by decide)) (by decide)

def collidingHonest : Query := { honestIssue with digests := collidingDigests }

def collidingStale : Query :=
  { honestIssue with
      digests := collidingDigests
      managedRegistry := supersededManagedRegistry
      ctx := { issueContext with moduleReleaseId := staleRelease }
      state := { governedState with moduleReleaseId := staleRelease } }

theorem colliding_queries_authorize :
    authorizes collidingHonest = true ∧ authorizes collidingStale = true := by decide

/-- What a colliding pair costs: the lane registry root no longer pins the
registry value, and in particular no longer pins the selected module release. -/
theorem colliding_pair_breaks_registry_pinning :
    Authorized collidingHonest ∧
    Authorized collidingStale ∧
    collidingHonest.ctx.policyRegistryRoot = collidingStale.ctx.policyRegistryRoot ∧
    collidingHonest.managedRegistry ≠ collidingStale.managedRegistry ∧
    collidingHonest.managedRegistry.moduleReleaseId ≠
      collidingStale.managedRegistry.moduleReleaseId ∧
    ¬ NoCollisionOn collidingDigests
        collidingHonest.managedRegistry collidingStale.managedRegistry :=
  ⟨(authorizes_eq_true_iff _).mp colliding_queries_authorize.1,
    (authorizes_eq_true_iff _).mp colliding_queries_authorize.2,
    by decide, by decide, by decide, collidingDigests_collide_on_the_pair⟩

/-! ## 14. Derived report -/

def boolField (b : Bool) : String :=
  if b then "true" else "false"

structure Vector where
  name : String
  query : Query

def vectors : List Vector :=
  [ ⟨"honest_issue", honestIssue⟩,
    ⟨"honest_burn", honestBurn⟩,
    ⟨"forge_outer_profile_root", forgeOuterProfileRoot⟩,
    ⟨"forge_outer_binding_root", forgeOuterBindingRoot⟩,
    ⟨"forge_route_policy_root", forgeRoutePolicyRoot⟩,
    ⟨"forge_lane_registry_root", forgeLaneRegistryRoot⟩,
    ⟨"forge_module_release", forgeModuleRelease⟩,
    ⟨"forge_state_conformance", forgeStateConformance⟩,
    ⟨"forge_command_kind_agrees", forgeCommandKindAgrees⟩,
    ⟨"forge_ordinary_class", forgeOrdinaryClass⟩,
    ⟨"forge_enabled", forgeEnabled⟩,
    ⟨"forge_subject", forgeSubject⟩,
    ⟨"forge_grant", forgeGrant⟩,
    ⟨"forge_cross_grant_burn", forgeCrossGrantBurn⟩,
    ⟨"forge_unknown_kind", forgeUnknownKind⟩,
    ⟨"forge_registry_asset_member", forgeRegistryAssetMember⟩,
    ⟨"forge_empty_state", forgeEmptyState⟩,
    ⟨"split_issue", splitIssue⟩,
    ⟨"split_burn", splitBurn⟩ ]

def obligationRow (q : Query) : List Bool := allObligations.map (obligationHolds q)

def vectorRow (v : Vector) : String :=
  String.intercalate ","
    (["VECTOR", v.name, boolField (authorizes v.query)] ++
      (obligationRow v.query).map boolField)

def obligationHeaderRow : String :=
  String.intercalate "," (["OBLIGATIONS"] ++ allObligations.map (fun o => toString (repr o)))

def kindRow (k : CommandKind) : String :=
  String.intercalate "," ["KIND", k.code, (authorizedSupplyEffectKind k).code]

def classRow (c : AssetClass) : String :=
  String.intercalate "," ["CLASS", c.code]

def statusRow (s : ReleaseStatus) : String :=
  String.intercalate "," ["STATUS", s.code]

def digestRow (name : String) (r : ManagedPolicyRegistry) : String :=
  String.intercalate ","
    ["DIGEST", name, r.moduleReleaseId, managedRootOf r, collidingManagedRootOf r]

def digestRows : List String :=
  [ digestRow "governed" governedManagedRegistry,
    digestRow "superseded" supersededManagedRegistry,
    digestRow "alt_burn" altBurnManagedRegistry,
    digestRow "no_ord" noOrdManagedRegistry ]

def bindingRow (ck : Token) : String :=
  String.intercalate ","
    ["BINDING", ck,
      match lookupBinding managedAssetPolicyKind ck governedOuterRegistry.bindings with
      | none => "NONE"
      | some b => b.policyRoot,
      match lookupBinding managedAssetPolicyKind ck splitKindOuterRegistry.bindings with
      | none => "NONE"
      | some b => b.policyRoot]

def memberRow (a : Asset) : String :=
  String.intercalate ","
    ["MEMBER", a,
      match lookupPolicy a governedManagedRegistry.policies with
      | none => "NONE"
      | some p => p.assetClass.code,
      match lookupPolicy a governedState.policies with
      | none => "NONE"
      | some p => boolField p.enabled]

def memberProbes : List Asset :=
  [disabledToken, ordinaryToken, undisciplinedToken, protocolToken, absentToken]

def challengeReportV1 : String :=
  String.intercalate "\n"
    (allCommandKinds.map kindRow ++
      allAssetClasses.map classRow ++
      allReleaseStatuses.map statusRow ++
      digestRows ++
      allCommandKinds.map (fun k => bindingRow k.code) ++
      memberProbes.map memberRow ++
      [obligationHeaderRow] ++
      vectors.map vectorRow)

/-! ## 15. Report-level sanity facts

Column order is `allObligations`: outerProfileRoot, outerBindingRoot,
routePolicyRoot, laneRegistryRoot, moduleRelease, stateConformance,
commandKindExact, commandKindAgrees, registryAssetMember, stateAssetMember,
ordinaryClass, enabled, subject, grant. -/

theorem obligationMatrix_eq :
    vectors.map (fun v => obligationRow v.query) =
      [ [true, true, true, true, true, true, true, true, true, true, true, true, true, true],
        [true, true, true, true, true, true, true, true, true, true, true, true, true, true],
        [false, true, true, true, true, true, true, true, true, true, true, true, true, true],
        [true, false, true, true, true, true, true, true, true, true, true, true, true, true],
        [true, true, false, true, true, true, true, true, true, true, true, true, true, true],
        [true, true, true, false, true, true, true, true, true, true, true, true, true, true],
        [true, true, true, true, false, true, true, true, true, true, true, true, true, true],
        [true, true, true, true, true, false, true, true, true, true, true, true, true, true],
        [true, true, true, true, true, true, true, false, true, true, true, true, true, true],
        [true, true, true, true, true, true, true, true, true, true, false, true, true, true],
        [true, true, true, true, true, true, true, true, true, true, true, false, true, true],
        [true, true, true, true, true, true, true, true, true, true, true, true, false, true],
        [true, true, true, true, true, true, true, true, true, true, true, true, true, false],
        [true, true, true, true, true, true, true, true, true, true, true, true, true, false],
        [true, false, false, true, true, true, false, true, true, true, true, true, false, false],
        [true, true, true, true, true, false, true, true, false, true, true, true, true, true],
        [true, true, true, true, true, true, true, true, true, false, false, false, false, false],
        [true, true, true, true, true, true, true, true, true, true, true, true, true, true],
        [true, true, true, true, true, true, true, true, true, true, true, true, true, true] ] := by
  decide

theorem checker_verdicts_eq :
    vectors.map (fun v => authorizes v.query) =
      [true, true, false, false, false, false, false, false, false, false, false,
        false, false, false, false, false, false, true, true] := by decide

theorem memberProbes_labels :
    memberProbes.map (fun a =>
        match lookupPolicy a governedManagedRegistry.policies with
        | none => "NONE"
        | some p => p.assetClass.code) =
      [ "registered_ordinary_token", "registered_ordinary_token", "canonical_zusd",
        "canonical_zusd", "NONE" ] := by decide

end ManagedAssetPolicyAuthorityV1Challenge
end Proofs
