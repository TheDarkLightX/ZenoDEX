import Proofs.ManagedAssetPolicyAuthorityV1

/-!
# Managed ordinary-token issue and self-burn — authority challenge module

The admission challenge for `Proofs.ManagedAssetPolicyAuthorityV1`. It does
three jobs.

**Typed challenge statements.** Each `challenge_*` theorem restates an intended
result with its type written out in full and closes with the named core theorem,
so an incompatible change to a bound signature stops this module from compiling.

**Three deliberately weakened checkers, each with a concrete forged
authorization.** `authorizesNoRegistryRoot` drops the profile-governed
policy-registry-root checks, `authorizesNoRelease` drops the module-release
check, and `authorizesNoGrant` keeps the subject rule but ignores the presented
grant root. For each one this module exhibits an input that the weakened checker
accepts, that the real checker rejects, and for which no `Authorized` witness
exists. The three forgeries are materially different from the honest ones: two
of them name `mallory` as the issue authority for the same asset the governed
registry assigns to `issuerSubject`, and the third self-burns under a grant
issued for the issue lane.

The stale-release forgery is the reason `Root` opacity matters. Roots here are
opaque identifiers with no claimed injectivity, so `staleRegistrySharingRoot` —
a superseded member list that declares the governed registry root — is
representable. The module-release check, not the root check, is what excludes
it in this model.

**Executable comparison output.** `challengeReportV1` is a deterministic string
built by *evaluating the definitions* — `parseCommandKind`, `lookupPolicy`,
`authorizes`, the three weakened checkers, and `authorizedSupplyEffectKind` — on
the fixed vector table below. It contains no hand-written behavioural labels.

## Bounded structural comparison only

`challengeReportV1` exists so that this model's authorization predicate can be
compared, on a fixed input table, against the current Python `_authorize` in
`src/core/managed_asset_lifecycle_module_v1.py` and the Rust `authorize` in
`zk/global_settlement_abi_v1/src/managed_asset_lifecycle.rs`. **No such
comparison is performed or claimed by this module**; it emits the string and
nothing more. Even a matching comparison would be bounded structural evidence,
not a runtime refinement proof: amounts, balances, supplies, widths, effect
rows, roots as digests, receipts, the cross-layer check ordering, and the
runtime reject-code enumeration and its precedence are all outside the model.
Nothing here asserts custody, possession, title, control, or key control over
any asset.
-/

namespace Proofs
namespace ManagedAssetPolicyAuthorityV1Challenge

open Proofs.ManagedAssetPolicyAuthorityV1

/-! ## 1. Bound signatures -/

/-- The deterministic checker decides exactly the typed witness. -/
theorem challenge_checker_decides_witness :
    ∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command),
      NoDuplicateAssets st.registry.members →
        (authorizes profile st ctx cmd = true ↔
          ∃ (kind : CommandKind) (policy : ManagedPolicy),
            Authorized profile st ctx cmd kind policy) :=
  fun profile st ctx cmd hnd => authorizes_eq_true_iff profile st ctx cmd hnd

/-- Authorization pins the active profile and the exact governed registry root. -/
theorem challenge_pins_governed_registry_root :
    ∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command)
      (kind : CommandKind) (policy : ManagedPolicy),
      Authorized profile st ctx cmd kind policy →
        profile.status = ProfileStatus.active ∧
        ctx.profileRoot = profile.profileRoot ∧
        ctx.policyRegistryRoot = profile.managedPolicyRegistryRoot ∧
        st.registry.registryRoot = profile.managedPolicyRegistryRoot :=
  fun _ _ _ _ _ _ h => authorized_pins_governed_registry_root h

/-- Authorization pins the unique registry member for the command's asset. -/
theorem challenge_pins_unique_member :
    ∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command)
      (kind : CommandKind) (policy : ManagedPolicy),
      Authorized profile st ctx cmd kind policy →
        policy ∈ st.registry.members ∧
        policy.asset = cmd.asset ∧
        (∀ q ∈ st.registry.members, q.asset = cmd.asset → q = policy) :=
  fun _ _ _ _ _ _ h => authorized_pins_unique_member h

/-- Authorization pins the module release and the exact wire command kind. -/
theorem challenge_pins_module_release_and_kind :
    ∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command)
      (kind : CommandKind) (policy : ManagedPolicy),
      Authorized profile st ctx cmd kind policy →
        ctx.moduleReleaseId = st.moduleReleaseId ∧
        cmd.commandKind = kind.code ∧
        policy.assetClass = AssetClass.registeredOrdinaryToken :=
  fun _ _ _ _ _ _ h =>
    ⟨authorized_pins_module_release h, authorized_pins_command_kind h,
      (authorized_requires_ordinary_class h).1⟩

/-- Issue authorization pins the paired issue authority: subject and grant. -/
theorem challenge_issue_pins_authority :
    ∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command)
      (policy : ManagedPolicy),
      Authorized profile st ctx cmd CommandKind.issue policy →
        policy.issueAuthority = some ⟨ctx.subject, ctx.grantRoot⟩ :=
  fun _ _ _ _ _ h => (authorized_issue_pins_authority h).1

/-- Self-burn authorization pins the account owner and the self-burn grant. -/
theorem challenge_burn_pins_owner_and_grant :
    ∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command)
      (policy : ManagedPolicy),
      Authorized profile st ctx cmd CommandKind.burn policy →
        ctx.subject = cmd.accountOwner ∧
        policy.selfBurnPolicyRoot = some ctx.grantRoot :=
  fun _ _ _ _ _ h =>
    ⟨(authorized_burn_pins_owner_and_grant h).1, (authorized_burn_pins_owner_and_grant h).2.1⟩

/-- Wrong-root rejection, on both the presented root and the carried root. -/
theorem challenge_wrong_root_rejections :
    ∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command)
      (kind : CommandKind) (policy : ManagedPolicy),
      (ctx.policyRegistryRoot ≠ profile.managedPolicyRegistryRoot →
        ¬ Authorized profile st ctx cmd kind policy) ∧
      (st.registry.registryRoot ≠ profile.managedPolicyRegistryRoot →
        ¬ Authorized profile st ctx cmd kind policy) :=
  fun _ _ _ _ _ _ =>
    ⟨fun hne => wrong_presented_registry_root_not_authorized hne,
      fun hne => wrong_registry_root_not_authorized hne⟩

/-- Wrong-release rejection. -/
theorem challenge_wrong_release_rejection :
    ∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command)
      (kind : CommandKind) (policy : ManagedPolicy),
      ctx.moduleReleaseId ≠ st.moduleReleaseId →
        ¬ Authorized profile st ctx cmd kind policy :=
  fun _ _ _ _ _ _ hne => wrong_release_not_authorized hne

/-- Issue-versus-burn confusion exclusion, at the grant root and at the wire
kind. -/
theorem challenge_kind_confusion_excluded :
    (∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmdI cmdB : Command)
      (policy : ManagedPolicy) (ia : IssueAuthority) (root : Root),
        policy.issueAuthority = some ia → policy.selfBurnPolicyRoot = some root →
          ia.policyRoot ≠ root →
            ¬ (Authorized profile st ctx cmdI CommandKind.issue policy ∧
               Authorized profile st ctx cmdB CommandKind.burn policy)) ∧
    (∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command)
      (p₁ p₂ : ManagedPolicy),
        Authorized profile st ctx cmd CommandKind.issue p₁ →
          Authorized profile st ctx cmd CommandKind.burn p₂ → False) :=
  ⟨fun _ _ _ _ _ _ _ _ hia hroot hne =>
      distinct_grant_roots_exclude_kind_confusion hia hroot hne,
    fun _ _ _ _ _ _ h₁ h₂ => authorized_kind_is_exclusive h₁ h₂⟩

/-! ## 2. Fixture tokens

Opaque identifiers. Only their equality or inequality is observed; nothing here
computes or verifies a digest. -/

def governedProfileRoot : Root := "root:profile-active"
def governedRegistryRoot : Root := "root:managed-policy-registry-7"
def forgedRegistryRoot : Root := "root:managed-policy-registry-forged"
def currentRelease : Root := "root:managed-asset-module-release-4"
def staleRelease : Root := "root:managed-asset-module-release-3"
def issuePolicyRoot : Root := "root:ordinary-issue-policy"
def ordinaryBurnPolicyRoot : Root := "root:ordinary-self-burn-policy"
def malloryPolicyRoot : Root := "root:mallory-policy"

def ordinaryToken : Asset := "ORD"
def protocolToken : Asset := "ZUSD"
def unregisteredToken : Asset := "GHOST"

def issuerSubject : Subject := "ordinary-token-issuer"
def alice : Subject := "alice"
def mallory : Subject := "mallory"

theorem fixture_roots_distinct :
    governedRegistryRoot ≠ forgedRegistryRoot ∧
    currentRelease ≠ staleRelease ∧
    issuePolicyRoot ≠ ordinaryBurnPolicyRoot ∧
    issuePolicyRoot ≠ malloryPolicyRoot ∧
    issuerSubject ≠ mallory ∧
    alice ≠ mallory := by decide

/-! ## 3. The governed state -/

/-- The registered ordinary token: a named issue authority and a self-burn root. -/
def ordinaryPolicy : ManagedPolicy where
  asset := ordinaryToken
  assetClass := AssetClass.registeredOrdinaryToken
  issueAuthority := some ⟨issuerSubject, issuePolicyRoot⟩
  selfBurnPolicyRoot := some ordinaryBurnPolicyRoot
  enabled := true

/-- A protocol-managed class. Generic authority is forbidden for it, and the
paired authority fields are absent. -/
def protocolPolicy : ManagedPolicy where
  asset := protocolToken
  assetClass := AssetClass.canonicalZusd
  issueAuthority := none
  selfBurnPolicyRoot := none
  enabled := true

def governedRegistry : ManagedPolicyRegistry where
  registryRoot := governedRegistryRoot
  members := [ordinaryPolicy, protocolPolicy]

def governedState : ModuleState where
  moduleReleaseId := currentRelease
  registry := governedRegistry

def activeProfile : ProfileSnapshot where
  profileRoot := governedProfileRoot
  managedPolicyRegistryRoot := governedRegistryRoot
  status := ProfileStatus.active

def shadowProfile : ProfileSnapshot where
  profileRoot := governedProfileRoot
  managedPolicyRegistryRoot := governedRegistryRoot
  status := ProfileStatus.shadow

theorem governedRegistry_noDuplicateAssets :
    NoDuplicateAssets governedState.registry.members := by decide

/-! ## 4. Honest commands and contexts -/

def issueCommand : Command where
  commandKind := "managed_asset_issue"
  asset := ordinaryToken
  accountOwner := alice

def burnCommand : Command where
  commandKind := "managed_asset_burn"
  asset := ordinaryToken
  accountOwner := alice

def protocolIssueCommand : Command where
  commandKind := "managed_asset_issue"
  asset := protocolToken
  accountOwner := alice

def unknownKindCommand : Command where
  commandKind := "managed_asset_mint"
  asset := ordinaryToken
  accountOwner := alice

def unregisteredAssetCommand : Command where
  commandKind := "managed_asset_issue"
  asset := unregisteredToken
  accountOwner := alice

/-- The issuer acts under the issue policy root. -/
def issueContext : Context where
  profileRoot := governedProfileRoot
  policyRegistryRoot := governedRegistryRoot
  moduleReleaseId := currentRelease
  subject := issuerSubject
  grantRoot := issuePolicyRoot

/-- The account owner acts under the self-burn policy root. -/
def burnContext : Context where
  profileRoot := governedProfileRoot
  policyRegistryRoot := governedRegistryRoot
  moduleReleaseId := currentRelease
  subject := alice
  grantRoot := ordinaryBurnPolicyRoot

theorem honest_issue_authorizes :
    authorizes activeProfile governedState issueContext issueCommand = true := by decide

theorem honest_burn_authorizes :
    authorizes activeProfile governedState burnContext burnCommand = true := by decide

/-- Non-vacuity: the honest issue really has the typed witness, at the exact
kind and the exact governed policy. -/
theorem honest_issue_witness :
    Authorized activeProfile governedState issueContext issueCommand
      CommandKind.issue ordinaryPolicy :=
  { profileActive := rfl
    profileNamed := rfl
    registryRootGoverned := rfl
    registryRootBound := rfl
    releaseMatched := rfl
    kindExact := by decide
    member := ⟨by decide, rfl, by decide⟩
    ordinaryClass := rfl
    enabled := rfl
    grantMatched := rfl }

theorem honest_burn_witness :
    Authorized activeProfile governedState burnContext burnCommand
      CommandKind.burn ordinaryPolicy :=
  { profileActive := rfl
    profileNamed := rfl
    registryRootGoverned := rfl
    registryRootBound := rfl
    releaseMatched := rfl
    kindExact := by decide
    member := ⟨by decide, rfl, by decide⟩
    ordinaryClass := rfl
    enabled := rfl
    grantMatched := ⟨rfl, rfl⟩ }

/-- Other authority rejections that are not the three omission counterexamples:
a protocol-managed class, an unknown wire kind, an unregistered asset, and a
non-active profile. -/
theorem honest_negative_vectors :
    authorizes activeProfile governedState issueContext protocolIssueCommand = false ∧
    authorizes activeProfile governedState issueContext unknownKindCommand = false ∧
    authorizes activeProfile governedState issueContext unregisteredAssetCommand = false ∧
    authorizes shadowProfile governedState issueContext issueCommand = false := by decide

/-! ## 5. Three weakened checkers

Each drops exactly one of the checks the task names, and nothing else. -/

/-- Registry-root omission: the profile-governed root binding and the carried
root binding are both dropped. -/
def contextAuthorizesNoRegistryRoot (profile : ProfileSnapshot) (st : ModuleState)
    (ctx : Context) (cmd : Command) (kind : CommandKind) (policy : ManagedPolicy) : Bool :=
  decide (profile.status = ProfileStatus.active) &&
  decide (ctx.profileRoot = profile.profileRoot) &&
  decide (ctx.moduleReleaseId = st.moduleReleaseId) &&
  decide (policy.assetClass = AssetClass.registeredOrdinaryToken) &&
  policy.enabled &&
  decide (GrantMatches ctx cmd kind policy)

def authorizesNoRegistryRoot (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context)
    (cmd : Command) : Bool :=
  match parseCommandKind cmd.commandKind with
  | none => false
  | some kind =>
    match lookupPolicy cmd.asset st.registry.members with
    | none => false
    | some policy => contextAuthorizesNoRegistryRoot profile st ctx cmd kind policy

/-- Module-release omission. -/
def contextAuthorizesNoRelease (profile : ProfileSnapshot) (st : ModuleState)
    (ctx : Context) (cmd : Command) (kind : CommandKind) (policy : ManagedPolicy) : Bool :=
  decide (profile.status = ProfileStatus.active) &&
  decide (ctx.profileRoot = profile.profileRoot) &&
  decide (ctx.policyRegistryRoot = profile.managedPolicyRegistryRoot) &&
  decide (st.registry.registryRoot = ctx.policyRegistryRoot) &&
  decide (policy.assetClass = AssetClass.registeredOrdinaryToken) &&
  policy.enabled &&
  decide (GrantMatches ctx cmd kind policy)

def authorizesNoRelease (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context)
    (cmd : Command) : Bool :=
  match parseCommandKind cmd.commandKind with
  | none => false
  | some kind =>
    match lookupPolicy cmd.asset st.registry.members with
    | none => false
    | some policy => contextAuthorizesNoRelease profile st ctx cmd kind policy

/-- The grant rule with the grant-root comparison removed. The subject rule is
kept, so this is the sharpest possible weakening: a checker that authenticates
who is acting and then ignores which grant they present. -/
def grantSubjectOnly (ctx : Context) (cmd : Command) (kind : CommandKind)
    (policy : ManagedPolicy) : Bool :=
  match kind with
  | .issue =>
      match policy.issueAuthority with
      | none => false
      | some ia => decide (ctx.subject = ia.subject)
  | .burn =>
      match policy.selfBurnPolicyRoot with
      | none => false
      | some _ => decide (ctx.subject = cmd.accountOwner)

def contextAuthorizesNoGrant (profile : ProfileSnapshot) (st : ModuleState)
    (ctx : Context) (cmd : Command) (kind : CommandKind) (policy : ManagedPolicy) : Bool :=
  decide (profile.status = ProfileStatus.active) &&
  decide (ctx.profileRoot = profile.profileRoot) &&
  decide (ctx.policyRegistryRoot = profile.managedPolicyRegistryRoot) &&
  decide (st.registry.registryRoot = ctx.policyRegistryRoot) &&
  decide (ctx.moduleReleaseId = st.moduleReleaseId) &&
  decide (policy.assetClass = AssetClass.registeredOrdinaryToken) &&
  policy.enabled &&
  grantSubjectOnly ctx cmd kind policy

def authorizesNoGrant (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context)
    (cmd : Command) : Bool :=
  match parseCommandKind cmd.commandKind with
  | none => false
  | some kind =>
    match lookupPolicy cmd.asset st.registry.members with
    | none => false
    | some policy => contextAuthorizesNoGrant profile st ctx cmd kind policy

/-- The weakened checkers agree with the real one on both honest vectors, so
they fail only in the forged direction. -/
theorem weakened_checkers_agree_on_honest_vectors :
    authorizesNoRegistryRoot activeProfile governedState issueContext issueCommand = true ∧
    authorizesNoRelease activeProfile governedState issueContext issueCommand = true ∧
    authorizesNoGrant activeProfile governedState issueContext issueCommand = true ∧
    authorizesNoRegistryRoot activeProfile governedState burnContext burnCommand = true ∧
    authorizesNoRelease activeProfile governedState burnContext burnCommand = true ∧
    authorizesNoGrant activeProfile governedState burnContext burnCommand = true := by decide

/-! ## 6. Forgery A — omitting the registry-root check

Mallory supplies a registry of her own, declaring a root the active profile does
not govern, whose sole member hands her the issue authority for the same asset
the governed registry assigns to `issuerSubject`. -/

def malloryIssuePolicy : ManagedPolicy where
  asset := ordinaryToken
  assetClass := AssetClass.registeredOrdinaryToken
  issueAuthority := some ⟨mallory, malloryPolicyRoot⟩
  selfBurnPolicyRoot := none
  enabled := true

def forgedRegistry : ManagedPolicyRegistry where
  registryRoot := forgedRegistryRoot
  members := [malloryIssuePolicy]

def forgedRegistryState : ModuleState where
  moduleReleaseId := currentRelease
  registry := forgedRegistry

def forgedRegistryContext : Context where
  profileRoot := governedProfileRoot
  policyRegistryRoot := forgedRegistryRoot
  moduleReleaseId := currentRelease
  subject := mallory
  grantRoot := malloryPolicyRoot

theorem forgedRegistry_noDuplicateAssets :
    NoDuplicateAssets forgedRegistryState.registry.members := by decide

/-- The forgery is material: the same asset resolves to a different authority. -/
theorem forgedRegistry_is_material :
    lookupPolicy ordinaryToken forgedRegistryState.registry.members = some malloryIssuePolicy ∧
    lookupPolicy ordinaryToken governedState.registry.members = some ordinaryPolicy ∧
    malloryIssuePolicy.issueAuthority = some ⟨mallory, malloryPolicyRoot⟩ ∧
    ordinaryPolicy.issueAuthority = some ⟨issuerSubject, issuePolicyRoot⟩ := by decide

theorem forgedRegistry_admitted_without_root_check :
    authorizesNoRegistryRoot activeProfile forgedRegistryState forgedRegistryContext
      issueCommand = true := by decide

theorem forgedRegistry_rejected_by_checker :
    authorizes activeProfile forgedRegistryState forgedRegistryContext issueCommand
      = false := by decide

/-- No witness exists, derived from the named pinning theorem rather than from
the checker, so the rejection does not depend on the checker's shape. -/
theorem forgedRegistry_has_no_witness :
    ¬ ∃ (kind : CommandKind) (policy : ManagedPolicy),
        Authorized activeProfile forgedRegistryState forgedRegistryContext issueCommand
          kind policy := by
  rintro ⟨kind, policy, h⟩
  exact wrong_presented_registry_root_not_authorized (by decide) h

/-- Omitting the registry-root check admits a concrete forged authorization. -/
theorem omitting_registry_root_admits_forgery :
    authorizesNoRegistryRoot activeProfile forgedRegistryState forgedRegistryContext
      issueCommand = true ∧
    authorizes activeProfile forgedRegistryState forgedRegistryContext issueCommand = false ∧
    ¬ ∃ (kind : CommandKind) (policy : ManagedPolicy),
        Authorized activeProfile forgedRegistryState forgedRegistryContext issueCommand
          kind policy :=
  ⟨forgedRegistry_admitted_without_root_check, forgedRegistry_rejected_by_checker,
    forgedRegistry_has_no_witness⟩

theorem authorizesNoRegistryRoot_is_strictly_weaker :
    ¬ (∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command),
        authorizesNoRegistryRoot profile st ctx cmd = authorizes profile st ctx cmd) := by
  intro h
  have hc := h activeProfile forgedRegistryState forgedRegistryContext issueCommand
  rw [forgedRegistry_admitted_without_root_check, forgedRegistry_rejected_by_checker] at hc
  exact absurd hc (by decide)

/-! ## 7. Forgery B — omitting the module-release check

A superseded member list that declares the governed registry root. Roots are
opaque identifiers in this model with no claimed injectivity, so nothing
prevents a stale registry from carrying the governed root; the module-release
check is what excludes it. -/

def staleRegistrySharingRoot : ManagedPolicyRegistry where
  registryRoot := governedRegistryRoot
  members := [malloryIssuePolicy]

def staleReleaseState : ModuleState where
  moduleReleaseId := staleRelease
  registry := staleRegistrySharingRoot

def staleReleaseContext : Context where
  profileRoot := governedProfileRoot
  policyRegistryRoot := governedRegistryRoot
  moduleReleaseId := currentRelease
  subject := mallory
  grantRoot := malloryPolicyRoot

theorem staleRelease_noDuplicateAssets :
    NoDuplicateAssets staleReleaseState.registry.members := by decide

/-- Every registry-root check passes on this input; only the release differs. -/
theorem staleRelease_passes_every_root_check :
    staleReleaseState.registry.registryRoot = activeProfile.managedPolicyRegistryRoot ∧
    staleReleaseContext.policyRegistryRoot = activeProfile.managedPolicyRegistryRoot ∧
    staleReleaseContext.profileRoot = activeProfile.profileRoot ∧
    staleReleaseContext.moduleReleaseId ≠ staleReleaseState.moduleReleaseId := by decide

theorem staleRelease_admitted_without_release_check :
    authorizesNoRelease activeProfile staleReleaseState staleReleaseContext issueCommand
      = true := by decide

theorem staleRelease_rejected_by_checker :
    authorizes activeProfile staleReleaseState staleReleaseContext issueCommand
      = false := by decide

theorem staleRelease_has_no_witness :
    ¬ ∃ (kind : CommandKind) (policy : ManagedPolicy),
        Authorized activeProfile staleReleaseState staleReleaseContext issueCommand
          kind policy := by
  rintro ⟨kind, policy, h⟩
  exact wrong_release_not_authorized (by decide) h

/-- Omitting the module-release check admits a concrete forged authorization. -/
theorem omitting_module_release_admits_forgery :
    authorizesNoRelease activeProfile staleReleaseState staleReleaseContext issueCommand
      = true ∧
    authorizes activeProfile staleReleaseState staleReleaseContext issueCommand = false ∧
    ¬ ∃ (kind : CommandKind) (policy : ManagedPolicy),
        Authorized activeProfile staleReleaseState staleReleaseContext issueCommand
          kind policy :=
  ⟨staleRelease_admitted_without_release_check, staleRelease_rejected_by_checker,
    staleRelease_has_no_witness⟩

theorem authorizesNoRelease_is_strictly_weaker :
    ¬ (∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command),
        authorizesNoRelease profile st ctx cmd = authorizes profile st ctx cmd) := by
  intro h
  have hc := h activeProfile staleReleaseState staleReleaseContext issueCommand
  rw [staleRelease_admitted_without_release_check, staleRelease_rejected_by_checker] at hc
  exact absurd hc (by decide)

/-! ## 8. Forgery C — omitting the grant check

The account owner self-burns while presenting the *issue* lane's policy root as
her grant. The subject rule passes, so a checker that authenticates the subject
and ignores the grant admits it. This is also the concrete issue-versus-burn
confusion the core module excludes. -/

def crossGrantBurnContext : Context where
  profileRoot := governedProfileRoot
  policyRegistryRoot := governedRegistryRoot
  moduleReleaseId := currentRelease
  subject := alice
  grantRoot := issuePolicyRoot

/-- Every check except the grant-root comparison passes on this input. -/
theorem crossGrantBurn_passes_every_other_check :
    crossGrantBurnContext.subject = burnCommand.accountOwner ∧
    crossGrantBurnContext.moduleReleaseId = governedState.moduleReleaseId ∧
    crossGrantBurnContext.policyRegistryRoot = activeProfile.managedPolicyRegistryRoot ∧
    ordinaryPolicy.selfBurnPolicyRoot = some ordinaryBurnPolicyRoot ∧
    crossGrantBurnContext.grantRoot ≠ ordinaryBurnPolicyRoot := by decide

theorem crossGrantBurn_admitted_without_grant_check :
    authorizesNoGrant activeProfile governedState crossGrantBurnContext burnCommand
      = true := by decide

theorem crossGrantBurn_rejected_by_checker :
    authorizes activeProfile governedState crossGrantBurnContext burnCommand = false := by
  decide

theorem crossGrantBurn_has_no_witness :
    ¬ ∃ (kind : CommandKind) (policy : ManagedPolicy),
        Authorized activeProfile governedState crossGrantBurnContext burnCommand
          kind policy := by
  rintro ⟨kind, policy, h⟩
  have hpolicy : ordinaryPolicy = policy := authorized_member_eq h (by decide) (by decide)
  have hkind : kind = CommandKind.burn := by
    have hb : parseCommandKind burnCommand.commandKind = some CommandKind.burn := by decide
    rw [h.kindExact] at hb
    exact Option.some.injEq _ _ ▸ hb
  subst hkind
  subst hpolicy
  exact wrong_selfBurn_grant_not_authorized (root := ordinaryBurnPolicyRoot)
    (by decide) (by decide) h

/-- Omitting the grant check admits a concrete forged authorization. -/
theorem omitting_grant_admits_forgery :
    authorizesNoGrant activeProfile governedState crossGrantBurnContext burnCommand = true ∧
    authorizes activeProfile governedState crossGrantBurnContext burnCommand = false ∧
    ¬ ∃ (kind : CommandKind) (policy : ManagedPolicy),
        Authorized activeProfile governedState crossGrantBurnContext burnCommand
          kind policy :=
  ⟨crossGrantBurn_admitted_without_grant_check, crossGrantBurn_rejected_by_checker,
    crossGrantBurn_has_no_witness⟩

theorem authorizesNoGrant_is_strictly_weaker :
    ¬ (∀ (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmd : Command),
        authorizesNoGrant profile st ctx cmd = authorizes profile st ctx cmd) := by
  intro h
  have hc := h activeProfile governedState crossGrantBurnContext burnCommand
  rw [crossGrantBurn_admitted_without_grant_check, crossGrantBurn_rejected_by_checker] at hc
  exact absurd hc (by decide)

/-! ## 9. Issue-versus-burn confusion, on the fixtures

The governed policy separates its issue and self-burn roots, so no single
context authorizes both kinds against it. -/

theorem governedPolicy_separates_grant_roots :
    ordinaryPolicy.issueAuthority = some ⟨issuerSubject, issuePolicyRoot⟩ ∧
    ordinaryPolicy.selfBurnPolicyRoot = some ordinaryBurnPolicyRoot ∧
    issuePolicyRoot ≠ ordinaryBurnPolicyRoot := by decide

theorem governedPolicy_excludes_kind_confusion
    (profile : ProfileSnapshot) (st : ModuleState) (ctx : Context) (cmdI cmdB : Command) :
    ¬ (Authorized profile st ctx cmdI CommandKind.issue ordinaryPolicy ∧
       Authorized profile st ctx cmdB CommandKind.burn ordinaryPolicy) :=
  distinct_grant_roots_exclude_kind_confusion
    (ia := ⟨issuerSubject, issuePolicyRoot⟩) (root := ordinaryBurnPolicyRoot)
    rfl rfl (by decide)

/-- The issuer's context cannot self-burn Alice's account, because the issue
rule pins the subject to the issue authority and the self-burn rule pins it to
the account owner. -/
theorem issueContext_cannot_selfBurn_alice :
    ¬ Authorized activeProfile governedState issueContext burnCommand
        CommandKind.burn ordinaryPolicy :=
  issue_context_cannot_selfBurn_foreign_account (ia := ⟨issuerSubject, issuePolicyRoot⟩)
    rfl honest_issue_witness (by decide)

/-! ## 10. Derived report

Every field below is computed from the definitions above. -/

def boolField (b : Bool) : String :=
  if b then "true" else "false"

structure Vector where
  name : String
  profile : ProfileSnapshot
  state : ModuleState
  ctx : Context
  cmd : Command

def vectors : List Vector :=
  [ ⟨"honest_issue", activeProfile, governedState, issueContext, issueCommand⟩,
    ⟨"honest_burn", activeProfile, governedState, burnContext, burnCommand⟩,
    ⟨"protocol_class", activeProfile, governedState, issueContext, protocolIssueCommand⟩,
    ⟨"unknown_kind", activeProfile, governedState, issueContext, unknownKindCommand⟩,
    ⟨"unregistered_asset", activeProfile, governedState, issueContext,
      unregisteredAssetCommand⟩,
    ⟨"profile_not_active", shadowProfile, governedState, issueContext, issueCommand⟩,
    ⟨"forged_registry_root", activeProfile, forgedRegistryState, forgedRegistryContext,
      issueCommand⟩,
    ⟨"stale_module_release", activeProfile, staleReleaseState, staleReleaseContext,
      issueCommand⟩,
    ⟨"cross_grant_self_burn", activeProfile, governedState, crossGrantBurnContext,
      burnCommand⟩ ]

def vectorVerdicts (v : Vector) : List Bool :=
  [ authorizes v.profile v.state v.ctx v.cmd,
    authorizesNoRegistryRoot v.profile v.state v.ctx v.cmd,
    authorizesNoRelease v.profile v.state v.ctx v.cmd,
    authorizesNoGrant v.profile v.state v.ctx v.cmd ]

def vectorRow (v : Vector) : String :=
  String.intercalate "," (["VECTOR", v.name] ++ (vectorVerdicts v).map boolField)

def kindRow (k : CommandKind) : String :=
  String.intercalate "," ["KIND", k.code, (authorizedSupplyEffectKind k).code]

def classRow (c : AssetClass) : String :=
  String.intercalate "," ["CLASS", c.code]

def statusRow (s : ProfileStatus) : String :=
  String.intercalate "," ["STATUS", s.code]

def parseRow (s : String) : String :=
  String.intercalate ","
    ["PARSE", s,
      match parseCommandKind s with
      | none => "NONE"
      | some k => k.code]

def parseProbes : List String :=
  [ "managed_asset_issue", "managed_asset_burn", "managed_asset_mint",
    "MANAGED_ASSET_ISSUE", "" ]

def lookupRow (a : Asset) : String :=
  String.intercalate ","
    ["LOOKUP", a,
      match lookupPolicy a governedState.registry.members with
      | none => "NONE"
      | some p => p.assetClass.code]

def lookupProbes : List Asset := [ordinaryToken, protocolToken, unregisteredToken]

/-- The full deterministic comparison report. -/
def challengeReportV1 : String :=
  String.intercalate "\n"
    (allCommandKinds.map kindRow ++
      allAssetClasses.map classRow ++
      allProfileStatuses.map statusRow ++
      parseProbes.map parseRow ++
      lookupProbes.map lookupRow ++
      vectors.map vectorRow)

/-! ## 11. Report-level sanity facts

These pin the interesting rows, so a silent change to the report shape fails
here rather than only in the source comparison. -/

/-- The verdict matrix, evaluated. Column order is
`authorizes, noRegistryRoot, noRelease, noGrant`. Every `true` in a weakened
column whose `authorizes` column is `false` is an admitted forgery. -/
theorem vectorVerdicts_eq :
    vectors.map vectorVerdicts =
      [ [true, true, true, true],
        [true, true, true, true],
        [false, false, false, false],
        [false, false, false, false],
        [false, false, false, false],
        [false, false, false, false],
        [false, true, false, false],
        [false, false, true, false],
        [false, false, false, true] ] := by decide

/-- Each weakened checker admits exactly its own forgery among the vectors, and
the real checker admits none of the three. -/
theorem each_omission_admits_exactly_its_own_forgery :
    authorizes activeProfile forgedRegistryState forgedRegistryContext issueCommand = false ∧
    authorizes activeProfile staleReleaseState staleReleaseContext issueCommand = false ∧
    authorizes activeProfile governedState crossGrantBurnContext burnCommand = false ∧
    authorizesNoRegistryRoot activeProfile forgedRegistryState forgedRegistryContext
      issueCommand = true ∧
    authorizesNoRelease activeProfile staleReleaseState staleReleaseContext issueCommand
      = true ∧
    authorizesNoGrant activeProfile governedState crossGrantBurnContext burnCommand
      = true ∧
    authorizesNoRelease activeProfile forgedRegistryState forgedRegistryContext issueCommand
      = false ∧
    authorizesNoGrant activeProfile forgedRegistryState forgedRegistryContext issueCommand
      = false ∧
    authorizesNoRegistryRoot activeProfile staleReleaseState staleReleaseContext issueCommand
      = false ∧
    authorizesNoGrant activeProfile staleReleaseState staleReleaseContext issueCommand
      = false ∧
    authorizesNoRegistryRoot activeProfile governedState crossGrantBurnContext burnCommand
      = false ∧
    authorizesNoRelease activeProfile governedState crossGrantBurnContext burnCommand
      = false := by decide

theorem parseProbes_labels :
    parseProbes.map (fun s =>
        match parseCommandKind s with
        | none => "NONE"
        | some k => k.code) =
      ["managed_asset_issue", "managed_asset_burn", "NONE", "NONE", "NONE"] := by decide

theorem lookupProbes_labels :
    lookupProbes.map (fun a =>
        match lookupPolicy a governedState.registry.members with
        | none => "NONE"
        | some p => p.assetClass.code) =
      ["registered_ordinary_token", "canonical_zusd", "NONE"] := by decide

end ManagedAssetPolicyAuthorityV1Challenge
end Proofs
