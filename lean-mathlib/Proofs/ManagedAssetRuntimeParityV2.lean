import Proofs.ManagedAssetLifecycleRefinementV2

/-!
# Managed-asset lifecycle V2 — executable runtime-parity harness

`Proofs.ManagedAssetLifecycleRefinementV2` states and proves properties of a
bounded model of `transition_managed_asset_lifecycle_v2`. This module evaluates
that model for comparison with the Python leaf on a finite corpus, using the
report shape already used by
`Proofs.AssetTransferRefinementV1Challenge` for the V1 transfer lane.

It does four jobs.

**Bound signatures.**  Each `parity_*` theorem restates an imported result with
its type written out in full and closes with the named core theorem, so an
incompatible change to one of those statements stops this module compiling.

**A fixed vector table.**  `vectors` is a finite table of concrete scenarios.
It covers issue, managed burn, and policy-bound authority; owner-role aliases
(issue to the authority subject, burn by the account owner, burn by a
non-owner); every reject code the bounded model can emit given the modeled
state invariant; the `i128` effect-delta edges and the `u128` supply edge; and
accepted transitions whose account row is created, grown, shrunk, and removed.

**A derived report.**  `runtimeParityReportV2` is a deterministic string built
by *evaluating* `transition`, `rejectCode`, `acceptedState`, and
`lifecyclePayload` on that table, plus a stateful history that interleaves
accepted and rejected steps and replays one occurrence.  It carries no
hand-written behavioural label, so it cannot agree with Python by accident of a
literal that drifted from the model.  The report also emits, per vector, the
scenario literals and the *relations between opaque root tokens* (does the
occurrence pre-state root equal the context root, does the command
authorization root equal the policy's expected root, ...).  Those rows let the
consuming test check that the Python twin of each vector encodes the same
situation, without needing any root value to be shared between the two
languages.

**Three fixed semantic mutants.**  `mutantRejectCodeM1` reverses the source's
supply-before-balance order on the issue arm; `mutantRejectCodeM2` authorizes
burns against the policy issue subject instead of the command account owner;
`mutantPayloadM3` reports an unchanged post supply in the conservation row.
For each, one theorem shows it *differs* from the real model on a named vector
and one shows it *agrees* everywhere else in the table, so each mutation is
live and surgical rather than wild.  The consuming test then shows the Python
runtime agrees with the real model and disagrees with each mutant.

## Scope

Root values, occurrence ids, and command-body digests are opaque equality
tokens here, exactly as in the imported model.  The report therefore transfers
lane-write *arity and orientation*, not root values: no hash, digest, or codec
equivalence is claimed.  The modeled state carries one registered asset, one
supply value, a balance function, and a projected account-row total; multi-asset
states, canonical row encoding, resource ceilings, the writer epoch, the module
journal, receipts, registry and release/profile authentication, coordinator
mounting, settlement, publication, migration, and production authority are all
outside it.  Evaluating this table beside the Python leaf is a bounded
differential over a finite enumerated corpus.  It is not a refinement proof of
the Python source, and it does not upgrade any production claim.
-/

namespace Proofs
namespace ManagedAssetRuntimeParityV2

open Proofs.ManagedAssetLifecycleRefinementV2

abbrev Principal := AssetTransferRefinementV2.Principal
abbrev Root := AssetTransferRefinementV2.Root
abbrev Occurrence := AssetTransferRefinementV2.Occurrence

/-! ## 1. Bound signatures

Each statement is written out in full and closed by the imported theorem. -/

/-- Acceptance holds exactly when no code is produced. -/
theorem parity_accepted_iff_no_reject :
    ∀ (roots : RootModel) (ctx : Context) (pre : LifecycleState) (command : Command),
      (transition roots ctx pre command).verdict = .accepted ↔
        rejectCode ctx pre command = none :=
  accepted_iff_no_reject

/-- Every input is decided as the literal rejection or the literal acceptance. -/
theorem parity_totality :
    ∀ (roots : RootModel) (ctx : Context) (pre : LifecycleState) (command : Command),
      (∃ code, rejectCode ctx pre command = some code ∧
        transition roots ctx pre command = reject code pre) ∨
      (rejectCode ctx pre command = none ∧
        transition roots ctx pre command =
          ⟨.accepted, acceptedState pre command, acceptedEffects roots ctx pre command⟩) :=
  transition_total

/-- A rejected step leaves the state alone. -/
theorem parity_rejected_post_eq_pre :
    ∀ {roots : RootModel} {ctx : Context} {pre : LifecycleState} {command : Command}
      {code : RejectCode},
      (transition roots ctx pre command).verdict = .rejected code →
        (transition roots ctx pre command).post = pre :=
  rejected_post_eq_pre

/-- A rejected step carries no effects. -/
theorem parity_rejected_effects_empty :
    ∀ {roots : RootModel} {ctx : Context} {pre : LifecycleState} {command : Command}
      {code : RejectCode},
      (transition roots ctx pre command).verdict = .rejected code →
        (transition roots ctx pre command).effects =
          AssetTransferRefinementV2.EffectEnvelope.empty :=
  rejected_effects_empty

/-- Accepted supply and projected account total both move by the signed amount,
and the conservation row records the same movement. -/
theorem parity_accepted_conservation :
    ∀ {roots : RootModel} {ctx : Context} {pre : LifecycleState} {command : Command},
      (transition roots ctx pre command).verdict = .accepted →
        (transition roots ctx pre command).post.accountTotalAtoms =
            pre.accountTotalAtoms + signedAmount command ∧
        (transition roots ctx pre command).post.supplyAtoms =
            pre.supplyAtoms + signedAmount command ∧
        (transition roots ctx pre command).effects.payload.map
          (fun payload => payload.conservation) =
          some ⟨pre.accountTotalAtoms, pre.accountTotalAtoms + signedAmount command,
            pre.supplyAtoms, pre.supplyAtoms + signedAmount command,
            (if isIssue command then command.amountAtoms else 0),
            (if isIssue command then 0 else command.amountAtoms)⟩ :=
  accepted_conservation_equations

/-- Acceptance consumes exactly the context occurrence. -/
theorem parity_accepted_consumes_exact_occurrence :
    ∀ {roots : RootModel} {ctx : Context} {pre : LifecycleState} {command : Command},
      (transition roots ctx pre command).verdict = .accepted →
        ∃ occurrence, ctx.occurrence = some occurrence ∧
          (transition roots ctx pre command).effects.occurrenceConsumptions =
            [occurrence.occurrenceId] :=
  accepted_consumes_exact_occurrence

/-- A burn is authorized against the account owner and the policy burn root. -/
theorem parity_accepted_burn_authority :
    ∀ {roots : RootModel} {ctx : Context} {pre : LifecycleState} {command : Command},
      isBurn command → (transition roots ctx pre command).verdict = .accepted →
        ∃ occurrence authorizationRoot,
          ctx.occurrence = some occurrence ∧
          pre.policy.burnAuthorizationRoot = some authorizationRoot ∧
          occurrence.subjectId = command.accountOwner ∧
          occurrence.grantRoot = authorizationRoot ∧
          command.authorizationRoot = some authorizationRoot :=
  fun hburn h => accepted_burn_authority_exact hburn h

/-! ## 2. Scenario constructors -/

def theAsset : AssetTransferRefinementV2.Asset := "ORD"
def otherAsset : AssetTransferRefinementV2.Asset := "EUR"
def protocolAsset : AssetTransferRefinementV2.Asset := "ZDEX"
def releaseId : Root := "release-v2"
def otherReleaseId : Root := "release-v3"
def globalPre : Root := "global-pre"
def otherGlobalPre : Root := "global-pre-other"
def originRoot : Root := "origin-ord"
def otherOriginRoot : Root := "origin-eur"
def protocolOriginRoot : Root := "origin-zdex"
def issueGrant : Root := "issue-grant"
def burnGrant : Root := "burn-grant"
def foreignGrant : Root := "foreign-grant"
def issuer : Principal := "issuer"
def alice : Principal := "alice"
def bob : Principal := "bob"
def mallory : Principal := "mallory"

/-- The principals whose balances the report enumerates. -/
def reportedPrincipals : List Principal := [alice, bob, issuer, mallory]

def u128Max : Int := AssetTransferRefinementV2.u128Max
def i128Max : Int := AssetTransferRefinementV2.i128Max
def i128Min : Int := AssetTransferRefinementV2.i128Min

def basePolicy : Policy :=
  { asset := theAsset
    assetClass := .registeredOrdinaryToken
    assetOriginRoot := some originRoot
    atomDecimals := 8
    issueAuthority := some ⟨issuer, issueGrant⟩
    burnAuthorizationRoot := some burnGrant
    enabled := true }

def totalOf : List (Principal × Int) → Int
  | [] => 0
  | (_, amount) :: rest => amount + totalOf rest

/-- A state with `policy`, the listed account rows, and `supply`.  The projected
account total is the sum of the listed rows, matching the Python row sum. -/
def stateOf (policy : Policy) (rows : List (Principal × Int)) (supply : Int) : LifecycleState :=
  { moduleReleaseId := releaseId
    policy := policy
    balance := ledger rows
    supplyAtoms := supply
    accountTotalAtoms := totalOf rows }

/-- The command-body digest is a function of the command body, as in Python. -/
def bodyDigest (kind : AssetTransferRefinementV2.CommandKind)
    (asset : AssetTransferRefinementV2.Asset) (owner : Principal) (amount : Int)
    (authorizationRoot : Option Root) : Root :=
  "body:" ++ kind ++ ":" ++ asset ++ ":" ++ owner ++ ":" ++ toString amount ++ ":" ++
    (match authorizationRoot with | none => "-" | some root => root)

def commandOf (kind : AssetTransferRefinementV2.CommandKind)
    (asset : AssetTransferRefinementV2.Asset) (assetClass : AssetClass)
    (originRoot : Option Root) (authorizationRoot : Option Root)
    (owner : Principal) (amount : Int) : Command :=
  { commandKind := kind
    commandBodyHash := bodyDigest kind asset owner amount authorizationRoot
    asset := asset
    assetClass := assetClass
    assetOriginRoot := originRoot
    atomDecimals := 8
    authorizationRoot := authorizationRoot
    accountOwner := owner
    amountAtoms := amount }

def issueOf (owner : Principal) (amount : Int) : Command :=
  commandOf issueCommandKind theAsset .registeredOrdinaryToken (some originRoot)
    (some issueGrant) owner amount

def burnOf (owner : Principal) (amount : Int) : Command :=
  commandOf burnCommandKind theAsset .registeredOrdinaryToken (some originRoot)
    (some burnGrant) owner amount

def occurrenceOf (command : Command) (subject : Principal) (grant : Root)
    (occurrenceId : Root) : Occurrence :=
  { preStateRoot := globalPre
    consumedObjectIds := []
    commandKind := command.commandKind
    commandBodyHash := command.commandBodyHash
    subjectId := subject
    grantRoot := grant
    occurrenceId := occurrenceId }

def contextOf (occurrence : Occurrence) : Context :=
  { moduleReleaseId := releaseId
    globalPreStateRoot := globalPre
    occurrence := some occurrence }

/-- The context that authorizes `command`: an issue is presented by the policy
subject with the issue grant, a burn by the account owner with the burn grant. -/
def authorizedContextOf (command : Command) (occurrenceId : Root) : Context :=
  if isIssue command then
    contextOf (occurrenceOf command issuer issueGrant occurrenceId)
  else
    contextOf (occurrenceOf command command.accountOwner burnGrant occurrenceId)

structure Scenario where
  name : String
  ctx : Context
  pre : LifecycleState
  cmd : Command

/-- Roots are opaque tokens.  This model distinguishes states by their two
projected totals, which is enough to expose a lane write that points the wrong
way; it claims nothing about the Python digest. -/
def parityRoots : RootModel :=
  ⟨fun state => "root:" ++ toString state.accountTotalAtoms ++ "/" ++ toString state.supplyAtoms⟩

def Scenario.run (scenario : Scenario) : TransitionResult :=
  transition parityRoots scenario.ctx scenario.pre scenario.cmd

/-! ## 3. The vector table -/

def scenarioOf (name : String) (pre : LifecycleState) (cmd : Command) : Scenario :=
  ⟨name, authorizedContextOf cmd ("occ:" ++ name), pre, cmd⟩

def fundedState : LifecycleState := stateOf basePolicy [(alice, 10)] 10
def emptyState : LifecycleState := stateOf basePolicy [] 0

def vectors : List Scenario :=
  [ -- accepted: issue, burn, row creation, row removal, owner-role aliases
    scenarioOf "issue_to_existing_holder" fundedState (issueOf alice 7),
    scenarioOf "issue_creates_new_row" fundedState (issueOf bob 5),
    scenarioOf "issue_one_atom" emptyState (issueOf alice 1),
    scenarioOf "issue_to_authority_subject_alias" fundedState (issueOf issuer 3),
    scenarioOf "burn_by_account_owner" fundedState (burnOf alice 4),
    scenarioOf "burn_removes_row_at_exact_balance" fundedState (burnOf alice 10),
    scenarioOf "burn_by_owner_who_is_also_issuer_alias"
      (stateOf basePolicy [(issuer, 9)] 9) (burnOf issuer 9),
    -- accepted: width edges
    scenarioOf "issue_at_i128_max_delta" emptyState (issueOf alice i128Max),
    scenarioOf "burn_at_negated_i128_min_delta"
      (stateOf basePolicy [(alice, 170141183460469231731687303715884105728)]
        170141183460469231731687303715884105728)
      (burnOf alice 170141183460469231731687303715884105728),
    scenarioOf "issue_to_exact_u128_supply_ceiling"
      (stateOf basePolicy [(alice, 340282366920938463463374607431768211454)]
        340282366920938463463374607431768211454)
      (issueOf alice 1),
    -- rejected: occurrence binding and release
    ⟨"missing_occurrence",
      { moduleReleaseId := releaseId, globalPreStateRoot := globalPre, occurrence := none },
      fundedState, issueOf alice 7⟩,
    ⟨"occurrence_pre_state_root_mismatch",
      { moduleReleaseId := releaseId
        globalPreStateRoot := otherGlobalPre
        occurrence := some (occurrenceOf (issueOf alice 7) issuer issueGrant "occ:pre-root") },
      fundedState, issueOf alice 7⟩,
    ⟨"occurrence_consumes_object_ids",
      contextOf
        { occurrenceOf (issueOf alice 7) issuer issueGrant "occ:consumed" with
          consumedObjectIds := ["object-1"] },
      fundedState, issueOf alice 7⟩,
    ⟨"release_mismatch",
      { moduleReleaseId := otherReleaseId
        globalPreStateRoot := globalPre
        occurrence := some (occurrenceOf (issueOf alice 7) issuer issueGrant "occ:release") },
      fundedState, issueOf alice 7⟩,
    -- rejected: command identity
    ⟨"unknown_command_kind",
      contextOf (occurrenceOf
        (commandOf "managed_asset_freeze" theAsset .registeredOrdinaryToken (some originRoot)
          (some issueGrant) alice 7) issuer issueGrant "occ:unknown-kind"),
      fundedState,
      commandOf "managed_asset_freeze" theAsset .registeredOrdinaryToken (some originRoot)
        (some issueGrant) alice 7⟩,
    ⟨"occurrence_kind_mismatch",
      contextOf
        { occurrenceOf (issueOf alice 7) issuer issueGrant "occ:kind-swap" with
          commandKind := burnCommandKind },
      fundedState, issueOf alice 7⟩,
    ⟨"occurrence_body_mismatch",
      contextOf (occurrenceOf (issueOf alice 8) issuer issueGrant "occ:body-swap"),
      fundedState, issueOf alice 7⟩,
    -- rejected: asset admission
    scenarioOf "unknown_asset" fundedState
      (commandOf issueCommandKind otherAsset .registeredOrdinaryToken (some otherOriginRoot)
        (some issueGrant) alice 7),
    scenarioOf "disabled_asset" (stateOf { basePolicy with enabled := false } [(alice, 10)] 10)
      (issueOf alice 7),
    scenarioOf "asset_class_mismatch" fundedState
      (commandOf issueCommandKind theAsset .lpShare (some originRoot) (some issueGrant) alice 7),
    scenarioOf "unregistered_asset"
      (stateOf { basePolicy with assetOriginRoot := none } [(alice, 10)] 10)
      (commandOf issueCommandKind theAsset .registeredOrdinaryToken none (some issueGrant)
        alice 7),
    scenarioOf "asset_origin_mismatch" fundedState
      (commandOf issueCommandKind theAsset .registeredOrdinaryToken (some otherOriginRoot)
        (some issueGrant) alice 7),
    scenarioOf "generic_authority_forbidden_for_protocol_asset"
      (stateOf
        { asset := protocolAsset
          assetClass := .zdexProtocolToken
          assetOriginRoot := some protocolOriginRoot
          atomDecimals := 8
          issueAuthority := none
          burnAuthorizationRoot := none
          enabled := true } [] 0)
      (commandOf issueCommandKind protocolAsset .zdexProtocolToken (some protocolOriginRoot)
        none alice 7),
    -- rejected: policy-bound authority
    scenarioOf "issue_disabled"
      (stateOf { basePolicy with issueAuthority := none } [(alice, 10)] 10) (issueOf alice 7),
    scenarioOf "burn_disabled"
      (stateOf { basePolicy with burnAuthorizationRoot := none } [(alice, 10)] 10)
      (commandOf burnCommandKind theAsset .registeredOrdinaryToken (some originRoot) none
        alice 4),
    ⟨"issue_by_unauthorized_subject",
      contextOf (occurrenceOf (issueOf alice 7) mallory issueGrant "occ:bad-issuer"),
      fundedState, issueOf alice 7⟩,
    ⟨"burn_presented_by_non_owner",
      contextOf (occurrenceOf (burnOf alice 4) mallory burnGrant "occ:bad-burner"),
      fundedState, burnOf alice 4⟩,
    ⟨"burn_presented_by_policy_issuer_not_owner",
      contextOf (occurrenceOf (burnOf alice 4) issuer burnGrant "occ:issuer-burns"),
      fundedState, burnOf alice 4⟩,
    ⟨"occurrence_grant_root_mismatch",
      contextOf (occurrenceOf (issueOf alice 7) issuer foreignGrant "occ:bad-grant"),
      fundedState, issueOf alice 7⟩,
    scenarioOf "command_authorization_root_mismatch" fundedState
      (commandOf issueCommandKind theAsset .registeredOrdinaryToken (some originRoot)
        (some foreignGrant) alice 7),
    -- rejected: amount and width
    scenarioOf "zero_amount" fundedState (issueOf alice 0),
    scenarioOf "issue_delta_overflow_at_i128_max_neighbor" emptyState
      (issueOf alice 170141183460469231731687303715884105728),
    scenarioOf "burn_delta_overflow_at_i128_min_neighbor"
      (stateOf basePolicy [(alice, 340282366920938463463374607431768211455)]
        340282366920938463463374607431768211455)
      (burnOf alice 170141183460469231731687303715884105729),
    -- rejected: post-stage supply and balance
    scenarioOf "issue_supply_overflow_only"
      (stateOf basePolicy [(bob, 340282366920938463463374607431768211455)]
        340282366920938463463374607431768211455)
      (issueOf alice 1),
    scenarioOf "issue_supply_and_balance_would_both_overflow"
      (stateOf basePolicy [(alice, 340282366920938463463374607431768211455)]
        340282366920938463463374607431768211455)
      (issueOf alice 1),
    scenarioOf "burn_exceeds_supply" (stateOf basePolicy [(alice, 3)] 3) (burnOf alice 4),
    scenarioOf "burn_exceeds_owner_balance_with_supply_available"
      (stateOf basePolicy [(alice, 1), (bob, 8)] 10) (burnOf alice 2) ]

/-! ## 4. Fixed semantic mutants

Each mutant changes one clause of the model.  `..._is_live` shows the change is
observable on a named vector; `..._is_surgical` shows it changes nothing else in
the table.  Together they make the mutant a near miss rather than a wild
function, so a corpus that kills it has really discriminated the clause. -/

def guardHolds (ctx : Context) (pre : LifecycleState) (command : Command)
    (code : RejectCode) : Bool :=
  decide (guardPasses ctx pre command code)

def firstFailingBool (g : RejectCode → Bool) : List RejectCode → Option RejectCode
  | [] => none
  | code :: rest => if g code then firstFailingBool g rest else some code

/-- The Boolean scan the mutants reuse is the model's own scan. -/
theorem firstFailingBool_eq_firstFailing (ctx : Context) (pre : LifecycleState)
    (command : Command) :
    ∀ codes : List RejectCode,
      firstFailingBool (guardHolds ctx pre command) codes =
        firstFailing (guardPasses ctx pre command) codes
  | [] => rfl
  | code :: rest => by
      by_cases h : guardPasses ctx pre command code
      · simp [firstFailingBool, firstFailing, guardHolds, h,
          firstFailingBool_eq_firstFailing ctx pre command rest]
      · simp [firstFailingBool, firstFailing, guardHolds, h]

/-- M1: the issue arm reports the balance ceiling before the supply ceiling.
The source computes the supply table first, so this reverses it. -/
def mutantPostStageM1 (pre : LifecycleState) (command : Command) : Option RejectCode :=
  if isIssue command then
    if pre.balance command.accountOwner > u128Max - command.amountAtoms then
      some .balanceOverflow
    else if pre.supplyAtoms > u128Max - command.amountAtoms then some .supplyOverflow
    else none
  else postStageRejectCode pre command

def mutantRejectCodeM1 (ctx : Context) (pre : LifecycleState) (command : Command) :
    Option RejectCode :=
  match firstFailingBool (guardHolds ctx pre command) authorizationRejectCodes with
  | some code => some code
  | none => mutantPostStageM1 pre command

/-- M2: a burn is authorized against the policy issue subject instead of the
command account owner. -/
def mutantGuardHoldsM2 (ctx : Context) (pre : LifecycleState) (command : Command) :
    RejectCode → Bool
  | .unauthorizedSubject =>
      decide (occurrencePasses ctx fun occurrence =>
        pre.policy.issueAuthority.map IssueAuthority.subject = some occurrence.subjectId)
  | code => guardHolds ctx pre command code

def mutantRejectCodeM2 (ctx : Context) (pre : LifecycleState) (command : Command) :
    Option RejectCode :=
  match firstFailingBool (mutantGuardHoldsM2 ctx pre command) authorizationRejectCodes with
  | some code => some code
  | none => postStageRejectCode pre command

/-- M3: the conservation row reports the pre-transition supply as the post
supply, so an accepted issue or burn looks supply-neutral. -/
def mutantPayloadM3 (pre : LifecycleState) (command : Command) : LifecyclePayload :=
  let honest := lifecyclePayload pre command
  { honest with
    conservation := { honest.conservation with supplyPostAtoms := pre.supplyAtoms } }

def realCode (scenario : Scenario) : Option RejectCode :=
  rejectCode scenario.ctx scenario.pre scenario.cmd

def mutantCodeM1 (scenario : Scenario) : Option RejectCode :=
  mutantRejectCodeM1 scenario.ctx scenario.pre scenario.cmd

def mutantCodeM2 (scenario : Scenario) : Option RejectCode :=
  mutantRejectCodeM2 scenario.ctx scenario.pre scenario.cmd

def m1KillVector : String := "issue_supply_and_balance_would_both_overflow"
def m2KillVector : String := "burn_by_account_owner"
def m3KillVector : String := "issue_to_existing_holder"

def namedVector (name : String) : List Scenario :=
  vectors.filter fun scenario => scenario.name == name

theorem m1_kill_vector_exists : (namedVector m1KillVector).length = 1 := by decide
theorem m2_kill_vector_exists : (namedVector m2KillVector).length = 1 := by decide
theorem m3_kill_vector_exists : (namedVector m3KillVector).length = 1 := by decide

theorem mutant_M1_is_live :
    ∀ scenario ∈ namedVector m1KillVector,
      realCode scenario = some .supplyOverflow ∧
      mutantCodeM1 scenario = some .balanceOverflow := by decide

/-- The vectors on which M1 is observable, named exactly. -/
def m1DivergentVectors : List String := [m1KillVector]

theorem mutant_M1_divergence_is_exactly_that_list :
    ∀ scenario ∈ vectors,
      (mutantCodeM1 scenario ≠ realCode scenario ↔
        m1DivergentVectors.contains scenario.name = true) := by decide

theorem mutant_M2_is_live :
    ∀ scenario ∈ namedVector m2KillVector,
      realCode scenario = none ∧
      mutantCodeM2 scenario = some .unauthorizedSubject := by decide

/-- The vectors on which M2 is observable, named exactly.  Every one is a burn
whose presenter is not the policy issue subject; the burn presented by an owner
who *is* the issue subject is absent, which is what makes the mutation a near
miss rather than a wild function. -/
def m2DivergentVectors : List String :=
  [ "burn_by_account_owner",
    "burn_removes_row_at_exact_balance",
    "burn_at_negated_i128_min_delta",
    "burn_presented_by_policy_issuer_not_owner",
    "burn_delta_overflow_at_i128_min_neighbor",
    "burn_exceeds_supply",
    "burn_exceeds_owner_balance_with_supply_available" ]

theorem mutant_M2_divergence_is_exactly_that_list :
    ∀ scenario ∈ vectors,
      (mutantCodeM2 scenario ≠ realCode scenario ↔
        m2DivergentVectors.contains scenario.name = true) := by decide

theorem mutant_M2_leaves_the_issuer_owned_burn_alias_alone :
    ∀ scenario ∈ namedVector "burn_by_owner_who_is_also_issuer_alias",
      mutantCodeM2 scenario = realCode scenario ∧ realCode scenario = none := by decide

theorem mutant_M3_is_live :
    ∀ scenario ∈ namedVector m3KillVector,
      (mutantPayloadM3 scenario.pre scenario.cmd).conservation.supplyPostAtoms ≠
        (lifecyclePayload scenario.pre scenario.cmd).conservation.supplyPostAtoms := by decide

theorem mutant_M3_touches_only_the_supply_post_field :
    ∀ scenario ∈ vectors,
      (mutantPayloadM3 scenario.pre scenario.cmd).accountOwner =
        (lifecyclePayload scenario.pre scenario.cmd).accountOwner ∧
      (mutantPayloadM3 scenario.pre scenario.cmd).accountDeltaAtoms =
        (lifecyclePayload scenario.pre scenario.cmd).accountDeltaAtoms ∧
      (mutantPayloadM3 scenario.pre scenario.cmd).supplyDeltaAtoms =
        (lifecyclePayload scenario.pre scenario.cmd).supplyDeltaAtoms ∧
      (mutantPayloadM3 scenario.pre scenario.cmd).conservation.supplyPreAtoms =
        (lifecyclePayload scenario.pre scenario.cmd).conservation.supplyPreAtoms := by decide

/-! ## 5. Table health

These are checked, not asserted in prose: names are unique, the table really
does produce the codes the consuming test enumerates, and the two codes the
modeled state invariant excludes are absent. -/

def vectorNames : List String := vectors.map Scenario.name

def hasDuplicateName : List String → Bool
  | [] => false
  | name :: rest => rest.contains name || hasDuplicateName rest

theorem vector_names_are_unique : hasDuplicateName vectorNames = false := by decide

def producedCodes : List RejectCode :=
  vectors.filterMap realCode

/-- Every reject code appears in the table except the two the modeled state
invariant makes unreachable: `assetDecimalsMismatch` (both decimal fields are
pinned to 8) and `balanceOverflow` (the account total is covered by the supply,
so the supply ceiling is reached first). -/
theorem table_produces_every_code_except_the_two_unreachable_ones
    (code : RejectCode) (hdecimals : code ≠ .assetDecimalsMismatch)
    (hbalance : code ≠ .balanceOverflow) :
    producedCodes.contains code = true := by
  cases code <;> first
    | exact absurd rfl hdecimals
    | exact absurd rfl hbalance
    | decide

theorem unreachable_codes_are_absent_from_the_table :
    producedCodes.contains .assetDecimalsMismatch = false ∧
    producedCodes.contains .balanceOverflow = false := by decide

theorem table_contains_accepted_vectors :
    (vectors.filter fun scenario => (realCode scenario).isNone).length = 10 := by decide

/-! ## 6. Stateful history

The history threads one state through accepted and rejected steps and replays a
consumed occurrence.  The leaf models no replay guard, so the replayed step is
expected to be accepted again; the report makes that visible instead of leaving
it implicit. -/

structure Step where
  label : String
  ctx : Context
  cmd : Command

def stepOf (label : String) (cmd : Command) (occurrenceId : Root) : Step :=
  ⟨label, authorizedContextOf cmd occurrenceId, cmd⟩

def historyStart : LifecycleState := emptyState

def historySteps : List Step :=
  [ stepOf "h1_issue_alice" (issueOf alice 20) "occ:h1",
    stepOf "h2_issue_alice_replayed_occurrence" (issueOf alice 20) "occ:h1",
    ⟨"h3_issue_rejected_unauthorized",
      contextOf (occurrenceOf (issueOf bob 5) mallory issueGrant "occ:h3"), issueOf bob 5⟩,
    stepOf "h4_issue_bob" (issueOf bob 5) "occ:h4",
    ⟨"h5_burn_rejected_wrong_presenter",
      contextOf (occurrenceOf (burnOf bob 5) alice burnGrant "occ:h5"), burnOf bob 5⟩,
    stepOf "h6_burn_bob_all" (burnOf bob 5) "occ:h6",
    stepOf "h7_burn_bob_rejected_empty_row" (burnOf bob 1) "occ:h7",
    stepOf "h8_burn_alice_partial" (burnOf alice 15) "occ:h8" ]

/-! ## 7. Derived report

Every field below is computed from the definitions above. -/

def flag (p : Prop) [Decidable p] : String := toString (decide p)

def verdictLabel : Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected code => code.code

def optionLabel : Option RejectCode → String
  | none => "ACCEPTED"
  | some code => code.code

def supplyKindLabel : SupplyEffectKind → String
  | .issue => "ISSUE"
  | .burn => "BURN"

def balanceFields (state : LifecycleState) : List String :=
  reportedPrincipals.map fun principal => toString (state.balance principal)

def codeRow (code : RejectCode) : String :=
  String.intercalate "," ["CODE", toString code.rank, code.code]

def widthRow : String :=
  String.intercalate ","
    ["WIDTH", toString u128Max, toString i128Min, toString i128Max]

def principalRow : String :=
  String.intercalate "," ("PRINCIPALS" :: reportedPrincipals)

/-- Scenario literals.  The consuming test builds its Python twin from these. -/
def scenarioRow (scenario : Scenario) : String :=
  let pre := scenario.pre
  String.intercalate ","
    (["SCENARIO", scenario.name, scenario.cmd.commandKind, scenario.cmd.asset,
      scenario.cmd.assetClass.code, toString scenario.cmd.atomDecimals,
      scenario.cmd.accountOwner, toString scenario.cmd.amountAtoms,
      pre.policy.asset, pre.policy.assetClass.code, toString pre.policy.atomDecimals,
      toString pre.supplyAtoms, toString pre.accountTotalAtoms] ++ balanceFields pre)

/-- Relations between the opaque tokens.  No root value crosses the boundary;
only the equalities the model actually reads do. -/
def relationRow (scenario : Scenario) : String :=
  let ctx := scenario.ctx
  let pre := scenario.pre
  let cmd := scenario.cmd
  let occFlag (predicate : Occurrence → Prop) [DecidablePred predicate] : String :=
    match ctx.occurrence with
    | none => "absent"
    | some occurrence => flag (predicate occurrence)
  String.intercalate ","
    ["RELATION", scenario.name,
      flag (ctx.occurrence ≠ none),
      occFlag (fun occurrence => occurrence.preStateRoot = ctx.globalPreStateRoot),
      occFlag (fun occurrence => occurrence.consumedObjectIds = []),
      flag (ctx.moduleReleaseId = pre.moduleReleaseId),
      occFlag (fun occurrence => occurrence.commandKind = cmd.commandKind),
      occFlag (fun occurrence => occurrence.commandBodyHash = cmd.commandBodyHash),
      flag (cmd.asset = pre.policy.asset),
      flag (pre.policy.enabled = true),
      flag (cmd.assetClass = pre.policy.assetClass),
      flag (cmd.atomDecimals = pre.policy.atomDecimals),
      flag (originRegistered pre cmd),
      flag (cmd.assetOriginRoot = pre.policy.assetOriginRoot),
      flag (pre.policy.assetClass =
        AssetTransferRefinementV2.AssetClass.registeredOrdinaryToken),
      flag (pre.policy.issueAuthority.isSome = true),
      flag (pre.policy.burnAuthorizationRoot.isSome = true),
      occFlag (fun occurrence =>
        pre.policy.issueAuthority.map IssueAuthority.subject = some occurrence.subjectId),
      occFlag (fun occurrence => occurrence.subjectId = cmd.accountOwner),
      occFlag (fun occurrence =>
        some occurrence.grantRoot = expectedAuthorizationRoot pre.policy cmd),
      flag (cmd.authorizationRoot = expectedAuthorizationRoot pre.policy cmd),
      flag (cmd.amountAtoms ≠ 0),
      flag (effectDeltaAdmitted cmd)]

/-- The complete modeled outcome of one vector. -/
def outcomeRow (scenario : Scenario) : String :=
  let result := scenario.run
  let effects := result.effects
  String.intercalate ","
    (["OUTCOME", scenario.name, verdictLabel result.verdict,
      toString result.post.supplyAtoms, toString result.post.accountTotalAtoms,
      toString effects.laneWrites.length,
      flag (effects.laneWrites =
        [⟨parityRoots.stateRoot scenario.pre, parityRoots.stateRoot result.post⟩]),
      toString effects.occurrenceConsumptions.length,
      String.intercalate ";" effects.occurrenceConsumptions,
      toString effects.externalOutbox.length,
      flag (effects.externalRoots = AssetTransferRefinementV2.ExternalRoots.zero),
      flag (effects.payload.isSome = true)] ++ balanceFields result.post)

/-- The modeled effect payload of an accepted vector, and the M3 mutant beside
it.  Rejected vectors emit no payload row. -/
def payloadRows (scenario : Scenario) : List String :=
  match scenario.run.effects.payload with
  | none => []
  | some payload =>
      [ String.intercalate ","
          ["PAYLOAD", scenario.name, payload.accountOwner,
            toString payload.accountDeltaAtoms, supplyKindLabel payload.supplyKind,
            toString payload.supplyDeltaAtoms,
            toString payload.conservation.ownedPreAtoms,
            toString payload.conservation.ownedPostAtoms,
            toString payload.conservation.supplyPreAtoms,
            toString payload.conservation.supplyPostAtoms,
            toString payload.conservation.authorizedIssueAtoms,
            toString payload.conservation.authorizedBurnAtoms],
        String.intercalate ","
          ["MUTANT_M3", scenario.name,
            toString (mutantPayloadM3 scenario.pre scenario.cmd).conservation.supplyPostAtoms] ]

def mutantRow (scenario : Scenario) : String :=
  String.intercalate ","
    ["MUTANT", scenario.name, optionLabel (realCode scenario),
      optionLabel (mutantCodeM1 scenario), optionLabel (mutantCodeM2 scenario)]

def historyRows : LifecycleState → List Step → List String
  | _, [] => []
  | state, step :: rest =>
      let result := transition parityRoots step.ctx state step.cmd
      String.intercalate ","
        (["HISTORY", step.label, step.cmd.commandKind, step.cmd.accountOwner,
          toString step.cmd.amountAtoms, verdictLabel result.verdict,
          toString result.post.supplyAtoms, toString result.post.accountTotalAtoms,
          toString result.effects.occurrenceConsumptions.length,
          String.intercalate ";" result.effects.occurrenceConsumptions,
          flag (result.post.supplyAtoms = state.supplyAtoms ∧
            result.post.accountTotalAtoms = state.accountTotalAtoms)] ++
          balanceFields result.post)
        :: historyRows result.post rest

def historyStartRow : String :=
  String.intercalate ","
    (["HISTORY_START", toString historyStart.supplyAtoms,
      toString historyStart.accountTotalAtoms] ++ balanceFields historyStart)

/-- The full deterministic comparison report. -/
def runtimeParityReportV2 : String :=
  String.intercalate "\n"
    (allRejectCodes.map codeRow ++
      [widthRow, principalRow] ++
      vectors.map scenarioRow ++
      vectors.map relationRow ++
      vectors.map outcomeRow ++
      (vectors.map payloadRows).foldr (fun rows acc => rows ++ acc) [] ++
      vectors.map mutantRow ++
      [historyStartRow] ++
      historyRows historyStart historySteps)

end ManagedAssetRuntimeParityV2
end Proofs
