import Proofs.GlobalSettlementCoreV1

/-!
# GlobalSettlementABI V1 — challenge module

This module is the admission challenge for `Proofs.GlobalSettlementCoreV1`. It
does two jobs.

**Signature binding.** Each `challenge_*` theorem restates an intended result
with its type written out in full and discharges it with the corresponding
theorem from the core module. If a core statement is later weakened,
renamed, or has a hypothesis added, this module stops compiling. The bindings
cover `Accepted` evidence construction, the full plan identities and
associativity, the reduced rejection equalities, per-asset projection and
application, and the rejection of a net-preserving issue/burn substitution.

**Executable comparison output.** `challengeReportV1` is a deterministic
string built by *evaluating the definitions* — `entryAdmissible`, `issuedFor`,
`burnedFor`, `netIssuance`, `applyPlan`, `Outcome.postState`,
`Outcome.effects`, and `planWellFormedOn`. It contains no hand-written
behavioural labels, so it cannot agree with Python by accident of a literal
that drifted from the proof. `entryAdmissible_iff` ties the executable
admission predicate back to the `EntryWellFormed` proposition, so evaluating
the Bool is evaluating the modeled rule.

`entryAdmissibleWeakIssue` is a deliberately weakened rule that drops ISSUE
strict positivity. It is emitted alongside the strict rule precisely so the
paired comparison can kill it: the strict vector must match Python and the
weakened vector must not.

## Bounded source comparison only

The report compares this file's abstractions against the current Python
enumerations and validators on a small fixed input set. It is a bounded
source comparison, not a runtime refinement proof, and it says nothing about
canonical row composition, roots, receipts, or production behaviour.
-/

namespace Proofs
namespace GlobalSettlementCoreV1Challenge

open Proofs.GlobalSettlementCoreV1

/-! ## 1. Bound signatures

Each statement below is written out in full and closed by the core theorem. -/

/-- `Accepted` is constructed from exactly these four obligations. -/
theorem challenge_accepted_evidence_construction :
    ∀ (pre : AssetBook) (p : AbstractEffectPlan) (post : AssetBook),
      PlanWellFormed p → PlanEntriesWellFormed p → Applies pre p post →
      NonNegativityAdmitted pre p → Accepted pre p post :=
  fun _ _ _ hw he ha hn =>
    { planWellFormed := hw, entriesWellFormed := he, applies := ha,
      nonNegativityAdmitted := hn }

/-- Accepted evidence is recoverable from an accepted outcome. -/
theorem challenge_accepted_outcome_carries_evidence :
    ∀ (pre : AssetBook) (p : AbstractEffectPlan) (post : AssetBook)
      (ev : Accepted pre p post),
      PlanWellFormed ((Outcome.accepted p post ev : Outcome pre).effects) ∧
      PlanEntriesWellFormed ((Outcome.accepted p post ev : Outcome pre).effects) ∧
      Applies pre ((Outcome.accepted p post ev : Outcome pre).effects)
        ((Outcome.accepted p post ev : Outcome pre).postState) ∧
      NonNegative ((Outcome.accepted p post ev : Outcome pre).postState) :=
  fun _ p post ev => accepted_outcome_carries_evidence p post ev

/-- An accepted outcome always has a non-negative post-book. -/
theorem challenge_accepted_outcome_is_nonNegative :
    ∀ (pre : AssetBook) (p : AbstractEffectPlan) (post : AssetBook)
      (ev : Accepted pre p post),
      NonNegative ((Outcome.accepted p post ev : Outcome pre).postState) :=
  fun _ _ _ ev => accepted_post_nonNegative ev

/-- Composition is unital and associative as a full structure identity. -/
theorem challenge_plan_identities :
    (∀ p : AbstractEffectPlan, seqPlan identityPlan p = p) ∧
    (∀ p : AbstractEffectPlan, seqPlan p identityPlan = p) ∧
    (∀ p q r : AbstractEffectPlan,
      seqPlan (seqPlan p q) r = seqPlan p (seqPlan q r)) :=
  ⟨seqPlan_identity_left, seqPlan_identity_right, seqPlan_assoc⟩

/-- Composition preserves both well-formedness predicates. -/
theorem challenge_plan_composition_preserves_wellFormedness :
    (∀ p q : AbstractEffectPlan,
      PlanWellFormed p → PlanWellFormed q → PlanWellFormed (seqPlan p q)) ∧
    (∀ p q : AbstractEffectPlan,
      PlanEntriesWellFormed p → PlanEntriesWellFormed q →
        PlanEntriesWellFormed (seqPlan p q)) :=
  ⟨fun _ _ hp hq => seqPlan_wellFormed hp hq,
    fun _ _ hp hq => seqPlan_entriesWellFormed hp hq⟩

/-- Rejection reduces definitionally: both equalities hold by `rfl` here. -/
theorem challenge_rejection_reduces :
    ∀ (pre : AssetBook) (c : RejectCode),
      (Outcome.rejected c : Outcome pre).postState = pre ∧
      (Outcome.rejected c : Outcome pre).effects = emptyAbstractPlan ∧
      (Outcome.rejected c : Outcome pre).effects.journal = [] :=
  fun _ _ => ⟨rfl, rfl, rfl⟩

/-- Per-asset projection is additive over journal concatenation. -/
theorem challenge_per_asset_projection :
    ∀ (a : Asset) (xs ys : AccountingJournal),
      issuedFor a (xs ++ ys) = issuedFor a xs + issuedFor a ys ∧
      burnedFor a (xs ++ ys) = burnedFor a xs + burnedFor a ys ∧
      netIssuance a (xs ++ ys) = netIssuance a xs + netIssuance a ys :=
  fun a xs ys =>
    ⟨issuedFor_append a xs ys, burnedFor_append a xs ys, netIssuance_append a xs ys⟩

/-- Entries for other assets never contribute. -/
theorem challenge_asset_separation :
    ∀ (a : Asset) (e : JournalEntry) (rest : AccountingJournal),
      e.asset ≠ a → netIssuance a (e :: rest) = netIssuance a rest :=
  fun _ _ _ h => netIssuance_ignores_other_assets h

/-- A well-formed plan moves both columns by the journal's net issuance. -/
theorem challenge_application_moves_by_projection :
    ∀ (pre post : AssetBook) (p : AbstractEffectPlan),
      PlanWellFormed p → Applies pre p post → ∀ a : Asset,
        post.accountedHoldings a = pre.accountedHoldings a + netIssuance a p.journal ∧
        post.accountedSupply a = pre.accountedSupply a + netIssuance a p.journal :=
  fun _ _ _ hw ha a => wellFormed_applies_moves_by_netIssuance hw ha a

/-- The net-preserving substitution keeps the derived deltas and is rejected. -/
theorem challenge_net_preserving_substitution_rejected :
    (∀ a : Asset,
      netPreservingSubstitutionPlan.holdingsDelta a = issuePlan.holdingsDelta a) ∧
    (∀ a : Asset,
      netPreservingSubstitutionPlan.supplyDelta a = issuePlan.supplyDelta a) ∧
    PlanWellFormed issuePlan ∧
    ¬ PlanWellFormed netPreservingSubstitutionPlan :=
  ⟨netPreservingSubstitution_same_holdingsDelta,
    netPreservingSubstitution_same_supplyDelta,
    issuePlan_wellFormed,
    netPreservingSubstitution_not_wellFormed⟩

/-- Non-negativity is separate: this plan is well-formed yet inadmissible. -/
theorem challenge_nonNegativity_is_separate :
    PlanWellFormed burnPlan ∧
    NonNegative thinBook ∧
    ¬ NonNegative (applyPlan thinBook burnPlan) ∧
    ¬ Accepted thinBook burnPlan (applyPlan thinBook burnPlan) :=
  ⟨burnPlan_wellFormed, thinBook_nonNegative, thinBook_burn_post_not_nonNegative,
    thinBook_burn_no_accepted_evidence⟩

/-! ## 2. Executable admission predicate

`entryAdmissible` computes the modeled entry rule, and `entryAdmissible_iff`
proves it decides `EntryWellFormed`, so evaluating it evaluates the rule. -/

/-- Executable form of `EntryWellFormed`. For `issue` the strict positivity
already forces nonzero, and likewise for `burn`. -/
def entryAdmissible (e : JournalEntry) : Bool :=
  match e.kind with
  | EffectKind.issue => decide (0 < e.deltaAtoms)
  | EffectKind.burn => decide (e.deltaAtoms < 0)
  | _ => decide (e.deltaAtoms ≠ 0)

theorem entryAdmissible_iff (e : JournalEntry) :
    entryAdmissible e = true ↔ EntryWellFormed e := by
  constructor
  · intro h
    cases hk : e.kind <;>
      simp only [entryAdmissible, hk, decide_eq_true_eq] at h <;>
      exact
        { nonzero := by omega
          issuePositive := by
            intro hi
            rw [hk] at hi
            first
              | exact absurd hi (by decide)
              | omega
          burnNegative := by
            intro hb
            rw [hk] at hb
            first
              | exact absurd hb (by decide)
              | omega }
  · intro h
    cases hk : e.kind <;>
      simp only [entryAdmissible, hk, decide_eq_true_eq] <;>
      first
        | exact h.issuePositive hk
        | exact h.burnNegative hk
        | exact h.nonzero

/-- A deliberately weakened rule that drops ISSUE strict positivity. It exists
only so the paired source comparison can kill it. -/
def entryAdmissibleWeakIssue (e : JournalEntry) : Bool :=
  match e.kind with
  | EffectKind.burn => decide (e.deltaAtoms < 0)
  | _ => decide (e.deltaAtoms ≠ 0)

/-- A negative ISSUE entry: rejected by the modeled rule, accepted by the
weakened one. -/
def negativeIssueEntry : JournalEntry where
  kind := EffectKind.issue
  principal := treasury
  asset := zusd
  controlDomain := ledgerDomain
  deltaAtoms := -1

theorem weakIssue_differs_on_negative_issue :
    entryAdmissible negativeIssueEntry = false ∧
    entryAdmissibleWeakIssue negativeIssueEntry = true := by decide

theorem weakIssue_is_strictly_weaker :
    ¬ (∀ e : JournalEntry, entryAdmissibleWeakIssue e = entryAdmissible e) := by
  intro h
  have hstrict : entryAdmissible negativeIssueEntry = false :=
    weakIssue_differs_on_negative_issue.1
  have hweak : entryAdmissibleWeakIssue negativeIssueEntry = true :=
    weakIssue_differs_on_negative_issue.2
  have hcontra := h negativeIssueEntry
  rw [hstrict, hweak] at hcontra
  exact absurd hcontra (by decide)

/-- Executable admissibility of a whole journal. -/
def journalAdmissible : AccountingJournal → Bool
  | [] => true
  | e :: rest => entryAdmissible e && journalAdmissible rest

theorem entriesWellFormed_of_journalAdmissible :
    ∀ journal : AccountingJournal, journalAdmissible journal = true →
      ∀ e ∈ journal, EntryWellFormed e := by
  intro journal
  induction journal with
  | nil =>
      intro _ e he
      nomatch he
  | cons x rest ih =>
      intro h e he
      simp only [journalAdmissible, Bool.and_eq_true] at h
      cases he with
      | head => exact (entryAdmissible_iff _).mp h.1
      | tail _ hrest => exact ih h.2 e hrest

/-! ## 3. Bounded executable well-formedness check -/

/-- Checks the two conservation equations on a finite asset list. -/
def planWellFormedOn (p : AbstractEffectPlan) : List Asset → Bool
  | [] => true
  | a :: rest =>
      decide (p.authorizedIssue a = issuedFor a p.journal)
        && decide (p.authorizedBurn a = burnedFor a p.journal)
        && planWellFormedOn p rest

theorem planWellFormedOn_of_wellFormed (p : AbstractEffectPlan)
    (h : PlanWellFormed p) : ∀ assets : List Asset, planWellFormedOn p assets = true := by
  intro assets
  induction assets with
  | nil => rfl
  | cons a rest ih =>
      have h1 : decide (p.authorizedIssue a = issuedFor a p.journal) = true :=
        decide_eq_true (h.issue a)
      have h2 : decide (p.authorizedBurn a = burnedFor a p.journal) = true :=
        decide_eq_true (h.burn a)
      simp only [planWellFormedOn, h1, h2, ih, Bool.and_self]

/-- A failing bounded check refutes well-formedness outright. -/
theorem not_wellFormed_of_planWellFormedOn_false (p : AbstractEffectPlan)
    (assets : List Asset) (h : planWellFormedOn p assets = false) :
    ¬ PlanWellFormed p := by
  intro hwf
  have htrue := planWellFormedOn_of_wellFormed p hwf assets
  exact absurd (htrue.symm.trans h) (by decide)

/-! ## 4. Shared bounded comparison inputs -/

def zbtc : Asset := "ZBTC"

/-- Assets probed by the comparison, including one absent from the journal. -/
def comparisonAssets : List Asset := [zusd, zdex, zbtc]

/-- A mixed journal: an issue, a burn, a two-sided transfer, and a second
asset. -/
def comparisonJournal : AccountingJournal :=
  [ { kind := EffectKind.issue, principal := treasury, asset := zusd,
      controlDomain := ledgerDomain, deltaAtoms := 250 },
    { kind := EffectKind.burn, principal := treasury, asset := zusd,
      controlDomain := ledgerDomain, deltaAtoms := -70 },
    { kind := EffectKind.accountMovement, principal := alice, asset := zusd,
      controlDomain := ledgerDomain, deltaAtoms := -100 },
    { kind := EffectKind.accountMovement, principal := bob, asset := zusd,
      controlDomain := ledgerDomain, deltaAtoms := 100 },
    { kind := EffectKind.issue, principal := treasury, asset := zdex,
      controlDomain := ledgerDomain, deltaAtoms := 40 } ]

/-- The plan whose totals are taken directly from the journal projections, so
it is well-formed by construction. -/
def comparisonPlan : AbstractEffectPlan where
  journal := comparisonJournal
  authorizedIssue := fun a => issuedFor a comparisonJournal
  authorizedBurn := fun a => burnedFor a comparisonJournal

theorem comparisonPlan_wellFormed : PlanWellFormed comparisonPlan :=
  { issue := fun _ => rfl, burn := fun _ => rfl }

theorem comparisonPlan_entriesWellFormed : PlanEntriesWellFormed comparisonPlan :=
  entriesWellFormed_of_journalAdmissible comparisonJournal (by decide)

def comparisonBook : AssetBook where
  accountedHoldings := fun a => if zusd = a then 1000 else if zdex = a then 500 else 0
  accountedSupply := fun a => if zusd = a then 1000 else if zdex = a then 500 else 0

/-! ## 5. Derived report

Every field below is computed from the definitions above. -/

def boolField (b : Bool) : String :=
  if b then "true" else "false"

def laneRow (l : LaneId) : String :=
  String.intercalate "," ["LANE", l.code, toString l.index]

def kindRow (k : EffectKind) : String :=
  String.intercalate "," ["KIND", k.code]

def rejectCodeRow (c : RejectCode) : String :=
  String.intercalate "," ["REJECTCODE", c.code]

def probeEntry (k : EffectKind) (d : Int) : JournalEntry where
  kind := k
  principal := treasury
  asset := zusd
  controlDomain := ledgerDomain
  deltaAtoms := d

def signRow (k : EffectKind) (d : Int) : String :=
  String.intercalate ","
    ["SIGN", k.code, toString d, boolField (entryAdmissible (probeEntry k d))]

def signWeakRow (k : EffectKind) (d : Int) : String :=
  String.intercalate ","
    ["SIGNWEAK", k.code, toString d, boolField (entryAdmissibleWeakIssue (probeEntry k d))]

def signRowsForKind (k : EffectKind) : List String :=
  [signRow k (-1), signRow k 0, signRow k 1]

def signWeakRowsForKind (k : EffectKind) : List String :=
  [signWeakRow k (-1), signWeakRow k 0, signWeakRow k 1]

def signMatrix : List String :=
  (allEffectKinds.map signRowsForKind).foldr (fun xs acc => xs ++ acc) []

def signWeakMatrix : List String :=
  (allEffectKinds.map signWeakRowsForKind).foldr (fun xs acc => xs ++ acc) []

def projectionRow (a : Asset) : String :=
  String.intercalate ","
    ["PROJ", a, toString (issuedFor a comparisonJournal),
      toString (burnedFor a comparisonJournal),
      toString (netIssuance a comparisonJournal)]

def applyRow (a : Asset) : String :=
  String.intercalate ","
    ["APPLY", a,
      toString (comparisonBook.accountedHoldings a),
      toString (comparisonBook.accountedSupply a),
      toString ((applyPlan comparisonBook comparisonPlan).accountedHoldings a),
      toString ((applyPlan comparisonBook comparisonPlan).accountedSupply a)]

def rejectRow (c : RejectCode) : String :=
  String.intercalate ","
    ["REJECT", c.code,
      toString ((Outcome.rejected c : Outcome comparisonBook).postState.accountedHoldings zusd),
      toString ((Outcome.rejected c : Outcome comparisonBook).postState.accountedSupply zusd),
      toString ((Outcome.rejected c : Outcome comparisonBook).effects.journal.length),
      toString ((Outcome.rejected c : Outcome comparisonBook).effects.authorizedIssue zusd),
      toString ((Outcome.rejected c : Outcome comparisonBook).effects.authorizedBurn zusd)]

def substRow (label : String) (p : AbstractEffectPlan) : String :=
  String.intercalate ","
    ["SUBST", label, boolField (planWellFormedOn p comparisonAssets)]

def substMatrix : List String :=
  [substRow "honest" issuePlan, substRow "inflated" netPreservingSubstitutionPlan]

/-- The full deterministic comparison report. -/
def challengeReportV1 : String :=
  String.intercalate "\n"
    (allLaneIds.map laneRow ++
      allEffectKinds.map kindRow ++
      allRejectCodes.map rejectCodeRow ++
      signMatrix ++
      signWeakMatrix ++
      comparisonAssets.map projectionRow ++
      comparisonAssets.map applyRow ++
      allRejectCodes.map rejectRow ++
      substMatrix)

/-! ## 6. Report-level sanity facts

These pin the interesting rows so a silent change to the report shape fails
here rather than only in the Python comparison. -/

theorem substMatrix_separates_honest_from_inflated :
    planWellFormedOn issuePlan comparisonAssets = true ∧
    planWellFormedOn netPreservingSubstitutionPlan comparisonAssets = false := by
  decide

/-- The bounded check refutes the substitution, independently of the core
theorem, by way of `not_wellFormed_of_planWellFormedOn_false`. -/
theorem substitution_refuted_by_bounded_check :
    ¬ PlanWellFormed netPreservingSubstitutionPlan :=
  not_wellFormed_of_planWellFormedOn_false netPreservingSubstitutionPlan comparisonAssets
    substMatrix_separates_honest_from_inflated.2

theorem comparisonJournal_projection_values :
    issuedFor zusd comparisonJournal = 250 ∧
    burnedFor zusd comparisonJournal = 70 ∧
    netIssuance zusd comparisonJournal = 180 ∧
    issuedFor zdex comparisonJournal = 40 ∧
    burnedFor zdex comparisonJournal = 0 ∧
    netIssuance zbtc comparisonJournal = 0 := by
  decide

end GlobalSettlementCoreV1Challenge
end Proofs
