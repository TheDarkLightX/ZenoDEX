import Proofs.GlobalEconomicStateRefinementV2
import Proofs.PerpsMarginTransitionV1

/-!
# Per-account margin claim episodes

This model isolates `advance_margin_claims_v2`: the existing economic kernel
supplies one replacement account. A slot owns that account and its optional
active claim, reflecting the exact account/binding coverage of PerpsMarginStateV2.
Tables are keyed partial maps; IDs are opaque. Existing accounts keep their
owner, and the supplied collateral fits u128. These are explicit premises from
the economic transition, not authentication or arithmetic proved here.

The universal result concerns the modeled episode transition. The companion
Python gate checks finite executable correspondence with the actual helper.
The missing-active-record branch is unreachable under WellFormed; Python raises
there, whereas this model has no successor. Malformed-input parity is excluded.
Canonical ordering, ID hashing/collision resistance, collection limits, roots,
Python ownership, global effects, authorization, and publication are excluded.
All authority remains NONE.
-/

namespace ZenoDEX.PerpsMarginClaimsV2

open Proofs.GlobalSettlementCoreV2
open Proofs.GlobalEconomicStateRefinementV2
open PerpsMarginTransitionV1 (Account)

structure Entry where
  account : Account
  claim : Option Identifier
  deriving DecidableEq, Repr

structure State where
  asset : Asset
  entries : Identifier → Option Entry
  terminals : Identifier → Option TerminalObligation

def setAt {α : Type} (table : Identifier → α) (key : Identifier) (value : α) :
    Identifier → α := fun other => if other = key then value else table other

def openClaim (asset : Asset) (id : Identifier) (a : Account) : TerminalObligation :=
  ⟨id, .perpsMarket, a.owner, asset, "perps_margin", a.collateral, .open⟩

def activeId (s : State) (key : Identifier) : Option Identifier :=
  (s.entries key).bind fun entry => entry.claim

def install (s : State) (a : Account) (claim : Option Identifier)
    (terminals : Identifier → Option TerminalObligation) : State :=
  { s with entries := setAt s.entries a.id (some ⟨a, claim⟩), terminals := terminals }

theorem active_install (s a claim terminals key) :
    activeId (install s a claim terminals) key =
      if key = a.id then claim else activeId s key := by
  by_cases h : key = a.id
  · subst key
    simp only [activeId, install, setAt, ite_true, Option.bind_some]
  · simp only [activeId, install, setAt, if_neg h]

theorem active_from_entry (s : State) (key : Identifier) (entry : Entry)
    (h : s.entries key = some entry) : activeId s key = entry.claim := by
  simp only [activeId, h, Option.bind_some]

def EntryValid (s : State) (key : Identifier) (entry : Entry) : Prop :=
  entry.account.id = key ∧ FitsU128 (entry.account.collateral : Int) ∧
  match entry.claim with
  | none => entry.account.collateral = 0
  | some id => 0 < entry.account.collateral ∧
      s.terminals id = some (openClaim s.asset id entry.account)

structure WellFormed (s : State) : Prop where
  entriesValid : ∀ key entry, s.entries key = some entry → EntryValid s key entry
  unique : ∀ left right id, activeId s left = some id →
    activeId s right = some id → left = right
  terminalKeys : ∀ id row, s.terminals id = some row → row.obligationId = id
  terminalValid : ∀ id row, s.terminals id = some row → TerminalObligationAdmitted row
  openCovered : ∀ id row, s.terminals id = some row → row.laneId = .perpsMarket →
    row.status = .open → ∃ key, activeId s key = some id

def OwnerPreserved (s : State) (a : Account) : Prop :=
  ∀ entry, s.entries a.id = some entry → entry.account.owner = a.owner

/-- Collision or missing active record fails without a successor. Economic
authorization and replacement-account validity belong to the calling kernel. -/
def advance (s : State) (a : Account) (fresh : Identifier) : Option State :=
  match activeId s a.id with
  | some id => match s.terminals id with
    | none => none
    | some old =>
      let claim := if a.collateral = 0 then none else some id
      let row := if a.collateral = 0 then { old with status := .drained }
        else { old with amountAtoms := a.collateral }
      some (install s a claim (setAt s.terminals id (some row)))
  | none =>
    if a.collateral = 0 then
      some (install s a none s.terminals)
    else if s.terminals fresh = none then
      some (install s a (some fresh)
        (setAt s.terminals fresh (some (openClaim s.asset fresh a))))
    else none

theorem active_entry (s : State) (key id : Identifier) (h : activeId s key = some id) :
    ∃ entry, s.entries key = some entry ∧ entry.claim = some id := by
  cases he : s.entries key with
  | none =>
      simp only [activeId, he, Option.bind_none] at h
      cases h
  | some entry => exact ⟨entry, rfl, by simpa only [activeId, he, Option.bind_some] using h⟩

theorem active_record (s : State) (wf : WellFormed s) (key id : Identifier)
    (h : activeId s key = some id) :
    ∃ entry, s.entries key = some entry ∧ entry.account.id = key ∧
      0 < entry.account.collateral ∧
      s.terminals id = some (openClaim s.asset id entry.account) := by
  obtain ⟨entry, he, hc⟩ := active_entry s key id h
  have hv := wf.entriesValid key entry he
  simp only [EntryValid, hc] at hv
  exact ⟨entry, he, hv.1, hv.2.2.1, hv.2.2.2⟩

private theorem open_admitted (asset id a) (fits : FitsU128 (a.collateral : Int))
    (positive : 0 < a.collateral) : TerminalObligationAdmitted (openClaim asset id a) := by
  refine ⟨fits, ?_⟩
  intro _
  change 0 < (a.collateral : Int)
  omega

/-- Every well-formed selected episode has a successor when a newly needed ID
is fresh. Positive updates, drains and empty closes need no fresh ID. -/
theorem advance_available (s : State) (wf : WellFormed s) (a : Account)
    (fresh : Identifier)
    (freshWhenNeeded : activeId s a.id = none → a.collateral ≠ 0 → s.terminals fresh = none) :
    ∃ post, advance s a fresh = some post := by
  cases active : activeId s a.id with
  | some id =>
      obtain ⟨entry, _, _, _, record⟩ := active_record s wf a.id id active
      simp only [advance, active, record]
      exact ⟨_, rfl⟩
  | none =>
      by_cases zero : a.collateral = 0
      · simp only [advance, active, if_pos zero]
        exact ⟨_, rfl⟩
      · simp only [advance, active, if_neg zero, if_pos (freshWhenNeeded active zero)]
        exact ⟨_, rfl⟩

theorem correspondence_preserved (s : State) (a : Account) (fresh : Identifier)
    (post : State) (wf : WellFormed s) (owner : OwnerPreserved s a)
    (fits : FitsU128 (a.collateral : Int)) (accepted : advance s a fresh = some post) :
    WellFormed post := by
  have ev := wf.entriesValid
  have uq := wf.unique
  have tk := wf.terminalKeys
  have tv := wf.terminalValid
  have oc := wf.openCovered
  cases active : activeId s a.id with
  | none =>
      by_cases zero : a.collateral = 0
      · simp only [advance, active, if_pos zero] at accepted
        cases accepted
        constructor <;> simp only [EntryValid, activeId, install, setAt] at *
          <;> grind [active_from_entry]
      · by_cases freshAbsent : s.terminals fresh = none
        · simp only [advance, active, if_neg zero, if_pos freshAbsent] at accepted
          cases accepted
          have positive : 0 < a.collateral := by omega
          have admitted := open_admitted s.asset fresh a fits positive
          have freshUnbound : ∀ key, activeId s key ≠ some fresh := by
            intro key bound
            obtain ⟨entry, _, _, _, record⟩ := active_record s wf key fresh bound
            rw [freshAbsent] at record
            cases record
          constructor <;> simp only [EntryValid, activeId, install, setAt, openClaim] at *
            <;> grind [active_from_entry]
        · simp only [advance, active, if_neg zero, if_neg freshAbsent] at accepted
          cases accepted
  | some id =>
      obtain ⟨entry, he, hi, hp, ht⟩ := active_record s wf a.id id active
      have sameOwner := owner entry he
      by_cases zero : a.collateral = 0
      · simp only [advance, active, ht, if_pos zero] at accepted
        cases accepted
        have admitted := tv id (openClaim s.asset id entry.account) ht
        constructor <;> simp only [EntryValid, activeId, install, setAt, openClaim,
          TerminalObligationAdmitted] at * <;> grind [active_from_entry]
      · simp only [advance, active, ht, if_neg zero] at accepted
        cases accepted
        have positive : 0 < a.collateral := by omega
        have admitted := open_admitted s.asset id a fits positive
        constructor <;> simp only [EntryValid, activeId, install, setAt, openClaim] at *
          <;> grind [active_from_entry]

/-- A successful episode writes one account coordinate and at most one terminal
coordinate. The complete sibling account (including owner and nonce) is framed. -/
theorem advance_frame (s : State) (a : Account) (fresh : Identifier) (post : State)
    (accepted : advance s a fresh = some post) :
    post.asset = s.asset ∧
    (∀ key, key ≠ a.id → post.entries key = s.entries key) ∧
    (∀ id, id ≠ (activeId s a.id).getD fresh → post.terminals id = s.terminals id) := by
  unfold advance at accepted
  split at accepted
  · split at accepted
    · cases accepted
    · cases accepted
      simp only [install, setAt]
      grind
  · split at accepted
    · cases accepted
      simp only [install, setAt]
      grind
    · split at accepted
      · cases accepted
        simp only [install, setAt]
        grind
      · cases accepted

/-- Drain retains the actual last positive record amount, not a zero-valued
replacement or the account's original funding amount. -/
theorem drain_retains_last_amount (s : State) (wf : WellFormed s) (a : Account)
    (fresh id : Identifier) (active : activeId s a.id = some id)
    (zero : a.collateral = 0) :
    ∃ old post, s.terminals id = some old ∧ 0 < old.amountAtoms ∧
      advance s a fresh = some post ∧ activeId post a.id = none ∧
      post.terminals id = some { old with status := .drained } := by
  obtain ⟨entry, _, _, positive, record⟩ := active_record s wf a.id id active
  let old := openClaim s.asset id entry.account
  let post := install s a none (setAt s.terminals id (some { old with status := .drained }))
  refine ⟨old, post, record, ?_, ?_, ?_, ?_⟩
  · change 0 < (entry.account.collateral : Int)
    omega
  · simp only [advance, active, record, if_pos zero]
    rfl
  · simp only [post, active_install, ite_true]
  · simp only [post, install, setAt, ite_true]

/-- A positive refill needs a key absent from the complete historical registry. -/
theorem refill_requires_fresh_record (s : State) (a : Account) (fresh : Identifier)
    (post : State) (inactive : activeId s a.id = none) (positive : 0 < a.collateral)
    (accepted : advance s a fresh = some post) :
    s.terminals fresh = none ∧ activeId post a.id = some fresh ∧
      post.terminals fresh = some (openClaim s.asset fresh a) := by
  have nonzero : a.collateral ≠ 0 := by omega
  simp only [advance, inactive, if_neg nonzero] at accepted
  split at accepted
  · cases accepted
    refine ⟨by assumption, ?_, ?_⟩
    · simp only [active_install, ite_true]
    · simp only [install, setAt, ite_true]
  · cases accepted

theorem refill_collision_rejected (s : State) (a : Account) (fresh : Identifier)
    (old : TerminalObligation) (inactive : activeId s a.id = none)
    (positive : 0 < a.collateral) (occupied : s.terminals fresh = some old) :
    advance s a fresh = none := by
  have nonzero : a.collateral ≠ 0 := by omega
  simp only [advance, inactive, if_neg nonzero, occupied, Option.some_ne_none, if_false]

/-- A terminal that is already drained or tombstoned is immutable under every
accepted episode; its claimant and prior amount cannot be reassigned. -/
theorem inactive_history_preserved (s : State) (wf : WellFormed s) (a : Account)
    (fresh : Identifier) (post : State) (id : Identifier) (old : TerminalObligation)
    (record : s.terminals id = some old) (inactive : old.status ≠ .open)
    (accepted : advance s a fresh = some post) : post.terminals id = some old := by
  cases active : activeId s a.id with
  | some current =>
      obtain ⟨entry, _, _, _, currentRecord⟩ := active_record s wf a.id current active
      have distinct : id ≠ current := by
        intro eq
        subst id
        rw [record] at currentRecord
        cases currentRecord
        exact inactive rfl
      have framed := (advance_frame s a fresh post accepted).2.2 id
      simp only [active, Option.getD_some] at framed
      exact (framed distinct).trans record
  | none =>
      by_cases zero : a.collateral = 0
      · simp only [advance, active, if_pos zero] at accepted
        cases accepted
        exact record
      · have freshAbsent := (refill_requires_fresh_record s a fresh post active
          (by omega) accepted).1
        have distinct : id ≠ fresh := by
          intro eq
          subst id
          rw [record] at freshAbsent
          cases freshAbsent
        have framed := (advance_frame s a fresh post accepted).2.2 id
        simp only [active, Option.getD_none] at framed
        exact (framed distinct).trans record

/-- Every changed terminal satisfies the existing V2 lifecycle predicate.
Unchanged positive amounts generate no delta and need no lifecycle admission. -/
theorem changed_terminal_admitted (s : State) (wf : WellFormed s) (a : Account)
    (fresh : Identifier) (post : State) (owner : OwnerPreserved s a)
    (fits : FitsU128 (a.collateral : Int)) (accepted : advance s a fresh = some post)
    (id : Identifier) (after : TerminalObligation) (record : post.terminals id = some after)
    (changed : s.terminals id ≠ some after) :
    TerminalDeltaAdmitted ⟨id, s.terminals id, after⟩ := by
  have postWF := correspondence_preserved s a fresh post wf owner fits accepted
  have admitted := postWF.terminalValid id after record
  have mutation : id = (activeId s a.id).getD fresh := by
    by_cases same : id = (activeId s a.id).getD fresh
    · exact same
    · exact (changed (((advance_frame s a fresh post accepted).2.2 id same).symm.trans record)).elim
  cases active : activeId s a.id with
  | none =>
      simp only [active, Option.getD_none] at mutation
      subst id
      by_cases zero : a.collateral = 0
      · simp only [advance, active, if_pos zero] at accepted
        cases accepted
        exact (changed record).elim
      · obtain ⟨absent, _, newRecord⟩ := refill_requires_fresh_record s a fresh post
          active (by omega) accepted
        rw [record] at newRecord
        cases newRecord
        simp only [TerminalDeltaAdmitted, absent, openClaim]
        exact ⟨True.intro, admitted, True.intro⟩
  | some current =>
      simp only [active, Option.getD_some] at mutation
      subst id
      obtain ⟨entry, _, _, _, oldRecord⟩ := active_record s wf a.id current active
      have oldAdmitted := wf.terminalValid current _ oldRecord
      by_cases zero : a.collateral = 0
      · simp only [advance, active, oldRecord, if_pos zero] at accepted
        cases accepted
        simp only [install, setAt, ite_true] at record
        cases record
        simp only [TerminalDeltaAdmitted, oldRecord, TerminalIdentityPreserved, openClaim] at *
        grind
      · simp only [advance, active, oldRecord, if_neg zero] at accepted
        cases accepted
        simp only [install, setAt, ite_true] at record
        cases record
        simp only [TerminalDeltaAdmitted, oldRecord, TerminalIdentityPreserved, openClaim] at *
        grind

/-- Old keys are retained even when their active record changes status or amount. -/
theorem terminal_registry_retains (s : State) (a : Account) (fresh : Identifier)
    (post : State) (accepted : advance s a fresh = some post)
    (id : Identifier) (old : TerminalObligation) (record : s.terminals id = some old) :
    ∃ after, post.terminals id = some after := by
  unfold advance at accepted
  split at accepted
  · split at accepted
    · cases accepted
    · cases accepted
      simp only [install, setAt]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨old, record⟩
  · split at accepted
    · cases accepted
      exact ⟨old, record⟩
    · split at accepted
      · cases accepted
        simp only [install, setAt]
        split
        · exact ⟨_, rfl⟩
        · exact ⟨old, record⟩
      · cases accepted

def aliceAccount (id : Identifier) (collateral nonce : Nat) : Account :=
  ⟨id, "alice", 0, 0, collateral, nonce, false⟩

/-- Equal owner and equal amount still have two distinct account/claim coordinates. -/
def sameOwnerState : State :=
  { asset := "usd"
    entries := setAt (setAt (fun _ => none) "a"
      (some ⟨aliceAccount "a" 2 1, some "old-a"⟩)) "b"
      (some ⟨aliceAccount "b" 2 1, some "old-b"⟩)
    terminals := setAt (setAt (fun _ => none) "old-a"
      (some (openClaim "usd" "old-a" (aliceAccount "a" 2 1)))) "old-b"
      (some (openClaim "usd" "old-b" (aliceAccount "b" 2 1))) }

theorem same_owner_state_well_formed : WellFormed sameOwnerState := by
  constructor
  case openCovered =>
    intro id row record _ _
    by_cases hb : id = "old-b"
    · subst id
      exact ⟨"b", rfl⟩
    · by_cases ha : id = "old-a"
      · subst id
        exact ⟨"a", rfl⟩
      · simp only [sameOwnerState, setAt, if_neg hb, if_neg ha] at record
        cases record
  all_goals
    simp only [EntryValid, activeId, sameOwnerState, setAt,
      aliceAccount, openClaim, TerminalObligationAdmitted, FitsU128, maxU128]
    grind

/-- A real accepted drain/refill history keeps Alice's other account and claim,
retains the drained old-a record, and binds a to a new claim. -/
theorem same_owner_two_account_history :
    ∃ drained refilled,
      advance sameOwnerState (aliceAccount "a" 0 2) "unused" = some drained ∧
      advance drained (aliceAccount "a" 1 3) "new-a" = some refilled ∧
      activeId refilled "a" = some "new-a" ∧
      refilled.entries "b" = sameOwnerState.entries "b" ∧
      refilled.terminals "old-b" = sameOwnerState.terminals "old-b" ∧
      refilled.terminals "old-a" = some
        { openClaim "usd" "old-a" (aliceAccount "a" 2 1) with status := .drained } := by
  let drained := install sameOwnerState (aliceAccount "a" 0 2) none
    (setAt sameOwnerState.terminals "old-a" (some
      { openClaim "usd" "old-a" (aliceAccount "a" 2 1) with status := .drained }))
  let refilled := install drained (aliceAccount "a" 1 3) (some "new-a")
    (setAt drained.terminals "new-a"
      (some (openClaim "usd" "new-a" (aliceAccount "a" 1 3))))
  exact ⟨drained, refilled, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ZenoDEX.PerpsMarginClaimsV2
