import Proofs.ForbiddenTraceMinor
import Proofs.NoFreeResourceTraceLedger
import Mathlib

/-!
# ZenoDEX Disaster Schema Instantiations

This module gives small concrete instantiations of the generic disaster-state
schemas:

- no-free-resource trace ledgers for API scan, reward, bounty, and proof-work
  budget surfaces
- forbidden trace motifs for stale settlement, missing oracle settlement,
  unpaired COW netting, and API overscan-style disasters

These are still proof adapters, not a full runtime refinement proof. They make
the reusable theorem schemas easier to bind to concrete replay receipts.
-/

namespace Proofs
namespace ZenoDEXDisasterSchemaInstantiations

open Proofs.NoFreeResourceTraceLedger
open Proofs.ForbiddenTraceMinor

universe u

variable {Event : Type u}

/-! ## No-free-resource ledger adapters -/

/-- If every accepted event has a nonpositive protected-resource delta, then the
whole accepted trace cannot have a positive protected-resource delta. -/
theorem nonpositive_event_deltas_cannot_create_positive_resource
    (delta : Event → Int)
    (events : List Event)
    (heventSafe : ∀ e : Event, e ∈ events → delta e ≤ 0) :
    ¬ 0 < traceDelta (0 : Int) (fun a b => a + b) delta events := by
  intro hcreated
  have hsafeCone :
      SafeCone (0 : Int) (fun a b => a + b) (fun r : Int => r ≤ 0) := by
    constructor
    · omega
    · intro a b ha hb
      change a + b ≤ 0
      omega
  have htraceSafe :
      traceDelta (0 : Int) (fun a b => a + b) delta events ≤ 0 := by
    exact trace_delta_safe_of_eventwise_safe
      (0 : Int)
      (fun a b => a + b)
      delta
      (fun r : Int => r ≤ 0)
      hsafeCone
      events
      heventSafe
  omega

/-- Budget-bearing event families used by replay receipts and simulations. -/
inductive BudgetEvent
  | apiScan (units : Nat)
  | proofMiningReward (amount : Nat)
  | bountyPayout (amount : Nat)
  | proofWork (units : Nat)
  | noop
  deriving DecidableEq, Repr

def apiScanCost : BudgetEvent → Nat
  | .apiScan units => units
  | _ => 0

def proofMiningRewardCost : BudgetEvent → Nat
  | .proofMiningReward amount => amount
  | _ => 0

def bountyPayoutCost : BudgetEvent → Nat
  | .bountyPayout amount => amount
  | _ => 0

def proofWorkCost : BudgetEvent → Nat
  | .proofWork units => units
  | _ => 0

/-- API scan claims cannot exceed the declared prefix resource budget. -/
theorem api_scan_prefix_claim_above_budget_rejected
    (events pref : List BudgetEvent)
    (budget claim : Nat)
    (hprefixSafe : PrefixBudgetSafe apiScanCost events budget)
    (hprefix : IsPrefix pref events)
    (hclaim : budget < claim) :
    claim ≤ natTraceSpend apiScanCost pref → False := by
  exact no_prefix_claim_above_budget apiScanCost events pref budget claim
    hprefixSafe hprefix hclaim

/-- Proof-mining reward claims cannot exceed the chain-visible reward budget. -/
theorem proof_mining_reward_claim_above_budget_rejected
    (events : List BudgetEvent)
    (budget claim : Nat)
    (hspend : natTraceSpend proofMiningRewardCost events ≤ budget)
    (hclaim : budget < claim) :
    claim ≤ natTraceSpend proofMiningRewardCost events → False := by
  exact no_claim_above_budget_if_spend_bounded proofMiningRewardCost events
    budget claim hspend hclaim

/-- Bounty payouts cannot exceed the declared bounty budget. -/
theorem bounty_claim_above_budget_rejected
    (events : List BudgetEvent)
    (budget claim : Nat)
    (hspend : natTraceSpend bountyPayoutCost events ≤ budget)
    (hclaim : budget < claim) :
    claim ≤ natTraceSpend bountyPayoutCost events → False := by
  exact no_claim_above_budget_if_spend_bounded bountyPayoutCost events
    budget claim hspend hclaim

/-- Proof-work claims cannot exceed the accepted proof-work accounting budget. -/
theorem proof_work_claim_above_budget_rejected
    (events : List BudgetEvent)
    (budget claim : Nat)
    (hspend : natTraceSpend proofWorkCost events ≤ budget)
    (hclaim : budget < claim) :
    claim ≤ natTraceSpend proofWorkCost events → False := by
  exact no_claim_above_budget_if_spend_bounded proofWorkCost events
    budget claim hspend hclaim

/-! ## Forbidden motif adapters -/

inductive TraceAtom
  | staleQuote
  | settlementUse
  | oracleMissing
  | perpSettle
  | unpairedCowFill
  | apiOverscanRequest
  | unrelated
  deriving DecidableEq, Repr

abbrev DisasterTrace := List TraceAtom

/-- A simple motif embedding relation: every atom in the motif appears in the
larger trace. Concrete replay receipts may replace this with an order-aware or
state-aware embedding relation. -/
def Embeds (motif trace : DisasterTrace) : Prop :=
  ∀ atom : TraceAtom, atom ∈ motif → atom ∈ trace

theorem embeds_refl (trace : DisasterTrace) : Embeds trace trace := by
  intro atom hmem
  exact hmem

theorem embeds_trans {a b c : DisasterTrace}
    (hab : Embeds a b) (hbc : Embeds b c) : Embeds a c := by
  intro atom hmem
  exact hbc atom (hab atom hmem)

def staleSettlementMotif : DisasterTrace :=
  [.staleQuote, .settlementUse]

def missingOracleSettleMotif : DisasterTrace :=
  [.oracleMissing, .perpSettle]

def unpairedCowMotif : DisasterTrace :=
  [.unpairedCowFill]

def apiOverscanMotif : DisasterTrace :=
  [.apiOverscanRequest]

def knownMotifs : List DisasterTrace :=
  [
    staleSettlementMotif,
    missingOracleSettleMotif,
    unpairedCowMotif,
    apiOverscanMotif
  ]

def KnownMotif (motif : DisasterTrace) : Prop :=
  motif ∈ knownMotifs

/-- A trace is motif-bad when it embeds one of the known dangerous motifs. -/
def MotifBad (trace : DisasterTrace) : Prop :=
  ∃ motif : DisasterTrace, KnownMotif motif ∧ Embeds motif trace

/-- The motif rejection adapter rejects exactly traces embedding a known motif. -/
def MotifRejected (trace : DisasterTrace) : Prop :=
  ∃ motif : DisasterTrace, KnownMotif motif ∧ Embeds motif trace

theorem known_motif_covers_motif_bad :
    MotifCoversBad Embeds KnownMotif MotifBad := by
  intro trace hbad
  exact hbad

theorem known_motifs_rejected :
    ∀ motif : DisasterTrace, KnownMotif motif → MotifRejected motif := by
  intro motif hknown
  exact ⟨motif, hknown, embeds_refl motif⟩

theorem motif_rejection_upward_closed :
    EmbeddingUpwardClosed Embeds MotifRejected := by
  intro motif trace hemb hrej
  rcases hrej with ⟨basis, hbasis, hbasisEmbeds⟩
  exact ⟨basis, hbasis, embeds_trans hbasisEmbeds hemb⟩

/-- Concrete adapter: known motif rejection rejects any trace in the
motif-bad family. -/
theorem known_motif_bad_traces_rejected :
    ∀ trace : DisasterTrace, MotifBad trace → MotifRejected trace := by
  exact motif_rejection_lifts_to_all_bad
    Embeds
    KnownMotif
    MotifBad
    MotifRejected
    known_motif_covers_motif_bad
    known_motifs_rejected
    motif_rejection_upward_closed

/-- If accepted traces are disjoint from motif-rejected traces, no accepted
trace can contain a known bad motif. -/
theorem accepted_known_motif_bad_impossible
    (Accepted : DisasterTrace → Prop)
    (hdisjoint : ∀ trace : DisasterTrace, Accepted trace → MotifRejected trace → False) :
    ∀ trace : DisasterTrace, Accepted trace → MotifBad trace → False := by
  intro trace haccepted hbad
  exact hdisjoint trace haccepted (known_motif_bad_traces_rejected trace hbad)

end ZenoDEXDisasterSchemaInstantiations
end Proofs
