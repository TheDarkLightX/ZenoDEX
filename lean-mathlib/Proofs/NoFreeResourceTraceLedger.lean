import Mathlib

/-!
# No-Free-Resource Trace Ledger

This module proves a generic theorem layer for typed resource conservation
across protocol traces.

The intended ZenoDEX use is to model assets, reward budgets, oracle freshness,
execution authority, proof work, and CPU scan budget as typed resources. Every
accepted event carries a safe ledger delta. If the safe cone is closed under
trace composition, an accepted trace cannot create a protected resource for
free.

This is a schema. Concrete assurance requires instantiating `Resource`,
`traceDelta`, `Safe`, `Created`, and the budget predicates against a real
runtime surface.
-/

namespace Proofs
namespace NoFreeResourceTraceLedger

universe u v

variable {Event : Type u}
variable {Resource : Type v}

/-- Fold event deltas into one trace delta using an abstract additive operation. -/
def traceDelta
    (zero : Resource)
    (add : Resource → Resource → Resource)
    (delta : Event → Resource) : List Event → Resource :=
  List.foldl (fun acc e => add acc (delta e)) zero

/-- A safe resource cone contains zero and is closed under addition. -/
def SafeCone
    (zero : Resource)
    (add : Resource → Resource → Resource)
    (Safe : Resource → Prop) : Prop :=
  Safe zero ∧ ∀ a b : Resource, Safe a → Safe b → Safe (add a b)

/-- A trace is eventwise safe when every event delta lies in the safe cone. -/
def EventwiseSafe
    (delta : Event → Resource)
    (Safe : Resource → Prop)
    (events : List Event) : Prop :=
  ∀ e : Event, e ∈ events → Safe (delta e)

/-- A resource creation predicate is forbidden when it is disjoint from the safe cone. -/
def CreationDisjointFromSafe
    (Safe Created : Resource → Prop) : Prop :=
  ∀ r : Resource, Safe r → Created r → False

/-- Core composition theorem: if every event delta is safe and the safe cone is
closed under trace composition, then the whole trace delta is safe. -/
theorem trace_delta_safe_of_eventwise_safe
    (zero : Resource)
    (add : Resource → Resource → Resource)
    (delta : Event → Resource)
    (Safe : Resource → Prop)
    (hsafeCone : SafeCone zero add Safe) :
    ∀ events : List Event,
      EventwiseSafe delta Safe events →
      Safe (traceDelta zero add delta events) := by
  intro events hsafe
  induction events using List.reverseRecOn with
  | nil =>
      exact hsafeCone.1
  | append_singleton xs x ih =>
      unfold traceDelta
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact hsafeCone.2
        (traceDelta zero add delta xs)
        (delta x)
        (ih (fun e he => hsafe e (by simp [he])))
        (hsafe x (by simp))

/-- Accepted-event version: if accepted events always have safe deltas, then an
accepted trace has a safe total delta. -/
theorem accepted_trace_delta_safe
    (zero : Resource)
    (add : Resource → Resource → Resource)
    (delta : Event → Resource)
    (Safe : Resource → Prop)
    (AcceptedEvent : Event → Prop)
    (hsafeCone : SafeCone zero add Safe)
    (hacceptedSafe : ∀ e : Event, AcceptedEvent e → Safe (delta e)) :
    ∀ events : List Event,
      (∀ e : Event, e ∈ events → AcceptedEvent e) →
      Safe (traceDelta zero add delta events) := by
  intro events haccepted
  exact trace_delta_safe_of_eventwise_safe zero add delta Safe hsafeCone events
    (fun e he => hacceptedSafe e (haccepted e he))

/-- No-free-resource theorem: accepted traces cannot create a protected resource
when creation is disjoint from the safe cone. -/
theorem no_free_resource_creation_from_accepted_trace
    (zero : Resource)
    (add : Resource → Resource → Resource)
    (delta : Event → Resource)
    (Safe Created : Resource → Prop)
    (AcceptedEvent : Event → Prop)
    (hsafeCone : SafeCone zero add Safe)
    (hacceptedSafe : ∀ e : Event, AcceptedEvent e → Safe (delta e))
    (hdisjoint : CreationDisjointFromSafe Safe Created) :
    ∀ events : List Event,
      (∀ e : Event, e ∈ events → AcceptedEvent e) →
      Created (traceDelta zero add delta events) →
      False := by
  intro events haccepted hcreated
  have hsafe : Safe (traceDelta zero add delta events) :=
    accepted_trace_delta_safe zero add delta Safe AcceptedEvent hsafeCone hacceptedSafe events haccepted
  exact hdisjoint _ hsafe hcreated

/-- Nat-valued budget spend for concrete resource surfaces such as reward pools,
proof-mining payouts, API scan budgets, and bounty budgets. -/
def natTraceSpend (cost : Event → Nat) : List Event → Nat :=
  List.foldl (fun acc e => acc + cost e) 0

/-- If total spend is bounded by a budget, no claim strictly above that budget
can be justified by the trace spend. -/
theorem no_claim_above_budget_if_spend_bounded
    (cost : Event → Nat)
    (events : List Event)
    (budget claim : Nat)
    (hspend : natTraceSpend cost events ≤ budget)
    (hclaim : budget < claim) :
    claim ≤ natTraceSpend cost events → False := by
  intro hclaimSpend
  omega

/-- A prefix relation stated without relying on a particular List API. -/
def IsPrefix (pref events : List Event) : Prop :=
  ∃ suffix : List Event, pref ++ suffix = events

/-- Every prefix stays inside a concrete Nat budget. -/
def PrefixBudgetSafe
    (cost : Event → Nat)
    (events : List Event)
    (budget : Nat) : Prop :=
  ∀ pref : List Event, IsPrefix pref events → natTraceSpend cost pref ≤ budget

/-- Prefix no-overdraft theorem: if every prefix spend is budget-safe, then no
prefix can justify a claim above budget. This prevents transient overdraft
disasters even when the final trace would net out. -/
theorem no_prefix_claim_above_budget
    (cost : Event → Nat)
    (events pref : List Event)
    (budget claim : Nat)
    (hprefixSafe : PrefixBudgetSafe cost events budget)
    (hprefix : IsPrefix pref events)
    (hclaim : budget < claim) :
    claim ≤ natTraceSpend cost pref → False := by
  intro hclaimSpend
  have hspend : natTraceSpend cost pref ≤ budget := hprefixSafe pref hprefix
  omega

end NoFreeResourceTraceLedger
end Proofs
