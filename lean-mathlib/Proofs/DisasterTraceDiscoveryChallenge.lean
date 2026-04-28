import Proofs.AbstractInterpretationDisasterSafety
import Proofs.FiniteTraceBarriers
import Mathlib

/-!
# Disaster Trace Discovery Challenge

Open-ended theorem-discovery packet.

ZenoDEX uses bounded what-if witness search to show named disaster states are
unreachable in specific harnesses.  The existing Lean proof library has forward
simulation and barrier theorems.  This file provides a compact theorem layer
for lifting bounded witness certificates into replayable unreachability claims.

## Theorem surface

1. **Seed theorems** (5): harness trace lifting, barrier-based exclusion,
   forward-simulation exclusion, async product composition, and
   counterexample refutation.

2. **Discovery layer**: `DisasterUnreachCert` structure, product-axis composition
   laws, multi-axis exclusion, certificate weakening/strengthening, and the
   master harness-to-concrete lifting theorem.
-/

namespace Proofs.DisasterTraceDiscoveryChallenge

open Proofs.FiniteTraceBarriers
open Proofs.FiniteTraceBarriers.TransitionSystem
open Proofs.AbstractInterpretationDisasterSafety.TransitionSystem

variable {σ τ α β : Type _}

/-- A named disaster axis is excluded when every state satisfying `safe`
rejects the corresponding disaster predicate. -/
def AxisExcluded (safe disaster : σ → Prop) : Prop :=
  ∀ {s : σ}, safe s → ¬ disaster s

/-- A finite witness harness is sound for an unbounded concrete system if every
harness step is a concrete step. -/
def HarnessSound (H C : TransitionSystem σ) : Prop :=
  StepIncluded H C

-- ═══════════════════════════════════════════════════════════════════════════
-- SEED THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════

/-- If a harness is a subsystem of the concrete system, then every harness trace
ending in a disaster is also a concrete reachable disaster. -/
theorem concrete_disaster_of_harness_trace
    {H C : TransitionSystem σ}
    (hSound : HarnessSound H C)
    {n : Nat} {s t : σ}
    (hTrace : H.TraceN n s t)
    {disaster : σ → Prop}
    (hDisaster : disaster t) :
    C.Reachable s t ∧ disaster t :=
  ⟨reachable_of_stepIncluded hSound (reachable_of_traceN hTrace), hDisaster⟩

/-- Barrier certificates exclude named disasters over finite harness traces. -/
theorem no_disaster_of_harness_barrier_trace
    [Preorder α]
    {H : TransitionSystem σ}
    {safe disaster : σ → Prop}
    {score : σ → α} {cutoff : α}
    (hStep : H.BarrierPreserved score cutoff)
    (hSound : BarrierSound safe score cutoff)
    (hExcluded : AxisExcluded safe disaster)
    {n : Nat} {s t : σ}
    (hTrace : H.TraceN n s t)
    (hInit : cutoff ≤ score s) :
    ¬ disaster t :=
  hExcluded (hSound (barrier_of_traceN hStep hTrace hInit))

/-- Forward simulation plus abstract disaster exclusion lifts concrete trace
search into semantic unreachability. -/
theorem no_disaster_of_trace_forward_simulation
    {C : TransitionSystem σ} {A : TransitionSystem β}
    {R : σ → β → Prop} {Inv : β → Prop} {disaster : σ → Prop}
    (hSim : ForwardSimulation C A R)
    (hInv : AbstractInvariant A Inv)
    (hExcluded : ExcludesDisaster R Inv disaster)
    {n : Nat} {c0 c : σ} {a0 : β}
    (hInitialRep : R c0 a0)
    (hInitialInv : Inv a0)
    (hTrace : C.TraceN n c0 c) :
    ¬ disaster c :=
  no_disaster_of_concrete_traceN_simulation
    hSim hInv hExcluded hInitialRep hInitialInv hTrace

/-- Product disasters are unreachable when each component barrier excludes its
own disaster under asynchronous composition. -/
theorem no_pair_disaster_of_async_barriers
    [Preorder α] [Preorder β]
    {S : TransitionSystem σ} {T : TransitionSystem τ}
    {safeS disasterS : σ → Prop}
    {safeT disasterT : τ → Prop}
    {scoreS : σ → α} {cutoffS : α}
    {scoreT : τ → β} {cutoffT : β}
    (hS : S.BarrierPreserved scoreS cutoffS)
    (hT : T.BarrierPreserved scoreT cutoffT)
    (hSoundS : BarrierSound safeS scoreS cutoffS)
    (hSoundT : BarrierSound safeT scoreT cutoffT)
    (hExclS : AxisExcluded safeS disasterS)
    (hExclT : AxisExcluded safeT disasterT)
    {p q : σ × τ}
    (hReach : Reachable (AsyncProduct S T) p q)
    (hInit : cutoffS ≤ scoreS p.1 ∧ cutoffT ≤ scoreT p.2) :
    ¬ (disasterS q.1 ∨ disasterT q.2) := by
  have hPair := pair_safe_of_async_reachable hS hT hSoundS hSoundT hReach hInit
  intro h
  rcases h with hL | hR
  · exact hExclS hPair.1 hL
  · exact hExclT hPair.2 hR

/-- Counterexample interpretation: if a concrete trace reaches a disaster, then
no barrier certificate with the stated initial score and exclusion property can
exist for that trace. -/
theorem disaster_trace_refutes_barrier_certificate
    [Preorder α]
    {T : TransitionSystem σ}
    {safe disaster : σ → Prop}
    {score : σ → α} {cutoff : α}
    {n : Nat} {s t : σ}
    (hTrace : T.TraceN n s t)
    (hInit : cutoff ≤ score s)
    (hDisaster : disaster t) :
    ¬ (T.BarrierPreserved score cutoff ∧
        BarrierSound safe score cutoff ∧
        AxisExcluded safe disaster) := by
  intro ⟨hStep, hSound, hExcluded⟩
  exact no_disaster_of_harness_barrier_trace hStep hSound hExcluded hTrace hInit hDisaster

-- ═══════════════════════════════════════════════════════════════════════════
-- DISCOVERY LAYER
-- ═══════════════════════════════════════════════════════════════════════════

/-! ### Harness composition -/

/-- Harness soundness composes transitively: if H₁ ⊆ H₂ ⊆ C then H₁ ⊆ C. -/
theorem harnessSound_trans {H₁ H₂ C : TransitionSystem σ}
    (h₁₂ : HarnessSound H₁ H₂) (h₂C : HarnessSound H₂ C) :
    HarnessSound H₁ C :=
  fun hStep => h₂C (h₁₂ hStep)

/-- A barrier certificate on a concrete system transfers to any sound harness. -/
theorem harness_barrier_of_concrete [Preorder α]
    {H C : TransitionSystem σ} {score : σ → α} {cutoff : α}
    (hSound : HarnessSound H C)
    (hBarrier : C.BarrierPreserved score cutoff) :
    H.BarrierPreserved score cutoff :=
  barrierPreserved_of_stepIncluded hSound hBarrier

/-! ### Disaster Unreachability Certificate -/

/-- A disaster unreachability certificate bundles a barrier certificate with an
axis exclusion proof. This is the core object that a bounded witness search
should produce as its output receipt. -/
structure DisasterUnreachCert (T : TransitionSystem σ) (disaster : σ → Prop)
    (α : Type*) [Preorder α] where
  /-- The safety predicate implied by the barrier. -/
  safe : σ → Prop
  /-- The barrier certificate witnessing safety. -/
  barrier : BarrierCertificate T safe α
  /-- Proof that safety excludes the named disaster. -/
  excluded : AxisExcluded safe disaster

/-- The core unreachability theorem for a `DisasterUnreachCert`: if the initial
state is above cutoff, no reachable state is a disaster. -/
theorem DisasterUnreachCert.no_disaster_reachable
    [Preorder α] {T : TransitionSystem σ} {disaster : σ → Prop}
    (cert : DisasterUnreachCert T disaster α)
    {s t : σ} (hReach : T.Reachable s t)
    (hInit : cert.barrier.cutoff ≤ cert.barrier.score s) :
    ¬ disaster t :=
  cert.excluded (cert.barrier.safe_of_reachable hReach hInit)

/-- Trace-bounded version. -/
theorem DisasterUnreachCert.no_disaster_traceN
    [Preorder α] {T : TransitionSystem σ} {disaster : σ → Prop}
    (cert : DisasterUnreachCert T disaster α)
    {n : Nat} {s t : σ} (hTrace : T.TraceN n s t)
    (hInit : cert.barrier.cutoff ≤ cert.barrier.score s) :
    ¬ disaster t :=
  cert.no_disaster_reachable (reachable_of_traceN hTrace) hInit

/-- Lifting a concrete certificate to a harness: if the concrete system has a
disaster unreachability certificate, then every sound harness inherits one. -/
noncomputable def DisasterUnreachCert.of_concrete
    [Preorder α] {H C : TransitionSystem σ} {disaster : σ → Prop}
    (hSound : HarnessSound H C)
    (cert : DisasterUnreachCert C disaster α) :
    DisasterUnreachCert H disaster α where
  safe := cert.safe
  barrier := {
    score := cert.barrier.score
    cutoff := cert.barrier.cutoff
    step_ok := harness_barrier_of_concrete hSound cert.barrier.step_ok
    sound := cert.barrier.sound
  }
  excluded := cert.excluded

/-! ### Product-axis composition laws -/

/-- Given independent barrier certificates for two subsystems, their synchronous
product excludes the disjunction of both disasters. -/
theorem no_pair_disaster_of_sync_barriers
    [Preorder α] [Preorder β]
    {S : TransitionSystem σ} {T : TransitionSystem τ}
    {safeS disasterS : σ → Prop}
    {safeT disasterT : τ → Prop}
    {scoreS : σ → α} {cutoffS : α}
    {scoreT : τ → β} {cutoffT : β}
    (hS : S.BarrierPreserved scoreS cutoffS)
    (hT : T.BarrierPreserved scoreT cutoffT)
    (hSoundS : BarrierSound safeS scoreS cutoffS)
    (hSoundT : BarrierSound safeT scoreT cutoffT)
    (hExclS : AxisExcluded safeS disasterS)
    (hExclT : AxisExcluded safeT disasterT)
    {p q : σ × τ}
    (hReach : Reachable (SyncProduct S T) p q)
    (hInit : cutoffS ≤ scoreS p.1 ∧ cutoffT ≤ scoreT p.2) :
    ¬ (disasterS q.1 ∨ disasterT q.2) := by
  have hPair := pair_barrier_of_sync_reachable hS hT hReach hInit
  intro h
  rcases h with hL | hR
  · exact hExclS (hSoundS hPair.1) hL
  · exact hExclT (hSoundT hPair.2) hR

/-- Async product with finite traces: neither disaster axis is reachable. -/
theorem no_pair_disaster_of_async_barriers_traceN
    [Preorder α] [Preorder β]
    {S : TransitionSystem σ} {T : TransitionSystem τ}
    {safeS disasterS : σ → Prop}
    {safeT disasterT : τ → Prop}
    {scoreS : σ → α} {cutoffS : α}
    {scoreT : τ → β} {cutoffT : β}
    (hS : S.BarrierPreserved scoreS cutoffS)
    (hT : T.BarrierPreserved scoreT cutoffT)
    (hSoundS : BarrierSound safeS scoreS cutoffS)
    (hSoundT : BarrierSound safeT scoreT cutoffT)
    (hExclS : AxisExcluded safeS disasterS)
    (hExclT : AxisExcluded safeT disasterT)
    {n : Nat} {p q : σ × τ}
    (hTrace : TraceN (AsyncProduct S T) n p q)
    (hInit : cutoffS ≤ scoreS p.1 ∧ cutoffT ≤ scoreT p.2) :
    ¬ (disasterS q.1 ∨ disasterT q.2) :=
  no_pair_disaster_of_async_barriers hS hT hSoundS hSoundT hExclS hExclT
    (reachable_of_traceN hTrace) hInit

/-- Multi-axis exclusion: a single safety predicate excludes a list of
disaster axes simultaneously. -/
theorem no_any_disaster_of_all_excluded
    {safe : σ → Prop}
    {disasters : List (σ → Prop)}
    (hExcls : ∀ d ∈ disasters, AxisExcluded safe d)
    {s : σ} (hSafe : safe s) :
    ∀ d ∈ disasters, ¬ d s :=
  fun d hd => hExcls d hd hSafe

/-- Multi-axis barrier exclusion over reachable states. -/
theorem no_any_disaster_of_barrier_reachable
    [Preorder α]
    {T : TransitionSystem σ}
    {safe : σ → Prop}
    {score : σ → α} {cutoff : α}
    {disasters : List (σ → Prop)}
    (hStep : T.BarrierPreserved score cutoff)
    (hSound : BarrierSound safe score cutoff)
    (hExcls : ∀ d ∈ disasters, AxisExcluded safe d)
    {s t : σ} (hReach : T.Reachable s t)
    (hInit : cutoff ≤ score s) :
    ∀ d ∈ disasters, ¬ d t := by
  intro d hd
  exact (hExcls d hd) (hSound (barrier_of_reachable hStep hReach hInit))

/-! ### Certificate refutation -/

/-- Stronger refutation: if a reachable disaster exists (not just a finite
trace), then the full certificate triple cannot hold. -/
theorem disaster_reachable_refutes_barrier_certificate
    [Preorder α]
    {T : TransitionSystem σ}
    {safe disaster : σ → Prop}
    {score : σ → α} {cutoff : α}
    {s t : σ}
    (hReach : T.Reachable s t)
    (hInit : cutoff ≤ score s)
    (hDisaster : disaster t) :
    ¬ (T.BarrierPreserved score cutoff ∧
        BarrierSound safe score cutoff ∧
        AxisExcluded safe disaster) := by
  intro ⟨hStep, hSound, hExcluded⟩
  exact hExcluded (hSound (barrier_of_reachable hStep hReach hInit)) hDisaster

/-- A witnessed disaster trace refutes a `DisasterUnreachCert`. -/
theorem disaster_trace_refutes_cert
    [Preorder α]
    {T : TransitionSystem σ} {disaster : σ → Prop}
    (cert : DisasterUnreachCert T disaster α)
    {n : Nat} {s t : σ}
    (hTrace : T.TraceN n s t)
    (hInit : cert.barrier.cutoff ≤ cert.barrier.score s)
    (hDisaster : disaster t) :
    False :=
  cert.no_disaster_traceN hTrace hInit hDisaster

/-! ### Barrier weakening and strengthening -/

/-- If `safe₁ → safe₂` and safe₂ excludes a disaster, then safe₁ also excludes
it. Useful when a stronger invariant implies a weaker known-safe predicate. -/
theorem axisExcluded_of_stronger_safe
    {safe₁ safe₂ disaster : σ → Prop}
    (hImpl : ∀ s, safe₁ s → safe₂ s)
    (hExcl : AxisExcluded safe₂ disaster) :
    AxisExcluded safe₁ disaster :=
  fun hs => hExcl (hImpl _ hs)

/-- If `disaster₂ → disaster₁` and safe excludes disaster₁, then safe
excludes disaster₂. Useful for weakening a disaster predicate. -/
theorem axisExcluded_of_weaker_disaster
    {safe disaster₁ disaster₂ : σ → Prop}
    (hImpl : ∀ s, disaster₂ s → disaster₁ s)
    (hExcl : AxisExcluded safe disaster₁) :
    AxisExcluded safe disaster₂ :=
  fun hs hd => hExcl hs (hImpl _ hd)

/-! ### Harness-to-concrete master theorems -/

/-- **Caveat theorem**: harness soundness alone does NOT guarantee concrete
barrier preservation. The harness barrier only covers harness traces. This
theorem states the weaker, harness-only guarantee. -/
theorem harness_only_no_disaster
    [Preorder α]
    {H : TransitionSystem σ}
    {safe disaster : σ → Prop}
    {score : σ → α} {cutoff : α}
    (hStep : H.BarrierPreserved score cutoff)
    (hSound : BarrierSound safe score cutoff)
    (hExcluded : AxisExcluded safe disaster)
    {s t : σ} (hReach : H.Reachable s t)
    (hInit : cutoff ≤ score s) :
    ¬ disaster t :=
  hExcluded (hSound (barrier_of_reachable hStep hReach hInit))

/-- **Master theorem**: given a barrier certificate that excludes a named
disaster on the full concrete system, no concrete trace from an initial state
above cutoff can reach the disaster. A sound harness is used to discover the
certificate, but the barrier must hold on the concrete system for full
coverage. -/
theorem concrete_no_disaster_of_barrier
    [Preorder α]
    {C : TransitionSystem σ}
    {safe disaster : σ → Prop}
    {score : σ → α} {cutoff : α}
    (hConcreteBarrier : C.BarrierPreserved score cutoff)
    (hSound : BarrierSound safe score cutoff)
    (hExcluded : AxisExcluded safe disaster)
    {s t : σ} (hReach : C.Reachable s t) (hInit : cutoff ≤ score s) :
    ¬ disaster t :=
  hExcluded (hSound (barrier_of_reachable hConcreteBarrier hReach hInit))

/-! ### Forward simulation + barrier composition -/

/-- Combining forward simulation with barrier certificates: if the abstract
system has a barrier certificate that excludes an abstract disaster, and the
concretization relation preserves the disaster meaning, then the concrete
system is disaster-free from represented initial states. -/
theorem no_disaster_of_simulation_barrier
    [Preorder α]
    {C : TransitionSystem σ} {A : TransitionSystem β}
    {R : σ → β → Prop} {disaster : σ → Prop}
    {safe_abs : β → Prop}
    {score : β → α} {cutoff : α}
    (hSim : ForwardSimulation C A R)
    (hBarrier : A.BarrierPreserved score cutoff)
    (hSound : BarrierSound safe_abs score cutoff)
    (hExcl : ∀ {c : σ} {a : β}, R c a → safe_abs a → ¬ disaster c)
    {c0 c : σ} {a0 : β}
    (hInitRep : R c0 a0)
    (hInitScore : cutoff ≤ score a0)
    (hReach : C.Reachable c0 c) :
    ¬ disaster c := by
  rcases reachable_lift_exists hSim hInitRep hReach with ⟨a, hAbsReach, hRep⟩
  exact hExcl hRep (hSound (barrier_of_reachable hBarrier hAbsReach hInitScore))

end Proofs.DisasterTraceDiscoveryChallenge
