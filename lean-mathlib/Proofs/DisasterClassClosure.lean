import Mathlib

/-!
# Disaster Class Closure

This file proves the generic proof rule behind the disaster-class closure
packets.

The theorem is intentionally abstract. It does not assert that any concrete
ZenoDEX disaster class is closed. It proves the implication that each concrete
class must instantiate:

* every bad trace in the public-seeded class is covered by at least one local
  disaster axis;
* every covered local axis rejects accepted bad traces;
* therefore the whole class has no accepted bad traces.
-/

namespace Proofs
namespace DisasterClassClosure

universe u v

variable {Trace : Type u} {Axis : Type v}

/-- A disaster class is closed by a local axis family when every bad trace in
the class is covered by at least one axis from that family. -/
def ClassClosure
    (BadTrace : Trace -> Prop)
    (Axes : Axis -> Prop)
    (Covers : Axis -> Trace -> Prop) : Prop :=
  ∀ trace, BadTrace trace -> ∃ axis, Axes axis ∧ Covers axis trace

/-- A covered axis family rejects every trace it covers. -/
def AxisRejectionComplete
    (Axes : Axis -> Prop)
    (Covers : Axis -> Trace -> Prop)
    (AxisRejected : Axis -> Trace -> Prop) : Prop :=
  ∀ axis trace, Axes axis -> Covers axis trace -> AxisRejected axis trace

/-- Rejection is sound when a covered, rejected axis prevents an accepted bad
trace. -/
def AxisRejectionSound
    (Covers : Axis -> Trace -> Prop)
    (AxisRejected : Axis -> Trace -> Prop)
    (AcceptedBadTrace : Trace -> Prop) : Prop :=
  ∀ axis trace, Covers axis trace -> AxisRejected axis trace -> ¬ AcceptedBadTrace trace

/-- A disaster class is immune when no bad trace in the class can be accepted. -/
def ClassImmune
    (BadTrace : Trace -> Prop)
    (AcceptedBadTrace : Trace -> Prop) : Prop :=
  ∀ trace, BadTrace trace -> ¬ AcceptedBadTrace trace

/-- Generic closure theorem: class coverage plus complete, sound axis rejection
implies class-level immunity. -/
theorem class_immune_of_closure_and_axis_rejection
    {BadTrace AcceptedBadTrace : Trace -> Prop}
    {Axes : Axis -> Prop}
    {Covers AxisRejected : Axis -> Trace -> Prop}
    (hClosure : ClassClosure BadTrace Axes Covers)
    (hComplete : AxisRejectionComplete Axes Covers AxisRejected)
    (hSound : AxisRejectionSound Covers AxisRejected AcceptedBadTrace) :
    ClassImmune BadTrace AcceptedBadTrace := by
  intro trace hBad
  rcases hClosure trace hBad with ⟨axis, hAxis, hCovers⟩
  exact hSound axis trace hCovers (hComplete axis trace hAxis hCovers)

/-- Counterexample localization: if a bad trace is accepted despite coverage and
sound rejection, some covering axis was not rejected. This is the fuzzing/search
form of the theorem. -/
theorem accepted_bad_trace_exposes_unrejected_covering_axis
    {BadTrace AcceptedBadTrace : Trace -> Prop}
    {Axes : Axis -> Prop}
    {Covers AxisRejected : Axis -> Trace -> Prop}
    (hClosure : ClassClosure BadTrace Axes Covers)
    (hSound : AxisRejectionSound Covers AxisRejected AcceptedBadTrace)
    {trace : Trace}
    (hBad : BadTrace trace)
    (hAccepted : AcceptedBadTrace trace) :
    ∃ axis, Axes axis ∧ Covers axis trace ∧ ¬ AxisRejected axis trace := by
  rcases hClosure trace hBad with ⟨axis, hAxis, hCovers⟩
  refine ⟨axis, hAxis, hCovers, ?_⟩
  intro hRejected
  exact hSound axis trace hCovers hRejected hAccepted

end DisasterClassClosure
end Proofs
