/-
Trajectory composition bound for the ZenoDEX autonomous-governance drift budget.

THE CLAIM THIS FORMALIZES: the trajectory tier's drift budget gives a GLOBAL
displacement bound across windows. ESSO (gov_epoch_machine_v1.yaml) proves the
per-window invariant `drift_used ≤ B` inductively; Kani proves the Rust gate's
accept ⇒ `|Δ| ≤ B − used` over the full u16 domain; the Python walk test shows
the 3-steps-then-halt behavior empirically. What none of them STATE is the
composition: over m completed windows, the parameter ends at most m·B from
where it started — however the per-revision deltas are chosen, in either
direction, oscillating or not. That composition is this file.

Model: a window is the list of signed deltas applied within it; a trajectory is
the list of windows. The gate's per-window guarantee is the hypothesis
`(w.map abs).sum ≤ B` (exactly what `drift_used ≤ B` means at window close:
drift_used IS the sum of |δ| admitted in the window). The conclusion bounds the
END-TO-END displacement — not assumed anywhere in the hypotheses, derived via
|Σδ| ≤ Σ|δ| per window and summation across windows.

Honest scope: ℤ model of the committed parameter sequence (the Python/Rust
gates operate on bounded ints; ℤ is the faithful abstraction since all gate
arithmetic is exact — the u16 domain bound is enforced separately by the band
gates). The per-window hypothesis is the gate's guarantee, not re-proved here;
binding it to committed state is the WS5 clause.
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

namespace GovTrajectoryBound

/-- A parameter trajectory: start value plus the flattened deltas of all windows. -/
def finalValue (x0 : ℤ) (windows : List (List ℤ)) : ℤ :=
  x0 + (windows.map List.sum).sum

/-- Per-window net movement is bounded by the window's drift charge:
`|Σ δ| ≤ Σ |δ|` — oscillation consumes budget without producing displacement,
which is exactly why the budget counts magnitude, not direction. -/
theorem window_net_le_charge (w : List ℤ) : |w.sum| ≤ (w.map abs).sum := by
  induction w with
  | nil => simp
  | cons d rest ih =>
      have htri : |d + rest.sum| ≤ |d| + |rest.sum| := abs_add_le d rest.sum
      have : |d| + |rest.sum| ≤ |d| + (rest.map abs).sum :=
        add_le_add le_rfl ih
      calc |(d :: rest).sum| = |d + rest.sum| := by simp
        _ ≤ |d| + |rest.sum| := htri
        _ ≤ |d| + (rest.map abs).sum := this
        _ = ((d :: rest).map abs).sum := by simp

/-- THE TRAJECTORY BOUND: if every window's drift charge is within the budget B
(the gate invariant ESSO proves per window), the end-to-end displacement after
m windows is at most m·B — a poisoned proposer's reachable set grows linearly
in WINDOWS, not in revisions. Derived, not assumed: the hypotheses speak only
about per-window |δ| sums; the conclusion bounds the composed walk. -/
theorem trajectory_bound (x0 : ℤ) (windows : List (List ℤ)) (B : ℤ)
    (hB : ∀ w ∈ windows, (w.map abs).sum ≤ B) :
    |finalValue x0 windows - x0| ≤ windows.length * B := by
  induction windows with
  | nil => simp [finalValue]
  | cons w rest ih =>
      have hw : (w.map abs).sum ≤ B := hB w List.mem_cons_self
      have hrest : ∀ v ∈ rest, (v.map abs).sum ≤ B :=
        fun v hv => hB v (List.mem_cons_of_mem w hv)
      have ihr := ih hrest
      have hnet : |w.sum| ≤ B := le_trans (window_net_le_charge w) hw
      have hsplit :
          finalValue x0 (w :: rest) - x0
            = w.sum + (finalValue x0 rest - x0) := by
        simp only [finalValue, List.map_cons, List.sum_cons]; ring
      calc |finalValue x0 (w :: rest) - x0|
          = |w.sum + (finalValue x0 rest - x0)| := by rw [hsplit]
        _ ≤ |w.sum| + |finalValue x0 rest - x0| := abs_add_le _ _
        _ ≤ B + rest.length * B := add_le_add hnet ihr
        _ = (w :: rest).length * B := by
              simp only [List.length_cons]; push_cast; ring

/-- Reference-constant instantiation: with the fee surface's budget (150 = 3
steps of 50) a full year of 720-epoch windows (12 windows ≈ 8640 epochs) moves
the fee at most 1800 bps from its anchor — vs 9000 bps (0 → 90× cap-crossing
attempts) if only the per-step bound existed at one revision per cooldown. -/
theorem fee_surface_yearly_bound (x0 : ℤ) (windows : List (List ℤ))
    (hlen : windows.length = 12)
    (hB : ∀ w ∈ windows, (w.map abs).sum ≤ 150) :
    |finalValue x0 windows - x0| ≤ 1800 := by
  have := trajectory_bound x0 windows 150 hB
  rw [hlen] at this
  norm_num at this
  exact this

/-- Non-vacuity: the hypotheses are satisfiable by a real walk — three full
+50 steps in each of two windows is admitted by the budget and lands exactly
at the bound's prediction territory (|Δ| = 300 ≤ 2·150). -/
theorem witness_two_window_walk :
    let windows : List (List ℤ) := [[50, 50, 50], [50, 50, 50]]
    (∀ w ∈ windows, (w.map abs).sum ≤ 150)
      ∧ |finalValue 500 windows - 500| = 300
      ∧ (300 : ℤ) ≤ 2 * 150 := by
  refine ⟨?_, by native_decide, by norm_num⟩
  intro w hw
  fin_cases hw <;> native_decide

/-- Achievement: the bound m·B is ATTAINED at this concrete instance (m = 3,
B = 150) by the always-max same-direction walk. The same construction scales
to any m and B ≥ 0, so the m·B form is not sharpenable in general — but what
is PROVED here is exactly this instance's equality, nothing stronger. -/
theorem witness_bound_tight :
    let windows : List (List ℤ) := [[150], [150], [150]]
    (∀ w ∈ windows, (w.map abs).sum ≤ 150)
      ∧ |finalValue 0 windows - 0| = 3 * 150 := by
  refine ⟨?_, by native_decide⟩
  intro w hw
  fin_cases hw <;> native_decide

/-- Oscillation consumes budget without displacement (the anti-thrash rationale
made precise): a +50/−50/+50 window nets 50 of movement but charges 150 —
magnitude-counting is what makes `drift_used` an honest movement meter. -/
theorem witness_oscillation_charges :
    let w : List ℤ := [50, -50, 50]
    (w.map abs).sum = 150 ∧ |w.sum| = 50 := by
  constructor <;> native_decide

end GovTrajectoryBound
