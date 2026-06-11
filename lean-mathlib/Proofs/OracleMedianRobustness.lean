import Mathlib.Tactic
import Proofs.PerpEpochSafety

/-!
# Oracle Median Robustness

The ZenoOracle aggregates reporter values by median.  Every solvency
theorem downstream (perp epoch safety, zUSD MCR) conditions on the
aggregated price, so this file pins the exact robustness algebra of the
aggregation step and its composition with the runtime clamp:

* **Breakdown point** (`median3_robust_corrupt_*`): with `k = 3` reporters,
  ONE arbitrarily corrupt reporter cannot move the median outside the
  interval spanned by the two honest reports.  The median needs no
  honesty assumption on the corrupt value — only on the other two.
* **Breakdown witness** (`witness_two_corrupt_unbounded`): TWO corrupt
  reporters move the median anywhere.  The 2-coalition is therefore the
  binding adversary at `k = 3`, and its deterrence is exactly
  `EconomicSecurityEnvelope.median3_coalition_bond_floor`:
  `2·slash ≥ (1+margin)·coalition-extractable MEV`.
* **Defense-in-depth corollaries** (`corrupt_report_damage_bounded`,
  `corrupt_report_cannot_insolve_in_one_epoch`): even a FULLY corrupted
  aggregate (both honest reporters bribed, or quorum logic broken) is
  bounded by the runtime clamp for one epoch — the clamp lemmas of
  `PerpEpochSafety` hold for arbitrary raw inputs, so a maintenance-safe
  account survives any single corrupted update.  Corruption kills via
  PERSISTENCE (repeated epochs inside the clamp band), which is governed
  by the staleness window, dispute lane, and coalition bonds — the
  mechanism surface, not the arithmetic surface.

The file proves aggregation algebra only.  It does not prove reporter
honesty, network delivery, or that the runtime wires the median into the
clamp (that wiring is the runtime-binding obligation).
-/

namespace Proofs
namespace OracleMedianRobustness

/-- Median of three via lattice operations:
    `median3 a b c = max (min a b) (min (max a b) c)`. -/
def median3 (a b c : ℚ) : ℚ := max (min a b) (min (max a b) c)

/-- Robustness, corrupt third input: if `a` and `b` lie in `[lo, hi]`, the
    median lies in `[lo, hi]` for EVERY value of `c`. -/
theorem median3_robust_corrupt_third (lo hi a b c : ℚ)
    (ha1 : lo ≤ a) (ha2 : a ≤ hi) (hb1 : lo ≤ b) (hb2 : b ≤ hi) :
    lo ≤ median3 a b c ∧ median3 a b c ≤ hi := by
  unfold median3
  constructor
  · exact le_trans (le_min ha1 hb1) (le_max_left _ _)
  · apply max_le
    · exact le_trans (min_le_left a b) ha2
    · exact le_trans (min_le_left (max a b) c) (max_le ha2 hb2)

/-- Robustness, corrupt second input: if `a` and `c` lie in `[lo, hi]`, the
    median lies in `[lo, hi]` for EVERY value of `b`. -/
theorem median3_robust_corrupt_second (lo hi a b c : ℚ)
    (ha1 : lo ≤ a) (ha2 : a ≤ hi) (hc1 : lo ≤ c) (hc2 : c ≤ hi) :
    lo ≤ median3 a b c ∧ median3 a b c ≤ hi := by
  unfold median3
  constructor
  · refine le_trans (le_min ?_ hc1) (le_max_right _ _)
    exact le_trans ha1 (le_max_left a b)
  · apply max_le
    · exact le_trans (min_le_left a b) ha2
    · exact le_trans (min_le_right (max a b) c) hc2

/-- Robustness, corrupt first input: if `b` and `c` lie in `[lo, hi]`, the
    median lies in `[lo, hi]` for EVERY value of `a`. -/
theorem median3_robust_corrupt_first (lo hi a b c : ℚ)
    (hb1 : lo ≤ b) (hb2 : b ≤ hi) (hc1 : lo ≤ c) (hc2 : c ≤ hi) :
    lo ≤ median3 a b c ∧ median3 a b c ≤ hi := by
  unfold median3
  constructor
  · refine le_trans (le_min ?_ hc1) (le_max_right _ _)
    exact le_trans hb1 (le_max_right a b)
  · apply max_le
    · exact le_trans (min_le_right a b) hb2
    · exact le_trans (min_le_right (max a b) c) hc2

/-- Manipulation-shift form: with one corrupt reporter, the median stays
    inside the interval spanned by the two honest reports — the maximum
    induced shift relative to either honest value is the honest
    disagreement `|h₁ − h₂|`, independent of the corrupt magnitude. -/
theorem median3_shift_bounded_by_honest_disagreement (h₁ h₂ c : ℚ) :
    min h₁ h₂ ≤ median3 h₁ h₂ c ∧ median3 h₁ h₂ c ≤ max h₁ h₂ := by
  exact median3_robust_corrupt_third (min h₁ h₂) (max h₁ h₂) h₁ h₂ c
    (min_le_left _ _) (le_max_left _ _) (min_le_right _ _) (le_max_right _ _)

/-- Breakdown witness: TWO corrupt reporters move the median-of-3 to an
    arbitrary value (here `10⁶` against an honest `0`).  At `k = 3` the
    binding adversary is the 2-coalition; its economic closure is
    `EconomicSecurityEnvelope.median3_coalition_bond_floor`. -/
theorem witness_two_corrupt_unbounded :
    median3 0 1000000 1000000 = 1000000 := by
  norm_num [median3]

/-! ## Defense-in-depth: clamp bounds one corrupted epoch -/

/-- Even a fully corrupted aggregate `v` (arbitrary) produces at most an
    `m`-bps applied move for the epoch: the clamp lemma holds for every
    raw input.  Restatement of `PerpEpochSafety.abs_clamp_move_sub_le`
    with the oracle-corruption reading. -/
theorem corrupt_report_damage_bounded (P v m : ℚ) (hP : 0 ≤ P) (hm : 0 ≤ m) :
    |PerpEpochSafety.clamp_move P v m - P| ≤ m * P / 10000 :=
  PerpEpochSafety.abs_clamp_move_sub_le P v m hP hm

/-- A maintenance-safe account survives ANY single corrupted oracle update:
    composition of the clamp bound with epoch solvency.  Corruption can
    only do damage through persistence across epochs, which is the
    staleness-window / dispute / coalition-bond surface. -/
theorem corrupt_report_cannot_insolve_in_one_epoch
    (pos P v C m maint : ℚ)
    (hP : 0 ≤ P) (hm : 0 ≤ m) (hmaint : m ≤ maint)
    (hC : |pos| * P * maint / 10000 ≤ C) :
    0 ≤ C + pos * (PerpEpochSafety.clamp_move P v m - P) :=
  PerpEpochSafety.collateral_nonneg_after_clamped_move pos P v C m maint hP hm hmaint hC

/-- Non-vacuity: honest pair (100, 104), corrupt third report 10⁶: the
    median is 104, inside the honest interval; with honest pair (100, 104)
    and corrupt LOW report 0 the median is 100. -/
theorem witness_median3_robust :
    median3 100 104 1000000 = 104 ∧ median3 100 104 0 = 100 := by
  constructor <;> norm_num [median3]

end OracleMedianRobustness
end Proofs
