import Mathlib.Tactic

/-!
# Economic Security Envelope Laws

Formalizes the deterrence/participation inequalities that the oracle
economic-security envelope (`docs/ZENO_ORACLE_ECONOMIC_SECURITY_V1.md`)
states as document-level laws, and generalizes the slash-deterrence law
with an explicit detection probability so the UPBA solver lane can reuse
it (see `docs/MECHANISM_DESIGN_IMPROVEMENT_ANALYSIS.md`, R5).

Two cheating models are covered:

* **post-hoc model** (`postHocCheatEV`): the cheater's gain is realized and
  the slash lands with certainty afterwards — the envelope doc's model
  (`slash_amount ≥ ceil(expected_cheat_gain · (1 + margin))`).
* **escape model** (`cheatEV`): the gain is realized only when the verifier
  misses (probability `1 − q`), and the slash lands when it catches
  (probability `q`).  At `q = 1` this degenerates to "any positive slash
  deters" (`cheatEV_at_certain_detection`), which is the README's
  solver-payoff assumption — the lemmas make that hidden assumption an
  explicit parameter.

The file proves only the parameter algebra.  It does not prove that bonds
are custodied, that detection actually has probability `q`, or that gains
are measured truthfully.
-/

namespace Proofs
namespace EconomicSecurityEnvelope

/-- Expected value of cheating when the gain is kept only on escape
    (probability `1 − q`) and the slash lands on detection (probability `q`). -/
def cheatEV (gain slash q : ℚ) : ℚ := (1 - q) * gain - q * slash

/-- Post-hoc cheating value: gain realized, slash certain
    (the envelope doc's model). -/
def postHocCheatEV (gain slash : ℚ) : ℚ := gain - slash

/-- **Deterrence with margin (escape model).**  If the expected slash
    exceeds the expected escape gain by the factor `1 + margin`, cheating
    has EV at most `−margin · (1 − q) · gain`.  Pure parameter algebra: no
    sign hypotheses are needed for this form. -/
theorem cheatEV_le_neg_margin (gain slash q margin : ℚ)
    (hdet : (1 + margin) * ((1 - q) * gain) ≤ q * slash) :
    cheatEV gain slash q ≤ -(margin * ((1 - q) * gain)) := by
  unfold cheatEV
  have hexp : (1 + margin) * ((1 - q) * gain)
      = (1 - q) * gain + margin * ((1 - q) * gain) := by ring
  linarith

/-- Deterrence (escape model), non-positivity form: with `q ≤ 1`, `0 ≤ gain`,
    `0 ≤ margin`, the margin-deterred cheat EV is non-positive. -/
theorem cheatEV_nonpos (gain slash q margin : ℚ)
    (hgain : 0 ≤ gain) (hq1 : q ≤ 1) (hmargin : 0 ≤ margin)
    (hdet : (1 + margin) * ((1 - q) * gain) ≤ q * slash) :
    cheatEV gain slash q ≤ 0 := by
  have h := cheatEV_le_neg_margin gain slash q margin hdet
  have hescape : 0 ≤ (1 - q) * gain := mul_nonneg (by linarith) hgain
  have hmarg : 0 ≤ margin * ((1 - q) * gain) := mul_nonneg hmargin hescape
  linarith

/-- At certain detection (`q = 1`) the escape model degenerates: the cheat
    EV is exactly `−slash`, so ANY positive slash deters.  This is the
    README's solver-payoff assumption, recovered as the `q = 1` slice. -/
theorem cheatEV_at_certain_detection (gain slash : ℚ) :
    cheatEV gain slash 1 = -slash := by
  unfold cheatEV
  ring

/-- **Envelope slash-deterrence law (post-hoc model).**
    `slash ≥ (1 + margin) · gain` forces `postHocCheatEV ≤ −margin · gain`:
    the doc-level law `slash_amount ≥ ceil(expected_cheat_gain·(1+margin))`. -/
theorem postHoc_deterrence (gain slash margin : ℚ)
    (hdet : (1 + margin) * gain ≤ slash) :
    postHocCheatEV gain slash ≤ -(margin * gain) := by
  unfold postHocCheatEV
  have hexp : (1 + margin) * gain = gain + margin * gain := by ring
  linarith

/-- **Envelope attack-cost law.**  If the attack cost floor exceeds the
    maximum extractable value by the factor `1 + margin`, the attack nets
    at most `−margin · mev`. -/
theorem attack_cost_law (mev cost margin : ℚ)
    (hcost : (1 + margin) * mev ≤ cost) :
    mev - cost ≤ -(margin * mev) := by
  have hexp : (1 + margin) * mev = mev + margin * mev := by ring
  linarith

/-- **Envelope honest-reward law.**  Reward at least cost plus risk premium
    makes honest participation individually rational with surplus at least
    the premium. -/
theorem honest_reward_law (reward cost premium : ℚ)
    (hreward : cost + premium ≤ reward) :
    premium ≤ reward - cost := by
  linarith

/-- Production-envelope witness (values from
    `ZENO_ORACLE_ECONOMIC_SECURITY_V1.md`): slash `125e9` against cheat gain
    `50e9` at margin `2000` bps satisfies the post-hoc deterrence law, and
    reporter reward `30e6` covers cost `20e6` plus premium `5e6`. -/
theorem witness_oracle_envelope :
    (1 + 2000 / 10000 : ℚ) * 50000000000 ≤ 125000000000 ∧
    (20000000 : ℚ) + 5000000 ≤ 30000000 := by
  norm_num

/-- Escape-model witness: gain 100, detection probability `q = 3/4`, margin
    `1/5`.  The deterrence premise holds with equality at slash 40, and the
    cheat EV is exactly `−5 = −margin · escape-gain`. -/
theorem witness_escape_model :
    cheatEV 100 40 (3 / 4) = -5 ∧
    (1 + 1 / 5 : ℚ) * ((1 - 3 / 4) * 100) ≤ (3 / 4) * 40 := by
  constructor <;> norm_num [cheatEV]

/-! ## Coalition deterrence

Every law above is unilateral: one cheater, one slash.  For a quorum
aggregator the binding constraint is the smallest coalition that controls
the output — for median-of-`(2f+1)`, any `f+1` reporters (`f+1 = 2` at the
production `k = 3`).  The pooled coalition gain is the full extractable
value, while the slash scales only with coalition SIZE, so the deterrence
inequality must be stated against `k_break · slash`, not against the
per-reporter gain.  `witness_unilateral_sizing_insufficient` shows the gap
concretely: a slash sized to deter the unilateral gain leaves the
2-coalition strictly profitable. -/

/-- Post-hoc coalition value: `k` members are each slashed `slash`; the
    coalition's pooled gain is `gain`. -/
def coalitionPostHocEV (gain slash : ℚ) (k : ℕ) : ℚ := gain - (k : ℚ) * slash

/-- **Coalition deterrence law**: if the aggregate slash of a `k`-coalition
    exceeds the pooled gain by the factor `1 + margin`, the coalition nets
    at most `−margin · gain`. -/
theorem coalition_deterrence (gain slash margin : ℚ) (k : ℕ)
    (hdet : (1 + margin) * gain ≤ (k : ℚ) * slash) :
    coalitionPostHocEV gain slash k ≤ -(margin * gain) := by
  unfold coalitionPostHocEV
  have hexp : (1 + margin) * gain = gain + margin * gain := by ring
  linarith

/-- Median-of-3 bond floor: the binding coalition is TWO reporters, so the
    per-reporter slash must satisfy `2 · slash ≥ (1 + margin) · gain` where
    `gain` is the COALITION-extractable value (the full oracle-mediated
    MEV), not the per-reporter share. -/
theorem median3_coalition_bond_floor (gain slash margin : ℚ)
    (hdet : (1 + margin) * gain ≤ 2 * slash) :
    coalitionPostHocEV gain slash 2 ≤ -(margin * gain) := by
  have h2 : ((2 : ℕ) : ℚ) = 2 := by norm_num
  refine coalition_deterrence gain slash margin 2 ?_
  rw [h2]
  exact hdet

/-- Unilateral sizing is insufficient for a quorum: slash 12 deters the
    unilateral gain 10 at margin 20% (`12 ≥ 1.2 · 10`), yet a 2-coalition
    whose pooled extractable gain is 100 nets `100 − 2·12 = +76`.  Bonds
    must scale with coalition-extractable value. -/
theorem witness_unilateral_sizing_insufficient :
    (1 + 2 / 10 : ℚ) * 10 ≤ 12 ∧
    coalitionPostHocEV 100 12 2 = 76 ∧
    (0 : ℚ) < coalitionPostHocEV 100 12 2 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> norm_num [coalitionPostHocEV]

end EconomicSecurityEnvelope
end Proofs
