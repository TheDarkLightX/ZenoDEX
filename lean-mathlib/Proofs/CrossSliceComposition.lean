import Proofs.ArbitrageCertificate
import Mathlib.Tactic

/-!
# Cross-Slice Composition: Rounding Tolerance of Arbitrage Certificates

Connects arbitrage certificates to bounded edge-perturbation reasoning
via a margin-absorption lemma.

## Key result

If a potential certificate has margin ≥ ε on all edges (reduced cost ≥ ε),
and actual weights differ from theoretical by at most ε (e.g., due to rounding),
then the certificate still certifies no-arbitrage on the actual graph.

This file is intentionally limited to **edgewise** perturbation reasoning.
It does not derive an edgewise budget from a route-level total-gap theorem;
that bridge must be provided separately by the caller.

## Composition chain

1. `ArbitrageCertificate.certificate_soundness`: exact weights → no-arb cycles
2. `margin_absorbs_perturbation` (this file): margin ε absorbs error ≤ ε
3. a separate bridge that turns a route-level gap bound into an edgewise budget
4. **Composition once that bridge exists**: margin ≥ ε → no-arb cycles under ε-bounded edge perturbations
-/

namespace Proofs
namespace CrossSliceComposition

open ArbitrageCertificate (pathWeight certificate_soundness)

/-! ## Core margin absorption -/

/-- **MARGIN ABSORPTION**: A certificate with margin ε absorbs perturbations ≤ ε.

    If w(u,v) + π(u) - π(v) ≥ ε for all edges (certificate with margin),
    and w_actual(u,v) ≥ w(u,v) - ε (perturbation bounded by ε),
    then w_actual(u,v) + π(u) - π(v) ≥ 0 (certificate still valid).

    This is the key lemma connecting arbitrage certificates to rounding tolerance.
    The proof follows from the triangle of inequalities:
      w_actual ≥ w - ε and w + π_u - π_v ≥ ε  →  w_actual + π_u - π_v ≥ 0. -/
theorem margin_absorbs_perturbation
    (w w_actual : ℕ → ℕ → ℤ) (π : ℕ → ℤ) (ε : ℤ) (_hε : 0 ≤ ε)
    (h_margin : ∀ u v, w u v + π u - π v ≥ ε)
    (h_perturb : ∀ u v, w_actual u v ≥ w u v - ε) :
    ∀ u v, w_actual u v + π u - π v ≥ 0 := by
  intro u v
  have h1 := h_margin u v
  have h2 := h_perturb u v
  linarith

/-- **CROSS-SLICE COMPOSITION**: Certificate with margin absorbs perturbation,
    and the resulting certificate certifies no-arbitrage on the actual graph.

    This composes `margin_absorbs_perturbation` with
    `ArbitrageCertificate.certificate_soundness`. -/
theorem perturbed_no_arbitrage
    (w w_actual : ℕ → ℕ → ℤ) (π : ℕ → ℤ) (ε : ℤ) (hε : 0 ≤ ε)
    (h_margin : ∀ u v, w u v + π u - π v ≥ ε)
    (h_perturb : ∀ u v, w_actual u v ≥ w u v - ε)
    (s : ℕ) (mid : List ℕ) :
    pathWeight w_actual (s :: (mid ++ [s])) ≥ 0 :=
  certificate_soundness w_actual π
    (margin_absorbs_perturbation w w_actual π ε hε h_margin h_perturb) s mid

/-! ## Rounding-specific instantiations -/

/-- If a caller provides a **uniform edgewise** perturbation budget
    `2*k - 1`, then certificate margin `2*k - 1` absorbs that budget.

    This theorem does not derive the edgewise budget from the actual route
    length `mid.length + 1`; it only packages the margin-absorption step once
    such a budget is already available. -/
theorem k_hop_conservative_margin
    (w w_actual : ℕ → ℕ → ℤ) (π : ℕ → ℤ) (k : ℕ) (hk : 0 < k)
    (h_margin : ∀ u v, w u v + π u - π v ≥ 2 * ↑k - 1)
    (h_round : ∀ u v, w_actual u v ≥ w u v - (2 * ↑k - 1))
    (s : ℕ) (mid : List ℕ) :
    pathWeight w_actual (s :: (mid ++ [s])) ≥ 0 :=
  perturbed_no_arbitrage w w_actual π (2 * ↑k - 1) (by omega) h_margin h_round s mid

/-- If a caller provides a **uniform edgewise** perturbation budget `k`,
    then certificate margin `k` absorbs that budget.

    As above, this theorem is an abstract edgewise packaging lemma, not a
    derivation from a route-level rounding theorem. -/
theorem k_hop_lipschitz_margin
    (w w_actual : ℕ → ℕ → ℤ) (π : ℕ → ℤ) (k : ℕ) (hk : 0 < k)
    (h_margin : ∀ u v, w u v + π u - π v ≥ ↑k)
    (h_round : ∀ u v, w_actual u v ≥ w u v - ↑k)
    (s : ℕ) (mid : List ℕ) :
    pathWeight w_actual (s :: (mid ++ [s])) ≥ 0 :=
  perturbed_no_arbitrage w w_actual π ↑k (by omega) h_margin h_round s mid

/-! ## Margin monotonicity -/

/-- If margin is sufficient for k hops, it's sufficient for any j ≤ k hops.
    (Larger margin absorbs smaller perturbation.) -/
theorem margin_sufficient_for_fewer_hops
    (w w_actual : ℕ → ℕ → ℤ) (π : ℕ → ℤ) (j k : ℕ) (hjk : j ≤ k)
    (h_margin : ∀ u v, w u v + π u - π v ≥ 2 * ↑k - 1)
    (h_round : ∀ u v, w_actual u v ≥ w u v - (2 * ↑j - 1)) :
    ∀ u v, w_actual u v + π u - π v ≥ 0 := by
  intro u v
  have h1 := h_margin u v
  have h2 := h_round u v
  have : (2 : ℤ) * ↑j - 1 ≤ 2 * ↑k - 1 := by omega
  linarith

/-- Corollary: fewer-hop margin sufficiency implies no-arbitrage cycles. -/
theorem fewer_hops_no_arbitrage
    (w w_actual : ℕ → ℕ → ℤ) (π : ℕ → ℤ) (j k : ℕ) (hjk : j ≤ k)
    (h_margin : ∀ u v, w u v + π u - π v ≥ 2 * ↑k - 1)
    (h_round : ∀ u v, w_actual u v ≥ w u v - (2 * ↑j - 1))
    (s : ℕ) (mid : List ℕ) :
    pathWeight w_actual (s :: (mid ++ [s])) ≥ 0 :=
  certificate_soundness w_actual π
    (margin_sufficient_for_fewer_hops w w_actual π j k hjk h_margin h_round) s mid

/-! ## Non-vacuity witnesses -/

/-- Witness: triangle with margin 3, perturbation 2 — certificate survives.
    Original weights [6, 5, -2], potentials [0, 3, 5].
    Reduced costs: 6+0-3=3, 5+3-5=3, -2+5-0=3. All ≥ 3. -/
theorem witness_margin_3 :
    let w : ℕ → ℕ → ℤ := fun a b =>
      if a = 0 ∧ b = 1 then 6
      else if a = 1 ∧ b = 2 then 5
      else if a = 2 ∧ b = 0 then -2
      else 0
    let π : ℕ → ℤ := fun x =>
      if x = 0 then 0 else if x = 1 then 3 else if x = 2 then 5 else 0
    w 0 1 + π 0 - π 1 = 3 ∧
    w 1 2 + π 1 - π 2 = 3 ∧
    w 2 0 + π 2 - π 0 = 3 := by
  simp (config := { decide := true })

/-- Witness: perturbed weights [4, 3, -4] (each reduced by 2).
    Cycle weight: 4 + 3 + (-4) = 3 ≥ 0. Certificate survived! -/
theorem witness_perturbed_survives :
    pathWeight (fun a b =>
      if a = 0 ∧ b = 1 then 4
      else if a = 1 ∧ b = 2 then 3
      else if a = 2 ∧ b = 0 then -4
      else 0)
    [0, 1, 2, 0] = 3 := by
  simp [pathWeight]

/-- Witness: perturbed reduced costs are all ≥ 0 (certificate valid). -/
theorem witness_perturbed_certificate_valid :
    let w_p : ℕ → ℕ → ℤ := fun a b =>
      if a = 0 ∧ b = 1 then 4
      else if a = 1 ∧ b = 2 then 3
      else if a = 2 ∧ b = 0 then -4
      else 0
    let π : ℕ → ℤ := fun x =>
      if x = 0 then 0 else if x = 1 then 3 else if x = 2 then 5 else 0
    w_p 0 1 + π 0 - π 1 ≥ 0 ∧
    w_p 1 2 + π 1 - π 2 ≥ 0 ∧
    w_p 2 0 + π 2 - π 0 ≥ 0 := by
  simp (config := { decide := true })

/-- Witness: margin 1, perturbation 2 — certificate BREAKS.
    Original [4, 4, -4], potentials [0, 3, 5]. Min margin = 1.
    Perturbed by 2: [2, 2, -6]. Reduced cost: 2+0-3 = -1 < 0. -/
theorem witness_insufficient_margin :
    let w_p : ℕ → ℕ → ℤ := fun a b =>
      if a = 0 ∧ b = 1 then 2
      else if a = 1 ∧ b = 2 then 2
      else if a = 2 ∧ b = 0 then -6
      else 0
    let π : ℕ → ℤ := fun x =>
      if x = 0 then 0 else if x = 1 then 3 else if x = 2 then 5 else 0
    w_p 0 1 + π 0 - π 1 < 0 := by
  simp (config := { decide := true })

/-- Witness: the margin threshold is TIGHT — margin exactly ε = perturbation
    gives reduced cost exactly 0 (barely valid).
    Original [5, 5, -4], potentials [0, 3, 5]:
    5+0-3=2, 5+3-5=3, -4+5-0=1. Min margin = 1.
    Perturbed by 1: [4, 4, -5]. Reduced costs: 4+0-3=1, 4+3-5=2, -5+5-0=0.
    Min reduced cost = 0 (tight!). -/
theorem witness_tight_margin :
    let w_p : ℕ → ℕ → ℤ := fun a b =>
      if a = 0 ∧ b = 1 then 4
      else if a = 1 ∧ b = 2 then 4
      else if a = 2 ∧ b = 0 then -5
      else 0
    let π : ℕ → ℤ := fun x =>
      if x = 0 then 0 else if x = 1 then 3 else if x = 2 then 5 else 0
    w_p 0 1 + π 0 - π 1 ≥ 0 ∧
    w_p 1 2 + π 1 - π 2 ≥ 0 ∧
    w_p 2 0 + π 2 - π 0 = 0 := by
  simp (config := { decide := true })

end CrossSliceComposition
end Proofs
