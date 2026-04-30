import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Potential-Based Arbitrage Certificate Soundness

Arbitrage-freedom certificates via potential functions:
if π : V → ℤ satisfies w(u,v) + π(u) - π(v) ≥ 0 for every edge,
then every cycle has non-negative total weight. The key insight is
telescoping: along a cycle v₀→v₁→...→vₖ=v₀, the potential terms
cancel: Σᵢ (π(vᵢ) - π(vᵢ₊₁)) = π(v₀) - π(vₖ) = 0.

## Algebraic structure

`pathWeightHom` is a Mathlib `AddMonoidHom` from weight functions `(ℕ → ℕ → ℤ)`
to `ℤ`, capturing the fact that path weights respect the additive structure of the
weight space. Certificate composition (`certificate_add`) and weight negation
(`pathWeight_neg`) are direct consequences.

The `Certificate` structure bundles a potential function with its validity proof.
Certificate composition `Certificate.add` witnesses the monoidal structure.

## Dual certificates and coboundaries

When both `w` and `-w` admit certificates, `dual_certificate_constant` forces the
potentials to sum to a constant, and `dual_certificate_coboundary` shows `w` is an
exact coboundary: `w(u,v) = π(v) - π(u)`. This is the discrete analogue of
"conservative ⟺ curl-free ⟺ has a potential" from vector calculus, and
`coboundary_cycle_zero` confirms that coboundary weight functions have zero
circulation on every cycle.

## Key results

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `path_eq_reduced_sub_potential` | Core | pathWeight = reducedPath - potentialDiff |
| 2 | `potential_telescopes` | Core | Potential differences telescope to first minus last |
| 3 | `potential_cycle_zero` | Corollary | Telescoping on cycles gives zero |
| 4 | `reduced_path_nonneg` | Core | Certificate condition → reduced path weight ≥ 0 |
| 5 | `certificate_soundness` | Main | Certificate → every cycle non-negative |
| 6 | `path_lower_bound` | Main | Certificate → path weight ≥ π(last) - π(first) |
| 7 | `pathWeight_add` | Algebraic | pathWeight is additive in weight functions |
| 8 | `pathWeightHom` | Algebraic | pathWeight as AddMonoidHom (ℕ → ℕ → ℤ) →+ ℤ |
| 9 | `certificate_add` | Algebraic | Certificates compose under weight addition |
| 10 | `no_certificate_for_negative_cycle` | Converse | Negative cycle → no valid certificate exists |
| 11 | `dual_certificate_constant` | Main | Dual certificates → potentials sum to constant |
| 12 | `dual_certificate_coboundary` | Main | Dual certificates → w is exact coboundary |
| 13 | `coboundary_cycle_zero` | Main | Coboundary weight functions have zero cycles |
| 14 | `incremental_soundness` | Corollary | Single-edge update preserves certificate |

## Scope limitation

The model uses total functions `ℕ → ℕ → ℤ` for weights, not an explicit
graph/edge-set type. The certificate condition is checked universally over
all vertex pairs. This is the standard reduced-cost formulation from
shortest-path theory; it does not formalize LP duality or complexity bounds.
-/

namespace Proofs
namespace ArbitrageCertificate

/-! ## Walk definitions using vertex sequences -/

/-- Total weight along a vertex sequence [v₀, v₁, ..., vₖ].
    Sums w(vᵢ, vᵢ₊₁) for consecutive pairs. -/
def pathWeight (w : ℕ → ℕ → ℤ) : List ℕ → ℤ
  | [] => 0
  | [_] => 0
  | u :: v :: rest => w u v + pathWeight w (v :: rest)

/-- Sum of potential differences along consecutive pairs. -/
def potentialDiff (π : ℕ → ℤ) : List ℕ → ℤ
  | [] => 0
  | [_] => 0
  | u :: v :: rest => (π u - π v) + potentialDiff π (v :: rest)

/-- Reduced weight (w + potential difference) along consecutive pairs. -/
def reducedPath (w : ℕ → ℕ → ℤ) (π : ℕ → ℤ) : List ℕ → ℤ
  | [] => 0
  | [_] => 0
  | u :: v :: rest => (w u v + π u - π v) + reducedPath w π (v :: rest)

/-! ## Core decomposition -/

/-- Path weight = reduced path weight - potential differences. -/
theorem path_eq_reduced_sub_potential (w : ℕ → ℕ → ℤ) (π : ℕ → ℤ)
    (verts : List ℕ) :
    pathWeight w verts = reducedPath w π verts - potentialDiff π verts := by
  induction verts with
  | nil => simp [pathWeight, reducedPath, potentialDiff]
  | cons a rest ih =>
    match rest with
    | [] => simp [pathWeight, reducedPath, potentialDiff]
    | b :: tl =>
      simp only [pathWeight, reducedPath, potentialDiff]
      have := ih
      simp only [] at this
      linarith

/-! ## Telescoping -/

/-- Potential differences telescope to first minus last. -/
theorem potential_telescopes (π : ℕ → ℤ) (a : ℕ) (rest : List ℕ)
    (hne : rest ≠ []) :
    potentialDiff π (a :: rest) = π a - π (rest.getLast hne) := by
  induction rest generalizing a with
  | nil => exact absurd rfl hne
  | cons b tl ih =>
    match h : tl with
    | [] =>
      simp [potentialDiff, List.getLast]
    | c :: tl' =>
      simp only [potentialDiff]
      have hne' : (c :: tl') ≠ [] := List.cons_ne_nil c tl'
      have ih_b := ih b hne'
      simp only [potentialDiff] at ih_b
      rw [ih_b]
      simp [List.getLast]

/-- **Telescoping Theorem**: potential differences along a cycle sum to zero.
    A cycle is a path [v₀, ..., vₖ, v₀] where first = last. -/
theorem potential_cycle_zero (π : ℕ → ℤ) (s : ℕ) (mid : List ℕ)
    (hne : (mid ++ [s]) ≠ []) :
    potentialDiff π (s :: (mid ++ [s])) = 0 := by
  rw [potential_telescopes π s (mid ++ [s]) hne]
  simp [List.getLast_append_of_ne_nil]

/-! ## Reduced weight non-negativity -/

/-- If the certificate holds for all pairs, reduced path weight is non-negative. -/
theorem reduced_path_nonneg (w : ℕ → ℕ → ℤ) (π : ℕ → ℤ)
    (h_cert : ∀ u v, w u v + π u - π v ≥ 0)
    (verts : List ℕ) :
    reducedPath w π verts ≥ 0 := by
  induction verts with
  | nil => simp [reducedPath]
  | cons a rest ih =>
    match rest with
    | [] => simp [reducedPath]
    | b :: tl =>
      simp only [reducedPath]
      have := h_cert a b
      have : reducedPath w π (b :: tl) ≥ 0 := ih
      linarith

/-! ## The certificate theorem -/

/-- **Certificate Soundness**: If potentials π satisfy the reduced cost condition
    for all vertex pairs, then every cycle has non-negative total weight.

    A cycle is [s, v₁, ..., vₖ, s] — starts and ends at s. -/
theorem certificate_soundness (w : ℕ → ℕ → ℤ) (π : ℕ → ℤ)
    (h_cert : ∀ u v, w u v + π u - π v ≥ 0)
    (s : ℕ) (mid : List ℕ) :
    pathWeight w (s :: (mid ++ [s])) ≥ 0 := by
  rw [path_eq_reduced_sub_potential w π]
  have h_tele := potential_cycle_zero π s mid (by simp)
  have h_nonneg := reduced_path_nonneg w π h_cert (s :: (mid ++ [s]))
  linarith

/-! ## Path lower bound (generalization of certificate to non-cycles) -/

/-- **Path Lower Bound**: under the certificate condition, any path from `first`
    to the last vertex has weight ≥ π(last) - π(first). This generalizes
    `certificate_soundness` (which is the special case where first = last).

    For shortest paths: if π(v) = shortest-path distance from source to v,
    then pathWeight ≥ π(last) - π(first) = d(last) - d(first). -/
theorem path_lower_bound (w : ℕ → ℕ → ℤ) (π : ℕ → ℤ)
    (h_cert : ∀ u v, w u v + π u - π v ≥ 0)
    (first : ℕ) (rest : List ℕ) (hne : rest ≠ []) :
    pathWeight w (first :: rest) ≥ π (rest.getLast hne) - π first := by
  rw [path_eq_reduced_sub_potential w π (first :: rest)]
  have h_tele := potential_telescopes π first rest hne
  have h_nonneg := reduced_path_nonneg w π h_cert (first :: rest)
  linarith

/-! ## Incremental update -/

/-- If the certificate holds and a single edge's weight changes but still
    satisfies the reduced cost condition, the certificate remains valid. -/
theorem incremental_soundness (w w' : ℕ → ℕ → ℤ) (π : ℕ → ℤ)
    (h_cert : ∀ u v, w u v + π u - π v ≥ 0)
    (u₀ v₀ : ℕ)
    (h_unchanged : ∀ u v, (u, v) ≠ (u₀, v₀) → w' u v = w u v)
    (h_new : w' u₀ v₀ + π u₀ - π v₀ ≥ 0) :
    ∀ u v, w' u v + π u - π v ≥ 0 := by
  intro u v
  by_cases h : (u, v) = (u₀, v₀)
  · obtain ⟨rfl, rfl⟩ := Prod.eq_iff_fst_eq_snd_eq.mp h
    exact h_new
  · rw [h_unchanged u v h]
    exact h_cert u v

/-! ## Certificate structure -/

/-- An arbitrage certificate: a potential function bundled with its validity proof. -/
structure Certificate (w : ℕ → ℕ → ℤ) where
  potential : ℕ → ℤ
  valid : ∀ u v, w u v + potential u - potential v ≥ 0

/-! ## Algebraic structure: pathWeight is additive in weights -/

/-- **WEIGHT ADDITIVITY**: pathWeight is a homomorphism in the weight function.
    `pathWeight (w₁ + w₂) verts = pathWeight w₁ verts + pathWeight w₂ verts`.

    This is the algebraic backbone of certificate composition. -/
theorem pathWeight_add (w₁ w₂ : ℕ → ℕ → ℤ) (verts : List ℕ) :
    pathWeight (fun u v => w₁ u v + w₂ u v) verts =
    pathWeight w₁ verts + pathWeight w₂ verts := by
  induction verts with
  | nil => simp [pathWeight]
  | cons a rest ih =>
    match rest with
    | [] => simp [pathWeight]
    | b :: tl =>
      simp only [pathWeight]
      have := ih
      simp only [] at this
      linarith

/-- Zero weight function gives zero path weight.
    This is the `map_zero` law for the `AddMonoidHom` below. -/
theorem pathWeight_zero (verts : List ℕ) :
    pathWeight (fun _ _ => (0 : ℤ)) verts = 0 := by
  induction verts with
  | nil => simp [pathWeight]
  | cons a rest ih =>
    match rest with
    | [] => simp [pathWeight]
    | b :: tl =>
      simp only [pathWeight]
      have := ih; simp only [] at this
      linarith

/-- **PATH WEIGHT HOMOMORPHISM**: For a fixed vertex list, the map
    `w ↦ pathWeight w verts` is an `AddMonoidHom` from the additive group
    of weight functions `(ℕ → ℕ → ℤ)` to `ℤ`.

    This captures the algebraic essence of arbitrage theory: path weights
    respect the additive structure of the weight space. Certificate composition
    (`certificate_add`) and weight negation (`pathWeight_neg`) are direct
    consequences of this homomorphism. -/
def pathWeightHom (verts : List ℕ) : (ℕ → ℕ → ℤ) →+ ℤ where
  toFun w := pathWeight w verts
  map_zero' := pathWeight_zero verts
  map_add' w₁ w₂ := pathWeight_add w₁ w₂ verts

/-- Negating all edge weights negates the path weight. -/
theorem pathWeight_neg (w : ℕ → ℕ → ℤ) (verts : List ℕ) :
    pathWeight (fun u v => -w u v) verts = -pathWeight w verts := by
  induction verts with
  | nil => simp [pathWeight]
  | cons a rest ih =>
    match rest with
    | [] => simp [pathWeight]
    | b :: tl =>
      simp only [pathWeight]
      have := ih; simp only [] at this
      linarith

/-- **CERTIFICATE COMPOSITION**: if w₁ has certificate π₁ and w₂ has certificate π₂,
    then (w₁ + w₂) has certificate (π₁ + π₂).

    Proof: reduced cost of the sum is the sum of reduced costs, both non-negative. -/
theorem certificate_add (w₁ w₂ : ℕ → ℕ → ℤ) (π₁ π₂ : ℕ → ℤ)
    (h₁ : ∀ u v, w₁ u v + π₁ u - π₁ v ≥ 0)
    (h₂ : ∀ u v, w₂ u v + π₂ u - π₂ v ≥ 0) :
    ∀ u v, (w₁ u v + w₂ u v) + (π₁ u + π₂ u) - (π₁ v + π₂ v) ≥ 0 := by
  intro u v
  have h1 := h₁ u v
  have h2 := h₂ u v
  linarith

/-- Certificate composition via the `Certificate` structure. -/
def Certificate.add {w₁ w₂ : ℕ → ℕ → ℤ}
    (c₁ : Certificate w₁) (c₂ : Certificate w₂) :
    Certificate (fun u v => w₁ u v + w₂ u v) :=
  ⟨fun v => c₁.potential v + c₂.potential v,
   certificate_add w₁ w₂ c₁.potential c₂.potential c₁.valid c₂.valid⟩

/-! ## Dual certificates and coboundaries -/

/-- **DUAL CERTIFICATE RIGIDITY**: If both `w` and `-w` admit certificates,
    the potentials sum to a constant. This forces `w` to be an exact coboundary
    (potential difference), connecting to the discrete analogue of "curl-free
    vector fields have a potential function" from vector calculus.

    Proof: the certificate for `w` gives `(π+ρ)(u) ≥ (π+ρ)(v)`,
    and the certificate for `-w` gives the reverse, forcing equality. -/
theorem dual_certificate_constant (w : ℕ → ℕ → ℤ) (π ρ : ℕ → ℤ)
    (h_pos : ∀ u v, w u v + π u - π v ≥ 0)
    (h_neg : ∀ u v, -w u v + ρ u - ρ v ≥ 0) :
    ∀ u v, π u + ρ u = π v + ρ v := by
  intro u v
  have h1 := h_pos u v
  have h2 := h_neg u v
  have h3 := h_pos v u
  have h4 := h_neg v u
  linarith

/-- **COBOUNDARY CHARACTERIZATION**: When both `w` and `-w` have certificates,
    `w` is an exact coboundary: `w(u,v) = π(v) - π(u)` for all u, v.
    The upper and lower bounds from the two certificates collapse to equality
    via `dual_certificate_constant`. -/
theorem dual_certificate_coboundary (w : ℕ → ℕ → ℤ) (π ρ : ℕ → ℤ)
    (h_pos : ∀ u v, w u v + π u - π v ≥ 0)
    (h_neg : ∀ u v, -w u v + ρ u - ρ v ≥ 0)
    (u v : ℕ) :
    w u v = π v - π u := by
  have h1 := h_pos u v
  have h2 := h_neg u v
  have hconst := dual_certificate_constant w π ρ h_pos h_neg u v
  linarith

/-- **COBOUNDARY CYCLES ARE ZERO**: If `w(u,v) = π(v) - π(u)` for some potential,
    every cycle has zero total weight — the discrete analogue of "conservative
    force fields have zero circulation". -/
theorem coboundary_cycle_zero (π : ℕ → ℤ) (s : ℕ) (mid : List ℕ) :
    pathWeight (fun u v => π v - π u) (s :: (mid ++ [s])) = 0 := by
  rw [path_eq_reduced_sub_potential (fun u v => π v - π u) π]
  have h_tele := potential_cycle_zero π s mid (by simp)
  suffices h_red : reducedPath (fun u v => π v - π u) π (s :: (mid ++ [s])) = 0 by linarith
  -- Each reduced cost (π v - π u) + π u - π v = 0
  generalize (s :: (mid ++ [s])) = verts
  induction verts with
  | nil => simp [reducedPath]
  | cons a rest ih =>
    match rest with
    | [] => simp [reducedPath]
    | b :: tl =>
      simp only [reducedPath]
      have := ih
      simp only [] at this
      linarith

/-! ## Converse: negative cycles rule out certificates -/

/-- **CONVERSE**: if any cycle has negative total weight, no valid certificate exists.

    Contrapositive of `certificate_soundness`: a negative-weight cycle is
    an explicit obstruction to the existence of any potential function
    satisfying the reduced cost condition. -/
theorem no_certificate_for_negative_cycle (w : ℕ → ℕ → ℤ) (s : ℕ) (mid : List ℕ)
    (h_neg : pathWeight w (s :: (mid ++ [s])) < 0) :
    ¬ ∃ π : ℕ → ℤ, ∀ u v, w u v + π u - π v ≥ 0 := by
  intro ⟨π, h_cert⟩
  have h_nonneg := certificate_soundness w π h_cert s mid
  linarith

/-! ## Non-vacuity witnesses -/

/-- Witness: triangle 0→1→2→0 with weights [3, 2, -4] and potentials [0, 3, 5].
    Total cycle weight = 1 ≥ 0. -/
theorem witness_cycle_weight :
    pathWeight (fun a b => if a = 0 ∧ b = 1 then 3
                           else if a = 1 ∧ b = 2 then 2
                           else if a = 2 ∧ b = 0 then -4
                           else 0)
      [0, 1, 2, 0] = 1 := by
  simp [pathWeight]

/-- **Non-vacuous Certificate witness**: `w(u,v) = v - u + 1` with `π(v) = v`.
    Reduced cost = (v - u + 1) + u - v = 1 ≥ 0 for ALL vertex pairs.
    This is a genuine global `Certificate`, not just an edge-local check.

    Cycle weights are always positive: any k-cycle has weight k ≥ 1. -/
def witness_global_certificate : Certificate (fun (u v : ℕ) => (v : ℤ) - (u : ℤ) + 1) where
  potential := fun v => (v : ℤ)
  valid := by intro u v; omega

/-- The witness certificate gives non-trivial cycle weights. -/
theorem witness_global_cycle_weight :
    pathWeight (fun (u v : ℕ) => (v : ℤ) - (u : ℤ) + 1) [0, 5, 2, 0] = 3 := by
  simp [pathWeight]

/-- Witness: converse in action. The negative cycle [0,1,2,0] with weight -1
    rules out any valid certificate via `no_certificate_for_negative_cycle`. -/
theorem witness_converse :
    ¬ ∃ π : ℕ → ℤ, ∀ u v,
      (if u = 0 ∧ v = 1 then (1 : ℤ)
       else if u = 1 ∧ v = 2 then 1
       else if u = 2 ∧ v = 0 then -3
       else 0) + π u - π v ≥ 0 := by
  apply no_certificate_for_negative_cycle _ 0 [1, 2]
  simp [pathWeight]

/-- Witness: pathWeight additivity with concrete values. -/
theorem witness_pathWeight_add :
    let w₁ : ℕ → ℕ → ℤ := fun _ v => (v : ℤ)
    let w₂ : ℕ → ℕ → ℤ := fun u _ => (u : ℤ)
    pathWeight (fun u v => w₁ u v + w₂ u v) [0, 3, 1] =
    pathWeight w₁ [0, 3, 1] + pathWeight w₂ [0, 3, 1] := by
  simp [pathWeight]

/-- Witness: `coboundary_cycle_zero` applied to the nonlinear potential π(v) = v².
    Cycle [0, 5, 2, 0] with w(u,v) = v² - u²: weight = (25-0)+(4-25)+(0-4) = 0. -/
theorem witness_coboundary_zero :
    pathWeight (fun (u v : ℕ) => (v : ℤ) ^ 2 - (u : ℤ) ^ 2) [0, 5, 2, 0] = 0 :=
  coboundary_cycle_zero (fun v => (v : ℤ) ^ 2) 0 [5, 2]

/-- Witness: dual certificate constant. w(u,v) = v-u, π(v) = v, ρ(v) = -v.
    Certificate conditions: reduced costs are identically 0.
    Rigidity: π + ρ = 0 everywhere (constant). -/
theorem witness_dual :
    let w : ℕ → ℕ → ℤ := fun u v => (v : ℤ) - (u : ℤ)
    let π : ℕ → ℤ := fun v => (v : ℤ)
    let ρ : ℕ → ℤ := fun v => -(v : ℤ)
    -- Certificate for w: reduced cost = (v-u) + u - v = 0 ≥ 0
    w 3 7 + π 3 - π 7 = 0 ∧
    -- Certificate for -w: reduced cost = (u-v) + (-u) - (-v) = 0 ≥ 0
    -w 3 7 + ρ 3 - ρ 7 = 0 ∧
    -- Constant: π(u) + ρ(u) = 0 for all u
    π 42 + ρ 42 = 0 := by
  simp

end ArbitrageCertificate
end Proofs
