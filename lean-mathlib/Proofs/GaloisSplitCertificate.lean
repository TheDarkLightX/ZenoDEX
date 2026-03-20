import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Discrete Concavity Certificate for Split Routing

An O(1) optimality certificate for integer-valued objectives on finite domains:
if f : ℕ → ℤ is discretely concave on {0,...,D} and f(a) ≥ f(a±1) at a candidate
point, then a is a global maximum.

The certificate requires only 2 local comparisons (left and right neighbors).
Boundary comparisons are unnecessary — they follow from concavity + neighbor checks.

## Key results

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `right_delta_chain` | Substantive | Non-positive deltas propagate rightward under concavity |
| 2 | `right_mono` | Substantive | f(a) ≥ f(a+n) for all n (telescoping from right_delta_chain) |
| 3 | `left_delta_chain` | Substantive | Non-negative deltas propagate leftward under concavity |
| 4 | `left_mono` | Substantive | f(a) ≥ f(j) for all j ≤ a (telescoping from left_delta_chain) |
| 5 | `certificate_implies_global_max` | Substantive | 2-check certificate → global maximum (main theorem) |
| 6 | `necessity_right` | Substantive | f(a) < f(a+1) → a is NOT the global max |
| 7 | `necessity_left` | Substantive | f(a) < f(a-1) → a is NOT the global max |
| 8 | `strict_concave_maximizers_adjacent` | Substantive | Strictly concave → maximizers within distance 1 |
| 9 | `maximizer_interval` | Substantive | Maximizer set is a contiguous interval |
-/

namespace Proofs
namespace GaloisSplitCertificate

/-- Discrete concavity on {0,...,D}: first differences are non-increasing. -/
def DiscreteConcave (f : ℕ → ℤ) (D : ℕ) : Prop :=
  ∀ i, i + 2 ≤ D →
    f (i + 2) - f (i + 1) ≤ f (i + 1) - f i

/-! ## Right side: all additions, no subtraction -/

/-- Under concavity, non-positive deltas propagate rightward. -/
theorem right_delta_chain (f : ℕ → ℤ) (D a : ℕ)
    (hconc : DiscreteConcave f D)
    (h_base : f (a + 1) ≤ f a)
    (n : ℕ) (hn : a + n + 1 ≤ D) :
    f (a + n + 1) ≤ f (a + n) := by
  induction n with
  | zero => simpa using h_base
  | succ k ih =>
    have h_ih := ih (by omega)
    have hc := hconc (a + k) (by omega)
    -- Unify Nat.succ forms with canonical a+k+_ forms
    show f (a + k + 2) ≤ f (a + k + 1)
    linarith

/-- f(a) ≥ f(a+n) for all n, from non-positive deltas (telescoping). -/
theorem right_mono (f : ℕ → ℤ) (D a : ℕ)
    (hconc : DiscreteConcave f D)
    (h_base : f (a + 1) ≤ f a)
    (n : ℕ) (hn : a + n ≤ D) :
    f a ≥ f (a + n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := right_delta_chain f D a hconc h_base k (by omega)
    -- h2 : f(a+k+1) ≤ f(a+k)
    -- h1 : f(a) ≥ f(a+k)
    -- Need: f(a) ≥ f(a+(k+1)) = f(a+k+1)
    show f a ≥ f (a + (k + 1))
    have : a + (k + 1) = a + k + 1 := by omega
    rw [this]
    linarith

/-! ## Left side: downward propagation using distance -/

/-- Under concavity, non-negative deltas propagate leftward.
    Expressed using distance d from a: f(a-d) ≥ f(a-d-1). -/
theorem left_delta_chain (f : ℕ → ℤ) (D a : ℕ)
    (hconc : DiscreteConcave f D) (haD : a ≤ D)
    (h_base : f a ≥ f (a - 1))
    (d : ℕ) (hd : d < a) :
    f (a - d) ≥ f (a - d - 1) := by
  induction d with
  | zero =>
    -- a - 0 = a, a - 0 - 1 = a - 1
    simp
    exact h_base
  | succ k ih =>
    have h_ih := ih (by omega)
    -- Concavity at position (a-k-2): need a-k-2+2 ≤ D
    have pos_eq : a - k - 2 + 2 = a - k := by omega
    have pos_eq2 : a - k - 2 + 1 = a - k - 1 := by omega
    have hc := hconc (a - k - 2) (by omega)
    rw [pos_eq, pos_eq2] at hc
    -- hc : f(a-k) - f(a-k-1) ≤ f(a-k-1) - f(a-k-2)
    -- Goal has a-(k+1) form; change to canonical a-k-1/a-k-2 form
    show f (a - k - 1) ≥ f (a - k - 2)
    linarith

/-- f(a) ≥ f(j) for all j ≤ a (left monotonicity from concavity). -/
theorem left_mono (f : ℕ → ℤ) (D a : ℕ)
    (hconc : DiscreteConcave f D) (haD : a ≤ D)
    (h_base : f a ≥ f (a - 1))
    (j : ℕ) (hj : j ≤ a) :
    f a ≥ f j := by
  -- Prove via distance d = a - j, carrying d ≤ a bound
  suffices h : ∀ d, d ≤ a → f a ≥ f (a - d) by
    have hd := h (a - j) (by omega)
    have heq : a - (a - j) = j := by omega
    rw [heq] at hd; exact hd
  intro d hda
  induction d with
  | zero => simp
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := left_delta_chain f D a hconc haD h_base k (by omega)
    have eq : a - k - 1 = a - (k + 1) := by omega
    rw [eq] at h2
    linarith

/-! ## The certificate theorem -/

/-- **Certificate Soundness**: If f is discretely concave on {0,...,D}
    and the 2-comparison certificate holds at a, then a is a global maximum.

    Certificate = 2 comparisons only:
    - f(a) ≥ f(a-1)   (left neighbor, vacuous when a=0)
    - f(a) ≥ f(a+1)   (right neighbor, vacuous when a=D)

    Boundary comparisons (f(a) ≥ f(0), f(a) ≥ f(D)) are NOT needed —
    they follow from concavity + neighbor checks via left_mono/right_mono.
    This strengthens the certificate from 4 checks to 2 checks. -/
theorem certificate_implies_global_max (f : ℕ → ℤ) (D a : ℕ)
    (ha : a ≤ D)
    (hconc : DiscreteConcave f D)
    (h_prev : 0 < a → f a ≥ f (a - 1))
    (h_next : a < D → f a ≥ f (a + 1))
    (j : ℕ) (hj : j ≤ D) :
    f a ≥ f j := by
  by_cases hja : j ≤ a
  · -- Left side: j ≤ a
    rcases Nat.eq_or_lt_of_le (Nat.zero_le a) with ha0 | hapos
    · -- a = 0, j ≤ 0, so j = 0
      subst ha0
      have hj0 : j = 0 := by omega
      subst hj0
      exact le_refl _
    · exact left_mono f D a hconc ha (h_prev hapos) j hja
  · -- Right side: j > a
    push_neg at hja
    rcases Nat.eq_or_lt_of_le ha with haD | haD'
    · -- a = D, j > D, contradiction with j ≤ D
      omega
    · -- a < D: use right monotonicity
      have h_drop : f (a + 1) ≤ f a := by linarith [h_next haD']
      obtain ⟨n, rfl⟩ : ∃ n, j = a + n := ⟨j - a, by omega⟩
      exact right_mono f D a hconc h_drop n (by omega)

/-! ## Certificate necessity -/

/-- **Necessity (right)**: if f(a) < f(a+1) then a is NOT the global max on {0,...,D}. -/
theorem necessity_right (f : ℕ → ℤ) (D a : ℕ)
    (ha : a < D)
    (h_fail : f a < f (a + 1)) :
    ∃ j, j ≤ D ∧ f j > f a :=
  ⟨a + 1, by omega, h_fail⟩

/-- **Necessity (left)**: if f(a) < f(a-1) then a is NOT the global max on {0,...,D}.
    Uses the natural number convention: a - 1 = 0 when a = 0 (vacuous). -/
theorem necessity_left (f : ℕ → ℤ) (D a : ℕ)
    (ha : a ≤ D) (hapos : 0 < a)
    (h_fail : f a < f (a - 1)) :
    ∃ j, j ≤ D ∧ f j > f a :=
  ⟨a - 1, by omega, h_fail⟩

/-! ## Strict concavity and uniqueness -/

/-- Strict discrete concavity: first differences are strictly decreasing. -/
def StrictDiscreteConcave (f : ℕ → ℤ) (D : ℕ) : Prop :=
  ∀ i, i + 2 ≤ D →
    f (i + 2) - f (i + 1) < f (i + 1) - f i

/-- Strict concavity implies (non-strict) concavity. -/
theorem strict_concave_is_concave (f : ℕ → ℤ) (D : ℕ)
    (h : StrictDiscreteConcave f D) : DiscreteConcave f D :=
  fun i hi => le_of_lt (h i hi)

/-- **Maximizers adjacent**: Under strict discrete concavity, if a ≤ b are both
    global maxima on {0,...,D} then b ≤ a + 1. The set of maximizers has at most
    2 elements (and they must be consecutive).

    Proof: If b ≥ a+2, strict concavity forces f(a+k+2) < f(a) for all valid k
    (strict propagation of negative deltas), contradicting f(b) = f(a). -/
theorem strict_concave_maximizers_adjacent (f : ℕ → ℤ) (D a b : ℕ)
    (hconc : StrictDiscreteConcave f D)
    (ha : a ≤ D) (hb : b ≤ D)
    (hmax_a : ∀ j, j ≤ D → f a ≥ f j)
    (hmax_b : ∀ j, j ≤ D → f b ≥ f j)
    (_hab : a ≤ b) :
    b ≤ a + 1 := by
  by_contra hge
  push_neg at hge
  -- b ≥ a + 2
  have heq : f a = f b := le_antisymm (hmax_b a ha) (hmax_a b hb)
  have h_base : f (a + 1) ≤ f a := hmax_a (a + 1) (by omega)
  have hconc_weak := strict_concave_is_concave f D hconc
  -- Key: f(a + k + 2) < f(a) for all valid k, by induction
  suffices key : ∀ k, a + k + 2 ≤ D → f (a + k + 2) < f a by
    have hk := key (b - a - 2) (by omega)
    have he : a + (b - a - 2) + 2 = b := by omega
    rw [he] at hk
    linarith
  intro k
  induction k with
  | zero =>
    -- Base: strict concavity at a gives f(a+2) - f(a+1) < f(a+1) - f(a) ≤ 0
    intro hbd
    have hsc := hconc a (by omega)
    linarith
  | succ m ih =>
    intro hbd
    have ihm := ih (by omega)
    -- f(a+(m+1)+1) ≤ f(a+(m+1)) from non-strict right_delta_chain
    have hdrop := right_delta_chain f D a hconc_weak h_base (m + 1) (by omega)
    -- Strict concavity at position a+m+1
    have hsc := hconc (a + m + 1) (by omega)
    -- Normalize Nat arithmetic for linarith
    have e1 : a + (m + 1) + 1 = a + m + 2 := by omega
    have e2 : a + (m + 1) = a + m + 1 := by omega
    have e3 : (a + m + 1) + 2 = a + m + 3 := by omega
    have e4 : (a + m + 1) + 1 = a + m + 2 := by omega
    have e5 : a + (m + 1) + 2 = a + m + 3 := by omega
    rw [e1, e2] at hdrop
    rw [e3, e4] at hsc
    -- hdrop: f(a+m+2) ≤ f(a+m+1), so delta ≤ 0
    -- hsc: f(a+m+3) - f(a+m+2) < f(a+m+2) - f(a+m+1) ≤ 0
    -- ihm: f(a+m+2) < f(a)
    -- Therefore f(a+m+3) < f(a+m+2) < f(a)
    show f (a + (m + 1) + 2) < f a
    rw [e5]
    linarith

/-! ## Maximizer set structure -/

/-- **MAXIMIZER INTERVAL**: Under discrete concavity, if `a` and `b` are both
    global maxima on {0,...,D} with `a ≤ c ≤ b`, then `c` is also a global maximum.
    The set of maximizers is a contiguous interval {a, a+1, ..., b}.

    Proof: `right_delta_chain` propagates non-positive deltas from `a` through to `c`,
    giving `f(c+1) ≤ f(c)`. Then `right_mono` from `c` yields `f(c) ≥ f(b)`.
    Since `b` is a global max, `f(c) ≥ f(b) ≥ f(a) ≥ f(j)` for all `j`. -/
theorem maximizer_interval (f : ℕ → ℤ) (D a c b : ℕ)
    (hconc : DiscreteConcave f D)
    (ha : a ≤ D) (hb : b ≤ D) (hac : a ≤ c) (hcb : c ≤ b)
    (hmax_a : ∀ j, j ≤ D → f a ≥ f j)
    (hmax_b : ∀ j, j ≤ D → f b ≥ f j) :
    ∀ j, j ≤ D → f c ≥ f j := by
  intro j hj
  rcases Nat.eq_or_lt_of_le hac with rfl | hac'
  · exact hmax_a j hj
  rcases Nat.eq_or_lt_of_le hcb with rfl | hcb'
  · exact hmax_b j hj
  -- Interior: a < c < b
  have ha1 : f (a + 1) ≤ f a := hmax_a (a + 1) (by omega)
  -- Propagate non-positive deltas from a to c
  have hc1 : f (c + 1) ≤ f c := by
    have h := right_delta_chain f D a hconc ha1 (c - a) (by omega)
    rwa [show a + (c - a) + 1 = c + 1 from by omega,
         show a + (c - a) = c from by omega] at h
  -- f(c) ≥ f(b) via right_mono from c
  have hcb_ge : f c ≥ f b := by
    have h := right_mono f D c hconc hc1 (b - c) (by omega)
    rwa [show c + (b - c) = b from by omega] at h
  -- Chain: f(c) ≥ f(b) ≥ f(a) ≥ f(j)
  linarith [hmax_b a ha, hmax_a j hj]

/-! ## Non-vacuity witnesses -/

/-- f(x) = -(x-5)² + 25 is discretely concave on {0,...,10}.
    The second difference is constantly -2. -/
theorem witness_concave :
    DiscreteConcave (fun x : ℕ => -((x : ℤ) - 5) ^ 2 + 25) 10 := by
  intro i hi
  have hi' : i ≤ 8 := by omega
  interval_cases i <;> norm_num

/-- f(x) = -(x-5)² + 25 is STRICTLY discretely concave on {0,...,10}. -/
theorem witness_strict_concave :
    StrictDiscreteConcave (fun x : ℕ => -((x : ℤ) - 5) ^ 2 + 25) 10 := by
  intro i hi
  have hi' : i ≤ 8 := by omega
  interval_cases i <;> norm_num

/-- End-to-end witness: a=5 is the global max of -(x-5)² + 25 on {0,...,10},
    proved via `certificate_implies_global_max` (not reproving independently). -/
theorem witness_global_max :
    let f : ℕ → ℤ := fun x => -((x : ℤ) - 5) ^ 2 + 25
    ∀ j : ℕ, j ≤ 10 → f 5 ≥ f j :=
  certificate_implies_global_max
    (fun x : ℕ => -((x : ℤ) - 5) ^ 2 + 25) 10 5
    (by omega)
    witness_concave
    (by intro; norm_num)
    (by intro; norm_num)

/-- Necessity witness: f(4) < f(5), so a=4 is NOT the global max. -/
theorem witness_necessity_right :
    let f : ℕ → ℤ := fun x => -((x : ℤ) - 5) ^ 2 + 25
    ∃ j, j ≤ 10 ∧ f j > f 4 := by
  exact necessity_right _ 10 4 (by omega) (by norm_num)

/-- Adjacency witness: any two global maxima of -(x-5)² + 25 on {0,...,10} are
    within distance 1 of each other. -/
theorem witness_adjacency :
    let f : ℕ → ℤ := fun x => -((x : ℤ) - 5) ^ 2 + 25
    ∀ a b : ℕ, a ≤ 10 → b ≤ 10 → a ≤ b →
    (∀ j, j ≤ 10 → f a ≥ f j) → (∀ j, j ≤ 10 → f b ≥ f j) → b ≤ a + 1 :=
  fun a b ha hb hab hma hmb =>
    strict_concave_maximizers_adjacent _ 10 a b witness_strict_concave ha hb hma hmb hab

/-- Maximizer interval witness: f(x) = min(x, 3) on {0,...,6} has
    maximizers {3, 4, 5, 6} — a contiguous interval, as predicted. -/
theorem witness_maximizer_interval :
    let f : ℕ → ℤ := fun x => min (x : ℤ) 3
    f 3 = 3 ∧ f 4 = 3 ∧ f 5 = 3 ∧ f 6 = 3 ∧ f 0 = 0 := by
  native_decide

end GaloisSplitCertificate
end Proofs
