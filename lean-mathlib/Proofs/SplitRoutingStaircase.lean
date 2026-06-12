import Proofs.CPMMInvariants
import Proofs.AntiFragmentation
import Mathlib.Tactic

/-!
# Staircase Structure of Fee-Aware Split Routing (Exact Jump Enumeration)

The runtime two-pool split optimizer searches `f(a) = out₀(a) + out₁(D−a)`
over integer splits `a`. Under v8 semantics (`fee = ⌈a·f/10⁴⌉`, output
floor), each pool's output is a **monotone staircase** in its gross input.
This file proves the two facts that turn the search into an exact,
closed-form jump enumeration:

1. **Candidate completeness** (`two_pool_split_candidate_complete`): the sum
   of a non-decreasing staircase and a non-increasing staircase attains its
   leftmost maximum either at the left endpoint or at a *jump point* of the
   increasing staircase. So only `{lo} ∪ jumps(out₀)` need to be evaluated —
   at most `1 + out₀(hi)` points instead of the whole interval.

2. **Closed-form jumps** (`le_feeOut_iff`, `jump_point_closed_form`): the
   minimal gross input reaching output level `t` is

       a_t = ⌈ ⌈t·x/(y−t)⌉ · 10⁴ / (10⁴−f) ⌉,

   two ceiling divisions — no search. Hence each jump point is computable
   in O(1) and the whole optimizer needs O(min(span, out₀(hi))) quote
   evaluations, with bit-exact agreement with brute force (it inspects a
   superset of the leftmost maximizers and applies the same tie-break).

## Key results

| # | Name | Statement |
|---|------|-----------|
| 1 | `netAmount_eq_floor` | a − ⌈a·f/10⁴⌉ = ⌊(10⁴−f)·a/10⁴⌋ |
| 2 | `feeOut_mono` | fee-aware output is monotone in gross input |
| 3 | `staircase_leftmost_dominates` | monotone + antitone sums: leftmost max at jumps |
| 4 | `ceilDiv_le_iff` | ⌈a/b⌉ ≤ c ↔ a ≤ b·c (b > 0) — ceiling/floor adjunction |
| 5 | `le_swapOutput_iff` | t ≤ out(n) ↔ ⌈t·x/(y−t)⌉ ≤ n (threshold inversion) |
| 6 | `le_feeOut_iff` | t ≤ out(a) ↔ a_t ≤ a (composed inversion, fee-aware) |
| 7 | `two_pool_split_candidate_complete` | candidate set {lo} ∪ jumps is complete |
| 8 | `jump_point_closed_form` | every jump point equals its closed form a_t |
| 9 | `multi_pool_snap_dominates` | k pools: optimum attained with all non-absorber coordinates on jump grids |

`ceilDiv_le_iff` is the Galois-connection fact `⌈·/b⌉ ⊣ (b·)` making the
inversions exact; `Nat.le_div_iff_mul_le` is its floor-side dual.
-/

namespace Proofs
namespace SplitRoutingStaircase

open CPMMInvariants (ceilDiv computeFee netAmount swapOutput)

/-! ## The fee-aware quote (v8 semantics) -/

/-- Fee-aware exact-in output: `⌊y·net/(x+net)⌋` with `net = a − ⌈a·f/10⁴⌉`.
    This is the algebraic core of the runtime `exact_out_for_pool_exact_in`
    (the runtime additionally rejects degenerate trades; rejection regimes
    are monotone so they only clip the search interval). -/
def feeOut (x y f a : ℕ) : ℕ := swapOutput x y (netAmount a f)

/-- **NET AS FLOOR**: the ceil-fee net amount is a floor of a linear map:
    `a − ⌈a·f/10⁴⌉ = ⌊(10⁴−f)·a/10⁴⌋` for `f ≤ 10⁴`. This identity converts
    the fee staircase into the floor form used by the threshold inversion. -/
theorem netAmount_eq_floor (a f : ℕ) (hf : f ≤ 10000) :
    netAmount a f = (10000 - f) * a / 10000 := by
  unfold CPMMInvariants.netAmount CPMMInvariants.computeFee CPMMInvariants.ceilDiv
  have hsplit : (10000 - f) * a + a * f = 10000 * a := by
    rw [mul_comm a f, ← Nat.add_mul, Nat.sub_add_cancel hf]
  generalize a * f = n at hsplit ⊢
  generalize (10000 - f) * a = q at hsplit ⊢
  omega

/-- **MONOTONE STAIRCASE**: the fee-aware output is non-decreasing in the
    gross input. Composition of the monotone net staircase with the
    monotone zero-fee output (`swapOut_mono_amount`). -/
theorem feeOut_mono (x y f : ℕ) (hf : f ≤ 10000) : Monotone (feeOut x y f) := by
  intro a b hab
  unfold feeOut
  have hnet : netAmount a f ≤ netAmount b f := by
    rw [netAmount_eq_floor a f hf, netAmount_eq_floor b f hf]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hab)
  exact AntiFragmentation.swapOut_mono_amount x y _ _ hnet

/-! ## Candidate completeness for monotone/antitone sums -/

/-- **STAIRCASE DOMINANCE**: if `u` is monotone and `v` antitone, then for
    every `a ≥ lo` there is a candidate `c ≤ a` with the same `u`-value that
    weakly improves the sum and is either `lo` or a jump point of `u`
    (`u(c−1) < u(c)`). Consequently the leftmost maximizer of `u + v` over
    `[lo, hi]` lies in `{lo} ∪ {jump points of u}`: between jumps `u` is
    constant and `v` non-increasing, so the left end of each level segment
    dominates the segment. -/
theorem staircase_leftmost_dominates (u v : ℕ → ℕ)
    (hu : Monotone u) (hv : Antitone v)
    (lo a : ℕ) (hla : lo ≤ a) :
    ∃ c, lo ≤ c ∧ c ≤ a ∧ u c = u a ∧ (c = lo ∨ u (c - 1) < u c) ∧
      u a + v a ≤ u c + v c := by
  classical
  have hp : ∃ n, lo ≤ n ∧ u n = u a := ⟨a, hla, rfl⟩
  obtain ⟨hlc, huc⟩ := Nat.find_spec hp
  have hca : Nat.find hp ≤ a := Nat.find_le ⟨hla, rfl⟩
  use Nat.find hp
  constructor
  · exact hlc
  constructor
  · exact hca
  constructor
  · exact huc
  constructor
  · rcases Nat.eq_or_lt_of_le hlc with heq | hlt
    · exact Or.inl heq.symm
    · right
      have hmin := Nat.find_min hp (m := Nat.find hp - 1) (by omega)
      have hle : u (Nat.find hp - 1) ≤ u (Nat.find hp) := hu (by omega)
      have hne : u (Nat.find hp - 1) ≠ u a := fun h => hmin ⟨by omega, h⟩
      omega
  · have hva : v a ≤ v (Nat.find hp) := hv hca
    omega

/-! ## Threshold inversions (closed-form jump points) -/

/-- **CEILING/MULTIPLICATION ADJUNCTION**: `⌈a/b⌉ ≤ c ↔ a ≤ b·c` for
    `b > 0`. This is the Galois connection making the staircase inversion
    exact: the minimal `n` with `a ≤ b·n` is precisely `⌈a/b⌉`. -/
theorem ceilDiv_le_iff {a b c : ℕ} (hb : 0 < b) :
    ceilDiv a b ≤ c ↔ a ≤ b * c := by
  unfold CPMMInvariants.ceilDiv
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hexp : (c + 1) * b = c * b + b := by ring
    have hge : (c + 1) * b ≤ a + b - 1 := by
      have : c * b + 1 ≤ a := by
        calc c * b + 1 = b * c + 1 := by ring_nf
          _ ≤ a := hlt
      omega
    have := (Nat.le_div_iff_mul_le hb).mpr hge
    omega
  · intro h
    have hlt : a + b - 1 < b * (c + 1) := by
      have : b * (c + 1) = b * c + b := by ring
      omega
    have := Nat.div_lt_iff_lt_mul hb |>.mpr (by linarith [hlt] : a + b - 1 < (c + 1) * b)
    omega

/-- **ZERO-FEE THRESHOLD INVERSION**: for `0 < x` and `t < y`, the output
    `⌊y·n/(x+n)⌋` reaches level `t` exactly when `n ≥ ⌈t·x/(y−t)⌉`.
    Cross-multiplying `t ≤ y·n/(x+n)` and cancelling `t·n` yields
    `t·x ≤ (y−t)·n`, then the ceiling adjunction inverts. -/
theorem le_swapOutput_iff {x y n t : ℕ} (hx : 0 < x) (hty : t < y) :
    t ≤ swapOutput x y n ↔ ceilDiv (t * x) (y - t) ≤ n := by
  unfold CPMMInvariants.swapOutput
  rw [Nat.le_div_iff_mul_le (by omega : 0 < x + n), ceilDiv_le_iff (by omega : 0 < y - t)]
  have hmul : (y - t) * n + t * n = y * n := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (le_of_lt hty)]
  have hexp : t * (x + n) = t * x + t * n := Nat.mul_add t x n
  constructor <;> intro h <;> linarith

/-- **FEE-AWARE THRESHOLD INVERSION** (the jump-point closed form): for
    `0 < x`, `t < y`, `f < 10⁴`, the fee-aware output reaches level `t`
    exactly at gross inputs

      a ≥ a_t := ⌈ ⌈t·x/(y−t)⌉ · 10⁴ / (10⁴−f) ⌉.

    Two ceiling divisions invert the two floors (fee staircase, output
    floor). This licenses O(1) computation of every jump point of the
    output staircase — the basis of exact jump-enumeration split routing. -/
theorem le_feeOut_iff {x y f a t : ℕ} (hx : 0 < x) (hty : t < y) (hf : f < 10000) :
    t ≤ feeOut x y f a ↔
      ceilDiv (ceilDiv (t * x) (y - t) * 10000) (10000 - f) ≤ a := by
  unfold feeOut
  rw [le_swapOutput_iff hx hty, netAmount_eq_floor a f (le_of_lt hf),
    Nat.le_div_iff_mul_le (by omega : (0:ℕ) < 10000),
    ceilDiv_le_iff (by omega : 0 < 10000 - f)]

/-! ## The two-pool candidate theorem -/

/-- **CANDIDATE COMPLETENESS (two pools)**: every split `a ∈ [lo, hi]` of
    the fee-aware objective `out₀(a) + out₁(D−a)` is weakly dominated by a
    candidate `c ≤ a` that is either `lo` or a jump point of `out₀`, with
    `out₀(c) = out₀(a)`. Hence an exact optimizer (including the leftmost
    tie-break) only needs to evaluate `{lo} ∪ {jump points of out₀}` —
    by `le_feeOut_iff` each jump point is `a_t` for its level `t`, so the
    candidate set is `{lo} ∪ {a_t : 1 ≤ t ≤ out₀(hi)}`, all closed-form. -/
theorem two_pool_split_candidate_complete
    (x₀ y₀ f₀ x₁ y₁ f₁ D : ℕ) (hf₀ : f₀ ≤ 10000) (hf₁ : f₁ ≤ 10000)
    (lo a : ℕ) (hla : lo ≤ a) :
    ∃ c, lo ≤ c ∧ c ≤ a ∧
      feeOut x₀ y₀ f₀ c = feeOut x₀ y₀ f₀ a ∧
      (c = lo ∨ feeOut x₀ y₀ f₀ (c - 1) < feeOut x₀ y₀ f₀ c) ∧
      feeOut x₀ y₀ f₀ a + feeOut x₁ y₁ f₁ (D - a)
        ≤ feeOut x₀ y₀ f₀ c + feeOut x₁ y₁ f₁ (D - c) :=
  staircase_leftmost_dominates
    (feeOut x₀ y₀ f₀) (fun a => feeOut x₁ y₁ f₁ (D - a))
    (feeOut_mono x₀ y₀ f₀ hf₀)
    (fun _ _ hab => feeOut_mono x₁ y₁ f₁ hf₁ (Nat.sub_le_sub_left hab D))
    lo a hla

/-- **JUMP POINTS ARE THE CLOSED FORMS**: a jump point `c` of the fee-aware
    staircase (with level `t = out(c)`) equals `a_t` exactly. Minimality of
    `c` among `{a : t ≤ out(a)}` pins it to the threshold of
    `le_feeOut_iff`. -/
theorem jump_point_closed_form {x y f c : ℕ} (hx : 0 < x) (hf : f < 10000)
    (hc : 0 < c)
    (hjump : feeOut x y f (c - 1) < feeOut x y f c) :
    c = ceilDiv (ceilDiv (feeOut x y f c * x) (y - feeOut x y f c) * 10000)
          (10000 - f) := by
  set t := feeOut x y f c with ht
  -- t ≥ 1 from the strict jump.
  have ht1 : 1 ≤ t := by omega
  -- The output never exceeds the reserve: t ≤ y.
  have hle : t ≤ y := by
    rw [ht]
    exact AntiFragmentation.swapOut_le_reserve x y (netAmount c f)
  -- The output is strictly below the reserve: t < y.
  have hty : t < y := by
    by_contra hge
    push_neg at hge
    -- y ≤ t = ⌊y·net/(x+net)⌋ cross-multiplies to y·x ≤ 0, forcing y = 0,
    -- which contradicts 1 ≤ t ≤ y.
    have hdiv : y ≤ y * netAmount c f / (x + netAmount c f) := by
      have h := hge
      rw [ht] at h
      unfold feeOut CPMMInvariants.swapOutput at h
      exact h
    have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < x + netAmount c f)).mp hdiv
    have hexp : y * (x + netAmount c f) = y * x + y * netAmount c f :=
      Nat.mul_add y x _
    have hsum : y * x + y * netAmount c f ≤ y * netAmount c f := by
      rw [← hexp]; exact hmul
    have hyx : y * x = 0 := by omega
    rcases Nat.mul_eq_zero.mp hyx with h | h <;> omega
  -- Minimality: c satisfies the threshold, c − 1 does not.
  have h1 : ceilDiv (ceilDiv (t * x) (y - t) * 10000) (10000 - f) ≤ c :=
    (le_feeOut_iff hx hty hf).mp (le_of_eq ht)
  have h2 : ¬ ceilDiv (ceilDiv (t * x) (y - t) * 10000) (10000 - f) ≤ c - 1 := by
    intro hle
    have := (le_feeOut_iff hx hty hf).mpr hle
    omega
  omega

/-! ## k-pool generalization: the snapping lemma

The two-pool candidate theorem extends to any number of pools. Fix one
"absorber" pool; every other pool's allocation can be snapped down to the
left end of its output-level segment (a jump point or 0) and the freed
budget handed to the absorber. Monotonicity makes this weakly improving,
and the snapped coordinates all lie on the closed-form jump grids of
`le_feeOut_iff`. This licenses exact k-pool optimizers that search jump
grids (or run DP over output levels) instead of scanning the full
allocation simplex. -/

/-- Total output of an allocation: Σ uᵢ(aᵢ), pools paired positionally. -/
def allocValue : List (ℕ → ℕ) → List ℕ → ℕ
  | u :: us, a :: as => u a + allocValue us as
  | _, _ => 0

/-- **SNAPPING LEMMA (k pools)**: for monotone staircases `u₀, u₁, …, uₖ`
    and any allocation `(a₀, as)`, there is an allocation `(b₀, bs)` with
    the same total budget and weakly larger total output in which EVERY
    non-absorber coordinate is 0 or a jump point of its own staircase.
    Hence the optimum over the budget simplex is attained on the product of
    closed-form jump grids (one coordinate absorbing the slack). -/
theorem multi_pool_snap_dominates (u₀ : ℕ → ℕ) (hu₀ : Monotone u₀) :
    ∀ us : List (ℕ → ℕ), (∀ u ∈ us, Monotone u) →
    ∀ as : List ℕ, as.length = us.length → ∀ a₀ : ℕ,
    ∃ (b₀ : ℕ) (bs : List ℕ),
      bs.length = us.length ∧
      b₀ + bs.sum = a₀ + as.sum ∧
      (∀ p ∈ bs.zip us, p.1 = 0 ∨ p.2 (p.1 - 1) < p.2 p.1) ∧
      u₀ a₀ + allocValue us as ≤ u₀ b₀ + allocValue us bs := by
  intro us
  induction us with
  | nil =>
    intro _ as hlen a₀
    have has : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst has
    exact ⟨a₀, [], rfl, rfl, by simp, le_refl _⟩
  | cons u us ih =>
    intro hmono as hlen a₀
    cases as with
    | nil => simp at hlen
    | cons a as' =>
      have hu : Monotone u := hmono u List.mem_cons_self
      have hmono' : ∀ v ∈ us, Monotone v := fun v hv => hmono v (List.mem_cons_of_mem _ hv)
      have hlen' : as'.length = us.length := by simpa using hlen
      -- Snap `a` to the left end of its u-level (two-pool lemma with v ≡ 0).
      obtain ⟨c, -, hca, hcu, hjump, -⟩ :=
        staircase_leftmost_dominates u (fun _ => 0) hu
          (fun _ _ _ => le_refl 0) 0 a (Nat.zero_le a)
      -- Recurse on the tail, absorbing the slack a − c into the head pool.
      obtain ⟨b₀, bs, hlenb, hsum, hjumps, hval⟩ := ih hmono' as' hlen' (a₀ + (a - c))
      use b₀
      use c :: bs
      constructor
      · simpa using hlenb
      constructor
      · -- budget: b₀ + (c + bs.sum) = a₀ + (a + as'.sum)
        simp only [List.sum_cons]
        omega
      constructor
      · -- every snapped coordinate is 0 or a jump point
        intro p hp
        rw [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hjump
        · exact hjumps p hp
      · -- value: monotone absorption beats the original
        have habs : u₀ a₀ ≤ u₀ (a₀ + (a - c)) := hu₀ (Nat.le_add_right _ _)
        simp only [allocValue]
        rw [hcu]
        omega

/-- Witness (3 pools, zero fee, x=50, y=100): allocation (10, [33, 17])
    snaps to (11, [32, 17]) — coordinate 33 sits inside the level segment
    [32, 33] (out = 39), so it snaps to 32 and the absorber takes the
    slack; 17 is already a jump point. Total output improves 80 → 82. -/
theorem witness_multi_pool_snap :
    feeOut 50 100 0 32 = feeOut 50 100 0 33 ∧
    feeOut 50 100 0 16 < feeOut 50 100 0 17 ∧
    10 + (33 + 17) = 11 + (32 + 17) ∧
    feeOut 50 100 0 10 + (feeOut 50 100 0 33 + feeOut 50 100 0 17)
      ≤ feeOut 50 100 0 11 + (feeOut 50 100 0 32 + feeOut 50 100 0 17) := by
  decide

/-! ## Non-vacuity witnesses -/

/-- Witness: pool (x=1000, y=1000, f=30 bps). Output level t = 5 is first
    reached at a_5 = ⌈⌈5·1000/995⌉·10⁴/9970⌉ = ⌈6·10⁴/9970⌉ = 7, and indeed
    out(7) ≥ 5 > out(6). -/
theorem witness_jump_closed_form :
    feeOut 1000 1000 30 7 ≥ 5 ∧
    feeOut 1000 1000 30 6 < 5 ∧
    ceilDiv (ceilDiv (5 * 1000) (1000 - 5) * 10000) (10000 - 30) = 7 := by
  decide

/-- Witness: the staircase dominance is non-trivial — for pools
    (x₀=50, y₀=100, f₀=0) and (x₁=50, y₁=100, f₁=0) with D = 60, the
    objective at a = 33 is dominated by the jump candidate c = 32 with the
    same out₀ value (the level segment's left end: out₀(31)=38 < out₀(32)=
    out₀(33)=39). -/
theorem witness_staircase_dominance :
    feeOut 50 100 0 32 = feeOut 50 100 0 33 ∧
    feeOut 50 100 0 31 < feeOut 50 100 0 32 ∧
    feeOut 50 100 0 33 + feeOut 50 100 0 (60 - 33)
      ≤ feeOut 50 100 0 32 + feeOut 50 100 0 (60 - 32) := by
  decide

end SplitRoutingStaircase
end Proofs
