import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Fee Pipeline: Decay, Effective Fee, and Cross-Fee Coupling (H-RG-004)

## Key Property

zUSD uses a shared `base_rate_bps` that affects BOTH borrow fees and redemption
fees. This creates a cross-fee coupling vulnerability (H-RG-004): an attacker
minting repeatedly bumps `base_rate_bps`, which also inflates redemption fees
for all users.

This file formalizes:
- The decay function: `max(0, base_rate - decay_per_epoch * elapsed)`
- The effective fee: `min(min(floor + base_rate, max_bps), BPS_SCALE)`
- The runtime mint update: decay first, then bump, then cap at `BPS_SCALE`
- The cross-fee coupling: higher post-mint base rate → higher redemption fee (H-RG-004)
- Cost bookkeeping identities for sustained fee elevation attempts

## What This File Proves (8 substantive theorems)

### Decay properties (zusd.py:100-105)
1. **decay_nonneg**: Decayed base rate is always ≥ 0
2. **decay_monotone_elapsed**: More time elapsed → lower decayed rate
3. **decay_reaches_floor**: After enough time, rate reaches 0

### Effective fee properties (zusd.py:108-114)
4. **effective_fee_bounded**: fee ≤ min(max_bps, BPS_SCALE)
5. **effective_fee_mono_base**: Higher base rate → higher effective fee (up to cap)

### Cross-fee coupling — H-RG-004 (THE VULNERABILITY PROOF)
6. **post_mint_base_rate_eq_uncapped**: when not capped, mint updates to `decayed_rate + bump`
7. **post_mint_base_rate_strict_increase_of_room**: with positive bump and cap room, mint strictly raises the decayed base rate
8. **cross_fee_attack_total_cost_identity**: attack spend is linear in mint count

## Pattern
All arithmetic over ℤ (matching Python integer semantics).
The `min` function over ℤ is `Int.min` / standard `min`.
-/

namespace Proofs

namespace ZUSDFeePipeline

/-! ## Part 1: Decay Function

`_decayed_base_rate_bps` in zusd.py:100-105:
```python
elapsed = now_epoch - last_epoch
decay = decay_per_epoch_bps * elapsed
return max(0, base_rate_bps - decay)
```
-/

/-- Decayed base rate: max(0, base_rate - decay_rate × elapsed).
    Over ℤ for generality; returns ℕ-like (≥ 0) values. -/
def decayed_rate (base_rate decay_per_epoch elapsed : ℤ) : ℤ :=
  max 0 (base_rate - decay_per_epoch * elapsed)

/-- The decayed rate is always non-negative.
    This is immediate from the max(0, ...) definition, but
    it's the foundational safety property: fees can't go negative. -/
theorem decay_nonneg (base_rate decay_per_epoch elapsed : ℤ) :
    0 ≤ decayed_rate base_rate decay_per_epoch elapsed := by
  unfold decayed_rate
  exact le_max_left 0 _

/-- More time elapsed means lower (or equal) decayed rate.
    Proof: if decay_per_epoch ≥ 0 and e₁ ≤ e₂, then
    decay_per_epoch * e₂ ≥ decay_per_epoch * e₁, so the
    subtracted amount is larger, yielding smaller max(0, ...). -/
theorem decay_monotone_elapsed (base_rate decay_per_epoch e₁ e₂ : ℤ)
    (hd : 0 ≤ decay_per_epoch) (he : e₁ ≤ e₂) :
    decayed_rate base_rate decay_per_epoch e₂ ≤
    decayed_rate base_rate decay_per_epoch e₁ := by
  unfold decayed_rate
  -- decay_per_epoch * e₁ ≤ decay_per_epoch * e₂
  have h1 : decay_per_epoch * e₁ ≤ decay_per_epoch * e₂ :=
    mul_le_mul_of_nonneg_left he hd
  -- base_rate - bigger ≤ base_rate - smaller
  -- max(0, smaller_result) ≤ max(0, bigger_result) won't work — reverse
  -- We need max(0, B - large) ≤ max(0, B - small)
  exact max_le_max_left 0 (by linarith)

/-- After enough epochs, the rate reaches 0.
    Specifically, if decay_per_epoch * elapsed ≥ base_rate, then
    decayed_rate = 0.
    Proof: max(0, base_rate - decay) = max(0, non-positive) = 0. -/
theorem decay_reaches_floor (base_rate decay_per_epoch elapsed : ℤ)
    (h_enough : base_rate ≤ decay_per_epoch * elapsed) :
    decayed_rate base_rate decay_per_epoch elapsed = 0 := by
  unfold decayed_rate
  exact max_eq_left (by linarith)

/-! ## Part 2: Effective Fee Function

`_effective_fee_bps` in zusd.py:108-114:
```python
fee_bps = floor_bps + decayed_base_rate_bps
if fee_bps > max_bps: fee_bps = max_bps
if fee_bps > BPS_SCALE: fee_bps = BPS_SCALE
return fee_bps
```
This is: min(min(floor + base, max_bps), BPS_SCALE)
-/

/-- Effective fee: min(min(floor + base, max_bps), BPS_SCALE).
    The two min operations cap the fee at both the protocol maximum
    and the absolute ceiling of 100% (BPS_SCALE = 10000). -/
def effective_fee (floor_bps base_rate max_bps bps_scale : ℤ) : ℤ :=
  min (min (floor_bps + base_rate) max_bps) bps_scale

/-- Effective fee is bounded by both max_bps and BPS_SCALE.
    This is the core safety property: fees never exceed configured caps. -/
theorem effective_fee_bounded (floor_bps base_rate max_bps bps_scale : ℤ) :
    effective_fee floor_bps base_rate max_bps bps_scale ≤ max_bps ∧
    effective_fee floor_bps base_rate max_bps bps_scale ≤ bps_scale := by
  unfold effective_fee
  constructor
  · exact le_trans (min_le_left _ _) (min_le_right _ _)
  · exact min_le_right _ _

/-- Effective fee is monotone in base_rate (up to the caps).
    Higher base_rate → higher effective fee (or same if already at cap).
    This is THE bridge theorem for H-RG-004: it shows that
    increasing base_rate actually increases fees. -/
theorem effective_fee_mono_base (floor_bps b₁ b₂ max_bps bps_scale : ℤ)
    (hb : b₁ ≤ b₂) :
    effective_fee floor_bps b₁ max_bps bps_scale ≤
    effective_fee floor_bps b₂ max_bps bps_scale := by
  unfold effective_fee
  exact min_le_min_right bps_scale
    (min_le_min_right max_bps (by linarith))

/-! ## Part 3: Cross-Fee Coupling (H-RG-004)

THE VULNERABILITY: minting bumps `base_rate_bps`, which is shared
with the redemption fee channel. An attacker who mints repeatedly
inflates redemption fees for all other users.

The attack:
1. Attacker mints → base_rate_bps += borrow_bump_bps
2. Other users try to redeem → effective_fee is higher
3. Attacker pays borrow fees (proportional to borrow_bump_bps)
4. All redeemers pay inflated fees

This section formalizes that the attack WORKS (base rate increase
propagates to redemption fees) and isolates the bookkeeping identities
needed for a later cost lower-bound argument.
-/

/-- Runtime post-mint base rate: decay first, then add the borrow bump, then cap. -/
def post_mint_base_rate (base_rate decay_per_epoch elapsed bump bps_scale : ℤ) : ℤ :=
  min bps_scale (decayed_rate base_rate decay_per_epoch elapsed + bump)

/-- When the post-mint rate is below the cap, the runtime update is exactly
    `decayed_rate + bump`. This matches `mint_zusd` in `zusd.py`. -/
theorem post_mint_base_rate_eq_uncapped
    (base_rate decay_per_epoch elapsed bump bps_scale : ℤ)
    (hcap : decayed_rate base_rate decay_per_epoch elapsed + bump ≤ bps_scale) :
    post_mint_base_rate base_rate decay_per_epoch elapsed bump bps_scale =
      decayed_rate base_rate decay_per_epoch elapsed + bump := by
  unfold post_mint_base_rate
  exact min_eq_right hcap

/-- With a positive bump and room below the cap, the post-mint base rate is
    strictly larger than the decayed pre-mint rate. -/
theorem post_mint_base_rate_strict_increase_of_room
    (base_rate decay_per_epoch elapsed bump bps_scale : ℤ)
    (hbump : 0 < bump)
    (hcap : decayed_rate base_rate decay_per_epoch elapsed + bump ≤ bps_scale) :
    post_mint_base_rate base_rate decay_per_epoch elapsed bump bps_scale >
      decayed_rate base_rate decay_per_epoch elapsed := by
  rw [post_mint_base_rate_eq_uncapped _ _ _ _ _ hcap]
  linarith

/-- Higher base rate leads to higher redemption fee.
    Combined with `post_mint_base_rate_strict_increase_of_room`, this proves
    that minting can increase redemption fees — the H-RG-004 cross-fee vulnerability.

    This is a direct corollary of effective_fee_mono_base,
    but stated explicitly for the attack surface analysis. -/
theorem higher_base_means_higher_redeem_fee
    (redeem_floor base₁ base₂ max_bps bps_scale : ℤ)
    (h_bump : base₁ < base₂) :
    effective_fee redeem_floor base₁ max_bps bps_scale ≤
    effective_fee redeem_floor base₂ max_bps bps_scale :=
  effective_fee_mono_base redeem_floor base₁ base₂ max_bps bps_scale
    (le_of_lt h_bump)

/-- Bookkeeping identity for attack spend.
    This does not prove the lower bound for sustained fee elevation.
    It only records that total spend is non-negative and linear in the mint count. -/
theorem cross_fee_attack_total_cost_identity
    (K bump decay_per_epoch N per_mint_cost : ℤ)
    (hK : 0 ≤ K) (_hbump : 0 < bump) (_hdecay : 0 ≤ decay_per_epoch)
    (_hN : 0 ≤ N) (hcost : 0 < per_mint_cost) :
    -- Net elevation after K mints and N epochs of decay
    let _net_elevation := K * bump - decay_per_epoch * N
    -- Attacker's total cost
    let total_cost := K * per_mint_cost
    -- If attacker wants net_elevation > 0, then K > decay*N/bump,
    -- so total_cost > (decay*N/bump) * per_mint_cost
    -- We prove: total cost is non-negative and proportional to K
    0 ≤ total_cost ∧ total_cost = K * per_mint_cost := by
  simp only
  exact ⟨by nlinarith, trivial⟩

/-- The critical cross-fee inequality: if the bump-side numerator beats the
    decay-side numerator, multiplying by a positive per-mint cost preserves
    that strict inequality.

    This is still weaker than a full lower bound over mint counts. -/
theorem sustained_elevation_cost (K bump decay_per_epoch N per_mint_cost : ℤ)
    (hcost : 0 < per_mint_cost)
    (h_elevated : K * bump > decay_per_epoch * N) :
    K * bump * per_mint_cost > decay_per_epoch * N * per_mint_cost := by
  exact mul_lt_mul_of_pos_right h_elevated hcost

/-! ## Part 4: Non-Vacuity Witnesses -/

/-- Witness: decay with base=500, decay_rate=50, elapsed=8.
    max(0, 500 - 50*8) = max(0, 500 - 400) = 100. -/
theorem witness_decay :
    decayed_rate 500 50 8 = 100 := by
  unfold decayed_rate; omega

/-- Witness: decay reaches floor. base=500, decay_rate=50, elapsed=10.
    max(0, 500 - 50*10) = max(0, 0) = 0. -/
theorem witness_decay_floor :
    decayed_rate 500 50 10 = 0 := by
  unfold decayed_rate; omega

/-- Witness: effective fee. floor=50, base=200, max=500, scale=10000.
    min(min(50+200, 500), 10000) = min(min(250, 500), 10000) = 250. -/
theorem witness_effective_fee :
    effective_fee 50 200 500 10000 = 250 := by
  unfold effective_fee; omega

/-- Witness: effective fee cap. floor=50, base=600, max=500, scale=10000.
    min(min(650, 500), 10000) = min(500, 10000) = 500. -/
theorem witness_effective_fee_capped :
    effective_fee 50 600 500 10000 = 500 := by
  unfold effective_fee; omega

/-- Witness: uncapped post-mint update. With zero elapsed decay and bump=10,
    the runtime post-mint base rate moves from 0 to 10. -/
theorem witness_post_mint_base_rate :
    post_mint_base_rate 0 0 0 10 10000 = 10 := by
  unfold post_mint_base_rate decayed_rate
  omega

/-- Witness: cross-fee attack on the uncapped branch. The higher post-mint
    base rate lifts the redemption fee from 50 to 60. -/
theorem witness_cross_fee_attack :
    effective_fee 50 0 500 10000 = 50 ∧
    effective_fee 50 10 500 10000 = 60 ∧
    effective_fee 50 10 500 10000 > effective_fee 50 0 500 10000 := by
  unfold effective_fee; omega

end ZUSDFeePipeline

end Proofs
