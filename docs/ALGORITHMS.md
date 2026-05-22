# TauSwap Algorithm Design Documentation

This document provides detailed algorithm specifications with complexity analysis, invariants, and formal proofs.

## Table of Contents

1. [CPMM Algorithm](#cpmm-algorithm)
2. [Exact-Out Routing Gate](#exact-out-routing-gate)
3. [Batch Clearing Algorithm](#batch-clearing-algorithm)
4. [Liquidity Management](#liquidity-management)
5. [Settlement Validation](#settlement-validation)

---

## CPMM Algorithm

### Algorithm Blueprint

**Type:** Fixed-Point Integer Arithmetic / Deterministic Rounding

**Complexity:**
- Time: O(1) per swap operation
- Space: O(1) auxiliary

**Data Structures:**
- `uint256` for reserves and amounts (fixed-point with 18 decimals)
- Struct for pool state: `(reserve0, reserve1, k, lp_supply, fee_bps)`
- Deterministic rounding rules encoded as integer inequalities

**Formal Proofs:**
- **Invariant:** After each swap, `x' * y' >= k` (where `k = x * y` before swap, adjusted for fees)
- **Termination:** All operations are O(1) arithmetic with bounded integer operations

### Exact-In Swap

**Formula:**
```
fee = ceil(amount_in * fee_bps / 10_000)
net_in = amount_in - fee
amount_out = floor(reserve_out * net_in / (reserve_in + net_in))
```

**Post-swap reserves:**
```
new_reserve_in = reserve_in + amount_in  (fee stays in pool)
new_reserve_out = reserve_out - amount_out
```

**Invariant Preservation:**
- Before: `k = reserve_in * reserve_out`
- After: `k' = new_reserve_in * new_reserve_out`
- Proof: `k' >= k` because fee increases `reserve_in` and rounding down `amount_out` ensures `k'` doesn't decrease below `k`

**Rounding Rules (Consensus-Critical):**
- Fee: `ceil(amount_in * fee_bps / 10_000)` - ensures protocol collects at least expected fee
- Output: `floor(...)` - ensures pool doesn't give away more than invariant allows

### Exact-Out Swap

**Formula:**
```
net_in = ceil(reserve_in * amount_out / (reserve_out - amount_out))
amount_in = ceil(net_in / (1 - fee_bps/10_000))
```

**Integer Implementation:**
```
amount_in = (net_in * 10_000 + (10_000 - fee_bps) - 1) // (10_000 - fee_bps)
```

**Constraints:**
- `amount_out < reserve_out` (cannot drain full reserve)
- `amount_in <= max_amount_in` (user slippage constraint)

---

## Exact-Out Routing Gate

### Algorithm Blueprint

**Type:** Deterministic adaptive prefilter for exact-out 2-hop search

**Goal:** Reduce unnecessary 2-hop quote work while preserving most value-capturing 2-hop wins.

**Base Features:**
- `stress = amount_out / direct_reserve_out`
- `pressure = direct_amount_in / amount_out`

**Policies:**
- `stress`: trigger 2-hop when `stress >= stress_threshold`
- `stress_or_pressure`: trigger 2-hop when `stress >= stress_threshold OR pressure >= pressure_threshold`
- `stress_or_pressure_adaptive`:
  - trigger 2-hop when `stress >= stress_threshold`, or
  - `pressure >= pressure_threshold + pressure_slope * max(0, stress_threshold - stress)`
- `stress_or_pressure_piecewise`:
  - if `stress >= stress_threshold`: trigger
  - else if `stress >= piecewise_stress_cutoff`: `pressure >= piecewise_pressure_mid`
  - else: `pressure >= piecewise_pressure_low`
- `stress_or_pressure_piecewise_fee`:
  - if `stress >= stress_threshold`: trigger
  - else if `stress >= fee_piecewise_stress_cutoff`: `pressure >= fee_piecewise_pressure_mid`
  - else: `pressure >= fee_piecewise_pressure_low + fee_piecewise_fee_slope * (direct_fee_bps / 10_000)`
- `stress_or_pressure_tripiece`:
  - if `stress >= stress_threshold`: trigger
  - else if `stress >= tripiece_stress_upper_cutoff`: `pressure >= tripiece_pressure_upper_band`
  - else if `stress >= tripiece_stress_lower_cutoff`: `pressure >= tripiece_pressure_mid_band`
  - else: `pressure >= tripiece_pressure_low_base + tripiece_fee_slope * (direct_fee_bps / 10_000)`

The adaptive variant is stricter in low-stress regimes and converges to the base OR policy near/above stress threshold.
The piecewise variant introduces explicit low-stress bands so compute can be reduced in deep low-stress tails without changing deterministic semantics.

### What Improved vs Prior Methods

Compared on deterministic held-out sweeps (10 seeds, 4000 samples/seed), artifact:
`runs/manual_morph_supervised/h110_exact_out_adaptive_gate_sweep/metrics.json`.

- Baseline `stress_or_pressure`:
  - capture rate mean: `0.9798`
  - avg quote calls: `1.9611`
- New `stress_or_pressure_adaptive` (slope `1.2`):
  - capture rate mean: `0.9759`
  - avg quote calls: `1.8494`

Delta (adaptive vs baseline):
- compute/cost: about `5.7%` fewer quote calls
- execution quality: about `0.38` percentage-point capture decrease

This point is non-dominated in the observed frontier and provides a better performance/quality balance than stress-only gating for most runs.

Additional piecewise sweep (12 seeds, 4000 samples/seed), artifact:
`runs/manual_morph_supervised/h111_gate_functional_search/robustness_multi_seed.json`.

- Baseline `stress_or_pressure`:
  - capture rate mean: `0.97986`
  - avg quote calls: `1.96049`
- New `stress_or_pressure_piecewise` (`cutoff=0.1`, `mid=1.55`, `low=2.2`):
  - capture rate mean: `0.98021`
  - avg quote calls: `1.91006`

Delta (piecewise vs baseline):
- compute/cost: about `2.6%` fewer quote calls
- execution quality: about `0.035` percentage-point capture increase

In this bounded evaluation, piecewise dominates the plain OR baseline on both dimensions.

Retuned piecewise + fee-aware sweep (14 seeds, 4000 samples/seed), artifact:
`runs/manual_morph_supervised/h112_fee_aware_gate_search/robustness_multi_seed.json`.

- Previous piecewise (`0.1, 1.55, 2.2`):
  - capture mean: `0.98005`
  - avg calls: `1.91034`
- Retuned piecewise (`0.15, 1.5, 2.2`):
  - capture mean: `0.98005`
  - avg calls: `1.89734`
- Fee-aware piecewise (`0.12, 1.5, 2.3, slope=12`):
  - capture mean: `0.98061`
  - avg calls: `1.90797`

Interpretation:
- Retuned piecewise is the better low-cost default (same capture, fewer calls).
- Fee-aware piecewise is a higher-capture variant (slightly more calls than retuned piecewise, still fewer than plain OR).

Code-replay confirmation with implemented policies (10 seeds, 4000 samples/seed), artifact:
`runs/manual_morph_supervised/h112_fee_aware_gate_search/code_replay_metrics.json`.

- `stress_or_pressure`: capture `0.97977`, calls `1.96114`
- `stress_or_pressure_piecewise` (retuned default): capture `0.98010`, calls `1.89645`
- `stress_or_pressure_piecewise_fee` (default): capture `0.98069`, calls `1.90803`

Tri-band discovery sweep (16 seeds, 5000 samples/seed), artifact:
`runs/manual_morph_supervised/h113_hyper_gate_search/robustness_multi_seed.json`.

- Existing `stress_or_pressure_piecewise` (`piecewise_v2`):
  - capture mean: `0.97807`
  - avg calls: `1.87452`
- New `stress_or_pressure_tripiece` (`tripiece_v1`):
  - capture mean: `0.97853`
  - avg calls: `1.87200`

Delta (tripiece vs piecewise_v2):
- execution quality: `+0.046` percentage points capture
- compute/cost: `-0.00252` avg calls

This is a strict Pareto improvement in the bounded robustness run.

Code-replay confirmation with implemented `stress_or_pressure_tripiece` (12 seeds, 5000 samples/seed), artifact:
`runs/manual_morph_supervised/h113_hyper_gate_search/code_replay_metrics.json`.

- `stress_or_pressure_piecewise` (v2): capture `0.97770`, calls `1.87540`
- `stress_or_pressure_tripiece` (default): capture `0.97817`, calls `1.87295`

### Formal Obligations

Lean lemmas (compiled via `lake build Proofs`) in `lean-mathlib/Proofs/ExactOutAdaptiveGate.lean` establish:
- adaptive threshold is always at least the base pressure threshold when `slope >= 0`
- adaptive decision implies base OR decision when `slope >= 0`
- adaptive threshold is monotone in slope
- piecewise gate implies base OR gate under threshold constraints
- fee-aware piecewise gate implies base OR gate when low-band base threshold and fee slope are nonnegative
- tri-piece gate implies base OR gate when band thresholds and fee slope assumptions hold

These properties keep the mechanism deterministic and interpretable under parameter changes.

---

## Batch Clearing Algorithm

### Algorithm Blueprint

**Type:** Greedy Monotone Processing / Constrained Optimization

**Complexity:**
- Time: O(n log n) for sorting + O(n) for processing, where n = number of intents
- Space: O(n) for intent storage and delta tracking

**Data Structures:**
- Sorted array of intents (by limit price, then intent_id for determinism)
- Delta tracking:
  - `BalanceDelta[pubkey, asset] = (add, sub)`
  - `ReserveDelta[pool_id, asset] = (add, sub)`
  - `LPDelta[pubkey, pool_id] = (add, sub)`

**Formal Proofs:**
- **Invariant:** After processing intent i, total deltas satisfy conservation: `Σ_account_deltas + Σ_pool_deltas = 0` (per asset)
- **Termination:** Bounded loop over sorted intents, each iteration processes exactly one intent

### Algorithm Steps

1. **Group intents by pool_id**
   - Separate pool-specific intents from non-pool intents (CREATE_POOL, etc.)

2. **Sort intents deterministically**
   - For swaps: sort by effective limit price (best first)
   - Tie-break by `intent_id` for determinism
   - Limit price calculation:
     - SWAP_EXACT_IN: `min_amount_out / amount_in` (higher is better)
     - SWAP_EXACT_OUT: `amount_out / max_amount_in` (higher is better)

3. **Process intents sequentially**
   - For each intent, compute fill using CPMM formulas
   - Check slippage constraints
   - Update reserves after each fill
   - Accumulate deltas

4. **Aggregate deltas across all pools**
   - Combine balance deltas, reserve deltas, LP deltas

5. **Verify global conservation and non-negativity**
   - Per-asset: `Σ_account_deltas + Σ_pool_deltas = 0`
   - All balances and reserves remain non-negative

### Determinism Guarantee

The algorithm is deterministic because:
- Sorting uses fixed comparison: `(limit_price, intent_id)`
- Processing order is fixed: sorted order
- CPMM calculations are deterministic (fixed rounding rules)
- No external randomness or time-dependent behavior

---

## Liquidity Management

### Create Pool

**LP Minting Formula (First Deposit):**
```
lp = floor(sqrt(amount0 * amount1)) - MIN_LP_LOCK
```

Where `MIN_LP_LOCK = 1000` prevents division-by-zero attacks.

**Pool ID Derivation:**
```
pool_id = H("TauSwapPool" || asset0 || asset1 || fee_bps || "CPMM" || "")
```

This ensures deterministic pool IDs across all nodes.

### Add Liquidity

**LP Minting Formula (Subsequent Deposits):**
```
lp = min(
    floor(amount0_used * lp_supply / reserve0),
    floor(amount1_used * lp_supply / reserve1)
)
```

**Ratio Constraint:**
The settlement must choose `(amount0_used, amount1_used)` such that:
```
amount0_used / amount1_used = reserve0 / reserve1
```
(within integer rounding constraints)

### Remove Liquidity

**Output Formula:**
```
amount0_out = floor(lp_amount * reserve0 / lp_supply)
amount1_out = floor(lp_amount * reserve1 / lp_supply)
```

**Constraints:**
- `lp_amount <= lp_supply`
- `amount0_out >= amount0_min`
- `amount1_out >= amount1_min`

---

## Settlement Validation

### Validation Rules

1. **Intent Coverage**
   - Every intent in the block must be in `included_intents`
   - Each intent must have exactly one entry (FILL or REJECT)

2. **Fill Consistency**
   - Every FILL action must have a corresponding fill detail
   - Fill details must match intent constraints

3. **Balance Non-Negativity**
   ```
   forall delta in balance_deltas:
       balance[delta.pubkey, delta.asset] + delta.net() >= 0
   ```

4. **Reserve Non-Negativity**
   ```
   forall delta in reserve_deltas:
       reserve[delta.pool_id, delta.asset] + delta.net() >= 0
   ```

5. **Asset Conservation**
   ```
   forall asset:
       Σ_account_deltas(asset) + Σ_pool_deltas(asset) = 0
   ```

6. **LP Conservation**
   ```
   forall pool_id:
       Σ_lp_deltas(pool_id) = Σ_lp_mints - Σ_lp_burns
   ```

7. **Price Protection**
   - SWAP_EXACT_IN: `amount_out >= min_amount_out`
   - SWAP_EXACT_OUT: `amount_in <= max_amount_in`

### Validation Complexity

- Time: O(n + m) where n = number of deltas, m = number of assets
- Space: O(m) for asset delta aggregation

---

## Security Considerations

### Overflow Prevention

All arithmetic operations use bounded integer types (uint256). Multiplication operations are checked to prevent overflow:
- CPMM: `k = reserve0 * reserve1` must fit in uint256
- Swap calculations: intermediate results checked before division

### Rounding Attacks

Deterministic rounding rules prevent manipulation:
- Fees rounded up (protocol benefits)
- Outputs rounded down (pool benefits)
- This ensures no value can be extracted through rounding

### Invariant Preservation

All operations preserve:
- CPMM invariant: `x * y >= k_min`
- Balance non-negativity
- Asset conservation

These invariants are checked both in Python (runtime) and Tau Language (formal verification).
