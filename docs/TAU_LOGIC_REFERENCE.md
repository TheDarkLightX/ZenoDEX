# ZenoDex Tau Specification Logic Reference

This document translates Tau Language specifications into standard mathematical logic notation and plain English. It serves as:
- **Internal reference** for developers and AI assistants understanding spec semantics
- **External documentation** for auditors and reviewers unfamiliar with Tau syntax
- **Cross-validation tool** to verify specs express intended invariants

---

## Logic Symbol Legend

### Propositional Logic

| Symbol | Name | Tau Syntax | Meaning | Example |
|--------|------|------------|---------|---------|
| ∧ | Conjunction | `&&` | "and" - both must be true | `A ∧ B` = "A and B" |
| ∨ | Disjunction | `\|\|` | "or" - at least one true | `A ∨ B` = "A or B" |
| ¬ | Negation | `!` | "not" - inverts truth value | `¬A` = "not A" |
| → | Implication | `->` | "if...then" - antecedent implies consequent | `A → B` = "if A then B" |
| ↔ | Biconditional | `<->` | "if and only if" - both directions | `A ↔ B` = "A iff B" |

### Predicate Logic

| Symbol | Name | Meaning | Example |
|--------|------|---------|---------|
| ∀ | Universal | "for all" | `∀x: P(x)` = "for all x, P holds" |
| ∃ | Existential | "there exists" | `∃x: P(x)` = "there exists an x where P holds" |

### Temporal Logic

| Symbol | Name | Tau Syntax | Meaning | Example |
|--------|------|------------|---------|---------|
| □ | Always | `always` | "at all times" | `□P` = "P is always true" |
| ◇ | Eventually | (derived) | "at some future time" | `◇P` = "P will eventually be true" |
| [t] | Time index | `[t]` | "at time t" | `P[t]` = "P at time t" |

### Comparison & Arithmetic

| Symbol | Name | Tau Syntax | Meaning |
|--------|------|------------|---------|
| = | Equality | `=` | "equals" |
| ≠ | Inequality | `!=` | "not equal to" |
| < | Less than | `<` | "strictly less than" |
| ≤ | Less or equal | `<=` | "less than or equal to" |
| > | Greater than | `>` | "strictly greater than" |
| ≥ | Greater or equal | `>=` | "greater than or equal to" |
| · | Multiplication | `*` | "times" |
| + | Addition | `+` | "plus" |
| − | Subtraction | `-` | "minus" |
| ⌊x⌋ | Floor | (computed externally) | "round down" |

### Set Theory

| Symbol | Name | Meaning | Example |
|--------|------|---------|---------|
| ∈ | Element of | "is a member of" | `x ∈ S` = "x is in set S" |
| ⊆ | Subset | "is contained in" | `A ⊆ B` = "A is a subset of B" |
| ∅ | Empty set | "nothing" | `S = ∅` = "S is empty" |

### Common Abbreviations

| Abbreviation | Expansion |
|--------------|-----------|
| bps | Basis points (1 bps = 0.01%) |
| k | Constant product invariant (x · y) |
| Δ | Delta (change/difference) |

---

## How to Read This Document

Each specification entry follows this format:

```
### Spec Name
**File:** `path/to/spec.tau`
**Purpose:** What this spec validates

**Logic Notation:**
[Standard mathematical logic]

**Plain English:**
[Human-readable explanation]

**Key Invariant:**
[The core property being enforced]
```

---

## Core DEX Specifications

### CPMM Swap Validity
**File:** `src/tau_specs/recommended/cpmm_v1.tau`
**Purpose:** Validates swap parameters for constant-product market maker

**Logic Notation:**
```
□ (SWAP_VALID[t] ↔
    (reserve_in > 0) ∧
    (reserve_out > 0) ∧
    (amount_in > 0) ∧
    (0 ≤ fee_bps ≤ 10000) ∧
    (amount_out > 0) ∧
    (amount_out ≤ reserve_out))
```

**Plain English:**
> At all times, a swap is valid if and only if:
> 1. The input reserve is positive (pool has tokens to receive)
> 2. The output reserve is positive (pool has tokens to give)
> 3. The input amount is positive (non-zero swap)
> 4. The fee is between 0 and 10000 basis points (0% to 100%)
> 5. The output amount is positive (user receives something)
> 6. The output amount does not exceed the output reserve (can't drain more than exists)

**Key Invariant:** `amount_out ≤ reserve_out` — you cannot withdraw more than the pool contains.

---

### Balance Safety
**File:** `src/tau_specs/recommended/balance_safety_v1.tau`
**Purpose:** Ensures all balance components are non-negative

**Logic Notation:**
```
□ (BALANCE_SAFE[t] ↔
    (balance ≥ 0) ∧
    (delta_add ≥ 0) ∧
    (delta_sub ≥ 0))
```

**Plain English:**
> At all times, a balance operation is safe if and only if:
> 1. The current balance is non-negative
> 2. The amount being added is non-negative
> 3. The amount being subtracted is non-negative

**Key Invariant:** All balance values must be non-negative — no negative money.

---

### Batch Canonical Ordering
**File:** `src/tau_specs/recommended/batch_canonical_v1_4.tau`
**Purpose:** Enforces deterministic ordering of batch intents

**Logic Notation:**
```
□ (BATCH_CANONICAL[t] ↔ (id₀ < id₁ < id₂ < id₃))
```

**Plain English:**
> At all times, a batch is canonically ordered if and only if:
> - Intent IDs are strictly increasing: first < second < third < fourth

**Key Invariant:** Strict ordering eliminates sequencer manipulation — the order is determined solely by intent IDs, not by who processes the batch.

---

### Batch Execution Validity
**File:** `src/tau_specs/recommended/batching_v1_4.tau`
**Purpose:** Validates batch execution matches canonical ordering

**Logic Notation:**
```
□ (BATCH_VALID[t] ↔
    DISTINCT(id₀, id₁, id₂, id₃) ∧
    ∀i ∈ {0,1,2,3}: exec_i ∈ {id₀, id₁, id₂, id₃} ∧
    (exec₀ < exec₁ < exec₂ < exec₃))
```

Where `DISTINCT(a,b,c,d)` means:
```
(a ≠ b) ∧ (a ≠ c) ∧ (a ≠ d) ∧ (b ≠ c) ∧ (b ≠ d) ∧ (c ≠ d)
```

**Plain English:**
> At all times, batch execution is valid if and only if:
> 1. All intent IDs in the batch are distinct (no duplicates)
> 2. Each executed ID is a member of the original intent set
> 3. Execution order is strictly increasing

**Key Invariant:** Executed IDs must be a strictly-ordered permutation of input IDs — prevents reordering attacks.

---

## Governance Specifications

### Governance Timelock
**File:** `src/tau_specs/recommended/governance_timelock_v1.tau`
**Purpose:** Enforces minimum delay before governance actions execute

**Logic Notation:**
```
□ (DELAY_ELAPSED[t] ↔ (current_ts ≥ proposal_ts) ∧ (current_ts − proposal_ts ≥ min_delay))

□ (EXECUTION_VALID[t] ↔ DELAY_ELAPSED[t] ∧ exec_requested)

□ (GOVERNANCE_SAFE[t] ↔ (¬exec_requested ∨ DELAY_ELAPSED[t]))
```

**Plain English:**
> - **Delay elapsed:** The current time is at or after the proposal time, AND enough time has passed (at least min_delay)
> - **Execution valid:** The delay has elapsed AND execution was requested
> - **Governance safe:** Either no execution was requested, OR the delay has elapsed

**Key Invariant:** `exec_requested → DELAY_ELAPSED` — cannot execute a proposal before the timelock expires.

---

### Parameter Registry
**File:** `src/tau_specs/recommended/parameter_registry_v1.tau`
**Purpose:** Applies parameter updates only when approved

**Logic Notation:**
```
□ (GATE_OK[t] ↔ (exec_req = 1) ∧ (revision_ok = 1))

∀param: □ (applied[t] = (GATE_OK[t] → next) ∧ (¬GATE_OK[t] → current))
```

**Plain English:**
> - The update gate opens only when BOTH execution is requested AND revision is approved
> - For each parameter: if gate is open, use the new value; otherwise keep the current value

**Key Invariant:** Parameters only update when explicitly approved — no silent changes.

---

## Tokenomics Specifications

### Rate Calculation (BPS)
**File:** `src/tau_specs/recommended/tokenomics_rate_bps_32_v1.tau`
**Purpose:** Validates basis-point rate calculations with overflow protection

**Logic Notation:**
```
□ (RATE_IN_RANGE[t] ↔ (rate ≤ 10000) ∧ (rate ≤ cap))

□ (RATE_CALC_OK[t] ↔
    (out · 10000 ≥ base · rate) ∧
    (out · 10000 ≤ base · rate + 9999))

□ (CAPS_OK[t] ↔ (out ≤ base) ∧ (out ≤ out_cap))

□ (RATE_MODULE_OK[t] ↔ RATE_IN_RANGE ∧ RATE_CALC_OK ∧ CAPS_OK ∧ SAFE_RANGE)
```

**Plain English:**
> - **Rate in range:** Rate is at most 10000 bps (100%) and within the configured cap
> - **Rate calculation:** Output equals ⌊base × rate / 10000⌋ with tolerance for rounding
> - **Caps:** Output doesn't exceed base amount or the configured cap
> - **Module OK:** All checks pass AND values are in safe multiplication range

**Key Invariant:** `out = ⌊base × rate / 10000⌋` — precise BPS math with bounded rounding error.

---

### Fee Split
**File:** `src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau`
**Purpose:** Validates fee distribution across buyback, treasury, and rewards

**Logic Notation:**
```
□ (SHARES_SUM_OK[t] ↔ (buyback_bps + treasury_bps + rewards_bps = 10000))

∀bucket: □ (COMPONENT_OK[t] ↔
    (component · 10000 ≥ fee · share) ∧
    (component · 10000 ≤ fee · share + 9999))

□ (SPLIT_SUM_OK[t] ↔
    (buyback + treasury + rewards ≤ fee) ∧
    (buyback + treasury + rewards + 2 ≥ fee))
```

**Plain English:**
> - **Shares sum:** Buyback + treasury + rewards shares must total exactly 10000 bps (100%)
> - **Component calculation:** Each bucket receives ⌊fee × share / 10000⌋ (with rounding tolerance)
> - **Split sum:** Total distributed equals fee minus at most 2 units rounding loss

**Key Invariant:** `Σ(shares) = 100%` and `Σ(components) ≈ fee` — fees are fully allocated with minimal rounding loss.

---

### Buyback Floor
**File:** `src/tau_specs/recommended/tokenomics_buyback_floor_32_v1.tau`
**Purpose:** Validates buyback-and-burn respects minimum supply floor

**Logic Notation:**
```
□ (BUYBACK_CALC_OK[t] ↔
    (buyback · 10000 ≥ fee · share) ∧
    (buyback · 10000 ≤ fee · share + 9999))

□ (BURN_AMOUNT_OK[t] ↔ burn ≤ buyback)

□ (FLOOR_OK[t] ↔
    (supply_before ≥ burn) ∧
    (supply_after = supply_before − burn) ∧
    (supply_after ≥ floor))
```

**Plain English:**
> - **Buyback calculation:** Buyback amount follows BPS math
> - **Burn bound:** Cannot burn more than what was bought back
> - **Floor protection:** After burning, supply must remain at or above the minimum floor

**Key Invariant:** `supply_after ≥ floor` — token supply never drops below the configured minimum.

---

### Usage Rebate
**File:** `src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau`
**Purpose:** Ties rebates to actual protocol usage, not passive holding

**Logic Notation:**
```
□ (USAGE_OK[t] ↔ (usage_score ≥ min_usage) ∧ (rebate ≤ usage_score))

□ (REBATE_MATH_OK[t] ↔
    (rate ≤ 10000) ∧
    (rebate · 10000 ≥ fee · rate) ∧
    (rebate · 10000 ≤ fee · rate + 9999))

□ (CAP_OK[t] ↔ rebate ≤ rebate_cap)
```

**Plain English:**
> - **Usage gate:** User must have usage score at least min_usage, and rebate cannot exceed usage
> - **Rebate math:** Rebate follows BPS calculation from fees
> - **Cap:** Rebate cannot exceed the configured maximum

**Key Invariant:** `usage_score ≥ min_usage` — only active users receive rebates, preventing sybil farming.

---

## Safety Specifications

### Circuit Breaker
**File:** `src/tau_specs/recommended/circuit_breaker_v1.tau`
**Purpose:** Halts trading when price deviates beyond threshold

**Logic Notation:**
```
□ (DEVIATION_OK[t] ↔ |price_current − price_reference| · 10000 ≤ price_reference · max_deviation_bps)

□ (COOLDOWN_OK[t] ↔ cooldown_elapsed = 1)

□ (CIRCUIT_BREAKER_OK[t] ↔ PARAMS_OK ∧ DEVIATION_OK ∧ COOLDOWN_OK)
```

**Plain English:**
> - **Deviation check:** The percentage difference between current and reference price must be within max_deviation_bps
> - **Cooldown:** The cooldown period must have elapsed before trading can resume
> - **Circuit breaker OK:** All parameters valid, deviation within bounds, cooldown satisfied

**Key Invariant:** Trading halts if `|Δprice| > threshold%` — protects against flash crashes and manipulation.

---

### Rate Limiter
**File:** `src/tau_specs/recommended/rate_limiter_v1.tau`
**Purpose:** Limits transaction frequency to prevent spam

**Logic Notation:**
```
□ (LIMIT_OK[t] ↔ tx_limit > 0)

□ (COUNT_WITHIN_LIMIT[t] ↔ tx_count ≤ tx_limit)

□ (RATE_LIMIT_OK[t] ↔ LIMIT_OK ∧ (COUNT_WITHIN_LIMIT ∨ window_reset))
```

**Plain English:**
> - **Limit valid:** Transaction limit must be positive
> - **Count check:** Current transaction count must be at or below the limit
> - **Rate limit OK:** Either count is within limit, OR the rate-limit window has reset

**Key Invariant:** `tx_count ≤ tx_limit` per window — prevents DoS via transaction spam.

---

### Oracle Freshness
**File:** `src/tau_specs/recommended/oracle_freshness_v2.tau`
**Purpose:** Validates oracle data is fresh and monotonically increasing

**Logic Notation:**
```
□ (FRESHNESS_OK[t] ↔ (current_ts − oracle_ts) ≤ max_staleness)

□ (MONOTONIC_OK[t] ↔ oracle_ts > prev_oracle_ts)

□ (JUMP_BOUNDED[t] ↔ (oracle_ts − prev_oracle_ts) ≤ max_jump)

□ (ORACLE_V2_OK[t] ↔ PARAMS_OK ∧ FRESHNESS_OK ∧ MONOTONIC_OK ∧ JUMP_BOUNDED)
```

**Plain English:**
> - **Freshness:** Oracle timestamp must be within max_staleness of current time
> - **Monotonic:** New oracle timestamp must be strictly greater than previous
> - **Jump bounded:** Timestamp jump cannot exceed max_jump (prevents manipulation)
> - **Oracle OK:** All conditions satisfied

**Key Invariant:** `current − oracle ≤ stale_max` ∧ `oracle > prev` — oracle data is fresh and progresses forward.

---

### Flash Loan Guard
**File:** `src/tau_specs/recommended/flash_loan_guard_v1.tau`
**Purpose:** Prevents flash loan attack patterns

**Logic Notation:**
```
□ (FLASH_PATTERN_DETECTED[t] ↔
    (has_borrow = 1) ∧ (has_trade = 1) ∧ (has_repay = 1) ∧ (same_context = 1))

□ (FLASH_LOAN_SAFE[t] ↔ ¬FLASH_PATTERN_DETECTED[t])
```

**Plain English:**
> - **Flash pattern:** Detected when borrow, trade, AND repay all occur in the same atomic context
> - **Flash loan safe:** The dangerous pattern is NOT detected

**Key Invariant:** `¬(borrow ∧ trade ∧ repay ∧ same_context)` — critical operations must span multiple atomic contexts.

---

### Nonce Replay Guard
**File:** `src/tau_specs/recommended/nonce_replay_guard_v1.tau`
**Purpose:** Prevents replay of signed intents

**Logic Notation:**
```
□ (EXPECTED_OK[t] ↔ expected_nonce = last_used + 1)

□ (NONCE_FRESH[t] ↔ intent_nonce > last_used)

□ (NONCE_SEQUENTIAL[t] ↔ intent_nonce = expected_nonce)

□ (NONCE_REPLAY_OK[t] ↔ EXPECTED_OK ∧ NONCE_FRESH ∧ NONCE_SEQUENTIAL)
```

**Plain English:**
> - **Expected calculation:** Next expected nonce is last_used + 1
> - **Nonce fresh:** Intent nonce must be strictly greater than last used
> - **Sequential:** Intent nonce must exactly equal the expected value
> - **Replay OK:** Nonce is fresh and follows the exact sequence

**Key Invariant:** `nonce = last + 1` — strict sequential nonces prevent replay attacks.

---

### Slippage Protection
**File:** `src/tau_specs/recommended/slippage_protection_v1.tau`
**Purpose:** Ensures swap execution stays within user's tolerance

**Logic Notation:**
```
□ (MIN_AMOUNT_OK[t] ↔ actual · 10000 ≥ expected · (10000 − slippage_bps))

□ (MAX_AMOUNT_OK[t] ↔ actual · 10000 ≤ expected · (10000 + slippage_bps))

□ (SLIPPAGE_OK[t] ↔ PARAMS_OK ∧ MIN_AMOUNT_OK ∧ MAX_AMOUNT_OK)
```

**Plain English:**
> - **Minimum check:** Actual output is at least expected × (1 − slippage%)
> - **Maximum check:** Actual output is at most expected × (1 + slippage%)
> - **Slippage OK:** Actual output is within the slippage band around expected

**Key Invariant:** `expected · (1 − s) ≤ actual ≤ expected · (1 + s)` — user receives within their tolerance.

---

### Sandwich Detection
**File:** `src/tau_specs/recommended/sandwich_detection_v1.tau`
**Purpose:** Detects sandwich attack patterns via price movements

**Logic Notation:**
```
□ (FRONT_IMPACT_OK[t] ↔ |price_after_front − price_before| · 10000 ≤ price_before · max_impact_bps)

□ (BACK_IMPACT_OK[t] ↔ |price_after_back − price_after_target| · 10000 ≤ price_after_target · max_impact_bps)

□ (SANDWICH_SAFE[t] ↔ PARAMS_OK ∧ FRONT_IMPACT_OK ∧ BACK_IMPACT_OK)
```

**Plain English:**
> - **Front-run check:** Price movement before target transaction is within bounds
> - **Back-run check:** Price movement after target transaction is within bounds
> - **Sandwich safe:** No excessive price impact from surrounding transactions

**Key Invariant:** Price movements around a transaction must be bounded — large movements indicate sandwich attacks.

---

### MEV Protection
**File:** `src/tau_specs/recommended/mev_protection_v1.tau`
**Purpose:** Detects front-running via gas price analysis

**Logic Notation:**
```
□ (PRIORITY_OK[t] ↔ priority_fee · 10000 ≤ base_fee · max_priority_bps)

□ (DELAY_OK[t] ↔ block_delay ≥ min_block_delay)

□ (MEV_SAFE[t] ↔ PARAMS_OK ∧ PRIORITY_OK ∧ DELAY_OK)
```

**Plain English:**
> - **Priority check:** Priority fee is not suspiciously high relative to base fee
> - **Delay check:** Sufficient blocks have passed between submission and execution
> - **MEV safe:** No indicators of front-running detected

**Key Invariant:** `priority / base ≤ threshold` ∧ `delay ≥ min` — abnormal gas or same-block execution suggests MEV.

---

## AMM Invariant Specifications

### Reserve Invariant (k-monotonicity)
**File:** `src/tau_specs/recommended/reserve_invariant_guard_v1.tau`
**Purpose:** Enforces constant-product k never decreases

**Logic Notation:**
```
Let k = x · y (constant product)

□ (K_OK[t] ↔ (x_before · y_before > 0) ∧ (x_after · y_after > 0))

□ (K_MONOTONIC[t] ↔ (x_after · y_after) ≥ (x_before · y_before))

□ (RESERVE_INVARIANT_OK[t] ↔ PARAMS_OK ∧ K_OK ∧ K_MONOTONIC)
```

**Plain English:**
> - **k valid:** Product of reserves is positive both before and after
> - **k monotonic:** The constant product after is greater than or equal to before
> - **Invariant OK:** k never decreases (only increases from fees)

**Key Invariant:** `k_after ≥ k_before` — the CPMM invariant can only grow (from fee accumulation), never shrink.

---

### LP Mint/Burn Proportionality
**File:** `src/tau_specs/recommended/lp_mint_burn_v1.tau`
**Purpose:** Validates LP token operations match liquidity changes

**Logic Notation:**
```
□ (PROPORTION_OK[t] ↔
    (lp_delta · total_liquidity ≥ liquidity_delta · total_lp) ∧
    (lp_delta · total_liquidity ≤ liquidity_delta · total_lp + total_lp))

□ (LP_MINT_BURN_OK[t] ↔ PARAMS_OK ∧ PROPORTION_OK ∧ DIRECTION_OK)
```

Equivalently:
```
lp_delta / total_lp ≈ liquidity_delta / total_liquidity
```

**Plain English:**
> - **Proportion check:** LP tokens minted/burned is proportional to liquidity added/removed
> - **Tolerance:** Rounding error of at most 1 LP token
> - **LP mint/burn OK:** The proportion matches (prevents inflation attacks)

**Key Invariant:** `Δlp / lp_total = Δliquidity / liquidity_total` — LP tokens are fair claims on underlying liquidity.

---

## Quick Reference: Tau ↔ Logic Mapping

| Tau Syntax | Logic Symbol | Example Tau | Example Logic |
|------------|--------------|-------------|---------------|
| `&&` | ∧ | `a && b` | `a ∧ b` |
| `\|\|` | ∨ | `a \|\| b` | `a ∨ b` |
| `!` | ¬ | `!a` | `¬a` |
| `->` | → | `a -> b` | `a → b` |
| `<->` | ↔ | `a <-> b` | `a ↔ b` |
| `always` | □ | `always P` | `□P` |
| `[t]` | subscript | `o1[t]` | `o1ₜ` or `o1[t]` |
| `= 1:sbf` | = ⊤ | `o1[t]:sbf = 1:sbf` | `o1[t] = true` |
| `= 0:sbf` | = ⊥ | `o1[t]:sbf = 0:sbf` | `o1[t] = false` |
| `bv[32]` | ℤ₃₂ | `x : bv[32]` | `x ∈ [0, 2³² − 1]` |
| `{ #x2710 }` | 10000 | `{ #x2710 }:bv[32]` | `10000` |

---

## Appendix: Understanding the Encoding

### Why bv[16] and bv[32]?
Tau uses bounded bitvectors for formal verification. `bv[16]` is a 16-bit unsigned integer, `bv[32]` is 32-bit.

To represent larger values (like 32-bit numbers in 16-bit registers), specs use high/low limb encoding:
```
value = (hi · 2¹⁶) + lo
```

When you see `reserve_in_hi` and `reserve_in_lo`, the actual reserve is `(hi << 16) | lo`.

### Why #x2710?
This is hexadecimal for 10000 — the denominator for basis points (bps).
- `#x2710` = 10000 decimal
- `#x270F` = 9999 decimal (rounding tolerance)
- `#x00068DB8` = 429496 decimal (max safe value for 32-bit BPS multiplication)

### The Safe Range Guard
To prevent overflow in `base × rate`, values must be ≤ 429496 (approximately 2³² ÷ 10000). The `max_safe_32()` constant enforces this.

---

## Document Maintenance

When adding new Tau specs:
1. Add an entry following the template above
2. Include the logic notation using standard symbols
3. Write plain English that a non-technical reader could understand
4. Identify the key invariant being enforced
5. Update the Quick Reference if new syntax patterns appear

---

*Generated for ZenoDex Tau Specification Suite*
*Last updated: 2026-01-19*
