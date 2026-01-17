# Ecosystem Archetypes and Composition Strategy

This document defines reusable spec archetypes ("lego blocks") and a strategy to connect them into a DEX and a broader deflationary DAC ecosystem. The goal is economic stickiness: users gain durable benefits for staying inside the ecosystem, and value flows are provably consistent with intent.

## Architectural Layers

1. **Primitives (L0)**: math and safety predicates (`03_bitvector_basic.tau`, `28_balance_hilo_spec.tau`).
2. **Core DEX (L1)**: swap validity, batching, order matching (`07_cpmm_basic.tau`, `10_batching_canonical.tau`, `13_dex_complete.tau`).
3. **Risk + Integrity (L2)**: oracle freshness, anti-MEV, breaker, slippage (`32_oracle_nonce_spec.tau`, `35_circuit_breaker.tau`, `37_adaptive_fee.tau`, `30_slippage_guard_spec.tau`).
4. **Value Capture (L3)**: fee splitting, burn sinks, insurance, rewards (`101_fee_flywheel_split.tau`, `102_buyback_burn_sink.tau`, `105_insurance_buffer.tau`, `80_fee_distributor.tau`, `95_token_burn.tau`).
5. **Stickiness + Governance (L4)**: locks, exit taxes, loyalty discounts, POL floors (`103_stake_lock_tier.tau`, `104_loyalty_fee_discount.tau`, `107_exit_tax_lock.tau`, `108_protocol_owned_liquidity_floor.tau`, `64_governance_timelock.tau`).
6. **Composites (L5)**: AND-gates that join the above (`38_composite_dex_gate.tau`, `39_frontier_composite_dex.tau`, `100_ultimate_composite.tau`, `106_ecosystem_composite.tau`).

## Archetype Library (New Patterns)

### 1) Fee Flywheel Splitter
- **Spec**: `experiments/101_fee_flywheel_split.tau`
- **Purpose**: Enforces fee conservation and minimum burn/reserve commitments.
- **Why it matters**: Guarantees deflation + treasury growth even when governance changes.

### 2) Buyback Burn Sink (Hi:Lo)
- **Spec**: `experiments/102_buyback_burn_sink.tau`
- **Purpose**: Checks `supply_after = supply_before - burn`.
- **Why it matters**: Hardens deflationary credibility with explicit state transitions.

### 3) Stake Lock + Tier Assignment
- **Spec**: `experiments/103_stake_lock_tier.tau`
- **Purpose**: Withdrawals blocked until lock end; stake tiers enforced.
- **Why it matters**: Enforces user commitment and enables tiered privileges.

### 4) Loyalty Fee Discount Ladder
- **Spec**: `experiments/104_loyalty_fee_discount.tau`
- **Purpose**: Validates fee discounts by tier without underflow.
- **Why it matters**: Enables economic stickiness without unsafe arithmetic.

### 5) Insurance Buffer Update
- **Spec**: `experiments/105_insurance_buffer.tau`
- **Purpose**: Validates buffer updates and minimum coverage.
- **Why it matters**: Ensures solvency under stress and aligns risk pricing.

### 6) Exit Tax Lock
- **Spec**: `experiments/107_exit_tax_lock.tau`
- **Purpose**: Early exit pays tax; unlocked exit pays none.
- **Why it matters**: Creates a controlled liquidity flywheel and discourages mercenary flow.

### 7) Protocol-Owned Liquidity Floor
- **Spec**: `experiments/108_protocol_owned_liquidity_floor.tau`
- **Purpose**: Enforces minimum POL computed externally.
- **Why it matters**: Maintains liquidity stickiness even during market shocks.

### 8) Ecosystem Composite Gate
- **Spec**: `experiments/106_ecosystem_composite.tau`
- **Purpose**: AND-composes DEX + value + stickiness modules.
- **Why it matters**: Single boolean gate for "ecosystem-safe" execution.

## Composition Strategy (Lego Wiring)

1. **Bind inputs consistently**: Treat each module as a predicate over a specific input slice. The composite spec simply ANDs module outputs.
2. **Use explicit "valid" outputs**: Every module yields `o1` or `oX` as a validity flag. Composites only depend on flags.
3. **Gate execution, not state**: Specs express checks; execution engines should only proceed when all checks are true.
4. **Keep time local**: Temporal predicates should be encapsulated in their own module (e.g., breaker, TWAP) to avoid state bleed.
5. **Minimize cross-module arithmetic**: If a ratio or threshold is complex, compute it externally and verify via simple bounds.

## Ecosystem Design (Deflationary DACs)

### Entities
- **DEX Core**: Swap execution + routing (`13_dex_complete.tau`, `83_swap_router.tau`).
- **Oracle DAC**: Feeds price + median checks (`36_median_oracle.tau`, `32_oracle_nonce_spec.tau`).
- **Risk DAC**: Circuit breaker, volatility buckets (`35_circuit_breaker.tau`, `40_volatility_bucket_gate.tau`).
- **Treasury DAC**: Fee split, buyback, burn (`101_fee_flywheel_split.tau`, `102_buyback_burn_sink.tau`).
- **Insurance DAC**: Buffer tracking (`105_insurance_buffer.tau`).
- **Governance DAC**: Timelocks and policy updates (`64_governance_timelock.tau`).
- **Loyalty DAC**: Stake tiers + discounts (`103_stake_lock_tier.tau`, `104_loyalty_fee_discount.tau`, `107_exit_tax_lock.tau`).

### Value Flow (Flywheel)
1. Swaps generate fees.
2. Fees split into **burn + rewards + treasury + insurance** (Spec 101).
3. Treasury schedules buybacks, reducing supply (Spec 102).
4. Insurance buffer protects against shocks (Spec 105).
5. Staked users receive rewards + fee discounts (Spec 103/104).
6. Early exits pay tax, sustaining buffer and burn (Spec 107).

### Economic Stickiness
- **Time locks**: Users earn better fees only after lock maturity.
- **Exit friction**: Early exit tax penalizes hot money and funds insurance.
- **Privilege gating**: Higher tiers unlock routing priority and better spreads.
- **POL floor**: Protocol-owned liquidity keeps deep markets even in drawdowns.

## Example Composite Wiring

The canonical ecosystem gate uses outputs from core modules:

```
o1 = dex_ok
o2 = fee_split_ok
o3 = burn_ok
o4 = stake_ok
o5 = tier_ok
o6 = discount_ok
o7 = buffer_ok
o8 = ecosystem_ok = o1 & o2 & o3 & o4 & o5 & o6 & o7
```

In Tau, this is encoded in `experiments/106_ecosystem_composite.tau`.

## Integration Notes

- Keep each module independently testable.
- Update registry entries if you want formal completeness checks.
- For ratios, prefer cross-multiplication (`a * scale >= b * threshold`) to avoid division.
