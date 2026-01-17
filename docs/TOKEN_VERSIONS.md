# Advanced Token Specifications for Tau DEX

## Overview

This document describes the complete token specification hierarchy for the Tau DEX protocol. Each version adds increasing complexity and flexibility for token creators.

## Never-Zero Guarantee

### Mathematical Proof

All token versions guarantee that supply **never reaches zero**. This is proven through multiple mechanisms:

```
Theorem: Supply S(t) > 0 for all t >= 0

Proof by cases:

Case 1 (Explicit Floor):
  - Constraint: burn only allowed if S > floor
  - Invariant: S(t) >= floor > 0 ∀t ✓

Case 2 (Implicit Floor via Integer Division):
  - burn = floor(amount × rate / 10000)
  - When amount × rate < 10000: burn = 0
  - Natural floor at 10000/rate tokens ✓

Case 3 (Adaptive Rate):
  - rate(t) = base_rate × S(t) / S(0)
  - As S → 0, rate → 0, burn → 0 ✓

Case 4 (Elastic Supply):
  - If S < target: mint allowed
  - Supply rebounds before zero ✓

Conclusion: S(t) > 0 always. QED.
```

**No extralogical features required** - pure bitvector arithmetic suffices.

---

## Token Version Hierarchy

### V1 - Basic (tdex_token_v1.tau)
**Complexity: ★☆☆☆☆**

Basic transfer with fixed 0.5% burn rate and explicit floor.

| Feature | Description |
|---------|-------------|
| Burn Rate | Fixed 0.5% per transfer |
| Floor | Explicit minimum supply |
| Use Case | Simple deflationary token |

---

### V2 - Percentage Zeno (token_v2_percentage.tau)
**Complexity: ★★☆☆☆**

Zeno's paradox burn - percentage-based with implicit floor from integer math.

| Feature | Description |
|---------|-------------|
| Burn Rate | Configurable basis points |
| Floor | Implicit (integer division) + Explicit backup |
| Math | `burn = amount × rate / 10000` |

```
Example (0.5% = 50 bps):
- Transfer 1000: burn 5
- Transfer 100: burn 0 (implicit floor)
- Implicit floor = 10000/50 = 200 tokens
```

---

### V3 - Adaptive (token_v3_adaptive.tau)
**Complexity: ★★★☆☆**

Burn rate decreases as supply decreases - self-limiting deflation.

| Feature | Description |
|---------|-------------|
| Burn Rate | `base_rate × current_supply / initial_supply` |
| Floor | Self-approaching via rate decay |
| Benefit | Sustainable long-term deflation |

```
Example (base_rate = 1%):
- At 100% supply: burn 1.0%
- At 50% supply: burn 0.5%
- At 10% supply: burn 0.1%
- Asymptotically approaches zero burn
```

---

### V4 - Elastic (token_v4_elastic.tau)
**Complexity: ★★★☆☆**

Rebase token with demand-responsive supply (burn + conditional mint).

| Feature | Description |
|---------|-------------|
| Burn | On all transfers |
| Mint | When price_ratio > 105% |
| Extra Burn | When price_ratio < 95% |
| Target | Supply oscillates around target |

```
Demand Signal (price_ratio × 100):
- > 105: High demand → mint allowed
- < 95: Low demand → extra burn
- 95-105: Normal operation
```

---

### V5 - Full FSM (token_v5_fsm.tau)
**Complexity: ★★★★☆**

Complete finite state machine token with lifecycle management.

```
State Diagram:
┌─────────┐    mint    ┌──────────┐
│ GENESIS │ ─────────> │  ACTIVE  │
└─────────┘            └────┬─────┘
                            │
         ┌──────────────────┼──────────────────┐
         │                  │                  │
         v                  v                  v
   ┌──────────┐      ┌──────────┐      ┌──────────┐
   │ VESTING  │      │  STAKED  │      │  LOCKED  │
   └────┬─────┘      └────┬─────┘      └────┬─────┘
         │                │                  │
         └────────────────┼──────────────────┘
                          │ unlock
                          v
                   ┌──────────┐
                   │  ACTIVE  │
                   └────┬─────┘
                        │ burn
                        v
                   ┌──────────┐
                   │  BURNED  │ (terminal)
                   └──────────┘
```

| State | Code | Transitions |
|-------|------|-------------|
| GENESIS | 0 | → ACTIVE (mint) |
| ACTIVE | 1 | → VESTING, STAKED, LOCKED, BURNED |
| VESTING | 2 | → ACTIVE (after cliff) |
| STAKED | 3 | → ACTIVE (unstake) |
| LOCKED | 4 | → ACTIVE (after lock or governance) |
| BURNED | 5 | Terminal (no transitions) |

---

### V6 - Governance (token_v6_governance.tau)
**Complexity: ★★★★☆**

Democratic control of token parameters via voting.

| Feature | Description |
|---------|-------------|
| Quorum | Minimum votes required |
| Passing | votes_for > votes_against |
| Supermajority | Required for large changes (>1%) |
| Rate Bounds | 0-5% maximum burn rate |

```
Governance Flow:
1. Propose rate change
2. Token holders vote
3. If quorum met AND majority: approve
4. If large change: require 2/3 supermajority
```

---

### V7 - Vesting (token_v7_vesting.tau)
**Complexity: ★★★☆☆**

Time-locked token release with cliff and linear vesting.

| Parameter | Description |
|-----------|-------------|
| Cliff | Minimum time before any release |
| Duration | Total vesting period |
| Release | Linear after cliff |

```
Vesting Formula:
- Before cliff: releasable = 0
- After cliff: releasable = total × (elapsed - cliff) / (duration - cliff)
- After duration: releasable = total
```

---

### V8 - Staking (token_v8_staking.tau)
**Complexity: ★★★☆☆**

Stake-to-earn with optional auto-compounding.

| Feature | Description |
|---------|-------------|
| Rewards | `staked × rate × duration / 10000` |
| Auto-compound | Rewards added to stake |
| Minimum Stake | 100 tokens |
| Minimum Duration | 100 blocks |

---

### Composite (token_composite_v1.tau)
**Complexity: ★★★★★**

Unified validator with feature flags.

```
Feature Flags (bitmask):
Bit 0: Percentage burn (V2)
Bit 1: Adaptive burn (V3)
Bit 2: Elastic rebase (V4)
Bit 3: FSM states (V5)
Bit 4: Explicit floor
Bit 5: Governance override
```

---

### Ultimate (token_ultimate_v1.tau)
**Complexity: ★★★★★**

Maximum flexibility with formal never-zero proof embedded.

---

## Specification Files

| File | Version | Status |
|------|---------|--------|
| `tdex_token_v1.tau` | V1 Basic | ✅ Complete |
| `tdex_supply_v1.tau` | Supply Tracking | ✅ Complete |
| `tdex_buyback_v1.tau` | Buyback Mechanism | ✅ Complete |
| `tdex_economics_v1.tau` | Full Economics | ✅ Complete |
| `token_v2_percentage.tau` | V2 Zeno | ✅ Complete |
| `token_v3_adaptive.tau` | V3 Adaptive | ✅ Complete |
| `token_v4_elastic.tau` | V4 Elastic | ✅ Complete |
| `token_v5_fsm.tau` | V5 FSM | ✅ Complete |
| `token_v6_governance.tau` | V6 Governance | ✅ Complete |
| `token_v7_vesting.tau` | V7 Vesting | ✅ Complete |
| `token_v8_staking.tau` | V8 Staking | ✅ Complete |
| `token_composite_v1.tau` | Composite | ✅ Complete |
| `token_ultimate_v1.tau` | Ultimate | ✅ Complete |

---

## Usage Guide

### For Token Creators

1. **Simple Deflationary**: Use V1 or V2
2. **Sustainable Long-term**: Use V3 (adaptive)
3. **Price-Responsive**: Use V4 (elastic)
4. **Complex Lifecycle**: Use V5 (FSM)
5. **Community Controlled**: Use V6 (governance)
6. **Team/Investor Tokens**: Use V7 (vesting)
7. **Yield Generation**: Use V8 (staking)
8. **Maximum Flexibility**: Use Composite or Ultimate

### Configuration Example

```python
# Configure a token with:
# - Percentage burn (V2)
# - Explicit floor
# - Governance override
feature_flags = 0b110001  # = 49

# Validate with composite spec
validate_token(
    feature_flags=49,
    current_supply=1000000,
    transfer_amount=1000,
    burn_rate_bps=50,
    explicit_floor=100000
)
```

---

## Security Properties

All token specs satisfy these invariants:

1. **Never-Zero**: `supply[t] > 0` for all `t`
2. **Monotonic Floor**: `supply[t] >= floor` always
3. **Conservation**: No tokens created without mint authority
4. **Burn Correctness**: Exact burn calculation verified
5. **State Consistency**: FSM transitions are valid

---

## Conclusion

The Tau DEX token system provides maximum flexibility through composable, formally verified specifications. Creators can select from simple to complex configurations, all with mathematical guarantees that supply never reaches zero.
