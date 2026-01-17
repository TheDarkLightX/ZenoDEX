# Token Spec Governance & Mutability Rules

## Overview

This document categorizes all token specifications by their **mutability level** - whether parameters can be updated via governance, or if the spec represents immutable safety invariants.

**Rule of Thumb:**
- **Updatable**: thresholds, rates, caps, lists
- **Immutable**: conservation proofs, theft prevention, execution correctness

---

## ✅ UPDATABLE (Policy + Thresholds)

These specs contain "knobs" that should be tunable as markets evolve.

### Token Economic Parameters

| Spec | Updatable Parameters | Rationale |
|------|---------------------|-----------|
| `tdex_token_v1.tau` | `burn_rate_bps`, `explicit_floor` | Burn rate may need adjustment based on market conditions |
| `tdex_buyback_v1.tau` | `buyback_threshold`, fee split ratio | Buyback frequency tunable |
| `tdex_economics_v1.tau` | `burn_rate_bps`, `target_supply` | Economic policy parameters |
| `token_v2_percentage.tau` | `burn_rate_bps`, `explicit_floor` | Zeno burn rate tunable |
| `token_v3_adaptive.tau` | `base_rate_bps`, `explicit_floor` | Adaptive rate base tunable |
| `token_v4_elastic.tau` | `target_supply`, demand thresholds | Rebase targets tunable |
| `token_v6_governance.tau` | `quorum_threshold`, rate bounds | Governance parameters meta-tunable |
| `token_v7_vesting.tau` | `cliff_blocks`, `vesting_duration` | Schedule parameters (for new vestings) |
| `token_v8_staking.tau` | `reward_rate_bps`, `minimum_stake` | Staking incentive rates |

### Risk/Market Guards

| Spec | Updatable Parameters | Rationale |
|------|---------------------|-----------|
| `tdex_supply_v1.tau` | `min_supply` floor level | Floor may need adjustment |

---

## ⚠️ PARTIALLY UPDATABLE (Composites)

These allow **parameter changes** but **NOT logic changes** without hard governance upgrade.

| Spec | Updatable | Fixed |
|------|-----------|-------|
| `token_composite_v1.tau` | Feature flags, rate params | Core validation logic |
| `token_ultimate_v1.tau` | Thresholds, floor | Never-zero proof structure |
| `token_v5_fsm.tau` | Lock durations, governance flags | State transition rules |

**Recommendation:** Keep composite structure fixed, but allow parameter streams to flow into sub-modules.

---

## ❌ IMMUTABLE (Safety Core)

These are **fundamental invariants** - the "constitution" of the token system.

| Spec | Invariant Protected | Why Immutable |
|------|---------------------|---------------|
| `protocol_token_v1.tau` | Token conservation (transfer/mint/burn) | Prevents creation from nothing |
| `tdex_supply_v1.tau` (floor check) | Supply floor invariant | Prevents zero-supply |

### Immutable Properties Across All Token Specs

These properties are **hardcoded invariants** that must NEVER be governance-updatable:

1. **Conservation Law**: `tokens_out <= tokens_in` for transfers
2. **Never-Zero Guarantee**: `supply[t] > 0` for all `t`
3. **Burn Correctness**: `burned = calculated_burn` (no over-burn)
4. **Floor Enforcement**: `supply >= floor` always
5. **FSM Validity**: Only valid state transitions allowed

---

## Parameter Streams Architecture

For updatable specs, parameters should flow through **input streams** rather than hardcoded constants:

```
┌─────────────────┐
│   Governance    │
│   (votes)       │
└────────┬────────┘
         │ approved params
         v
┌─────────────────┐
│  Parameter      │
│  Registry       │
└────────┬────────┘
         │ i_param streams
         v
┌─────────────────┐
│   Token Spec    │
│   (validates)   │
└─────────────────┘
```

### Example: Updatable Burn Rate

```tau
# Instead of hardcoded:
# burnamt := amount * { #x0032 }:bv[16] / { #x2710 }:bv[16]

# Use input stream for rate:
# i4 = burn_rate_bps (from governance)
burnamt(amount : bv[16], rate : bv[16]) := (amount * rate) / { #x2710 }:bv[16].
```

---

## Spec Categorization Summary

| Category | Count | Examples |
|----------|-------|----------|
| ✅ Updatable | 9 | `tdex_token_v1`, `token_v2-v4`, `token_v6-v8` |
| ⚠️ Partial | 3 | `token_composite`, `token_ultimate`, `token_v5_fsm` |
| ❌ Immutable | 1 | `protocol_token_v1` (core) |

---

## Governance Update Flow

### For Updatable Parameters

```
1. Proposal submitted (new burn_rate = X)
2. Voting period (token_v6_governance validates)
3. If quorum + majority: approve
4. Parameter registry updated
5. Next transaction uses new parameter
```

### For Immutable Specs

```
❌ NO governance path
❌ NO parameter updates
✅ Only option: deploy new protocol version
```

---

## Implementation Notes

### Adding Mutability Annotations to Specs

Each spec header should declare its mutability:

```tau
# MUTABILITY: UPDATABLE
# UPDATABLE_PARAMS: burn_rate_bps, explicit_floor
# IMMUTABLE_INVARIANTS: supply >= floor, burn = calculated
```

### Registry Integration

Updatable specs should read parameters from input streams that are fed by a governance-controlled registry:

```python
# Python integration layer
def get_token_params():
    return {
        'burn_rate_bps': governance_registry.get('token.burn_rate'),
        'explicit_floor': governance_registry.get('token.floor'),
    }
```

---

## Security Considerations

1. **Rate Limits on Updates**: Even updatable params should have change velocity limits
2. **Timelock**: All parameter updates should have minimum delay (e.g., 24h)
3. **Bounds Checking**: `token_v6_governance.tau` enforces rate bounds (0-5%)
4. **Supermajority for Large Changes**: Changes >1% require 2/3 vote

---

## Conclusion

The token spec system separates:
- **Policy** (tunable via governance)
- **Safety** (immutable invariants)

This allows the DEX to adapt to market conditions while maintaining mathematical guarantees about token safety.
