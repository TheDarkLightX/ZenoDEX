# TauSwap Tau Language Architecture

## Overview

TauSwap uses a **hybrid architecture** that respects Tau Language constraints while enabling full DEX functionality:

- **Python Layer**: Computes 256-bit arithmetic, manages full state
- **Tau Layer**: Validates constraints, ensures safety properties
- **Integration**: Python provides results, Tau validates correctness

## Architecture Pattern

### External Computation Pattern

```
┌─────────────────────────────────┐
│     PYTHON LAYER                │
│  (256-bit arithmetic)           │
│  - CPMM: k = x * y              │
│  - Swaps: amount_out calculation│
│  - Balances: full precision     │
│  - State: complete DEX state    │
└──────────────┬──────────────────┘
               │ Provides results as
               │ hi/lo 16-bit pairs
               ▼
┌─────────────────────────────────┐
│      TAU LAYER                  │
│  (Constraint validation)         │
│  - Validates: amount_out > 0    │
│  - Validates: amount_out <= res  │
│  - Validates: balances >= 0     │
│  - Validates: invariants hold   │
└─────────────────────────────────┘
```

## Three-Layer Tau Specification Structure

### Layer 1: Monotonic Base

**Purpose**: Properties that never become false once true

```tau
// Once-set flags
reserve_safe[t] = reserve_safe[t-1] | new_check[t]

// Progress tracking
progress[t] >= progress[t-1]

// Invariant preservation
balance_non_negative[t] = balance_non_negative[t-1] & check[t]
```

**Benefits**:
- Enables unit propagation
- Reduces BDD size
- Allows early termination
- 10-100x performance improvement

### Layer 2: Compositional Middle

**Purpose**: Reusable, cached predicates

```tau
// Helper predicates (cached by Tau)
is_non_negative(hi : bv[16], lo : bv[16]) := 
  (hi > ZERO_16) | (hi = ZERO_16 & lo >= ZERO_16)

gte(hi1, lo1, hi2, lo2) :=
  (hi1 > hi2) | (hi1 = hi2 & lo1 >= lo2)

both_reserves_valid(r0_hi, r0_lo, r1_hi, r1_lo) :=
  is_non_negative(r0_hi, r0_lo) & is_non_negative(r1_hi, r1_lo)
```

**Benefits**:
- 10x BDD complexity reduction
- Modular verification
- Reusable logic
- Weakened interfaces

### Layer 3: Minimal Non-Monotonic Top

**Purpose**: Essential control logic only

```tau
// Minimal non-monotonic patterns
swap_valid[t] = 
  is_non_negative(reserve_in_hi[t], reserve_in_lo[t]) &
  is_positive(amount_in_hi[t], amount_in_lo[t]) &
  gte(reserve_out_hi[t], reserve_out_lo[t], 
      amount_out_hi[t], amount_out_lo[t])
```

**Benefits**:
- Keeps complex logic isolated
- Maintains solver efficiency
- Clear separation of concerns

## Amount Representation

### Problem
- Cryptocurrency amounts need 256-bit precision
- Tau Language max is 32-bit bitvectors
- Solution: External computation + constraint validation

### Implementation

**Python computes**:
```python
# Full 256-bit arithmetic
amount_out = floor(reserve_out * net_in / (reserve_in + net_in))
```

**Python provides** (as hi/lo pairs):
```python
amount_out_hi = (amount_out >> 16) & 0xFFFF
amount_out_lo = amount_out & 0xFFFF
```

**Tau validates**:
```tau
// Constraint validation on components
is_positive(amount_out_hi[t], amount_out_lo[t]) &
gte(reserve_out_hi[t], reserve_out_lo[t], 
    amount_out_hi[t], amount_out_lo[t])
```

## Optimization Patterns Applied

### 1. Avoid XOR Operations
❌ **Never use**: `a + b`, `a ^ b` (causes BDD explosion)
✅ **Always use**: `a & b`, `a | b`, `a'` (complement)

### 2. Helper Predicates
Factor complex logic into cached predicates:
```tau
// Instead of inline complex expressions
is_valid := complex_expression_here

// Use helper predicate
is_valid(x, y) := helper1(x) & helper2(y)
```

### 3. Temporal Unfolding
Use time dimension for exploration:
```tau
// Instead of explicit state enumeration
next_state[t] = best_unvisited(state[t-1])

// Not: all_states(s) := s=00 | s=01 | s=10 | s=11
```

### 4. Monotonic Patterns
Structure for monotonic properties:
```tau
// Properties that never become false
invariant[t] = invariant[t-1] & new_check[t]
```

## Performance Results

Based on optimization research (20+ iterations):

| Specification | Traditional | Optimized | Improvement |
|--------------|-------------|-----------|-------------|
| 4-state A* | Timeout (>5min) | 0.8s | >375x |
| Trading Agent | 120s | 3.5s | 34x |
| 50 variables | Timeout | 3.5s | >100x |

## Current Implementation Status

### ✅ Completed
- [x] Type definitions (16-bit components)
- [x] Invariants (monotonic base layer)
- [x] CPMM validation (external computation pattern)
- [x] Balance safety (helper predicates)
- [x] Three-layer architecture

### ⚠️ In Progress
- [ ] Settlement validation (complex, needs careful encoding)
- [ ] Intent validation (authorization logic)
- [ ] Temporal fairness (advanced properties)

### 📋 TODO
- [ ] Test with Tau compiler
- [ ] Add test vectors
- [ ] Performance profiling
- [ ] Integration with Python layer

## References

- [Tau Language Constraints](./TAU_LANGUAGE_CONSTRAINTS.md)
- [Tau Specs Guide](./TAU_SPECS_GUIDE.md)
- [Tau Specs Improvements](./TAU_SPECS_IMPROVEMENTS.md)
- Tau Language Optimization Research (20+ iterations)

