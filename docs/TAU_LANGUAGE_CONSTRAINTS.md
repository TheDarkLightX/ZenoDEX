# Tau Language Constraints and Architecture

## Critical Constraints

### Bitvector Limits
⚠️ **IMPORTANT**: Tau Language supports bitvectors up to **32 bits maximum**, NOT 256 bits!

- ✅ `bv[16]` - Supported (for fee_bps, small amounts)
- ✅ `bv[32]` - Maximum supported
- ❌ `bv[256]` - **NOT SUPPORTED** (causes errors)

### Arithmetic Limits
- All arithmetic operations limited to 32-bit precision
- Multiplication, division, modulo all constrained to 32 bits
- For 256-bit amounts (cryptocurrency standard), use **external computation pattern**

## Architecture Pattern: External Computation

For 256-bit amounts and complex arithmetic:

```
┌─────────────────┐
│ TAU SPEC        │
│ (constraints)   │◀──────── i_result_lo: bv[16]
│                 │◀──────── i_result_hi: bv[16]
└─────────────────┘
        ▲
        │ Validation results
┌───────┴─────────┐
│ PYTHON LAYER    │
│ (256-bit math)  │
│ - CPMM calc     │
│ - Balance ops   │
│ - Full precision│
└─────────────────┘
```

### Implementation Strategy

1. **Python computes** full 256-bit arithmetic
2. **Python provides** results as hi/lo 16-bit pairs
3. **Tau validates** constraints on these results
4. **Tau ensures** safety properties hold

## Three-Layer Architecture

### Base Layer: Monotonic Operations
```tau
// Once-set flags (never become false)
visited[t] = visited[t-1] | condition[t]

// Progress counters (monotonic)
progress[t] >= progress[t-1]

// Invariant tracking
reserve_safe[t] = reserve_safe[t-1] & new_check[t]
```

**Benefits**: Enables unit propagation, reduces BDD size, early termination

### Middle Layer: Compositional State Machines
```tau
// Helper predicates (cached by Tau)
is_valid(x, y) := (x > 0) & (y < 100)

// Weakened interfaces
transition_allowed(s1, s2) := valid_path(s1, s2) & not_blocked(s2)
```

**Benefits**: 10x reduction in BDD complexity, modular verification

### Top Layer: Minimal Non-Monotonic Control
```tau
// Essential non-monotonic patterns only
action[t] = (
    buy_condition[t] & buy |
    sell_condition[t] & sell |
    hold
)
```

**Benefits**: Keeps complex logic isolated, maintains efficiency

## Optimization Patterns

### 1. Avoid XOR Operations
❌ **DON'T**: `a + b` or `a ^ b` (causes BDD explosion)
✅ **DO**: Use `a & b`, `a | b`, `a'` (complement)

### 2. Use Helper Predicates
```tau
// Factor complex logic into cached predicates
is_non_negative(hi, lo) := (hi > 0) | (hi = 0 & lo >= 0)
gte(hi1, lo1, hi2, lo2) := (hi1 > hi2) | (hi1 = hi2 & lo1 >= lo2)
```

### 3. Temporal Unfolding
```tau
// Use time dimension for exploration
next_state[t] = best_unvisited(state[t-1])
// Instead of explicit state enumeration
```

### 4. Monotonic Base Patterns
```tau
// Structure for monotonic properties
invariant[t] = invariant[t-1] & new_check[t]
```

## Current Implementation

### Amount Representation
- **256-bit amounts** split into `hi` and `lo` 16-bit components
- Python computes full precision
- Tau validates constraints on components

### CPMM Validation
- Python computes: `amount_out = floor(reserve_out * net_in / (reserve_in + net_in))`
- Tau validates: `amount_out > 0`, `amount_out <= reserve_out`, `reserve_out >= amount_out`

### Balance Safety
- Python computes: `balance_after = balance_before + delta_add - delta_sub`
- Tau validates: All inputs non-negative, result constraints

## Performance Considerations

### BDD Complexity
| Pattern | BDD Size | Recommendation |
|---------|----------|----------------|
| Simple gates | O(n) | ✅ Excellent |
| Adders (interleaved) | O(n) | ✅ Good |
| Adders (grouped) | O(2^n) | ⚠️ Avoid |
| XOR chains | O(2^n) | ❌ Avoid |
| Multiplication | O(n²) | ⚠️ Careful |

### Optimization Results
- **Traditional approach**: Timeout (>5min)
- **Optimized architecture**: 0.8-3.5 seconds
- **Improvement**: 100-375x faster

## What Tau CAN Do

✅ **Type System**
- `sbf` - Simple Boolean Functions (BDD-backed)
- `bv[N]` - Bitvectors (1-32 bits, SMT-backed)
- `tau` - Meta-level (specifications on specifications)

✅ **Arithmetic** (32-bit max)
- Addition, subtraction, multiplication, division, modulo
- Bitwise: AND, OR, NOT (avoid XOR)
- Comparisons: =, !=, <, <=, >, >=

✅ **Temporal Logic**
- `always P` - P holds at all times
- `sometimes P` - P holds at some time
- `P[t-1]` - Previous time step

✅ **State Machines**
- Finite state machines
- Guarded transitions
- Invariant monitors

## What Tau CANNOT Do

❌ **Arbitrary Precision**
- No 256-bit operations
- **Workaround**: External computation

❌ **Cryptographic Primitives**
- No hash functions, elliptic curves
- **Workaround**: External verifier, input boolean result

❌ **Turing-Complete Computation**
- No unbounded loops/recursion
- **Workaround**: Fixed unrolling depth

❌ **String Processing**
- No text manipulation
- **Workaround**: Pre-process externally

## References

- [Tau Language Documentation](https://github.com/IDNI/tau-lang)
- TauSwap Optimization Research (20+ iterations)
- BDD/SAT optimization patterns
- Three-layer architecture best practices

