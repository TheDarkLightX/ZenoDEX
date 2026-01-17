# Base Case Fixes for Temporal Specs

## Issue Identified

Temporal specs referenced `t-1`/`t-2` without proper base-case constraints, making behavior at `t=0` (and `t=1` for `t-2`) undefined.

## Fixes Applied

### 1. `24_temporal_verified.tau`
**Before:** `always (o1[t]:sbf = 1:sbf <-> pricestable(...))`
**After:** `always (o1[0]:sbf = 0:sbf) && (o1[t]:sbf = 1:sbf <-> pricestable(...))`

Base case: `o1[0]=0` (no previous price at t=0, assume unstable)
Note: `pricestable` now uses boolean expansion (no ternary) for parser robustness.

### 2. `22_verified_dex.tau`
**Added base cases:**
- `o1[0], o1[1]` (explicit intent match at warmup steps)
- `o2[0]=0`, `o2[1]=pricestable(i3[1], i3[0])`
- `o3[0], o3[1]` (explicit canonical check at warmup steps)
- `o4[0]=0, o4[1]=0` (sandwich needs t-2)
- `o5[0]=0, o5[1]=0` (allvalid depends on above)

### 3. `25_complete_verified_dex.tau`
**Added base cases:**
- `o1[0], o1[1]` (explicit intent match at warmup steps)
- `o2[0]=0`, `o2[1]=pricestable(i3[1], i3[0])`
- `o3[0]=0, o3[1]=0` (sandwich needs t-2)

### 4. `35_circuit_breaker.tau`
**Fixed contradiction:** Original set `o1[0]=0` but also enforced `o1[t] <-> calm(...)` for ALL t.
**Solution:** Added explicit `o1[1]` constraint to properly separate base case from general case.

### 5. `37_adaptive_fee.tau`
**Added base cases:**
- `o1[0]=0` (stability needs t-1)
- `o2[0]=0` (fee validity needs t-1)

## Verification

All fixed specs compile successfully:
```
24_temporal_verified.tau: OK
22_verified_dex.tau: OK
25_complete_verified_dex.tau: OK
35_circuit_breaker.tau: OK
37_adaptive_fee.tau: OK
```

## Spec Status Summary

| Spec | Status | Notes |
|------|--------|-------|
| `23_minimal_verified.tau` | ✅ Complete | Pure combinational, no temporal |
| `24_temporal_verified.tau` | ✅ Fixed | Base case o1[0]=0 added |
| `22_verified_dex.tau` | ✅ Fixed | Base cases for t=0, t=1 added |
| `25_complete_verified_dex.tau` | ✅ Fixed | Base cases for t=0, t=1 added |
| `35_circuit_breaker.tau` | ✅ Fixed | Initial condition properly separated |
| `36_median_oracle.tau` | ✅ Complete | No temporal references |
| `37_adaptive_fee.tau` | ✅ Fixed | Base cases o1[0]=0, o2[0]=0 added |

## Design Pattern for Temporal Specs

```tau
# For specs using t-1:
always (o[0]:sbf = initial_value) && 
       (o[t]:sbf = 1:sbf <-> predicate(i[t], i[t-1])).

# For specs using t-2:
always (o[0]:sbf = initial_value) && 
       (o[1]:sbf = initial_value) && 
       (o[t]:sbf = 1:sbf <-> predicate(i[t], i[t-1], i[t-2])).
```

This ensures:
1. Explicit, defined behavior at warmup steps
2. No implicit constraints on non-existent prior inputs
3. Clear state machine semantics
