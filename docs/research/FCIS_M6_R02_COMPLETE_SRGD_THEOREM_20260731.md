# FCIS M6-R02 Complete Adaptive SRGD/AGQE Theorem

**Date:** 2026-07-31  
**Status:** `THEOREM_SPECIFICATION_WITH_EXISTING_ONE_STEP_CORE`  
**Depends on:** PR #496 sign-dual refinement and PR #497 SLNF occurrence semantics  
**Authority:** none; this is a mathematical and implementation-refinement contract

## 1. Result

The existing Lean work proves the difficult selector fact for three roles:

```text
valid strict deficit state
+ valid residual quota
+ support-respecting largest-score selection
-> unique bonus tuple
-> zero-sum post-state
-> every post-deficit remains strictly inside (-D,D)
```

The remaining R02 theorem is not a search for another allocator. It is the
composition of that one-step result with an overflow-safe Euclidean quotient,
the frozen SLNF occurrence word, and a history identity.

For every finite sequence of accepted transition-local occurrences, every
adaptive sequence of valid three-role policies, and every U256 amount, prove:

```text
1. exact conservation;
2. zero weight receives zero atoms;
3. each role receives floor or ceiling of its local ideal quota;
4. deficits sum to zero;
5. every deficit remains strictly inside (-D,D);
6. cumulative discrepancy is strictly less than one atom;
7. fixed role order makes the result deterministic;
8. Python and Rust compute the same state and allocations;
9. grouping occurs only inside one SLNF segment.
```

## 2. Frozen notation

There are exactly three semantic roles in protocol order:

```text
0 = buyback
1 = treasury
2 = rewards
```

Let:

```text
D > 0                         denominator; production D = 10,000
A_t in [0, 2^256-1]           occurrence amount at time t
w_t,i in [0,D]                policy weight of role i
sum_i w_t,i = D               valid policy
x_t,i                         allocated integer amount
```

The signed deficit convention is:

```text
d_t,i = cumulative ideal numerator before t
        - D * cumulative actual allocation before t
```

Thus initially:

```text
d_0,i = 0
```

and the exact history identity is:

```text
d_t,i = sum_{j<t} A_j*w_j,i - D*sum_{j<t} x_j,i
```

AGQE surplus is the sign-dual coordinate:

```text
sigma_t,i = -d_t,i
```

SRGD and AGQE are therefore two representations of one semantic transition,
not competing allocator mechanisms.

## 3. Overflow-safe Euclidean quota algorithm

Never compute `A*w_i` in a U256 register. Use:

```text
A = D*q + r
q = A div D
r = A mod D
0 <= r < D
```

For each role:

```text
base_i     = q*w_i + floor((r*w_i)/D)
remainder_i = (r*w_i) mod D
score_i     = d_i + remainder_i
```

This equals the mathematical floor exactly:

```text
A*w_i = D*base_i + remainder_i
base_i = floor(A*w_i/D)
```

The residual-seat count is:

```text
h = (remainder_0 + remainder_1 + remainder_2) / D
```

Because each remainder is in `[0,D)` and their sum is divisible by `D`:

```text
h in {0,1,2}
```

Choose exactly `h` roles satisfying `remainder_i > 0`, in descending order of:

```text
(score_i, negative role index)
```

Equivalently, larger score wins and ties use role order `0 < 1 < 2`.

Let `bonus_i` be the selected-role bit. Return:

```text
x_i  = base_i + bonus_i
d'_i = d_i + remainder_i - D*bonus_i
```

### 3.1 Machine-width proof obligations

For production `D=10,000`:

```text
r*w_i < D^2 = 100,000,000
```

so the residual product fits in an ordinary unsigned 32-bit value, though a
wider checked type may be used.

Also:

```text
q*w_i <= q*D <= A <= U256_MAX
base_i <= A
x_i <= A
```

Therefore a checked U256 multiplication for `q*w_i` cannot overflow on admitted
inputs. The implementation must still use checked operations and convert every
unexpected failure into a typed rejection; the proof explains why a valid input
cannot reach that rejection.

Deficits satisfy:

```text
-D < d_i < D
0 <= remainder_i < D
-D < score_i < 2D
```

so signed 32-bit arithmetic is sufficient for production D. Use a wider checked
signed type in Rust to keep the proof-to-code boundary simple.

## 4. One-occurrence theorem

Assume:

```text
ValidState(D,d):
  sum_i d_i = 0
  and forall i, -D < d_i < D

ValidPolicy(D,w):
  forall i, 0 <= w_i <= D
  and sum_i w_i = D
```

The Euclidean algorithm produces exact floors and remainders. The reviewed SRGD
selector theorem supplies one unique support-respecting bonus tuple. Then:

### 4.1 Conservation

Summing the three Euclidean identities gives:

```text
A*sum_i w_i = D*sum_i base_i + sum_i remainder_i
A*D         = D*sum_i base_i + D*h
A           = sum_i base_i + h
```

Since `sum_i bonus_i = h`:

```text
sum_i x_i = A
```

### 4.2 Zero support

If `w_i = 0`:

```text
base_i = 0
remainder_i = 0
```

The support rule forbids `bonus_i = 1`, hence:

```text
x_i = 0
```

### 4.3 Local quota

For every role:

```text
base_i = floor(A*w_i/D)
bonus_i in {0,1}
bonus_i = 1 -> remainder_i > 0
```

Therefore:

```text
floor(A*w_i/D) <= x_i <= ceil(A*w_i/D)
```

### 4.4 Zero-sum state

```text
sum_i d'_i
 = sum_i d_i + sum_i remainder_i - D*sum_i bonus_i
 = 0 + D*h - D*h
 = 0
```

### 4.5 Strict discrepancy state

The existing reviewed theorem proves:

```text
forall i, -D < d'_i < D
```

for the exact support-respecting score selection and fixed tie order.

### 4.6 Determinism

The reviewed bonus relation has exactly one satisfying bit tuple. Euclidean
quotient/remainder are unique, so `(x,d')` is a total deterministic function of:

```text
D, A, w, d, fixed role order
```

## 5. Finite adaptive trace theorem

Let the R01 SLNF semantic carrier be an ordered word of transition-local amount
vectors:

```text
V_0, V_1, ..., V_(n-1)
```

For each segment and key, invoke the allocator exactly once with that grouped
amount. Let policy `w_t` be independently authenticated for occurrence `t`.

The trace theorem is a direct induction:

```text
ValidState(D,d_0)
forall t<n:
  ValidPolicy(D,w_t)
  Step(D,A_t,w_t,d_t) = (x_t,d_(t+1))
```

One-step preservation yields:

```text
forall t<=n, ValidState(D,d_t)
```

and one-step conservation/quota/support yield those properties for every
occurrence. No fixed-policy premise is used. Policy rotation is arbitrary inside
the admitted policy type.

The fold must consume the exact SLNF ordered word. Replacing two accepted
segments with one aggregate is forbidden because R01 supplies executable
counterexamples where the final allocation and persistent state differ.

## 6. Cumulative discrepancy theorem

By induction on the transition word, the update preserves:

```text
d_t,i = sum_{j<t} A_j*w_j,i - D*sum_{j<t} x_j,i
```

Rearrange:

```text
sum_{j<t} x_j,i - sum_{j<t}(A_j*w_j,i/D)
  = -d_t,i/D
```

The strict invariant gives:

```text
abs(d_t,i) < D
```

therefore:

```text
abs(
  cumulative actual_i
  - cumulative ideal_i
) < 1 atom
```

This is the adaptive-policy fairness theorem. It does not require the policy to
remain fixed for a complete block.

## 7. Semantic/representation factorization

The persistent state identity must use one semantic profile:

```text
adaptive-global-quota-entitlement/three-role/v1
```

and separately record a representation codec:

```text
srgd-deficit/v1
or
agqe-surplus/v1
```

The entitlement key is:

```text
(distribution_domain, asset, semantic_profile, fixed_role_order)
```

Destination addresses, custody accounts, policy weights, and representation
codec are not entitlement-key dimensions.

The representation migration is:

```text
phi(d_0,d_1,d_2) = (-d_0,-d_1,-d_2)
```

with:

```text
phi(phi(d)) = d
phi(SRGD_step(d,e)) = AGQE_step(phi(d),e)
```

A migration must transport every entry by `phi`; initializing the new
representation to zero is an entitlement-history erasure attack.

## 8. Python/Rust refinement contract

Both implementations must expose the same pure relation:

```text
step(
  exact key,
  U256 amount,
  exact three-role policy,
  exact pre-deficit
)
-> Accept(exact allocation, exact post-deficit)
 | Reject(stable code, stable path)
```

### 8.1 Required implementation algorithm

1. Reject non-exact types, including Boolean/integer aliases.
2. Require exactly three weights and the fixed role order.
3. Require each weight in `[0,D]` and total exactly `D`.
4. Require amount in U256.
5. Require every deficit strictly inside `(-D,D)` and total zero.
6. Compute `(q,r)=divmod(A,D)`.
7. Compute each base and remainder through the Euclidean decomposition.
8. Compute `h=sum(remainders)/D`; reject if not an exact integer in `{0,1,2}`.
9. Canonically rank eligible roles by score descending, role index ascending.
10. Set exactly the first `h` bonus bits.
11. Compute allocations and post-deficits with checked arithmetic.
12. Revalidate all theorem conclusions before constructing `Accept`.
13. Emit canonical bytes and roots using one shared golden-vector manifest.

### 8.2 Rust arithmetic types

Recommended profile:

```text
amount, q, base, allocation: U256
D, weights, r, remainder, h: u32 or wider checked unsigned
pre/post deficit, score: i64
```

Do not cast U256 to a machine integer. Do not compute `amount * weight` in U256.
Do not use floating point.

### 8.3 Differential evidence

Required vectors:

```text
A = 0, 1, 2, 3
A = D-1, D, D+1
A = U256_MAX-1, U256_MAX
all zero-history policies in a frozen boundary catalog
all strict deficit states for D <= 12
adaptive policy traces of at least 1,000 steps
all tie cases
all zero-weight positions
R01 split/merge counterexamples
SRGD/AGQE sign-dual vectors
```

For small denominators exhaustively compare:

```text
Python result
Rust result
independent mathematical oracle
```

For production D use property and edge vectors plus Kani/SMT arithmetic proofs.

## 9. Lean completion plan

Create `Proofs/FCISFeeApportionmentSRGDTrace.lean` importing the reviewed SRGD
and AGQE/SRGD modules. The file must prove, without new axioms:

```text
safe_euclidean_floor
residual_count_zero_one_two
one_step_conservation
zero_weight_zero_allocation
one_step_local_quota
history_identity_step
valid_trace_preserved
cumulative_discrepancy_lt_one
sign_dual_trace_conjugacy
```

Keep the following theorem layers separate:

```text
integer mathematics
three-role selector relation
finite trace induction
Python implementation refinement
Rust implementation refinement
canonical byte/root parity
runtime authentication and mounting
```

A theorem that assumes an occurrence amount or policy is authenticated does not
prove the shell supplied the authenticated value.

## 10. Falsification suite

The complete theorem is rejected by any of these witnesses:

```text
R02-M01 allocation sum differs from amount
R02-M02 zero-weight role receives one atom
R02-M03 allocation falls outside floor/ceiling quota
R02-M04 post deficits do not sum to zero
R02-M05 abs(post deficit_i) >= D
R02-M06 cumulative discrepancy reaches one atom
R02-M07 equal-score Python/Rust role mismatch
R02-M08 any valid U256 input reaches arithmetic rejection
R02-M09 Boolean admitted as integer
R02-M10 policy weights do not sum to D but transition accepts
R02-M11 global aggregation erases an SLNF boundary
R02-M12 SRGD and AGQE traces fail sign-dual conjugacy
R02-M13 destination rotation resets deficits
R02-M14 representation migration initializes zero state
```

## 11. Promotion boundary

R02 may be marked complete only when the following are all independently green:

```text
Lean general trace theorem
Lean axiom/placeholder audit
Python exact implementation
Rust exact implementation
small-domain exhaustive three-way differential
production U256 arithmetic evidence
canonical byte/root parity
R01 ordered-word integration
R03 state identity and migration integration
exact-head independent review
```

Until then the correct status is:

```text
ONE_STEP_CORE_PROVED
TRACE_THEOREM_SPECIFIED
IMPLEMENTATION_PARTIAL
UNMOUNTED
```
