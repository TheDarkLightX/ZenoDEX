# Frontier Problem Selection: 5 Hard Problems for Structured Iteration

Date: 2026-06-29

Selected via 18-iteration sequential thinking run with explicit falsification
checks. Each problem was scored on compounding value (connections to the 5
AGENTS.md frontier surfaces), structured-iteration payoff, and falsification
risk before selection.

## Selection Criteria

A target qualifies when it connects at least 2 of:

- Lean/ESSO/SMT artifact
- Runtime checker, certificate, canonicalizer, or replay command
- Mechanism-design risk (collusion, MEV, griefing, cartel, withholding)
- Codebase pattern that makes invalid states unrepresentable
- Falsified broad claim replaced by a restricted theorem ladder

Additional filter: the problem must have a single key lemma or insight that
compresses multiple obligations (abstraction compression pattern).

## The 5 Problems

### P1: Coupled Lipschitz Bound (max not sum)

**Claim**: `|splitCont(x) - splitCont(y)| <= L * |x - y|` where
`L = max(c0*K0/M0, c1*K1/M1)`, tighter than the current formal bound
`K0/M0 + K1/M1`.

**Key lemma**: For `x, y >= 0`, `|x - y| <= max(x, y)`.
Proof: if `x >= y`, `|x-y| = x-y <= x = max(x,y)`. Symmetric for `y > x`.

**Application**: The split derivative `f'(a) = T0(a) - T1(a)` where
`T0(a) = c0*K0*M0/(M0+c0*a)^2 >= 0` and `T1(a) = c1*K1*M1/(M1+c1*(D-a))^2 >= 0`.
So `|f'(a)| <= max(T0(a), T1(a)) <= max(sup T0, sup T1) = max(c0*K0/M0, c1*K1/M1) = L`.

**Falsification history**: The initial claim "split Lipschitz = max" is FALSE.
The exact Lipschitz constant is `max(|f'(0)|, |f'(D)|)`, which is `<= L` but
not equal. The corrected claim "split Lipschitz <= L" is TRUE and tighter
than the triangle-inequality bound `K0/M0 + K1/M1`.

**Non-claims**:
- L is an upper bound, not the exact Lipschitz constant.
- The exact constant is `max(|f'(0)|, |f'(D)|) <= L`.

**Compounding value**: 4/5 surfaces. Tightens floor error (L+1 per pool),
argmax proximity (2L+2), and unlocks P3.

**Verification**: Lean proof extending `CpmmSplitConcavity.lean` or
`CeilingFeeRounding.lean`. Empirical test comparing L vs sum vs actual sup|f'|.

**Iteration estimate**: 10-15 (key insight already found).

---

### P2: Strong Concavity m From Pool Parameters

**Claim**: `m >= 2*c0^2*K0*M0/(M0+c0*D)^3 + 2*c1^2*K1*M1/(M1+c1*D)^3`

**Key lemma**: `inf(f+g) >= inf(f) + inf(g)` for continuous f, g on compact set.
Proof: for any a, `f(a) >= inf(f)` and `g(a) >= inf(g)`, so `(f+g)(a) >= inf(f)+inf(g)`,
so `inf(f+g) >= inf(f)+inf(g)`.

**Application**: `f''(a) = -T0(a) - T1(a)` where
`T0(a) = 2*c0^2*K0*M0/(M0+c0*a)^3` (decreasing) and
`T1(a) = 2*c1^2*K1*M1/(M1+c1*(D-a))^3` (increasing).
`|f''(a)| = T0(a) + T1(a) >= inf T0 + inf T1`.

**Non-claims**:
- This is a lower bound on m, not the exact m.
- The bound degenerates when `D >> M` (m -> 0), which is correct behavior.
- The exact m is `inf(T0+T1) >= inf T0 + inf T1`.

**Compounding value**: 3/5 surfaces. Removes external hypothesis, makes window
bound `sqrt(2*eps/m)` fully determined by pool parameters.

**Verification**: Lean proof extending `CpmmSplitConcavity.lean` or
`StrongConcavityWindowBound.lean`. Empirical test comparing lower bound vs
actual `inf|f''|`.

**Iteration estimate**: 15-20.

---

### P3: K-Pool Coupled Argmax Proximity

**Claim**: For K pools, `prodFloor(argmax_continuous) >= discrete_opt - ((K+1)*L + K)`
where `L = max_i(c_i*K_i/M_i)`.

**Key lemma**: P1 generalized to K pools via coordinate-slice induction. Each
gradient component `df/da_j = c_j*g_j'(c_j*a_j) - c_K*g_K'(c_K*a_K)` is a
difference of non-negative terms, so `|df/da_j| <= max(c_j*K_j/M_j, c_K*K_K/M_K) <= L`.

**Non-claims**:
- Uses L-infinity norm for the allocation vector.
- Quotient bridge assumes no-duplicate stable IDs.
- Top-level theorem requires the certificate format from `KPoolSplitConcavity.lean`.

**Compounding value**: 4/5 surfaces. Unlocks top-level all-K theorem, production
K-pool routing security.

**Verification**: Lean proof extending `KPoolSplitConcavity.lean` and
`KPoolDiscreteArgmaxProximity.lean`. Empirical K-pool simplex coverage.

**Iteration estimate**: 30-50 (most complex proof architecture).

**Depends on**: P1.

---

### P4: Nash Equilibrium Among Filled Users

**Claim**: In the min-out-cap game, filled users have no profitable `min_out`
deviation (restricted equilibrium over `min_out` only, among filled users only).

**Falsification history**: The broad claim "full Nash equilibrium" is FALSE.
Unfilled users can profitably deviate by lowering `min_out` (they go from 0
output to some output > 0). The corrected claim restricts to filled users,
who cannot improve by changing `min_out` (lowering doesn't change fill status
or output; raising risks becoming unfilled).

**Non-claims**:
- NOT a full Nash equilibrium (unfilled users can profitably deviate).
- NOT an equilibrium over input amounts (only `min_out`).
- NOT a Bayesian or correlated equilibrium.
- Unfilled user deviations are welfare-improving, not strategic manipulation.

**Compounding value**: 4/5 surfaces. Mechanism-design risk, collusion resistance.

**Verification**: Lean proof extending `MinOutCapGameTheory.lean`. Empirical
game-theory test with deviation enumeration.

**Iteration estimate**: 30-50 (game tree exploration, equilibrium concept design).

---

### P5: Tight Stateful Attack Bound With Pool Depth

**Claim**: `max_{a_B} gain(a_A, a_B) = K*a_A*s / ((M+s)*(M+a_A+s))` where
`s = sqrt(M*(M+a_A))`. The optimal attack size is `a_B* = sqrt(M*(M+a_A))`.

**Derivation**: `gain = K*a_A*a_B / ((M+a_B)*(M+a_A+a_B))`. Setting
`d(gain)/d(a_B) = 0` yields `a_B^2 = M*(M+a_A)`, so `a_B* = sqrt(M*(M+a_A))`.

**Key insight**: The tight bound decreases with pool depth M, while the
Lipschitz bound `L*a_A = K*a_A/M` does not capture this depth dependence.
The second-order approximation `|f''(0)|*a_A^2/2` was falsified as a universal
bound. The exact closed form is the correct replacement.

**Non-claims**:
- Fee-free CPMM only. Fee-bearing extension is open.
- Single pool (not multi-hop).
- The attacker optimizes a_B; a_A is fixed.

**Compounding value**: 5/5 surfaces (highest). Replaces falsified bound with
exact form, connects security to pool depth, provides runtime risk parameter.

**Verification**: Lean proof extending `ConcavityConservationLaw.lean`.
Empirical test comparing exact vs Lipschitz vs second-order.

**Iteration estimate**: 30-50 (calculus derivation, Lean formalization of
optimization).

---

## Dependency Graph

```
P1 (Coupled Lipschitz) ---> P3 (K-pool Coupled)
P2 (Strong Concavity)    (independent)
P4 (Nash Filled-User)    (independent)
P5 (Tight Attack Bound)  (independent)
```

P1, P2, P4, P5 can be worked on in parallel. P3 depends on P1.

## Execution Order

1. P1 (Coupled Lipschitz) - shortest proof, highest unlock value
2. P5 (Tight Attack Bound) - highest compounding (5/5), independent
3. P2 (Strong Concavity) - independent, removes external hypothesis
4. P4 (Nash Filled-User) - independent, mechanism-design surface
5. P3 (K-pool Coupled) - depends on P1, most complex architecture

## Tool Strategy

| Problem | Sequential Thinking | Morph | Research Kernel |
|---------|--------------------|-------|-----------------|
| P1      | 10-15 (light)      | No    | Record pattern  |
| P5      | 30-50 (heavy)      | Yes   | Record falsification + exact form |
| P2      | 15-20 (medium)     | Yes   | Record hypothesis removal |
| P4      | 30-50 (heavy)      | Yes   | Record restricted equilibrium |
| P3      | 30-50 (heavy)      | Yes   | Record top-level all-K theorem |

Total estimated iterations: 115-185.

## Reusable Abstraction Patterns Discovered

1. **|x-y| <= max(x,y) for x,y >= 0**: Replaces triangle inequality
   `|x-y| <= x+y` when both terms are non-negative. Applicable to any
   derivative that is a difference of positive monotone terms.

2. **inf(f+g) >= inf(f)+inf(g)**: Universal lower bound on the infimum of
   a sum. Applicable to any strong-concavity or curvature lower bound.

3. **Restricted equilibrium concept**: When full Nash is false, identify
   the subset of players and deviation types for which no-gain holds.
   The restriction is the theorem, not a weakness.

4. **Exact adversary optimization**: When the adversary's parameter has a
   clean optimal value (e.g., `a_B* = sqrt(M*(M+a_A))`), the exact bound
   replaces loose Lipschitz and falsified approximations.

5. **Pool depth as security parameter**: The tight attack bound decreases
   with M, making pool depth a first-class security parameter rather than
   just a liquidity parameter.
