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

**Status:** CLOSED as a formal/replay artifact. `CeilingFeeRounding.lean`
proves `split_lipschitz_coupled`; `ceiling_fee_rounding_test.py` now checks
20,000 random split pairs, verifies the exact boundary-slope constant stays
within `L`, and records that the gross production bound and low-fee effective-L
regression are not universally ordered under fees. The 2026-06-30 refinement
adds `cpmm_prod_certified_anchor_argmax_distance`, giving the production
ceiling-fee radius
`sqrt(2*(alpha + K0/M0 + K1/M1 + 2)/m)` from a certified anchor, plus
`abstract_oracle_perturbed_argmax_distance` for the exact
`sqrt(2*(f_cont(b*)-f_prod(argmax))/m)` oracle radius. The sharpness theorem
`abstract_one_sided_perturbed_argmax_distance_sharp_quadratic` now proves that
the generic `sqrt(2*(alpha+epsilon)/m)` one-sided radius is attained by a
quadratic strong-concavity witness, so the constant cannot be improved without
additional assumptions. The matching research certificate checker now rejects
domains outside its 128-bit float replay lane before recomputing `m`, `tau`, or
radii, converting a concrete overflow family into a structured `BAD_DOMAIN`
boundary result.

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

**Verification**: DONE in `CeilingFeeRounding.lean`,
`DiscreteArgmaxProximity.lean`, `docs/research/ceiling_fee_rounding_test.py`,
and `docs/research/discrete_argmax_proximity_test.py`.

**Iteration estimate**: 10-15 (key insight already found).

---

### P2: Strong Concavity m From Pool Parameters

**Status:** SYNTHESIS PROGRESS WITH BEST-COVER RATIONAL INTERVAL FLOOR. `CpmmSplitConcavity.lean`
now contains the arithmetic curvature-term lower-bound helper, proves the
endpoint lower bound is positive, proves
`splitFunctionCont_strong_concavity_from_m_certificate`, and adds
`splitFunctionCont_strong_concavity_from_curvature_floor`: if an external
checker supplies a positive local curvature floor `m <= T0(a)+T1(a)`, then the
conditional second-derivative identity implies `F''(a) <= -m`. It also proves
`strong_concavity_interval_lower_bound`, the local interval theorem
`T0(a)+T1(a) >= T0(hi)+T1(lo)` for `lo <= a <= hi`, and
`strong_concavity_interval_floor_refinement`, which proves splitting an
interval cannot lower either child interval floor.
`concavity_conservation_law_test.py` adds three research-scope pool-parameter
certificate checkers: endpoint, closed-form exact-minimizer replay, and a
rational interval floor checker with exact `{num,den}` arithmetic. The
closed-form exact-minimizer float lane now rejects domains above its 128-bit
research bound before conversion, so oversized pool-valid integers cannot
crash the checker with float overflow. The
best-cover interval builder chooses the largest exact floor from a deterministic
portfolio that includes the uniform cover, so generated best-cover certificates
cannot be worse than uniform placement for the same interval count. The greedy
refinement builder repeatedly splits the weakest interval and is backed by the
Lean split-monotonicity theorem. The bounded optimal midpoint audit searches
all midpoint split schedules under a 16-interval cap, emits the same interval
certificate schema, and found no greedy-vs-optimal counterexample in its seeded
exact-DP replay corpus.

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
- The endpoint m is `inf T0 + inf T1`; the exact m is `inf(T0+T1)` and can be
  strictly larger.
- The closed-form exact minimizer is deterministic research replay today, not
  yet Lean-proven.
- The closed-form exact-minimizer float lane is bounded to the 128-bit research
  domain. Larger domains must use the rational interval certificate path.
- The rational interval floor is a certified lower bound for a finite cover,
  not a proof that the floor equals `inf(T0+T1)`.
- The best-cover interval builder is a finite deterministic portfolio, not a
  proof of optimal interval placement.
- The greedy refinement theorem proves split monotonicity, not global
  optimality of weakest-interval splitting.
- The bounded optimal midpoint audit is exact within its 16-interval midpoint
  search cap, not a proof of unbounded greedy optimality.
- The interval-backed tight argmax composition path consumes a checked `m`
  certificate before accepting a tighter radius. It does not choose the
  production argmax.
- The second-derivative identity and Taylor-remainder bridge are still explicit
  external obligations.
- The `m` certificate checkers are research evidence only and have no
  production, settlement, or consensus authority.

**Compounding value**: 4/5 surfaces. Supplies a deterministic pool-parameter
`m` certificate boundary for the tight argmax-radius chain and now composes
that boundary into the tight argmax certificate checker, while preserving the
calculus assumptions as explicit obligations.

**Verification**: Lean proof in `CpmmSplitConcavity.lean`; endpoint and exact
curvature canonical JSON checkers, rational interval checker, and mutation tests in
`docs/research/concavity_conservation_law_test.py`; pytest wrapper in
`tests/research/test_concavity_conservation_law.py`; reports in
`docs/research/POOL_PARAMETER_M_CERTIFICATE_20260630.md` and
`docs/research/EXACT_CURVATURE_M_CERTIFICATE_20260630.md`.

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

**Status:** PARTIAL, with a sharper scope split and fee-bearing single-pool
extension. The finite optimizer formula is now Lean-proven for the fee-free and
fee-bearing single-pool donation/no-output perturbation models, and empirically
falsified as a bound for the existing filled-A state-change gain semantics.
`ConcavityConservationLaw.lean` proves `cpmm_donation_gain_argmax_bound` and
`cpmm_donation_gain_argmax_bound_with_fee`; `concavity_conservation_law_test.py`
replays both optimizers and includes a hard regression guard against applying
the donation optimizer to the filled-A model.

**Donation/no-output claim**:
`max_{a_B} gain_D(a_A, a_B) = K*a_A*s / ((M+s)*(M+a_A+s))` where
`s = sqrt(M*(M+a_A))`. The optimal donation/no-output attacker size is
`a_B* = sqrt(M*(M+a_A))`.

**Fee-bearing single-pool extension**: with net inputs
`u = gammaA*a_A` and `v = gammaB*a_B`, the gain is
`K*u*v / ((M+v)*(M+u+v))`. The optimum net attacker size is
`s = sqrt(M*(M+u))`, so the raw attacker size is `s/gammaB` when
`gammaB > 0`.

**Derivation**: `gain_D = K*a_A*a_B / ((M+a_B)*(M+a_A+a_B))`. Instead of
differentiating, the Lean proof uses the algebraic certificate
`s*(M+a_B)*(M+a_A+a_B) - a_B*(M+s)*(M+a_A+s) = s*(a_B-s)^2`
under `s^2 = M*(M+a_A)`.

**Key insight**: There are two stateful attack semantics. The existing filled-A
Lean model, where A receives CPMM output, has a different gain expression and
approaches the asymptotic bound `K*a_A/(M+a_A)` as `a_B` grows. The finite
optimizer `sqrt(M*(M+a_A))` belongs to the donation/no-output perturbation
model. Keeping those models separate prevents a plausible but false mechanism
claim from being promoted.

**Non-claims**:
- Single pool, not multi-hop.
- The fee-bearing theorem needs `gammaB > 0`; when `gammaB = 0`, no finite raw
  attacker-size optimizer is exposed.
- Donation/no-output optimizer is not a bound for filled-A state-change gain.
- The filled-A model still uses its existing asymptotic bound theorem.

**Compounding value**: 5/5 surfaces (highest). Replaces falsified bound with
exact form, connects security to pool depth, provides runtime risk parameter.

**Verification**: Lean proof in `ConcavityConservationLaw.lean`; empirical
optimizer replay and wrong-model falsifier in
`docs/research/concavity_conservation_law_test.py`.

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

1. P1 (Coupled Lipschitz) - CLOSED; use it as the dependency for P3.
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
