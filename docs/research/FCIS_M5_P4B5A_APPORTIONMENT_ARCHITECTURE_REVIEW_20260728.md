# FCIS M5-P4B5A Apportionment Architecture Review

**Outcome:** `KEEP_BPRIME_CHOOSE_CURSOR` — candidate 5, the scalar cursor
over a hierarchical mechanical-word schedule with closed prefix-count
formulas.

**Review of:** prompt
`docs/research/prompts/fcis_m5_p4b5a_fee_dimensions_and_accounting_v1/KIMI_APPORTIONMENT_ARCHITECTURE_REVIEW_PROMPT.md`

**Authority:** none. This document does not authorize implementation,
mounting, or amendment of the frozen packet. The frozen P4B5A D04 rule must
be amended separately after independent review.

**Research kernel:** run `run_78095dc928c34012`. Decision atom
`atom_7ec5d52c46e64171`; refutation plan `atom_e1c9632840c54ca1` with five
named falsification tests, three executed with zero violations; refutation
atoms `atom_ee50ac87ce254288` (stateless), `atom_179175a1f7e74ca7`
(contiguous cursor).

## 1. Source and exact SHA inspected

Worktree at `c4879d8a570ad0418ccb8778ab9ea401ad0c5aca`. Inspected: the
frozen P4B5A packet, the review prompt, `src/core/fcis_protocol_fee_accounting_values.py`,
`src/core/fcis_protocol_fee_accounting_transition.py` (D04 implementation
under review), `src/core/fcis_settlement_strong_validator.py` lines
1090–1176 (credit lineage), `src/core/fee_accumulator_transition.py` (V1
scalar), `src/core/fcis_step_evaluator.py` lines 544–637 (V1 fee
candidate), `src/core/batch_clearing.py` lines 701–740 (V1 recipient
credit). Every numerical witness below was produced by executing the
candidate formulas directly (deterministic script, no repository mutation;
the script is reproduced in the appendix).

## 2. Restatement of the fixed B′ boundary

```text
SettlementPhase(S_pre, command, authenticated_context)
  -> Reject(reason) | (S_mid, exact_protocol_fee_credits, replay_evidence)

ApportionmentPhase(S_mid, credits, authenticated_policy, q_pre)
  -> Reject(reason) | (S_post, distributions, q_post, canonical_patch)

Step -> Reject with no successor authority
      | one accepted candidate at one linearization point
```

`distributions` are evidence of balance changes already applied to
`S_post`, never executable shell instructions. A refutation attempt against
B′ itself appears in sections 5 and 12; B′ survives.

## 3. Candidate comparison table

| # | Candidate | Closest family | Eliminated at ranking level | Verdict |
|---|---|---|---|---|
| D04 | Monetary dust in accumulator + keyholder balance | carry-forward IOU | 1: unfunded monetary claim, permanent stuck state | Refuted (fact 5; trace T3) |
| 1 | Stateless canonical remainder | Hamilton / largest remainder | 3: fails L3 | Refuted (Q1 proof; trace T1) |
| 2 | Contiguous 10 000-slot cursor | cyclic schedule | 4: prefix discrepancy 2 222.4 atoms | Refuted (trace T2) |
| 2′ | SWRR smooth weighted scheduler | nginx SWRR | 5/6: per-atom loop; 3 counters | Refuted (L6) |
| 3 | Per-beneficiary error/residue vector | error diffusion | viable; dominated at 5–6 (2 free scalars vs 1) | Dominated runner-up |
| 4 | Smooth weighted scheduler, bounded discrepancy | deficit round-robin | 5: per-atom loop | Refuted (L6) |
| 5 | Scalar cursor, hierarchical mechanical word, closed prefix counts | online apportionment / mechanical-word hierarchy | passes all levels | **Chosen** |
| 6 | Smaller equivalent | — | none: Q1 lower bound is one scalar; candidate 5 achieves it | Subsumed |
| 7 | Locked-account monetary carry | escrow | out of scope; changes key-control semantics | V3 comparison only |

## 4. Formal transition algebra

### 4.1 Chosen candidate (mechanical-word cursor)

Per key `k = (source_account_pubkey, asset)`, policy `p = (w0, w1, w2)`
with `w0 + w1 + w2 = D = 10_000`, fixed semantic role order (buyback,
treasury, rewards):

```text
P0(t) = ⌊t·w0 / D⌋
R0(t) = t − P0(t)
P1(t) = ⌊R0(t)·w1 / (D − w0)⌋   if D − w0 > 0, else 0
P2(t) = t − P0(t) − P1(t)

Allocate_p(q, n):
    T  = q + n
    Ai = Pi(T) − Pi(q)           for i in {0, 1, 2}
    q' = T mod D
```

State: one integer `q ∈ [0, D)` per key. The source is debited `n` in
full; destinations are credited `A0, A1, A2`.

### 4.2 Runner-up (error vector)

State `(r0, r1)` signed residues (`r2 = −r0 − r1` derived):

```text
a0 = ⌊(n·w0 + r0)/D⌋;  r0' = n·w0 + r0 − a0·D
a1 = ⌊(n·w1 + r1)/D⌋;  r1' = n·w1 + r1 − a1·D
a2 = n − a0 − a1
```

Same laws, two independent scalars in `(−D, D)`, signed arithmetic in both
languages, no fairness gain. Dominated on state size and proof surface.

### 4.3 Refuted candidates

- D04: `total = f + d`; successor claims `dust'` that remains spendable.
  Trace T3 produces the permanent stuck state.
- Hamilton: floors plus largest-remainder tie-break. Trace T1 breaks L3.
- Contiguous cursor: contiguous weight ranges over slot positions. Trace
  T2 shows the burst.

## 5. Proofs and counterexamples for L1–L10

**L1.** `A0 + A1 + A2 = T − q = n` by telescoping of `P2`. Per key, per
asset only. ∎

**L2.** Every fresh atom is assigned in-step. Successor metadata is a
schedule position claiming no money, future debit, or IOU. This is the
exact repair of D04's L2 violation. ∎

**L3.** Lemma: `Pi(t + D) = Pi(t) + wi` for all `t ≥ 0`, by floor
arithmetic with the `D − w0 > 0` guard covering the joint `w0 = D`,
`w1 = 0` branch. With `q + a = q1 + cD`:
`Pi(q+a+b) − Pi(q+a) = Pi(q1+b) − Pi(q1)`, so legs telescope in amounts
and cursor. ∎ Corroboration: exhaustive `D ∈ {4, 7, 10}` over all weight
triples, cursors, and splits `a + b ≤ 2D` — zero violations; 3 000 random
`D = 10 000` cases — zero violations.

**L4.** Per-key state and inputs only; strict lexicographic output order
over `(source_account_pubkey, asset)`; no map iteration or worker order
enters the formula. ∎

**L5.** Deltas aggregate additively in the canonical balance transition.
Full alias yields net-zero deltas, patch `None`, and a valid distribution
record (`ΣAi = n` is alias-independent). ∎

**L6.** No per-atom loop: three closed-form floor evaluations per key.
O(1) time and state per key, O(K) total. Products stay below 2^54 under
the admitted bounds (§7 arithmetic in §10). ∎

**L7.** Floor division over nonnegative integers and `mod` by a constant
only. No signed arithmetic, floats, map order, coercion, or host-width
dependence. The division guard is explicit in both languages. ∎

**L8.** See §8: new policy epoch on any weight, destination, or version
change; cursors reset to 0; reset bound in the receipt with both policy
hashes; no reinterpretation; no caller-selected default. ∎

**L9.** Allocate is total over validated inputs; validation failures
return before any successor exists; the B′ wrapper discards the whole
step on any phase rejection. ∎

**L10.** V1 nonzero scalar dust remains `UNOWNED_LEGACY_DUST`. The cursor
state is a new schema family bound to the policy hash; `dust = 0` migrates
to all cursors 0. ∎

**B′ refutation attempt (Q9).** Trace: the protocol-fee recipient trades
in the same batch and spends the balance the fee phase would distribute.
Deterministic in-step ordering yields at worst a conservative whole-step
reject via `INSUFFICIENT_SOURCE_BALANCE`, never a wrong accept. Inline
distribution violates D08/D10 and grows settlement TCB; a cross-batch
command creates a spend window, a permanent stuck-key mode, operator
timing discretion, and a new command surface. B′ preserved.

## 6. Minimal distinguishing traces (all executed)

| ID | Trace | Result |
|---|---|---|
| T1 | Hamilton, D=10, w=(5,3,2), 1+1 vs 2 | `[2,0,0]` ≠ `[1,1,0]` — stateless eliminated |
| T2 | Contiguous cursor, w=(3333,3333,3334), full period | max prefix discrepancy **2222.4 atoms** |
| T3 | D04: credit 10, keyholder spends 10, next step | permanent `INSUFFICIENT_SOURCE_BALANCE` |
| T4 | Zero weights: (10000,0,0), (0,10000,0), (0,0,10000), (5000,5000,0), (1,1,9998), (9999,1,0) | period totals exactly `wi` |
| T5 | w=(3333,3333,3334), t=1,2,3 | first two atoms go to role2 (remainder sink) |
| T6 | q=9999, n=3, same weights | whole = (1,0,2); split 1+2 = (1,0,0)+(0,0,2) — telescopes |
| T7 | Recipient spends in same batch | conservative reject only |
| T8 | Full alias | net zero deltas, patch `None`, record valid |
| T9 | Policy epoch change at q≠0 | cursor resets to 0; receipt binds both hashes |
| T10 | q=9999, n=7.68·10^11 | intermediates < 2^54; u64 safe |

The prompt's ten required adversarial traces map: 1→T7 (spending after
the step is harmless: the cursor claims nothing spendable); 2, 3→L3
exhaustive sweep; 4→T4/T5; 5→T8; 6→§5 L4; 7→T9; 8→§7 predictability
bound; 9→T10; 10→checker mutation suite for the successor packet.

## 7. Strategic fairness and prefix-discrepancy analysis

Proved signed bounds (floor deficits `e0, f1 ∈ [0, 1)`):

```text
P0 − ideal0 ∈ (−1, 0]     role0 slightly under-receives at prefixes
P1 − ideal1 ∈ (−1, 1)     role1 symmetric
P2 − ideal2 ∈ [0, 2)      role2 is the remainder sink, never under-receives
```

Measured maxima over a full period: (0.9999, 0.9998, 1.9996) for
w=(1,1,9998); (0.9999, 0.6666, 1.3332) for w=(3333,3333,3334).

- Max consecutive atoms per destination: inherent to the weights; small
  weights are spaced ≈ `D/wi` apart, the best achievable spacing.
- Long-run: exact per period of D atoms, zero asymptotic bias.
- Starting state: cursor offset shifts phase only; per-period totals are
  offset-invariant.
- Predictability: the schedule is public and deterministic. Timing a fee
  to a cursor boundary moves any beneficiary by less than the prefix
  bound (under 2 atoms per role per epoch, dust-level). The schedule is
  amount-blind, so fee size cannot multiply this.
- Administrator resets: admins choose only when to change policy, never
  an interior reset point; the effect is bounded by the same envelope.
- Role-order bias is an explicit design choice: role2 absorbs residual
  rounding (`[0, 2)`), role0 carries `(−1, 0]`, role1 is symmetric.
  Reorder roles deliberately and version the choice in the policy schema.

**Narrow fairness claim:** exact per period; signed prefix discrepancy
within the bounds above; no participant action exceeds those bounds.
Nothing stronger is claimed.

## 8. Policy migration decision table

| Change | Weights | Destinations | Schema | Rule |
|---|---|---|---|---|
| Weight change | differs | any | same | New epoch; cursors reset 0; receipt binds both policy hashes |
| Destination change | same | differs | same | New epoch; cursors reset 0 (uniform rule) |
| Version/tag change | any | any | new | Authenticated migration with reset; new schema IDs |
| V1 scalar dust | — | — | — | `dust = 0` → cursors 0; nonzero → `UNOWNED_LEGACY_DUST` |
| Caller-initiated reset | — | — | — | Rejected by construction; no caller-selected reset |

## 9. ESSO-ready bounded model

Model: `D = 4`; weights `(2,1,1), (1,2,1), (0,4,0), (1,0,3)`; `q ∈ ℤ₄`;
`n ∈ 0..5`; two policy epochs with the reset rule. Properties: per-step
conservation; L3 for every `a + b ≤ 5`; alias aggregation determinism;
reset correctness; fragmentation invariance for every two-way partition
of N ≤ 5; rejection atomicity on invalid policy sums and out-of-range
cursors. Lifting: the arithmetic laws are proved D-parametrically; the
bounded model validates implementation control flow and guards, not the
parameter. It complements, and does not replace, the §5 proofs.

## 10. Python/Rust pseudocode with identical integer semantics

```text
constant D = 10_000                      # u64
require: w0 + w1 + w2 == D, q < D, n <= MAX_AGGREGATE

def allocate(w0, w1, w2, q, n):
    t      = q + n                       # < 2^40 under bound
    p0q    = (q * w0) // D               # products < 2^54, u64-safe
    p0t    = (t * w0) // D
    a0     = p0t - p0q
    r0q    = q - p0q
    r0t    = t - p0t
    if D - w0 > 0:
        a1 = (r0t * w1) // (D - w0) - (r0q * w1) // (D - w0)
    else:
        a1 = 0
    a2     = n - a0 - a1
    return ((a0, a1, a2), t % D)
```

Bounds: `n ≤ 256 × 3·10^9 = 7.68·10^11`; `t < 2^40`; products `< 2^54`;
even 65 536 credits keep products below `1.98·10^18 < 2^63`. Rust: `u64`
with `checked_*` at the boundary and identical guard order; no `u128`, no
signed values. Python matches floor semantics exactly (nonnegative
operands only). Every multiplication and addition requiring checked
arithmetic is enumerated above; there are no others.

## 11. Canonical encoding and golden-vector field inventory

New V2 schema family: `apportionment-cursor-map/v2` (canonical map
`(source_account_pubkey, asset) → cursor`, bound to `policy_hash`);
amended `fee-distribution-policy/v2`; amended `asset-fee-distribution/v2`
(drops `dust_carried`, adds `cursor_pre/cursor_post`); transition-result
envelope `{"schema": id, "value": projection}` over
`canonical_json_bytes`. Golden vectors: every required policy tuple;
`n ∈ {0, 1, 9 999, 10 000, max credit, max aggregate}`; cursors `{0, 1,
9 999}`; split-equivalence pairs; period crossings; alias configurations;
zero-credit steps; policy-reset receipts; V1 migration accept (dust=0)
and reject (nonzero); canonical bytes in both languages.

## 12. Recommended candidate with decision rationale

**Q1:** State is necessary. Stateless + L1 + L3 forces per-beneficiary
additivity, hence linearity `f_i(n) = c_i·n`, hence `Σc_i = 1`, a
single-beneficiary dictator. Hamilton counterexample executed (T1).
Lower bound: exact D-periodic schedules with `gcd(w, D) = 1` need D
positions; one scalar in `ℤ_D` is minimal and achieved.

**Q2:** Smallest sufficient state: one scalar cursor. Error vector needs
two free scalars and signed arithmetic; SWRR needs three counters plus an
illegal per-atom loop; stateless fails L3.

**Q5:** Aggregation before allocation is sound (L3 iterative). Unrelated
keys commute (per-key state, additive commutative balance aggregation,
lexicographic output), licensing bounded grouping and deterministic
parallel evaluation.

**Q9:** B′ preserved; the best attack found yields a conservative reject.

**Q10:** Double application is prevented at the type boundary:
distribution values exist only inside the token-gated transition result;
the shell receives projection bytes with no effect-typed variant (the
outbox registry stays without one); the sole state effect is
`CanonicalBalancePatchV1`; the commit bundle binds `(credits,
policy_hash, cursor_pre/post, patch, distributions)` for verifier replay.
A negative test asserts receipt bytes contain no effect opcode.

**Rationale by the ranking rule:** D04 fails level 1. Stateless fails
level 3. Contiguous cursor fails level 4. SWRR/DRR fail levels 5–6. The
error vector is lawful but dominated at levels 5–6 by the single-scalar
cursor, which also has the smallest proof surface (three floor
identities) and the simplest exact parity (unsigned floors only).

## 13. Explicit nonclaims and residual risks

- No fairness claim beyond the proved signed prefix bounds and exact
  per-period totals.
- The cursor schedule is predictable by design; influence is bounded
  (< 2 atoms per role per epoch) but nonzero.
- Role-order bias is real and must be chosen deliberately and versioned
  in the policy schema.
- L3 is a deliberate law; a future requirement for per-call
  amount-dependent rounding must revisit the law before the machine.
- The locked-account monetary carry remains the only design that would
  eliminate the remainder sink; it changes key-control semantics and
  stays a possible V3 research item outside P4B5A.
- This review authorizes nothing; D04 remains frozen until amended under
  independent review.
- The discrepancy bounds are proved and fuzz-verified; a formal
  Lean/ESSO proof of the D-parametric telescoping lemma is recommended
  before mount and was not produced here.

## 14. Exact next implementation checkpoint

**P4B5A packet amendment (prerequisite, review-only):**

1. D04 monetary dust → per-key non-monetary cursor with the §4.1
   algebra; D03 unchanged except the §7 role-order note; D05 bounds now
   cover credits, cursor entries, distributions, deltas, bytes; D08 adds
   the `apportionment-cursor-map/v2` family bound to `policy_hash` and
   the §8 epoch-reset migration rule; the target relation's accumulator
   becomes the cursor map.
2. After amendment: `CommittedFeeAccumulatorStateV2` carries cursor
   entries; `apply_protocol_fee_distribution_v2` uses `allocate`;
   `AssetFeeDistributionV2` drops `dust_carried` and gains
   `cursor_pre/cursor_post`; the dust-entry schema is deleted, per the
   authority-duplication rule; V1 migration maps to cursors.
3. Evidence: the frozen semantic items re-proven, plus §6 traces, §5 L3
   sweeps, §7 discrepancy vectors, §8 migration vectors, §9 ESSO model,
   §11 golden vectors in both languages.
4. Gate: independent review of the amendment before any code change; the
   kernel refutation plan stays open for falsification.

## Appendix: witness script

```python
from fractions import Fraction
import random

D = 10_000

def hamilton(w, n, D):
    floors = [n * wi // D for wi in w]
    rem = n - sum(floors)
    fracs = sorted(range(len(w)),
                   key=lambda i: (Fraction(n * w[i] % D, D), -i), reverse=True)
    out = floors[:]
    for i in fracs[:rem]:
        out[i] += 1
    return out

def contiguous_alloc(w, q, n, D):
    out = [0] * len(w)
    for t in range(q, q + n):
        pos = t % D
        acc = 0
        for i, wi in enumerate(w):
            if acc <= pos < acc + wi:
                out[i] += 1
                break
            acc += wi
    return out, (q + n) % D

def make_P(w, D):
    w0, w1, w2 = w
    def P0(t): return t * w0 // D
    def R0(t): return t - P0(t)
    def P1(t): return (R0(t) * w1 // (D - w0)) if D - w0 > 0 else 0
    def P2(t): return t - P0(t) - P1(t)
    return (P0, P1, P2)

def mech_alloc(w, q, n, D):
    P = make_P(w, D)
    return tuple(P[i](q + n) - P[i](q) for i in range(3)), (q + n) % D

# T1: Hamilton additivity failure
assert hamilton((5, 3, 2), 2, 10) != [
    x + y for x, y in zip(hamilton((5, 3, 2), 1, 10), hamilton((5, 3, 2), 1, 10))
]

# T2: contiguous prefix discrepancy (prints 2222.4 for (3333,3333,3334))
w = (3333, 3333, 3334)
q, counts, worst = 0, [0, 0, 0], Fraction(0)
for t in range(1, D + 1):
    one, q = contiguous_alloc(w, q, 1, D)
    counts = [c + o for c, o in zip(counts, one)]
    worst = max(worst, max(abs(counts[i] - Fraction(t * w[i], D)) for i in range(3)))

# T4: period exactness over zero-weight branches
for wq in [(0, 0, 10_000), (1, 1, 9_998), (3_333, 3_333, 3_334),
           (9_999, 1, 0), (10_000, 0, 0), (0, 10_000, 0), (5_000, 5_000, 0)]:
    P = make_P(wq, D)
    assert tuple(P[i](D) for i in range(3)) == wq

# L3: exhaustive small-D sweep
for Ds in (4, 7, 10):
    for w0 in range(Ds + 1):
        for w1 in range(Ds - w0 + 1):
            wq = (w0, w1, Ds - w0 - w1)
            for q0 in range(Ds):
                for a in range(0, 2 * Ds + 1):
                    for b in range(0, 2 * Ds + 1 - a):
                        whole, qw = mech_alloc(wq, q0, a + b, Ds)
                        A1, q1 = mech_alloc(wq, q0, a, Ds)
                        A2, q2 = mech_alloc(wq, q1, b, Ds)
                        assert whole == tuple(x + y for x, y in zip(A1, A2))
                        assert q2 == qw

# L3: random fuzz at production D
random.seed(20260728)
for _ in range(3000):
    w0 = random.randint(0, D)
    w1 = random.randint(0, D - w0)
    wq = (w0, w1, D - w0 - w1)
    q0 = random.randint(0, D - 1)
    a, b = random.randint(0, 50_000), random.randint(0, 50_000)
    whole, qw = mech_alloc(wq, q0, a + b, D)
    A1, q1 = mech_alloc(wq, q0, a, D)
    A2, q2 = mech_alloc(wq, q1, b, D)
    assert whole == tuple(x + y for x, y in zip(A1, A2)) and q2 == qw

# prefix discrepancy sweep
for wq in [(0, 0, 10_000), (1, 1, 9_998), (3_333, 3_333, 3_334), (9_999, 1, 0)]:
    P = make_P(wq, D)
    worst = [Fraction(0)] * 3
    for t in range(1, D + 1):
        for i in range(3):
            worst[i] = max(worst[i], abs(P[i](t) - Fraction(t * wq[i], D)))
```
