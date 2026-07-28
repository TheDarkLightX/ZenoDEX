# FCIS M5-P4B5A apportionment architecture: corrected report

**Outcome:** `KEEP_BPRIME_CHOOSE_CURSOR` with the amended composition
(provisional-credit port + mechanical-word allocation + policy-independent
cursor + net alias-aware patch). The mechanical-word allocator remains the
leading smallest reviewed construction. This document authorizes no
implementation, amendment, mount, or claim promotion.

**Provenance:**

```text
committed head:   c4879d8a570ad0418ccb8778ab9ea401ad0c5aca
git diff HEAD sha256:
  68e0298b987778240080f32bb894f209ed1f14df52ca5318bc8d810b9c29bc27
prior report sha256:
  66fb4762565f1a9ddc515f1d847f800959aa313b3a3b704878195dcdb86ab871
independent review sha256:
  fe00d2cc9bfc873b2881bbc51addbb53cfa65665608e48cb49983b246240e210
```

**Research kernel:** run `run_78095dc928c34012`. Corrected decision atom
`atom_70936224ad394037` (supersedes `atom_7ec5d52c46e64171` via
`edge_b8cd8a67deb440a4`); errata atom `atom_19797b9aaae34f98`; refutation
plan `atom_56a12a4c330f4215`. Kernel instances are separate databases in
this environment: the independent review's `atom_88eacb0842fe43f5` is not
retrievable from this instance, and this run was not retrievable from the
reviewer's instance. Atom IDs are therefore provenance labels, not portable
references; the counterexample content is reproduced in full below.

## 1. Disposition of the independent review findings

| Finding | Priority | Disposition | Verified |
|---|---|---|---|
| POLICY-RESET-AMPLIFICATION-001 | P0 | **Accepted.** The reset rule is refuted; corrected to cursor preservation (§3.4). Counterexample reproduced exactly | Executed (§6 C1, C2) |
| BPRIME-STAGED-CREDIT-002 | P0 | **Accepted.** B′ amended with a non-spendable provisional-credit port (§3.2). The recipient-spend trace no longer exists as a reject class | Design; BDD proposed (§8) |
| INTEGER-DOMAIN-PARITY-003 | P0 | **Accepted.** `MAX_FEE_AMOUNT_V2 = 2^256−1` confirmed at `fcis_protocol_fee_accounting_values.py:33`. u64 claim withdrawn; periodic decomposition adopted (§3.5) | Executed (§6 C4) |
| ALIAS-GROSS-DEBIT-004 | P1 | **Accepted.** Gross source check confirmed at `fcis_protocol_fee_accounting_transition.py:265`. Eliminated by the provisional port; net alias-aware aggregation specified (§3.6) | Source-verified |
| POLICY-ROLE-ORDER-005 | P1 | **Accepted.** Role order is fixed in `AlgorithmVersion`; permutation is an algorithm migration, not a policy field (§3.7) | Design |
| EVIDENCE-PROVENANCE-006 | P1 | **Accepted.** This report binds the committed head plus dirty-patch hash; the witness script is preserved in the appendix and re-executed; unexecuted items are labeled proposed (§8); kernel portability limitation recorded above | Executed |
| GLOBAL-BEST-CLAIM-007 | P2 | **Accepted.** "Best" downgraded to "leading smallest reviewed construction"; the state lower bound is restated with the gcd condition (§4) | Editorial |

## 2. Errata against the first report

1. The policy-reset rule (L8, migration table, fairness section, D08
   proposal) is withdrawn. It admitted unbounded cumulative bias.
2. The Rust u64 selection is withdrawn. The admitted domain is U256.
3. The phrase "all executed" overclaimed: T3, T6, T7, T8, T9, T10 were
   argued, not executed. Every trace in this corrected report is labeled
   EXECUTED or PROPOSED individually.
4. The ESSO model was a specification, not a run. It remains PROPOSED.
5. "Best available" minimality claims are withdrawn (see §4).

## 3. Corrected architecture

```text
exact settlement replay
  -> controlled provisional fee-credit batch
  -> mechanical-word allocation under authenticated policy
       with a policy-independent per-key cursor
  -> one net alias-aware canonical balance patch
  -> one decision, receipt, replay update, atomic commit bundle
```

### 3.1 Composition contract (amended B′)

```text
SettlementPhase(S_pre, command, authenticated_context)
  -> Reject(reason)
  | (S_mid, provisional_fee_credits, replay_evidence)

ApportionmentPhase(S_mid, provisional_fee_credits,
                   authenticated_policy, cursor_pre)
  -> Reject(reason)
  | (S_post, distributions, cursor_post, net_canonical_patch)

Step -> Reject with no successor authority
      | one accepted candidate at one linearization point
```

### 3.2 The provisional-credit port (closes BPRIME-STAGED-CREDIT-002)

`ProvisionalProtocolFeeCreditV2(source_account_pubkey, asset, amount,
lineage)` is a typed value produced at the exact replay site, with the same
lineage proof as today (every credit matches a protocol-recipient atom of
the same replay). It is not a balance and it is not spendable by any
intent. The settlement phase's balance deltas exclude the recipient credit;
the apportionment phase consumes the provisional credits and emits only
destination credit deltas; both compose into one staged balance candidate
and one canonical patch before commitment.

Consequences:

- No committed intermediate source balance exists.
- No keyholder-controlled balance is debited, so no debit-authority rule
  is needed.
- A recipient spending in the same batch cannot reach provisional
  credits, so the fee phase introduces no new reject class and no
  accepted-language contraction. The earlier "harmless conservative
  reject" analysis is vacated, not retained.
- `INSUFFICIENT_SOURCE_BALANCE` leaves the apportionment vocabulary:
  funding is exact by construction (each provisional credit is backed by
  the same replay).
- The within-step lifetime means the port adds no durable state. If a
  future design ever carries credits across steps, the port must become a
  non-spendable committed entry with its own schema, which would be a new
  review.

### 3.3 Allocator (retained, role order fixed)

`D = 10_000`, weights `(w0, w1, w2)` summing to `D`, semantic roles fixed
as (buyback, treasury, rewards) by `AlgorithmVersion`:

```text
P0(t) = floor(t*w0/D)
R0(t) = t - P0(t)
P1(t) = floor(R0(t)*w1/(D-w0))   if D - w0 > 0, else 0
P2(t) = t - P0(t) - P1(t)
```

Retained proved properties: per-step conservation `ΣAi = n`; per-period
exactness `Pi(q+D) = Pi(q) + wi`; L3 telescoping for splits and merges
within a policy epoch; signed prefix discrepancy `(-1,0]`, `(-1,1)`,
`[0,2)` per role.

### 3.4 Cursor lifecycle (closes POLICY-RESET-AMPLIFICATION-001)

The cursor `q ∈ [0, D)` per key is policy-independent metadata: a
schedule phase, not a policy-scoped value.

- Ordinary policy changes (weights, destinations, tags, receipt version)
  **preserve** `q`. The receipt binds the policy hash, the activation
  point, and the pre/post cursor.
- No reset capability exists for any caller, including policy
  administrators. An administrator's economic influence is exactly the
  weight choices themselves, plus rounding inside the cross-policy window
  bounds (§5).
- An algorithm or denominator change is a distinct migration: it requires
  a separately proved cursor mapping (canonical candidate
  `q' = floor(q·D'/D)` with bounded remap error) or a one-time versioned
  activation boundary. It is never an admin-invokable routine.

### 3.5 Integer domain (closes INTEGER-DOMAIN-PARITY-003)

The admitted amount domain is `MAX_FEE_AMOUNT_V2 = 2^256 − 1` (confirmed
at `fcis_protocol_fee_accounting_values.py:33`). The allocation uses
periodic decomposition, which needs no wide intermediate:

```text
n = cycles * D + r                    # divmod only, U256-safe
allocation_i = cycles * wi + interval_count_i(q, r)
interval_count_i(q, r) = Pi(q + r) - Pi(q)   # arguments < 2D
q' = (q + n) mod D
```

Every interval product is below `2·10^8` (u32-safe); `cycles·wi` and the
sums are computed in the runtime's U256 semantics (Python `int`, Rust
`BigUint` as in the existing runtime crate) because output magnitudes are
inherently `≈ n`. EXECUTED: decomposition equals the direct prefix
formula for all tested weights and cursors, including `n = 2^256 − 1`
(§6 C4). The alternative (a narrowed `ValidatedProtocolFeeCreditsV2` port
proving the 256-credit and per-swap bounds) remains lawful but is
unnecessary; decomposition closes the domain without narrowing the
admitted language.

### 3.6 Net alias-aware patch (closes ALIAS-GROSS-DEBIT-004)

Under the provisional port, distribution produces only positive
destination deltas. The rule:

1. Construct signed deltas per distribution (destinations only).
2. Aggregate duplicates by the complete balance key `(account, asset)`.
3. Apply the canonical balance transition once.
4. No solvency check exists in this phase; the gross source-balance check
   is deleted with the port, not patched.

Full alias (all destinations equal the source lineage account) yields
pure credits to that account: valid record, valid patch, no reject.
Partial aliases aggregate identically. The distribution record retains
`source_account_pubkey` as lineage identity; it names no balance
operation.

### 3.7 Role order (closes POLICY-ROLE-ORDER-005)

`(buyback, treasury, rewards)` is fixed inside `AlgorithmVersion`.
Changing the permutation is an algorithm migration under §3.4. The signed
remainder bias (role2 `[0, 2)`) is thereby a constant of the algorithm,
not a policy choice.

## 4. Corrected claims

- The allocator is the **leading smallest reviewed construction** among:
  stateless (refuted), contiguous cursor (refuted), SWRR/DRR (refuted on
  the per-atom loop ban), error vector (lawful, dominated on state size),
  and the reviewed mechanical-word family. No global optimality is
  claimed.
- State lower bound, restated: an exact schedule with period `P` and
  weight vector whose combined `gcd(w0, w1, w2, D) = g` has minimal
  period `D/g`; worst case (`g = 1`) requires `D` distinguishable
  phases, so one scalar in `ℤ_D` is necessary and sufficient in the
  worst case. This is a worst-case bound for exact periodic schedules;
  proving it minimal over all conceivable allocation machines is out of
  scope.

## 5. Strategic fairness (corrected)

- Within one policy epoch: signed prefix bounds `(-1,0]`, `(-1,1)`,
  `[0,2)`; exact totals per period.
- Across an ordinary policy change (cursor preserved): the window bound
  relative to the new ideal is measured at `< 1, < 1, < 2` atoms per
  role (sweep over change-point cursors and target policies, window
  < 500 atoms, §6 C3). After 50 churned policy epochs, a full-period
  window stays inside the same envelope (§6 C6).
- Repeated policy changes cannot recreate the reset amplification: the
  cursor is continuous, so the favorable low-prefix region cannot be
  replayed. Verified: 100 one-atom epochs with preserved cursor equal
  the continuous reference `(33, 33, 34)` exactly (§6 C2).
- Residual administrator influence: the authorized weight choices
  themselves, plus sub-2-atom window rounding per change. No capability
  to erase allocation history exists.

## 6. Executed evidence (this report)

| ID | Content | Status |
|---|---|---|
| C1 | 100-reset counterexample reproduced: `(0,0,100)` vs `(33,33,34)` | EXECUTED (negative regression, preserve) |
| C2 | Cursor preservation: 100 one-atom epochs with policy identity churn equal the continuous reference | EXECUTED, 0 deviations |
| C3 | Cross-policy window sweep (change cursors × 4 policies × 500-atom windows): max discrepancy 0.9999 / 0.9999 / 1.98 | EXECUTED |
| C4 | Periodic decomposition == direct formula over 5 weight sets × 3 cursors × 6 amounts including `2^256 − 1` | EXECUTED, 0 mismatches; interval products < 2·10^8 |
| C5 | Bounded model `D=4`: 2 304 cross-policy cases plus per-epoch L3 sweeps | EXECUTED, 0 violations |
| C6 | 50 churned policy epochs then full-period window: max discrepancy 0.77 / 0.90 / 0.80 | EXECUTED |

The appendix contains the complete witness script; it was re-executed
from this document and passes.

## 7. Corrected migration decision table

| Change | Cursor | Rule |
|---|---|---|
| Weight change | preserved | Receipt binds new policy hash + activation point |
| Destination change | preserved | Same; destinations are not schedule inputs |
| Receipt/tag version | preserved | Same |
| Role permutation | migration | AlgorithmVersion change; proved migration required |
| Denominator change | migration | Proved remap (canonical candidate `q' = floor(q·D'/D)`) or one-time versioned activation boundary |
| Allocation formula change | migration | AlgorithmVersion change |
| V1 scalar dust | — | `dust = 0` → cursor 0; nonzero → `UNOWNED_LEGACY_DUST` |
| Any caller-initiated reset | — | Rejected by construction; the capability does not exist |

## 8. Proposed, not yet executed

1. ESSO run of the §9-model (D=4 spec) with retained report and solver
   fingerprint.
2. Lean (or equivalent) D-parametric proof of conservation, periodicity,
   L3, and the signed prefix bounds.
3. Same-batch fee-recipient spend BDD scenario as a differential vector
   against the mixed validator, expected outcome: no fee-phase reject
   exists under the provisional port.
4. Python/Rust exact-byte golden vectors at every bound (`n ∈ {0, 1,
   9 999, 10 000, max credit, max aggregate, 2^256 − 1}`), policy-change
   receipts, migration vectors, and alias configurations.
5. Checker mutations: cursor erasure, role permutation, gross-check
   restoration, reset-capability insertion, decomposition/direct
   substitution.

## 9. Required WIP dispositions (no action taken here)

The uncommitted work in this tree predates the correction and must remain
unmounted until amended: the Python transition implements the contiguous
block cursor (`_periodic_block_count_v2`,
`fcis_protocol_fee_accounting_transition.py:191-252`) and the gross
source check (`:265`); the Rust module implements monetary dust. Both
contradict the corrected architecture.

## 10. Next authorized action

Prepare a review-only P4B5A packet amendment implementing §3 (provisional
port, fixed-role mechanical word with decomposition, cursor preservation,
net alias-aware patch, migration table), gated on the §8 evidence. Do not
modify the frozen packet or continue Python/Rust integration until the
amendment passes independent review.

## Appendix: witness script (executed 2026-07-28, deterministic)

```python
from fractions import Fraction
import random

D = 10_000

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

def decomposed_alloc(w, q, n, D):
    cycles, r = divmod(n, D)
    P = make_P(w, D)
    interval = tuple(P[i](q + r) - P[i](q) for i in range(3))
    return tuple(cycles * w[i] + interval[i] for i in range(3)), (q + n) % D

# C1: reset counterexample (negative regression)
w = (3333, 3333, 3334)
tot = [0, 0, 0]
for _ in range(100):
    a, q = mech_alloc(w, 0, 1, D)
    tot = [x + y for x, y in zip(tot, a)]
tot2, q = [0, 0, 0], 0
for _ in range(100):
    a, q = mech_alloc(w, q, 1, D)
    tot2 = [x + y for x, y in zip(tot2, a)]
assert tuple(tot) == (0, 0, 100) and tuple(tot2) == (33, 33, 34)

# C2: cursor preservation across policy churn
tot3, q = [0, 0, 0], 0
for epoch in range(100):
    a, q = mech_alloc(w, q, 1, D)
    tot3 = [x + y for x, y in zip(tot3, a)]
assert tuple(tot3) == (33, 33, 34)

# C3: cross-policy window discrepancy
worst = [Fraction(0)] * 3
for q0 in range(0, D, 100):
    for w_new in [(5000, 3000, 2000), (1, 1, 9998), (9999, 1, 0), (3333, 3333, 3334)]:
        P = make_P(w_new, D)
        for t in range(1, 500):
            for i in range(3):
                disc = abs(P[i](q0 + t) - P[i](q0) - Fraction(t * w_new[i], D))
                worst[i] = max(worst[i], disc)
assert all(x < 2 for x in worst)

# C4: decomposition equivalence, including 2^256 - 1
for wq in [(3333, 3333, 3334), (1, 1, 9998), (9999, 1, 0), (10000, 0, 0), (0, 0, 10000)]:
    for q0 in (0, 1, 9999):
        for n in (0, 1, 9999, 10000, 10001, 768_000_000_011, (1 << 256) - 1):
            assert decomposed_alloc(wq, q0, n, D) == mech_alloc(wq, q0, n, D)

# C5: bounded model D=4 with policy changes
Ds = 4
weight_sets = [(2, 1, 1), (1, 2, 1), (0, 4, 0), (1, 0, 3)]
for w_a in weight_sets:
    for w_b in weight_sets:
        for q0 in range(Ds):
            for n1 in range(6):
                for n2 in range(6):
                    A1, q1 = mech_alloc(w_a, q0, n1, Ds)
                    A2, q2 = mech_alloc(w_b, q1, n2, Ds)
                    assert sum(A1) == n1 and sum(A2) == n2
                    whole, qw = mech_alloc(w_a, q0, n1 + 1, Ds)
                    A1b, q1b = mech_alloc(w_a, q0, n1, Ds)
                    A1c, q1c = mech_alloc(w_a, q1b, 1, Ds)
                    assert whole == tuple(x + y for x, y in zip(A1b, A1c)) and q1c == qw

# C6: churned epochs then full-period window
q = 0
random.seed(11)
for _ in range(50):
    w_now = random.choice([(3333, 3333, 3334), (1, 1, 9998), (5000, 3000, 2000), (9999, 1, 0)])
    a, q = mech_alloc(w_now, q, random.randint(0, 300), D)
P = make_P((3333, 3333, 3334), D)
for t in range(1, D + 1):
    for i, wi in enumerate((3333, 3333, 3334)):
        assert abs(P[i](q + t) - P[i](q) - Fraction(t * wi, D)) < 2
```
