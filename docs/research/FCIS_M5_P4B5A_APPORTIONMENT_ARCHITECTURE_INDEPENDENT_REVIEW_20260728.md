# Independent review: FCIS M5-P4B5A apportionment architecture

**Reviewed artifact:**
`docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_REVIEW_20260728.md`

**Reviewed committed head:**
`c4879d8a570ad0418ccb8778ab9ea401ad0c5aca`

**Outcome:** `REVIEW_NO_GO_AMENDMENT_REQUIRED`

**Narrow retained result:**
`KEEP_BPRIME_KEEP_MECHANICAL_CURSOR_AS_LEADING_CANDIDATE`

**Authority:** none. This review does not authorize implementation, packet
amendment, mounting, or claim promotion.

## Executive verdict

Kimi found a strong allocator. For one fixed policy, the hierarchical
mechanical-word prefix construction has a compact algebra, exact conservation,
constant work per accounting key, a telescoping split/merge law, and a single
non-monetary cursor. Those are valuable results.

The submitted decision artifact is not sufficient to amend P4B5A. Its policy
reset rule admits an unbounded cumulative bias. Its B-prime refutation accepts
a new rejection without closing the staged-credit and accepted-language
semantics. Its Rust `u64` bound conflicts with the current 256-bit admitted
amount domain. Several stated executions are absent from the appendix, the
ESSO model was specified but not executed, and the cited Research Kernel run
and atoms were not retrievable from the configured shared kernel during this
review.

The allocator remains the leading candidate after these corrections. The
current contiguous-cursor Python work and monetary-dust Rust work do not
implement the selected formula and must remain unmounted.

## Grade

| Surface | Grade | Reason |
|---|---:|---|
| Fixed-policy allocation algebra | A- | Conservation, periodicity, and L3 have short credible proofs |
| Policy lifecycle and strategic behavior | NO-GO | Repeated authenticated resets amplify the signed bias without bound |
| B-prime composition contract | C | Leading structure retained; staged-credit availability and debit authority remain underspecified |
| Python/Rust integer refinement | C | Proposed `u64` bound conflicts with the present U256 domain |
| Evidence and provenance | C | Dirty-tree source is not SHA-bound; several claimed executions lack durable evidence |
| Overall amendment readiness | NO-GO | P0 findings remain |

## Findings

### POLICY-RESET-AMPLIFICATION-001

**Priority:** P0 before packet amendment

The report resets every cursor to zero on any weight, destination, version, or
tag change. It then claims that administrator influence remains inside the
single-epoch prefix envelope. That bound does not compose across resets.

For:

```text
D = 10_000
weights = (3333, 3333, 3334)
q = 0
n = 1
```

the chosen formula returns:

```text
(buyback, treasury, rewards) = (0, 0, 1)
```

Resetting before each of 100 one-atom epochs produces:

```text
(0, 0, 100)
```

Keeping the cursor continuous over the same 100 atoms produces:

```text
(33, 33, 34)
```

The reset gives role 2 an excess of 66 atoms. Repetition makes the deviation
unbounded. Authentication and receipt binding establish who reset the state;
they do not make the reset economically neutral.

This counterexample refutes the report's L8 conclusion, administrator-reset
analysis, narrow fairness claim, migration table, and proposed D08 amendment.
It was registered as an actual counterexample in Research Kernel atom
`atom_88eacb0842fe43f5`.

**Required correction:** keep the cursor phase independent of ordinary policy
weights, destinations, and policy tags. Preserve `q` across those changes.
Bind the active policy and activation point in the receipt. Treat a change to
the denominator or allocation algorithm as a distinct migration requiring a
proved cursor mapping or a canonical activation boundary. An administrator
must not obtain a general reset capability.

### BPRIME-STAGED-CREDIT-002

**Priority:** P0 before packet amendment

The exact replay currently credits the protocol-fee recipient as an ordinary
balance atom. The report then debits the complete credited amount from the
post-settlement intermediate state. It observes that the recipient may spend
that balance in the same settlement and classifies the resulting fee-phase
failure as a harmless conservative reject.

That conclusion leaves two obligations open:

1. The new reject contracts the accepted language for a V1 trace that can
   consume an earlier sequential fee credit. The versioned compatibility and
   liveness consequences are not specified.
2. A policy value does not by itself authorize debiting a committed balance
   controlled by a keyholder. B-prime must consume an exact provisional fee
   credit before it becomes independently spendable, or it must carry an
   authenticated debit authority with explicit semantics.

**Required correction:** define the settlement-to-fee port as a non-spendable,
same-lineage provisional credit. Compose the resulting distribution deltas
into one staged balance candidate and one canonical patch before commitment.
No committed intermediate source balance exists. If V2 intentionally rejects
traces that fund later same-batch activity from provisional fees, declare that
versioned language contraction and retain differential evidence for it.

B-prime remains the preferred composition operator. Its port and ordering law
need this correction.

### INTEGER-DOMAIN-PARITY-003

**Priority:** P0 before Python/Rust parity claims

The report derives `n <= 256 * 3_000_000_000` and selects Rust `u64`.
The current V2 value domain instead admits each fee amount through
`MAX_FEE_AMOUNT_V2 = 2^256 - 1`. The transition accepts exact public
`ProtocolFeeCreditV2` values and checks grouped totals against that U256-sized
limit. Exact settlement lineage may imply a smaller runtime amount, but the
current type and admission contract do not express that narrower theorem.

**Required correction:** choose one explicit boundary:

- introduce a controlled `ValidatedProtocolFeeCreditsV2` port whose
  construction proves the 256-credit and per-swap bounds, then encode the
  narrower amount domain in both schemas; or
- retain the U256 domain and implement the prefix counts without a wide
  `t * weight` product.

For the second option, use periodic decomposition:

```text
n = cycles * D + remainder
allocation_i = cycles * wi + interval_count_i(q, remainder)
```

Only the remainder uses the mechanical-word prefix formula, with arguments
below `2D`. This avoids narrowing the admitted language and avoids requiring a
270-bit intermediate.

### ALIAS-GROSS-DEBIT-004

**Priority:** P1 before implementation approval

The report proves alias closure using net aggregated deltas. The current
uncommitted Python transition first checks:

```text
source_balance >= distributed_amount
```

before adding destination credits and before canonical aggregation. A full
alias with zero source balance therefore rejects even though its net delta is
zero. Partial aliases may also require only the net outgoing amount.

**Required correction:** construct exact signed deltas, aggregate aliases by
the complete balance key, and apply the canonical balance transition once.
Any solvency check must use the resulting net debit. This does not close the
separate staged-credit issue above.

### POLICY-ROLE-ORDER-005

**Priority:** P1

The algebra begins with a fixed semantic role order. The fairness section then
allows administrators to reorder roles through policy. Those are different
protocols. Mutable role order allows selection of the positive remainder sink
and compounds the reset problem.

**Required correction:** fix `(buyback, treasury, rewards)` order in the
allocation algorithm version. Changing the role permutation is an algorithm
migration, not an ordinary policy field.

### EVIDENCE-PROVENANCE-006

**Priority:** P1 before accepting the review as evidence

The report names committed head `c4879d8...`, while the reviewed worktree also
contains uncommitted prompt, Python, Rust, checker, test, and documentation
changes. The SHA does not identify that full source state.

The appendix executes T1, T2, T4, L3 sweeps, and discrepancy sweeps. It does
not execute the stated T3, T7, T8, T9, T10, checker mutation suite, B-prime
runtime trace, or an ESSO model, despite the table heading `all executed`.
`ESSO-ready` is an appropriate status; `bounded verified` is not yet supported.

The cited Research Kernel run `run_78095dc928c34012` and decision atom
`atom_7ec5d52c46e64171` returned `unknown` from the configured shared kernel.
They may exist in another local database, but they are not currently replayable
evidence here.

**Required correction:** bind the report to a committed tree or a deterministic
patch hash; preserve the witness script as an executable repository artifact;
emit a result receipt; run the ESSO model; and describe unexecuted traces as
proposed tests. Import or attach any external Research Kernel records into the
shared run with provenance.

### GLOBAL-BEST-CLAIM-007

**Priority:** P2

The report establishes that the hierarchical formula is better than the
specific stateless, contiguous, and naive per-atom candidates it tested. It
does not establish global optimality among low-discrepancy periodic schedules
or accelerated weighted schedulers. The state lower bound is a worst-case
period argument and needs the exact `gcd(w0, w1, w2, D) = 1` condition plus a
minimal-period proof.

**Required correction:** describe candidate 5 as the leading smallest reviewed
construction. Reserve `best available` or minimality claims for a bounded
candidate class with a proved lower bound.

## Retained mathematics

Subject to fixed policy and exact admitted arithmetic, these parts are strong:

```text
P0(t) = floor(t*w0/D)
R0(t) = t - P0(t)
P1(t) = floor(R0(t)*w1/(D-w0))  when D-w0 > 0
P2(t) = t - P0(t) - P1(t)

Ai(q,n) = Pi(q+n) - Pi(q)
q' = (q+n) mod D
```

The conservation identity and periodic telescoping argument are credible. The
signed discrepancy bounds are also credible for a fixed role order. They
should become executable properties and a parameterized proof before mount.

## Corrected candidate architecture

The next design amendment should use this structure:

```text
exact settlement replay
  -> controlled provisional fee-credit batch
  -> mechanical-word allocation under authenticated policy
       using a policy-independent per-key cursor
  -> one net canonical balance patch
  -> one decision, receipt, replay update, and atomic commit bundle
```

Required state and bindings:

```text
ApportionmentCursorKey = (source_account_pubkey, asset)
CursorState            = q in [0, 10_000)
AlgorithmVersion       = fixed role order + prefix formulas + denominator
Policy                 = weights + exact destinations + activation identity
Receipt                = pre/post cursor + policy hash + provisional-credit root
                         + distributions + net patch root
```

Ordinary policy changes preserve the cursor. Algorithm or denominator changes
need an explicit migration theorem and activation gate.

## Required evidence before amendment approval

1. Preserve the 100-reset counterexample as a negative regression.
2. Prove policy-preserving cursor continuity and define algorithm migration.
3. Add the same-batch fee-recipient spend scenario as an explicit BDD and
   differential vector.
4. Replace gross source checks with net alias-aware balance application.
5. Close the amount domain and run exact Python/Rust vectors at every bound.
6. Execute the ESSO model and retain its report and solver fingerprint.
7. Add a parameterized Lean or equivalent arithmetic proof for conservation,
   periodicity, L3, and prefix bounds.
8. Bind every artifact to the exact committed source tree and algorithm
   version.

## Next authorized action

Revise the architecture report and prepare a new review-only P4B5A amendment.
Do not modify the frozen packet or continue the current Python/Rust integration
until the amendment independently passes this checklist.
