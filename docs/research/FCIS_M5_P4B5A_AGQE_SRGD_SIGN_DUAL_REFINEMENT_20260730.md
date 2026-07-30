# FCIS M5 P4B5A AGQE-3 / SRGD-v1 Sign-Dual Refinement

Date: 2026-07-30

Status: research-only, proved one-step refinement, executable parity tested,
unmounted

## 1. Result

AGQE-3 does not require a second ZenoDEX allocator implementation.

The reviewed SRGD-v1 transition and the AGQE-3 entitlement transition are the
same three-role transition under this state interpretation:

```text
AGQE surplus_i = -SRGD deficit_i
```

The lower allocations, residual remainders, selected bonus roles, final
allocations, and persistent state updates are identical after this sign map.

This checkpoint adds:

- a Lean proof of the exact selector relation and state-update relation;
- a Lean derivation of AGQE selector existence and uniqueness from SRGD;
- a Lean one-step proof of zero-sum and strict discrepancy preservation;
- an independent executable AGQE reference checked against the existing Python
  SRGD transition;
- a permanent event-granularity counterexample.

It does not rename the runtime algorithm, change a schema, add a dependency,
mount the allocator, or create publication authority.

## 2. Exact source pins

```text
ZenoDEX exact base:
  554758aa1536b01b911ba40b21afa4aec55c1b60

LEAP-MCP AGQE-3 / LineageCube source:
  PR #2
  6a3e30dd88d27fc3da1ef8026d43a8a0e694fedf

ZAG residual search source:
  PR #1
  33a8f83d320d828a511ae71383715d6de37ed203

Lean toolchain:
  leanprover/lean4:v4.27.0

Existing ZenoDEX algorithm identifier:
  SUPPORT_RESPECTING_GREEDY_DEFICIT_V1
```

LEAP and ZAG are discovery sources. The ZenoDEX Lean compiler and executable
tests decide the claims made by this checkpoint.

### 2.1 Occurrence terminology

ZenoDEX has two distinct occurrence layers:

```text
witness occurrence
  = one fill-bound provisional protocol-fee witness retained in settlement
    order with its own occurrence ID

allocator occurrence
  = one transition-level amount grouped by
    (fee_distribution_domain_id, asset)
```

The existing allocator consumes allocator occurrences. Within one accepted
settlement transition, duplicate same-key witness amounts are grouped and raw
input permutation does not change the allocator result. Across accepted
transitions, the persistent deficit state advances between groups, so an
adapter may not merge those transition boundaries.

This document uses `allocator occurrence` for the theorem input. The witness
tuple remains separate lineage evidence and must not be discarded.

## 3. Exact algebraic relation

For one grouped allocator occurrence, let:

```text
D                       = denominator
n                       = fee amount
w_i                     = role weight
d_i                     = SRGD pre-deficit
sigma_i                 = AGQE pre-surplus
n = cycles * D + r      = quotient/remainder decomposition
product_i               = r * w_i
lower_i                 = cycles * w_i + floor(product_i / D)
rho_i                   = product_i mod D
b_i                     = exact bonus bit
```

Both algorithms use the same `lower_i` and `rho_i`.

SRGD ranks eligible roles by descending:

```text
d_i + rho_i
```

with fixed precedence:

```text
buyback < treasury < rewards
```

AGQE ranks eligible roles by ascending:

```text
y_i = sigma_i - rho_i
```

Under `sigma_i = -d_i`:

```text
y_i = -d_i - rho_i
    = -(d_i + rho_i)
```

Therefore:

```text
argmin_i (y_i, role_index_i)
  =
argmax_i (d_i + rho_i, -role_index_i)
```

The exact bonus tuple is identical.

Both allocation views then use:

```text
allocation_i = lower_i + b_i
```

The SRGD state update is:

```text
d_i' = d_i + rho_i - D * b_i
```

The AGQE state update is:

```text
sigma_i' = sigma_i - rho_i + D * b_i
```

Substituting `sigma_i = -d_i` gives:

```text
sigma_i' = -d_i'
```

The history interpretations are the same fact with opposite signs:

```text
SRGD:
  d_i = cumulative_ideal_numerator_i - D * cumulative_actual_i

AGQE:
  sigma_i = D * cumulative_actual_i - cumulative_ideal_numerator_i

Therefore:
  sigma_i = -d_i
```

## 4. Lean theorem surface

The new proof file is:

```text
lean-mathlib/Proofs/FCISFeeApportionmentAGQESRGDRefinement.lean
```

It proves:

```text
bonus_relation_sign_dual
  Exact equivalence of the six tie-sensitive pairwise selector obligations.

update_sign_dual
  One coordinate of AGQE post-state equals the negative SRGD post-state.

transition_sign_dual
  One complete bonus transition carries the selector and all three updates.

agqe_bonus_exists_unique
  Every valid three-role residual quota has one exact AGQE bonus tuple.

agqe_step_preserves_strict_surplus
  One AGQE transition preserves sum zero and -D < sigma_i < D.

history_identity_sign_dual
  The cumulative entitlement identities are exact negatives.

zero_sum_sign_dual
strict_bound_sign_dual
  The committed-state invariants transport through the sign map.

witness_sign_dual_transition
  A concrete one-bonus transition establishes non-vacuity.
```

The proof adds no user-declared axiom, unsafe declaration, `sorry`, or `admit`.
The Lean axiom audit reports:

```text
bonus_relation_sign_dual:
  propext, Quot.sound

transition_sign_dual:
  propext, Quot.sound

history_identity_sign_dual:
  propext, Quot.sound

agqe_bonus_exists_unique:
  propext, Classical.choice, Quot.sound

agqe_step_preserves_strict_surplus:
  propext, Classical.choice, Quot.sound
```

These are standard Lean dependencies. The result is not advertised as
dependency-free.

The current Lean claim is one-step and relational. A recursive theorem over the
exact runtime occurrence fold remains a later obligation.

## 5. Executable refinement evidence

The independent test file is:

```text
tests/core/test_fcis_fee_apportionment_agqe_srgd_refinement.py
```

It implements AGQE as standalone test-only functions. It does not call the SRGD
selector while constructing the expected result.

The bounded selector campaign checks every valid pair of:

```text
strict zero-sum SRGD state
three-role residual vector
```

for every denominator from 1 through 12.

Exact checked transition count:

```text
164,528
```

Every checked point requires:

```text
AGQE bonuses = SRGD bonuses
AGQE post-surplus = -SRGD post-deficit
```

The production-denominator test additionally covers:

```text
D = 10,000
zero-weight policies
single-role policies
balanced and highly skewed policies
four distinct valid pre-states
amounts 0, 1, D-1, D, D+1, 2D+1, and U256_MAX
```

The stateful test carries the sign-dual state through 1,000 adaptive policy
changes. The policy choice depends on the visible current entitlement state.

## 6. Retained falsifiers

### 6.1 Wrong optimization direction

For:

```text
D = 3
d = (-2, 1, 1)
sigma = (2, -1, -1)
rho = (0, 1, 2)
```

correct AGQE and SRGD both select rewards:

```text
b = (0, 0, 1)
```

Selecting the largest AGQE surplus score instead selects treasury:

```text
b_wrong = (0, 1, 0)
```

The permanent mutation test kills this sign/order error.

### 6.2 Allocator-occurrence granularity

AGQE/SRGD is stateful per grouped allocator occurrence. Arbitrary splitting
across accepted transitions or merging across those transition boundaries
changes the protocol result.

Retained witness:

```text
D = 10
weights = (5, 2, 3)

one allocator occurrence of 867:
  (434, 173, 260)

two allocator occurrences of 493 then 374:
  (433, 174, 260)
```

Both outcomes satisfy quota bounds. They are different transitions.

Two raw witness amounts of 493 and 374 in the same accepted transition are
canonically grouped to one allocator occurrence of 867. The same amounts in
two accepted transitions are two allocator occurrences because the first
post-state becomes the second pre-state.

Therefore a mounted system must bind both the exact ordered witness tuple and
the exact grouped allocator-occurrence tuple into the candidate and receipt.
An adapter may not split, merge, or reorder accepted transition boundaries.

### 6.3 Role count

The theorem is exact for three roles. A fourth role requires a new algorithm
profile, state schema, theorem, vectors, and migration relation.

## 7. ATDD refinement contract

```text
ATDD-R1 Sign map
  Given a valid SRGD pre-state d
  When sigma is defined coordinate-wise as -d
  Then both states encode the same cumulative entitlement history.

ATDD-R2 Selector
  Given the same denominator, remainders, role order, and sign-dual state
  When SRGD maximizes d_i + rho_i and AGQE minimizes sigma_i - rho_i
  Then the exact bonus tuple is equal.

ATDD-R3 Transition
  Given equal lower allocations and equal bonus bits
  When both post-state equations are evaluated
  Then allocations are equal and sigma_post = -deficit_post.

ATDD-R4 Adaptive sequence
  Given an arbitrary authorized policy sequence and one fixed history identity
  When every grouped allocator occurrence carries the prior state forward
  Then the sign-dual relation holds after every tested step.

ATDD-R5 U256 boundary
  Given amount = U256_MAX
  When quotient/remainder evaluation is used
  Then the implementation agrees with the independent AGQE reference without
  evaluating amount * weight.

ATDD-R6 Granularity rejection
  Given the same amounts grouped in one accepted transition or split across two
  When their transition results differ
  Then lineage preserves both the witness tuple and allocator-occurrence tuple
  and an adapter must not merge the accepted transition boundary.
```

## 8. Evidence ledger

| Claim | Status | Evidence |
| --- | --- | --- |
| Selector sign duality | `PROVED` | `bonus_relation_sign_dual` |
| Post-state sign duality | `PROVED` | `transition_sign_dual` |
| AGQE selector totality and uniqueness | `PROVED` | `agqe_bonus_exists_unique` |
| One-step AGQE strict discrepancy | `PROVED` | `agqe_step_preserves_strict_surplus` |
| History identity sign duality | `PROVED` | `history_identity_sign_dual` |
| Python selector parity, D=1..12 | `TESTED` | 164,528 exact points |
| Python public transition parity | `TESTED` | D=10,000 and U256 boundaries |
| Adaptive-policy sign continuity | `TESTED` | 1,000-stateful-step trace |
| Event-partition equivalence | `REFUTED` | 867 versus 493+374 witness |
| Exact Python/Rust AGQE interpretation parity | `GAP` | Existing SRGD parity does not name this bridge |
| Exact runtime occurrence fold theorem | `GAP` | One-step theorem only |
| Policy authentication and currentness | `GAP` | Outside this checkpoint |
| Candidate, receipt, commit, recovery, outbox | `GAP` | Outside this checkpoint |
| Runtime authority | `UNMOUNTED` | No consumer or publication path added |

## 9. LineageCube boundary

LEAP-MCP PR #2 also supplies a generic LineageCube theorem. It shows that six
commuting faces make all semantic, authority, and durability exterior paths
reach one terminal artifact.

That theorem is useful for M6 composition. It does not yet provide:

```text
concrete ZenoDEX node types
canonical lineage identifiers
face-certificate schemas
source-bound face checkers
store-current rederivation
no-bypass evidence
```

The next LineageCube checkpoint should instantiate one allocator occurrence:

```text
grouped allocator occurrence
  -> SRGD/AGQE evaluation
  -> authenticated policy/current state
  -> candidate and receipt
  -> atomic committed state and outbox row
  -> reopened authorized head
```

Each face must be checked from its independent sources. Bundle-carried copies
remain equality targets, never authority sources.

## 10. Research-tool disposition

LEAP completed a bounded 512-point sign-dual diagram with operation digest:

```text
sha256:a40776d6cd6f342e82c6274a09664ab2f69850d531c7b98eb312e2a6ac082330
```

That run reported no scientific-support receipt. It was used to select the
formal theorem surface.

Aristotle proof-refinement project
`2c3241c8-b124-4571-8388-397a8daf9fc9` independently filled only
`bonus_relation_sign_dual`. The returned task retained the exact definitions,
statement, imports, and assumptions. Its direct six-obligation order-negation
proof is equivalent to the checked repository proof.

```text
Aristotle run:
  3885b33c-0154-4302-9e9b-f0e589d086ff

returned archive SHA-256:
  019907fac3c8446dcee0d94f0f08076bda807b4ad968e9871255333c9da8fe37

returned Lean file SHA-256:
  ec2c4aabd7738098c12792685d7b7edabf9792f653d73f36d

independent returned-project check:
  lake build
  PASS
```

Aristotle supplied proof-search corroboration. The pinned ZenoDEX Lean
compiler and theorem audit remain the claim-deciding evidence.

TheoremSearch supplied retrieval-only prior art. The promoted claim depends
only on the independently checked local Lean and executable evidence listed
above. No direct external theorem was used as evidence.

Research Kernel records the question, claim, bounded result, risk, refutation
plan, and reformulations. Those records preserve provenance and do not promote
runtime authority.

## 11. Non-claims

This checkpoint does not establish:

- canonical witness extraction or witness-to-allocator grouping;
- authentication of the active distribution policy;
- current-state provenance;
- a committed V2 state or state root;
- configuration-update authority;
- Python/Rust bridge-specific transition parity;
- a full recursive occurrence-fold theorem;
- candidate, receipt, bundle, proof, publication, recovery, or outbox behavior;
- ZenoFCIS LineageCube instantiation;
- no-bypass;
- production mounting or M6 promotion.

## 12. Smallest safe next checkpoint

Keep the existing SRGD-v1 implementation and schema unchanged.

Next, freeze the canonical ordered witness tuple and its deterministic mapping
to grouped allocator occurrences, then prove the recursive fold refinement over
those allocator occurrences. Add explicit Rust sign-dual vectors after that.
Only after those pass should the allocator enter a source-bound LineageCube
candidate and atomic publication design.
