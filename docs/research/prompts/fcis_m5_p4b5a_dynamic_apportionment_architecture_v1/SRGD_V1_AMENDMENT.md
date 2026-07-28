# FCIS M5-P4B5A SRGD-v1 architecture amendment

**Status:** `PROPOSED_REVIEW_ONLY`

**Amends:** `fcis-m5-p4b5a-dynamic-apportionment/v1`

**Selected allocator:** `SUPPORT_RESPECTING_GREEDY_DEFICIT_V1`

**Runtime implementation:** blocked pending independent amendment review

**Authority mount:** prohibited

## 1. Decision

Select Support-Respecting Greedy Deficit apportionment, abbreviated
`SRGD-v1`, as the protocol-fee apportionment algorithm for the three fixed
semantic roles:

```text
buyback
treasury
rewards
```

The integrated architecture is:

```text
OwnedSettlementV2 exact replay
  -> controlled provisional protocol-fee witnesses
  -> group by authenticated distribution domain and asset
  -> SRGD-v1 allocation
  -> balance writes
     + pool-reserve writes
     + fee-apportionment-state write
  -> one CanonicalDexPatchV2
  -> one receipt and atomic CommitBundleV2
```

The decision selects the allocator kernel and the surrounding protocol
requirements in this amendment. It does not authorize Python or Rust runtime
implementation.

## 2. Exact allocator

Let:

```text
D = 10_000
roles = (buyback, treasury, rewards)
key = FeeApportionmentKeyV2(domain_id, asset)
weights = (w0, w1, w2)
w0 + w1 + w2 = D
amount = n, an admitted U256 value
deficit_pre = (d0, d1, d2)
d0 + d1 + d2 = 0
-D < di < D
```

Compute:

```text
cycles, remainder = divmod(n, D)

lower_i    = cycles * wi + floor(remainder * wi / D)
fraction_i = (remainder * wi) mod D
score_i    = di + fraction_i

k = (fraction_0 + fraction_1 + fraction_2) / D
```

`k` is an exact integer in `{0,1,2}`.

Eligible roles satisfy:

```text
fraction_i > 0
```

Choose exactly `k` eligible roles using:

```text
descending score_i
then fixed semantic order:
  buyback
  treasury
  rewards
```

For the selected indicator `bonus_i in {0,1}`:

```text
allocation_i = lower_i + bonus_i
deficit_post_i = score_i - D * bonus_i
```

The normative ranking expression is `deficit_i + fraction_i`. The phrase
“greatest accumulated deficit” is insufficient and must not appear as the
executable rule.

The architecture-level relation is total and deterministic only with a
parameterized existence-and-uniqueness theorem. The checked theorem
`srgd_bonus_exists_unique` proves that, for every positive denominator and
valid three-role residual quota, exactly one bonus tuple satisfies the support,
seat-count, score, and fixed-tie clauses. Python and Rust executable selectors
must later refine that exact relation.

## 3. Allocator laws

For every valid step:

```text
allocation_0 + allocation_1 + allocation_2 = n

allocation_i in {
    floor(n * wi / D),
    ceil(n * wi / D),
}

fraction_i = 0
  -> bonus_i = 0

wi = 0
  -> allocation_i = 0

d0' + d1' + d2' = 0

-D < di' < D
```

For a history-derived state initialized at zero or produced by a proved
migration:

```text
di(T) = cumulative_ideal_numerator_i(T)
        - D * cumulative_actual_i(T)

abs(cumulative_actual_i(T) - cumulative_ideal_i(T)) < 1 atom
```

The policy may choose every future valid weight vector after observing all
public state and prior allocations.

### 3.1 Positive residual support

Bonus eligibility is `fraction_i > 0`. Checking only `wi > 0` is incorrect.
A positive weight can have zero current fractional entitlement.

### 3.2 Fixed-policy fragmentation

Exact temporal fragmentation equivalence is not required and is false.

For the same initial state, fixed weights, and equal total amount, any two
fragmentation schedules satisfy:

```text
abs(total_allocation_schedule_A_i
    - total_allocation_schedule_B_i) <= 1 atom
```

No fragmentation comparison is claimed across policy changes.

### 3.3 Claim scope

The published unrestricted-real online model proves the adaptive
three-recipient strict-quota theorem used by the SRGD reduction.

It does not prove either of these fixed-grid claims:

```text
SRGD-v1 is globally optimal for D = 10_000
every four-role fixed-grid allocator is impossible
```

Both remain `UNKNOWN`. Adding a fourth independently weighted role is an
algorithm-architecture review.

## 4. Committed state and provenance

Use:

```text
FeeApportionmentKeyV2(
    fee_distribution_domain_id,
    asset,
)

FeeDeficitEntryV2(
    key,
    deficit_buyback_i32,
    deficit_treasury_i32,
)

CommittedFeeApportionmentStateV2(
    algorithm_version = SRGD_V1,
    entries in strict ProtocolOrd,
)
```

Derive:

```text
deficit_rewards =
    -deficit_buyback - deficit_treasury
```

Admission validates all three strict bounds and the zero-sum relation.

The zero representation is unique:

```text
empty entries
  = canonical genesis and V1-dust-zero migration state

missing (pinned_domain, asset)
  = deficit (0,0,0)
  only when that key is introduced by an admitted provisional witness

deficit_post = (0,0,0)
  -> omit the entry
```

Retained all-zero entries are non-canonical. Duplicate keys, unknown fields,
Boolean values in integer fields, and out-of-range signed integers reject.

The exact schema family is:

```text
zenodex/fcis/fee-apportionment/key/v2
zenodex/fcis/fee-apportionment/deficit-entry/v2
zenodex/fcis/fee-apportionment/committed-state/v2
```

Each value uses the closed envelope
`{"schema": schema_id, "value": projection}` and the repository canonical JSON
codec. Signed deficits encode as canonical JSON integers in
`[-9_999, 9_999]`; strings encode without locale, case folding, or Unicode
normalization. `ProtocolOrd` for keys compares the admitted domain identifier's
UTF-8 bytes, then the admitted asset identifier's UTF-8 bytes, both as unsigned
lexicographic byte sequences. Encoding order does not substitute for this
ordering rule. Exact field registries and cross-language golden vectors bind
the tags and projections before implementation approval.

Numeric range validation alone does not establish state provenance. An
authoritative state exists only through:

```text
genesis zero state
proved V1 migration with scalar dust = 0
prior accepted SRGD-v1 successor
```

Decoding persisted state may reconstruct a candidate value. Authority arises
only after closed canonical revalidation against an authenticated state root,
supported snapshot version, and admitted predecessor or migration witness.
Request-derived decoded state and public constructors never create authority.

## 5. Stable distribution-domain authority

The first V2 mount uses one deployment-scoped domain identifier pinned by
authenticated committed configuration.

The domain identifier is never derived from:

```text
source account
destination account
policy hash
request data
caller-selected metadata
```

Ordinary weight, destination, or policy rotation preserves the exact deficit
state. No reset operation exists.

The first mount exposes no topology command. Domain creation, split, merge,
retirement, or reuse is unrepresentable through the V2 command language and is
covered by negative admission and registry tests.

If multiple domains are introduced later, a separately reviewed committed
registry must prove:

```text
each exact fee stream maps to one active domain
activation is sequenced
retirement creates a permanent tombstone
retired identifiers are never reused
split and merge reject in V2
```

## 6. Settlement ABI and provisional lineage

Removing the legacy protocol-recipient balance credit changes canonical
settlement semantics. P4B5A therefore uses exactly:

```text
OwnedSettlementV2
```

A V1/V2 normalization requires a later, separately reviewed amendment. Silent
reuse of `OwnedSettlementV1` is prohibited.

`OwnedSettlementV2` has the closed field registry:

```text
module
version
batch_ref
included_intents
fills
balance_deltas
reserve_deltas
lp_deltas
provisional_protocol_fee_witnesses
events
```

The first eight fields preserve their V1 typed shapes, except that
`balance_deltas` excludes the legacy protocol-recipient fee credit.
`provisional_protocol_fee_witnesses` is a mandatory canonical tuple, including
the empty tuple. `events` preserves the V1 optional-event semantics. The schema
ID is `zenodex/fcis/settlement/owned-settlement/v2`; the record tag is
`SETTLEMENT_V2`; and the settlement-root preimage uses the domain
`owned_settlement`, version `2`, followed by the exact canonical envelope.
Unknown, missing, or duplicate fields reject.

Promotion requires one source-derived consumer inventory and exact migration
for every settlement parser, strong replay validator, recomputation
certificate, proof guest/verifier ABI, Python/Rust codec, fixture/golden vector,
candidate, receipt, and commit-bundle binding. A consumer remaining on the V1
root is a release blocker.

Each provisional witness binds:

```text
pre-state root
command root
OwnedSettlementV2 root
authenticated configuration root and version
algorithm and accepted-language versions
settlement occurrence ID
intent ID and fill ordinal
pool
asset
distribution domain
authenticated quote
protocol fee policy
authenticated execution context
sender debit atom
pool reserve credit atom
provisional protocol fee amount
```

The replacement conservation law is:

```text
sender input debit
  =
pool input-reserve credit
  +
provisional protocol fee
```

The candidate proves:

```text
canonical expected occurrence tuple
  == canonical admitted witness occurrence tuple
  == canonical consumed occurrence tuple
```

Occurrence IDs are
`sha256(domain_sep("protocol_fee_occurrence", version=2) || command_root ||
canonical_fill_ordinal)`. Tuples are in settlement fill order and duplicate
occurrence IDs reject. Equal-valued fills remain distinct through occurrence
identity. The enclosing controlled witness batch binds the pre-state,
settlement, configuration, algorithm, and accepted-language roots, so none may
be supplied independently per witness.

Initially, provisional protocol fees are defined only for quoted CPMM swaps.
CoW or routed transitions with no protocol-fee field contribute zero. A CoW or
routed transition carrying a nonzero protocol-fee field returns a typed reject
and produces no provisional witness until its exact replay lineage is
separately specified and reviewed.

## 7. Explicit accepted-language version

V2 provisional fees cannot fund later intents in the same batch.

This is an intentional accepted-language change:

```text
V1 may accept
V2 may reject
```

Algorithm and accepted-language versions are bound before settlement
construction. The preserved BDD scenario demonstrates an earlier
protocol-fee credit attempting to fund a later same-batch intent.

## 8. Policy authority and economic switch

When the protocol fee share is nonzero, one authenticated active
`FeeDistributionPolicyV2` is required.

Policy and domain authority come from committed deployment configuration.
Request context cannot select:

```text
domain
weights
destinations
role order
algorithm version
```

The controlled value is:

```text
AuthenticatedFeeDistributionConfigurationV2(
    chain_deployment_id,
    configuration_root,
    configuration_version,
    expected_configuration_version,
    fee_distribution_domain_id,
    policy_root,
    policy,
    activation_sequence,
    algorithm_version,
    accepted_language_version,
)
```

Its exact schema IDs are:

```text
zenodex/fcis/fee-distribution/policy/v2
zenodex/fcis/fee-distribution/configuration-body/v2
zenodex/fcis/fee-distribution/authenticated-configuration/v2
```

The canonical configuration body has this normative field order:

```text
chain_deployment_id
configuration_version
fee_distribution_domain_id
policy_root
policy
activation_sequence
algorithm_version
accepted_language_version
```

The roots are non-circular:

```text
policy_root =
  sha256(
    domain_sep("fee_distribution_policy", version=2)
    || canonical_policy_envelope_v2
  )

configuration_root =
  sha256(
    domain_sep("fee_distribution_configuration", version=2)
    || canonical_configuration_body_envelope_v2
  )

expected_configuration_version = configuration_version observed by evaluation
```

Neither `configuration_root` nor `expected_configuration_version` appears
inside the hashed configuration body. The authenticated wrapper contains the
body, its recomputed `configuration_root`, and the expected version used by the
publication compare-and-swap. Closed admission rejects unknown, missing, or
duplicate fields and any mismatch among the embedded policy, `policy_root`,
configuration body, root, and expected version.

Only the authenticated shell's committed-configuration verifier constructs
this value. The evaluator revalidates its canonical bytes and exact root.
Candidate evidence, support evidence, receipt, `FCISCommittedStateV2`,
`CanonicalDexPatchV2`, and `CommitBundleV2` bind the chain/deployment ID,
configuration root and version, domain ID, policy root, activation sequence,
algorithm version, and accepted-language version. Expected-version publication
rejects stale or substituted configuration atomically with the state
compare-and-swap.

V2 changes value movement from one legacy recipient credit to direct
same-asset credits for buyback, treasury, and rewards accounts. This requires
an explicit normative economic authorization and versioned migration policy.

Any direct-recipient compatibility mode requires a separate closed variant,
receipt schema, and refinement review.

## 9. Composite patch and effect boundary

ZenoDEX balance state and pool-reserve state are separate committed
namespaces.

The accepted step returns one:

```text
CanonicalDexPatchV2(
    balance_writes,
    pool_writes,
    fee_apportionment_writes,
    ... unchanged committed namespaces,
)
```

Alias aggregation occurs only among complete balance keys:

```text
(account, asset)
```

Pool reserve writes remain pool writes. They are never represented as balance
writes.

`AssetFeeDistributionV2` is receipt evidence for writes already present in the
accepted patch. V2 has no fee-distribution outbox opcode or shell transfer
effect.

Remove these fields from V2 effect authority:

```text
assetless total_swap_fees
executable fee_allocation
```

## 10. State-root, support-root, and version closure

V2 introduces:

```text
FCISCommittedStateV2
schema = zenodex/fcis/state/committed-dex-state/v2
snapshot_version = 5
support_profile_version = 6
```

`FCISCommittedStateV2` keeps the V1 aggregate's balances, pools, LP balances,
nonces, vault, oracle, and perps fields. It replaces the scalar
`fee_accumulator` field with `fee_apportionment:
CommittedFeeApportionmentStateV2`; the two fields cannot coexist. Snapshot
version 5 includes this field in normative order and uses
`domain_sep("dex_snapshot", version=5) || canonical_snapshot_bytes_v5`.
This `dex_snapshot` version namespace is distinct from the legacy spot
`state_root` domain that also has a version 5; domain separation prevents a
version-number collision.

Support profile 6 commits exact presence or absence for every actual read:

```text
sender balance (account, asset)
pool input reserve (pool, asset)
fee-apportionment key (pinned domain, asset)
buyback destination balance (account, asset)
treasury destination balance (account, asset)
rewards destination balance (account, asset)
authenticated configuration fields and root
```

The fee relation does not add the legacy recipient balance to support. If the
same key is independently read by another command relation, that distinct read
remains. Profile 6 declares the apportionment read/write paths, destination
balance paths, configuration paths, absence encodings, actual-read containment,
and its own canonical support-set commitment. Its root preimage uses
`domain_sep("state_support_root", version=6)`.

The V2 authority schema and exhaustive dispatch admit only the exact V2 state,
context, settlement, patch, decision, receipt, and bundle family. The commit
reference applies all balance, pool, apportionment, replay, receipt, and outbox
records at one expected-state and expected-configuration linearization point.
Historical V1 decoders remain read-only replay/migration tools.

The compatibility matrix is fail closed:

```text
V1 command/context -> snapshot 4, support profile 5, V1 authority only
V2 command/context -> snapshot 5, support profile 6, V2 authority only
mixed V1/V2 state, settlement, receipt, proof, or bundle -> reject
```

Promotion requires byte-identical Python/Rust state and support roots, historical
V1 replay vectors, V1-to-V2 migration vectors, proof/verifier input migration,
commit-reference application, and mutation tests for every omitted or
cross-version field.

## 11. U256 and resource closure

The quotient/remainder decomposition avoids wide intermediate products:

```text
cycles, remainder = divmod(n, D)

cycles * wi
remainder * wi
```

`remainder * wi < D^2`. The large product `n * wi` is not evaluated.

Python uses nonnegative integer floor division and remainder. Rust uses the
runtime U256/BigUint semantics selected by the source-pinned implementation.
Every cross-language rejection and checked operation must have identical
precedence.

Work is `O(number_of_keys)` with constant work per key. A per-atom loop is
forbidden.

Grouping multiple provisional amounts must reject U256 aggregate overflow
before constructing authority.

## 12. Migration

V1 scalar dust has no recoverable asset or distribution-domain identity.

Release migration is:

```text
V1 dust = 0
  -> empty canonical apportionment map
     (missing admitted witness key reads as deficit (0,0,0))

V1 dust != 0
  -> release/migration blocker
```

Nonzero V1 dust is resolved before activation. It is not an ordinary
user-transition rejection after V2 is mounted.

The following changes require a separately proved algorithm migration:

```text
role permutation
denominator
support rule
ranking formula
fourth independently weighted role
deficit-state encoding
```

Rollback is shell or reorganization restoration unless a distinct forward
rollback transition is intentionally specified.

## 13. Required evidence before implementation approval

The amendment must receive an independent review that checks:

1. the exact `score_i = deficit_i + fraction_i` formula;
2. positive residual support;
3. the parameterized strict-deficit theorem;
4. the parameterized selector existence-and-uniqueness theorem;
5. ESSO or equivalent exhaustive small-domain inductiveness, with a
   non-vacuity/availability query;
6. settlement ABI versioning;
7. authenticated domain identity and state provenance;
8. expected/admitted/consumed witness-set equality;
9. balance/pool/apportionment namespace separation;
10. the explicit V1-to-V2 accepted-language change;
11. removal of executable distribution effects;
12. canonical zero-state encoding and exact schema tags;
13. authenticated configuration binding;
14. the single `OwnedSettlementV2` ABI;
15. snapshot-5/support-profile-6 closure.

Implementation approval then requires:

- source-pinned Python and Rust implementations;
- exact-byte vectors for values, rejects, state, policy, patch, receipt, and
  commit bundle;
- values at `0`, `D-1`, `D`, `D+1`, and `2^256-1`;
- mixed assets and aggregate-overflow boundaries;
- actual balance and pool-state composition tests;
- tests proving domain creation, retirement, split, merge, and reuse are
  unrepresentable or rejected in the first mount;
- policy-presence and policy-rotation tests;
- V1-accept/V2-reject same-batch BDD evidence;
- stateful replay and exactly-once witness consumption;
- a stateful adaptive-policy model asserting the history identity and strict
  sub-one-atom cumulative discrepancy after every step;
- fixed-policy fragmentation property evidence with the one-atom bound and the
  preserved counterexample against exact temporal fragmentation equivalence;
- canonical same-step group, partition, and input-permutation invariance for
  provisional witnesses sharing one `(domain, asset)` key;
- Python and Rust selector equality with the unique fixed-order top-`k`
  relation, including `eligible_count >= k` and the constant-size eight-tuple
  reference checker;
- formal receipts binding source SHA, normalized IR hash, tool source hash,
  exact command, solver/compiler versions, and result; an outcome fingerprint
  alone is insufficient;
- complete state-root, support-root, authority-dispatch, historical decoder,
  commit-reference, and mixed-version compatibility vectors;
- mutation tests for:

  ```text
  deficit-only ranking
  zero-support selection
  state reset
  source-account keying
  fourth-role insertion
  tie-order change
  recipient-credit restoration
  scalar fee summation
  pool write encoded as balance write
  distribution effect creation
  double application
  root omission
  configuration substitution
  retained zero-state entry
  settlement-v1 substitution
  support-key omission
  mixed-version bundle
  strengthened guard that removes nonzero transitions
  deleted positive-support guard
  relaxed or reversed tie order
  ```

## 14. Current WIP disposition

The uncommitted P4B5A Python and Rust experiments at source head
`6771bff2d55ba08421b586e2db75441deb87f582` do not implement this amendment.

Python uses a contiguous cursor with source-account state and a gross source
debit. Rust uses monetary dust with source-account state. Neither
representation may enter V2 authority.

Generic closed-admission or codec techniques may be reused only after
independent review.

## 15. Promotion boundary

Current status:

```text
SRGD_ALLOCATOR_SELECTED
PACKET_AMENDMENT_PROPOSED
IMPLEMENTATION_NOT_AUTHORIZED
RUNTIME_UNCHANGED
AUTHORITY_MOUNT_PROHIBITED
```

The next authorized action is independent review of this amendment and its
formal evidence. A passing amendment review may authorize a fresh unmounted
Python/Rust implementation checkpoint.
