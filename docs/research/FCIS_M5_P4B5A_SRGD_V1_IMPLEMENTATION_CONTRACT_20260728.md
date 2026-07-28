# FCIS M5-P4B5A SRGD-v1 implementation contract

**Status:** `FROZEN_FOR_FRESH_UNMOUNTED_CHECKPOINT_A`

**Architecture source:** commit
`371912c5cb25533a1b4e3523c478563991db25b0`

**Authority mount:** prohibited

## 1. Checkpoint boundary

Checkpoint A implements one deterministic Python/Rust kernel:

```text
candidate fee amounts
  -> canonical grouping by (fee_distribution_domain_id, asset)
  -> SRGD-v1 allocation
  -> sparse deficit-state successor
  -> evidence-only allocation records
```

The checkpoint does not implement or imply:

```text
authenticated configuration authority
OwnedSettlementV2 or provisional witness authority
balance or pool-reserve writes
receipts, support roots, state roots, decisions, or commit bundles
replay, outbox, migration, runtime dispatch, or authority mounting
```

Decoded values and direct constructors produce candidates only. State authority
requires the later provenance relation specified by the reviewed amendment.

## 2. Exact values

```text
FeeApportionmentKeyV2(
    fee_distribution_domain_id: ExactText,
    asset: ExactText,
)

FeeDeficitEntryV2(
    key: FeeApportionmentKeyV2,
    deficit_buyback: ExactInt[-9999,9999],
    deficit_treasury: ExactInt[-9999,9999],
)

deficit_rewards =
    -deficit_buyback - deficit_treasury

CommittedFeeApportionmentStateV2(
    algorithm_version = "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
    entries: exact tuple in strict ProtocolOrd,
)

FeeDistributionPolicyV2(
    buyback_bps: ExactInt[0,10000],
    treasury_bps: ExactInt[0,10000],
    rewards_bps: ExactInt[0,10000],
    buyback_destination: ExactText,
    treasury_destination: ExactText,
    rewards_destination: ExactText,
)

FeeAmountCandidateV2(
    key: FeeApportionmentKeyV2,
    amount: ExactU256,
)
```

The three policy weights sum exactly to `10_000`. Destination aliases are
valid. Destinations, source accounts, and policy hashes never enter the state
key.

`ExactText` is a nonempty Python/Rust Unicode scalar string bounded by the
existing state-string character and UTF-8 byte limits. Admission performs no
case folding or Unicode normalization. `ProtocolOrd` compares the domain
identifier's UTF-8 bytes, then the asset identifier's UTF-8 bytes, as unsigned
lexicographic byte sequences.

`ExactU256` is an exact non-Boolean integer in `[0, 2^256 - 1]`. Python uses
`int`; Rust uses a private bounded `BigUint` wrapper. Canonical JSON represents
the value as an unquoted integer.

The sparse state omits an entry whose three deficits are zero. Retained
all-zero entries, duplicate keys, and non-increasing ProtocolOrd keys reject.

## 3. Resource limits

```text
MAX_FEE_AMOUNT_V2 = 2^256 - 1
MAX_FEE_AMOUNT_CANDIDATES_V2 = 256
MAX_FEE_APPORTIONMENT_KEYS_V2 = 50_000
```

The admission engine's existing depth, node, collection, and canonical-byte
limits remain binding. Grouping rejects when the exact sum for one key exceeds
`MAX_FEE_AMOUNT_V2`. The reject path identifies the key, rather than an
input-order-dependent candidate index.

Zero is admitted by this arithmetic checkpoint. A zero-only key produces one
evidence row and no retained zero-state entry. The later settlement-witness
checkpoint decides whether zero-valued provisional witnesses are
unrepresentable.

## 4. SRGD-v1 transition

For each grouped key, with `D = 10_000`:

```text
cycles, remainder = divmod(amount, D)

lower_i    = cycles * weight_i + floor(remainder * weight_i / D)
fraction_i = (remainder * weight_i) mod D
score_i    = deficit_pre_i + fraction_i

k = (fraction_0 + fraction_1 + fraction_2) / D
eligible_i = fraction_i > 0
```

Select exactly `k` eligible roles by descending `score_i`, then by the fixed
role order:

```text
buyback < treasury < rewards
```

For each role:

```text
allocation_i = lower_i + bonus_i
deficit_post_i = score_i - D * bonus_i
```

The implementation evaluates the large amount only through quotient/remainder
decomposition. It never computes `amount * weight` and never loops per atom.

Candidate inputs are grouped before allocation. Grouping is input-permutation
independent. Keys are evaluated in ProtocolOrd. Untouched state entries remain
unchanged. Policy and destination rotation preserve the exact pre-state
deficits.

The accepted result is privately constructed:

```text
FeeApportionmentTransitionOkV2(
    state: CommittedFeeApportionmentStateV2,
    allocations: tuple[AssetFeeAllocationV2, ...],
)
```

Each evidence-only `AssetFeeAllocationV2` binds:

```text
key
amount
buyback_destination
treasury_destination
rewards_destination
buyback_fraction
treasury_fraction
rewards_fraction
buyback_bonus
treasury_bonus
rewards_bonus
buyback_amount
treasury_amount
rewards_amount
deficit_buyback_pre
deficit_treasury_pre
deficit_rewards_pre
deficit_buyback_post
deficit_treasury_post
deficit_rewards_post
```

These records describe allocator output. They are not balance operations,
shell effects, receipts, or publication authority.

## 5. Rejections and precedence

The Python and Rust transition APIs use the same closed codes:

```text
WRONG_EXACT_TYPE
ITEM_LIMIT
NONCANONICAL_IDENTIFIER
AMOUNT_OUT_OF_RANGE
INVALID_POLICY
INVALID_PRESTATE
AGGREGATE_OVERFLOW
INTERNAL_RELATION_FAILURE
```

Validation first checks the three top-level exact types. It then enforces the
candidate and state-entry item limits before traversing either bounded
container. Within those bounds, it checks every record, scalar, and nested-key
exact type before semantic validation. This ordering keeps rejection
deterministic without permitting an oversized input to force an unbounded type
scan. Boolean values in integer fields produce `WRONG_EXACT_TYPE`.

Stable paths use:

```text
contributions/<index>/<field>
policy/<field>
state/<field>
state/entries/<index>/<field>
contributions/aggregate/<domain>/<asset>
relation/<field>
```

Every rejection carries no successor, allocation evidence, patch, receipt, or
effect.

## 6. Canonical ABI

Schema revision:

```text
zenodex/fcis/fee-apportionment/v2
```

Schema IDs:

```text
zenodex/fcis/fee-apportionment/key/v2
zenodex/fcis/fee-apportionment/amount-candidate/v2
zenodex/fcis/fee-apportionment/amount-candidate-batch/v2
zenodex/fcis/fee-apportionment/deficit-entry/v2
zenodex/fcis/fee-apportionment/committed-state/v2
zenodex/fcis/fee-distribution/policy/v2
zenodex/fcis/fee-apportionment/asset-allocation/v2
zenodex/fcis/fee-apportionment/asset-allocation-batch/v2
zenodex/fcis/fee-apportionment/transition-result/v2
```

Record tags:

```text
fee_apportionment_key_v2
fee_amount_candidate_v2
fee_deficit_entry_v2
committed_fee_apportionment_state_v2
fee_distribution_policy_v2
asset_fee_allocation_v2
```

Each encoding is:

```json
{"schema":"<schema-id>","value":"<closed projection>"}
```

using the repository canonical JSON codec. Admission registers only key,
candidate, deficit-entry, state, and policy schemas. Allocation and accepted
result values are token-controlled outputs and have codec registrations
without public admission constructors.

Checkpoint-A digests are evidence hashes:

```text
sha256(canonical envelope bytes)
```

They are not protocol state roots. Full snapshot, support, receipt, and bundle
root domains remain deferred.

## 7. Required evidence

The shared fixture is generated once from the Python reference surface and
consumed directly by both Python and Rust tests. It binds:

```text
input projections
accept or exact reject code/path
fractions
bonuses
allocations
pre/post deficits
canonical state, allocation, and result bytes
SHA-256 of each canonical envelope
```

Required gates include:

- the independent eight-bonus selector oracle over all 592 D=4 pairs;
- production vectors at `0`, `1`, `D-1`, `D`, `D+1`, and `2^256-1`;
- score, positive-support, and tie-order distinguishing vectors;
- U256 overflow and exact reject-precedence vectors;
- sparse-zero omission and ProtocolOrd ordering;
- same-step grouping and input-permutation invariance;
- adaptive policy/destination traces preserving the history identity;
- fixed-policy fragmentation bounded by one atom, while retaining the
  counterexample to exact fragmentation;
- whole-result Python/Rust equality from one pinned fixture;
- structural mutations for forbidden imports, private construction,
  registry drift, and obsolete fee-custody semantics.

## 8. File and dependency surface

Fresh Python source:

```text
src/core/fcis_fee_apportionment_values.py
src/core/fcis_fee_apportionment_schema.py
src/core/fcis_fee_apportionment_codec.py
src/core/fcis_fee_apportionment_admission.py
src/core/fcis_fee_apportionment_allocator.py
```

Fresh Rust source:

```text
rust-runtime/crates/zenodex-runtime-core/src/fcis_fee_apportionment.rs
```

The Rust core adds only a module export. `serde_json` may be used as an
existing workspace dev-dependency solely to consume the shared fixture. No
production dependency is added.

The fresh source must not import the obsolete fee-custody experiment,
fee-accumulator state, balance transitions, settlements, evaluator, commit,
outbox, shell, or mounted runtime consumers.

## 9. Promotion boundary

Passing Checkpoint A permits review of the unmounted allocator substrate. It
does not close configuration provenance, settlement lineage, composite patch
application, state/support roots, receipts, commit bundles, replay, datastore
atomicity, Python/Rust full-runtime refinement, or the authority mount.
