# FCIS M6-R01 OwnedSettlementV2 witness language Revision 2

**Date:** 2026-07-31

**Status:** `DRAFT_FOR_INDEPENDENT_REVIEW`; design-only and unmounted

**Revision 1 target:** `dd4175ba5649e0c66d9c4af0594e747de8c3eea8`

**Revision 1 packet:** `53beba00217274ec9357c3cf42fd11fa2501d306`

## Result

Revision 1 correctly removed the settlement-root, command-root, occurrence-ID,
and batch-root cycles. Independent review found two remaining authority gaps:

```text
B1A-valid configuration
  was not checked against
exact pre-state configuration authority

admitted tuple = replayed tuple = consumed tuple
  named a third tuple that the machine graph did not own
```

The current research SLNF adapter also renumbers positive-fee witnesses after
zero-fee fills. That conflicts with command-derived identity based on original
settlement fill ordinals.

Revision 2 preserves the two-level witness architecture and adds:

```text
exact pre-state + B1A-validated claim
  -> state-bound active configuration

admitted claim tuple + freshly replayed claim tuple
  -> one exact controlled claim tuple

controlled witness batch
  owns the one exact controlled tuple
  -> V2 sparse-ordinal normal form
```

No carrier, binder, controlled batch, normalizer, allocator, receipt, bundle,
proof input, publication path, datastore integration, or runtime mount is
implemented by this revision.

## 1. Preflight record

### Authority surface

This revision owns only a review contract for:

```text
configuration source continuity
claim identity
root dependency order
future consumer ownership
rejection authority emptiness
```

It does not own operational state or effects.

### Existing values and consumers

The current unmounted replay retains original fill positions inside
`ProvisionalProtocolFeeWitnessV2`. Its V1 SLNF projection currently performs:

```text
enumerate(candidate.fee_witnesses)
```

That projection assigns contiguous positions inside the positive-fee subset.
The V1 SLNF also requires positions:

```text
0, 1, ..., number_of_witnesses - 1
```

These behaviors remain valid only for the existing research profile. They are
not a conforming consumer for the V2 claim language defined here.

### Trusted evidence level

The source-pinned inputs are:

```text
architecture amendment:
  c8fc946d916923fed8282112a5b4722fae774c67147e37a76b6099701f3f17e8

approved B1B state-binding design:
  cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5

current command-root source:
  d6b10072761318b07813bb6b0898e7f5b6592b1cd22ef4ae7bf2d11073952000
```

This revision is design and deterministic-checker evidence only.

## 2. State-bound active configuration

### 2.1 Separate validity from authority

The exact stages are:

```text
untrusted active configuration content
  -> closed B1A admission
  -> B1A semantic validation
  -> ValidatedFeeDistributionConfigurationClaimV2
  -> exact-state binder
  -> StateBoundFeeDistributionConfigurationV2
```

The validated claim carries no state authority.

The binder consumes:

```text
exact_pre_state_v2
validated_active_configuration_claim_v2
```

and freshly requires:

```text
validated.configuration_root
  =
canonical_configuration_root(validated.body)

validated.configuration_root
  =
exact_pre_state.authority_header
  .fee_distribution_configuration_root

validated.body.chain_deployment_id
  =
exact_pre_state.authority_header.chain_deployment_id

validated.body.activation_sequence
  <=
exact_pre_state.authority_header.sequence
```

Only successful binding constructs:

```text
state_bound_active_configuration_v2
```

### 2.2 Point-of-use reconstruction

The replay and controlled-batch derivations do not accept a caller-supplied
state-bound wrapper as authority.

They reconstruct it from:

```text
the same exact_pre_state_v2 used by replay
the freshly B1A-validated configuration claim
```

Publication must repeat this relation using the store-current exact state.

The resulting meaning is:

```text
this B1A-valid configuration
is committed by this exact pre-state
```

Historical exact state remains candidate evidence. Store currentness remains a
publication-shell obligation.

### 2.3 Configuration substitution witness

Let:

```text
exact pre-state configuration root = H_GOOD

C_MALLORY:
  B1A-valid
  same deployment
  same domain
  same protocol fee share
  different destinations or weights
  root = H_MALLORY
```

The local provisional fee tuple may be identical under both configurations.
The binder still rejects because:

```text
H_MALLORY != H_GOOD
```

Replay cannot begin under `C_MALLORY`.

## 3. Exact inner claim

The outer `OwnedSettlementV2` field registry remains:

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

The exact element type remains:

```text
ProvisionalProtocolFeeOccurrenceClaimV2
```

Its first field is now unambiguous:

```text
settlement_fill_ordinal
```

The complete ordered fields are:

```text
settlement_fill_ordinal
intent_id
fee_distribution_domain_id
pool_snapshot_fingerprint
pool_id
asset
sender_pubkey
swap_kind
recipient_pubkey
asset_out
amount_specified
limit_amount
recipient_output_credit
total_fee_amount
protocol_fee_share_bps
sender_input_debit
pool_reserve_credit
provisional_fee_amount
reserve_in_before
reserve_out_before
reserve_in_after
reserve_out_after
```

The ambiguous names are absent:

```text
fill_position
claim_position
```

Every downstream or independently sourced root remains absent.

## 4. Sparse settlement fill identity

For a settlement with fill tuple `fills`, every claim must require:

```text
0 <= claim.settlement_fill_ordinal < len(fills)
```

Claim ordinals are strictly increasing:

```text
claim[i].settlement_fill_ordinal
  <
claim[i + 1].settlement_fill_ordinal
```

They need not be contiguous.

Cardinality is defined against the complete settlement fill tuple:

```text
for each fill with provisional fee = 0:
  exactly zero claims identify that fill ordinal

for each fill with provisional fee > 0:
  exactly one claim identifies that fill ordinal

every claim:
  identifies a positive-fee fill
```

Insertion or removal of a zero-fee fill changes later settlement ordinals and
therefore changes the complete settlement and command identities. A consumer
cannot silently renumber the surviving positive-fee claims.

Occurrence identity uses:

```text
occurrence_id_v2 =
  sha256(
    domain_sep("protocol_fee_occurrence", version=2)
    || command_root_v2
    || canonical_settlement_fill_ordinal
  )
```

It never uses the index inside the positive-fee claim tuple.

## 5. One exact controlled claim tuple

Revision 2 removes the loose consumed-tuple surface.

The only inputs are:

```text
admitted_local_claim_tuple_v2
recomputed_local_claim_tuple_v2
```

The core requires exact equality and freshly owns the result as:

```text
exact_controlled_claim_tuple_v2
```

The controlled tuple is the complete ordered tuple. It is not filtered,
renumbered, reordered, grouped, or aggregated after equality.

The relation is:

```text
admitted_local_claim_tuple_v2
  -> exact_controlled_claim_tuple_v2

recomputed_local_claim_tuple_v2
  -> exact_controlled_claim_tuple_v2
```

There is no independently supplied:

```text
consumed_local_claim_tuple_v2
```

## 6. Smaller controlled batch

The future controlled batch constructor stores:

```text
StateBoundProvisionalProtocolFeeWitnessBatchV2(
  exact_authenticated_command,
  exact_pre_state,
  state_bound_active_configuration,
  authenticated_execution_context,
  exact_owned_settlement,
  exact_intent_tuple,
  exact_controlled_claim_tuple,
  exact_occurrence_id_tuple,
)
```

The derivation reconstructs `state_bound_active_configuration` internally from
the same `exact_pre_state` before constructing the batch.

These facts are derived properties, not constructor fields:

```text
command_root
pre_state_root
configuration_root
configuration_version
algorithm_version
accepted_language_version
execution_context_hash
owned_settlement_root
witness_batch_root
```

The batch root is computed only after the complete batch exists. It never
occurs in its own canonical preimage.

Direct construction, private tokens, frozen values, and canonical bytes do not
create protocol authority. Every authority-bearing use must repeat the complete
source-bound derivation.

## 7. Batch-owned downstream consumption

The future V2 normal-form port accepts:

```text
state_bound_witness_batch_v2
```

It reads:

```text
state_bound_witness_batch_v2.exact_controlled_claim_tuple
```

No overload accepts:

```text
loose claim tuple
copied claim tuple
caller-supplied consumed tuple
V1 contiguous-position projection
```

The V2 normal form preserves `settlement_fill_ordinal` while grouping same-key
amounts inside the accepted-transition boundary. Any internal contiguous loop
index is local scratch and cannot enter canonical identity, roots, receipts, or
occurrence IDs.

## 8. Complete dependency order

The normative order is:

```text
1. reauthenticate canonical command bytes
2. extract and admit the exact settlement and intent tuple
3. load the exact current pre-state
4. admit and B1A-validate active configuration content
5. bind that validated claim to the exact pre-state
6. authenticate the execution context
7. replay the complete accepted-language transition
8. derive the expected local claim tuple
9. require expected tuple = admitted settlement tuple
10. freshly own one exact controlled claim tuple
11. compute complete settlement and command roots
12. derive occurrence IDs from command root and settlement fill ordinals
13. construct the controlled batch from nested exact sources
14. compute the batch root
15. allow a V2 normalizer to consume only the batch-owned tuple
```

The machine-readable graph fixes every node, edge, and topological order.
Unknown isolated nodes also reject.

## 9. Rejection authority

Failure before controlled derivation returns none of:

```text
replay_candidate
controlled_claim_tuple
occurrence_id_tuple
witness_batch
successor
patch
allocation
receipt
bundle
proof_input
effect
outbox
```

A future committed-failure language requires a separately reviewed typed
result. It cannot be inferred from this early-rejection rule.

## 10. Required adversarial evidence

The permanent mutation set must kill:

```text
valid configuration H_OTHER against pre-state H_GOOD
same share and domain with different destinations
same share and domain with different weights
wrong deployment
future activation
validated claim bypasses exact-state binding
bundle-carried state replaces store-current state

zero-fee fill then positive-fee fill
positive, zero, positive fill sequence
sparse settlement ordinals 1 and 3
claim tuple re-enumeration
claim points to zero-fee fill
two claims point to one positive-fee fill
positive-fee fill has no claim
out-of-range settlement ordinal
claim reorder
occurrence ID uses claim tuple index

third loose consumed tuple
consumer drops, inserts, filters, reorders, groups, or copies a claim
normalizer bypasses batch ownership

duplicated root or version field in the controlled batch
batch root feeds its own preimage
early rejection retains an intermediate authority-like value
implementation or mount authority becomes true
```

## 11. Implementation boundary

Revision 2 does not authorize implementation of:

```text
OwnedSettlementV2 admission or codec
StateBoundFeeDistributionConfigurationV2
StateBoundProvisionalProtocolFeeWitnessBatchV2
V2 occurrence normal form
configuration authority
candidate, receipt, bundle, proof, publication, or datastore code
runtime mounting
```

Before implementing the carrier, independent review must still freeze:

```text
exact V2 module and version literals
exact command schema and command-root preimage
exact inner scalar schemas and bounds
exact settlement-root framing
stable rejection order and codes
Python/Rust canonical vectors
V1/V2 consumer migration inventory
```

## 12. Next safe checkpoint

After approval, implement only:

```text
ProvisionalProtocolFeeOccurrenceClaimV2
OwnedSettlementV2 source and admitted values
closed schemas and field registries
canonical Python/Rust bytes
full settlement root
positive/zero-fee and sparse-ordinal vectors
```

Keep state binding, controlled batch construction, occurrence-ID authority,
normalization, allocation, candidate, receipt, bundle, proof input,
publication, datastore integration, and runtime mounting outside that carrier
checkpoint.
