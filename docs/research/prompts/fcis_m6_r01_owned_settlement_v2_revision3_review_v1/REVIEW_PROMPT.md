# Independent review prompt: M6-R01 OwnedSettlementV2 Revision 3

Act as an adversarial functional-core authority reviewer. Work read-only. Do
not implement, amend, commit, push, open a pull request, or mount authority.

## Exact target

```text
repository: TheDarkLightX/ZenoDEX
target commit: 1b3e7d773438705f7b61b34f4f234676e18d3f0d
target tree: f8dbe8db82df97ab1e4baded63fa45a0fabba0af
target parent: d6cd7e02e04b4721d993056bb95d68ab0dac1db9
revision 2 target: 16db3da7e3a6ee2716fac260f3de21b47bfd4827
revision 2 packet: d6cd7e02e04b4721d993056bb95d68ab0dac1db9
```

First verify `SOURCE_MANIFEST.sha256`. Stop with `NO_GO` on a missing,
modified, or uninspectable required file.

## Review question

Does Revision 3 make fee-claim replay independent of submitted claims and bind
each controlled claim to exactly one command-derived occurrence identity while
preserving the acyclic, design-only, unmounted witness language?

Approval requires all of these statements:

1. Fresh replay consumes one exact recursively claim-erased settlement
   projection and four independent exact sources.
2. The whole claim-bearing settlement, command, and submitted claim tuple have
   no edge into the recomputed claim tuple.
3. Claim-only settlement mutation preserves the replay projection and
   independently recomputed tuple, so exact equality rejects the mutation.
4. Admitted and recomputed claims meet in one controlled claim tuple.
5. Each controlled occurrence owns one exact claim and the occurrence ID
   freshly derived for that claim from the complete command root and original
   settlement fill ordinal.
6. The future batch owns one paired controlled-occurrence tuple and has no
   parallel claim or occurrence-ID tuple.
7. The V2 normal form consumes only the batch-owned paired tuple and retains
   every ordered occurrence ID in lineage.
8. Exact-state binding proves configuration authority for one state candidate;
   only later atomic publication proves datastore currentness.
9. Composite rejection exports no controlled intermediate or downstream
   authority-like value.
10. The target remains design-only and unmounted.

## Proposed correction

The replay input pipeline is:

```text
admitted_owned_settlement_v2
  -> admitted_local_claim_tuple_v2

admitted_owned_settlement_v2
  -> ExactSettlementReplayProjectionV2
     with exact closed fields:
       module
       version
       batch_ref
       included_intents
       fills
       balance_deltas
       reserve_deltas
       lp_deltas
       events
```

The projection excludes `provisional_protocol_fee_witnesses` recursively and
has no independent root or authority.

The recomputation pipeline is:

```text
exact_settlement_replay_projection_v2
+ admitted_intent_tuple_v2
+ exact_pre_state_v2
+ state_bound_active_configuration_v2
+ authenticated_execution_context_v2
  -> recomputed_local_claim_tuple_v2
```

The controlled occurrence pipeline is:

```text
admitted_local_claim_tuple_v2
+ recomputed_local_claim_tuple_v2
  -> exact_controlled_claim_tuple_v2

exact_controlled_claim_tuple_v2
+ command_root_v2
  -> exact_controlled_occurrence_tuple_v2

exact controlled occurrence =
  (exact claim, H(command root, claim settlement fill ordinal))
```

The downstream path is:

```text
state_bound_witness_batch_v2
  -> batch_owned_controlled_occurrence_tuple_v2
  -> v2_occurrence_normal_form_v2
```

## Mandatory falsification pass

### A. Claim-erased projection closure

Add `provisional_protocol_fee_witnesses` to the replay projection. Also try a
nested mapping, extension member, alias, or wrapper that carries any submitted
claim or copied claim field.

Confirm exact recursive field closure rejects each mutant. Confirm the
projection cannot be decoded, rooted, or accepted independently from the
admitted complete settlement.

### B. Replay noninterference

Construct two admitted settlements with identical claim-independent material
and different submitted local claim tuples. Hold intents, exact pre-state,
state-bound configuration, and authenticated context fixed.

Require:

```text
replay_projection(S1) = replay_projection(S2)

recomputed_claims(S1) = recomputed_claims(S2)
```

Try each implementation mutant:

```text
return submitted claims directly
read submitted provisional_fee_amount
read submitted settlement_fill_ordinal
read the whole admitted settlement
read the whole exact command
read a copied claim nested in projection metadata
```

Each must reject through field closure, exact predecessor closure, or the
future executable noninterference property.

### C. Exact replay sources

Delete each of the five replay predecessors in turn. Add each forbidden whole
claim-bearing source in turn. Add an extra caller-supplied expected tuple or
root.

Confirm the checker requires exactly:

```text
claim-erased projection
admitted intents
exact pre-state
state-bound active configuration
authenticated execution context
```

### D. Pointwise occurrence identity

Use two controlled claims at settlement fill ordinals `1` and `3`. The correct
pairs are:

```text
(claim_1, H(command_root || 1))
(claim_3, H(command_root || 3))
```

Try:

```text
swap the two IDs
truncate the pair tuple
extend the pair tuple
duplicate an ID
use an ordinal absent from claims
use the positive-fee claim tuple index
reorder claims independently from IDs
accept a caller-supplied ID
```

Each must reject before a controlled occurrence tuple exists.

### E. Minimal batch and downstream lineage

Add each forbidden batch field:

```text
exact_settlement_replay_projection
exact_controlled_claim_tuple
exact_occurrence_id_tuple
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

Confirm each mutation rejects. Then make the normalizer consume only claims,
use a copied ID tuple, re-enumerate the positive-fee subset, or omit IDs from
its lineage root. Each path must be nonconforming.

Confirm equal claims under two different complete command roots retain distinct
lineage.

### F. Sparse settlement identity and cardinality

Retain the Revision 2 cases:

```text
zero fee, positive fee
positive fee, zero fee, positive fee
positive fee claims at settlement ordinals 1 and 3
```

Confirm ordinals stay bounded, strictly increasing, sparse, and derived from
the complete settlement fill tuple. Exercise missing-positive, duplicate,
zero-fee, out-of-range, reordered, and re-enumerated claims.

### G. State binding and currentness

Confirm state binding still checks recomputed configuration root, the exact
pre-state-committed root, deployment, and activation sequence.

Bind a valid configuration to a historical exact state. Confirm the result is
candidate evidence and does not claim datastore currentness. The later
publication relation must atomically load store-current exact state and
rederive the complete batch.

### H. Dependency cycles

Write and reject each cycle explicitly:

```text
settlement -> command root -> controlled occurrence -> settlement
batch -> batch root -> batch
normal form -> batch -> normal form
```

Confirm the frozen 22-node, 35-edge graph topologically sorts.

### I. Composite rejection authority

Fail admission, configuration binding, replay, tuple equality, occurrence
pairing, batch construction, and normalization in turn.

Confirm composite rejection exports no:

```text
state-bound active configuration
replay candidate
controlled claim tuple
controlled occurrence tuple
occurrence ID
witness batch
batch-owned controlled occurrence tuple
V2 occurrence normal form
successor
patch
allocation
receipt
bundle
proof input
effect
outbox
```

### J. Scope and promotion

Search the exact target for an implemented or mounted:

```text
OwnedSettlementV2 carrier or codec
ExactSettlementReplayProjectionV2
StateBoundFeeDistributionConfigurationV2
ControlledProvisionalProtocolFeeOccurrenceV2
StateBoundProvisionalProtocolFeeWitnessBatchV2
V2 occurrence normalizer or allocator consumer
authenticated V2 command
committed V2 state
transition, receipt, bundle, proof, publication, or datastore path
runtime mount
```

Names in Markdown, JSON, policy constants, checkers, and mutation tests carry no
runtime authority. Any production implementation of an excluded surface is a
scope violation.

## Required direct answers

1. Is the replay projection recursively claim-erased and non-authoritative?
2. Are the five recomputed-claim predecessors exact and claim-independent?
3. Does claim-only mutation leave recomputation unchanged?
4. Can whole command or settlement data influence the alleged fresh replay?
5. Is each claim pointwise bound to exactly one command-derived occurrence ID?
6. Can any permutation, truncation, duplication, or tuple index survive the
   paired construction?
7. Does the normal form consume and retain command-bound occurrence lineage?
8. Does the binder avoid claiming datastore currentness?
9. Are the settlement, command, occurrence, batch, and normal-form dependencies
   acyclic?
10. Is composite rejection authority-empty for every listed artifact?
11. Does the target remain design-only and unmounted?

## Verdict rule

Return exactly one:

```text
APPROVE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_3_UNMOUNTED
REVISE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_3
NO_GO
```

Approval permits only the next settlement carrier, claim-erased projection,
schema, codec, full-root, and vector checkpoint. It does not authorize
state-bound configuration, controlled occurrences, witness batches,
normalization, allocation, committed V2 state, transitions, receipts, bundles,
proof inputs, publication, datastore integration, migration, or runtime
mounting.
