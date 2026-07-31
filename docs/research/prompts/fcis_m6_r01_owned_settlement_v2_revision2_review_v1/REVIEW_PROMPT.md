# Independent review prompt: M6-R01 OwnedSettlementV2 Revision 2

Act as an adversarial functional-core authority reviewer. Work read-only. Do
not implement, amend, commit, push, open a pull request, or mount authority.

## Exact target

```text
repository: TheDarkLightX/ZenoDEX
target commit: 16db3da7e3a6ee2716fac260f3de21b47bfd4827
target tree: 8c7a830e9c5e3cacf3431c6b06d432ffbe195302
target parent: 53beba00217274ec9357c3cf42fd11fa2501d306
revision 1 target: dd4175ba5649e0c66d9c4af0594e747de8c3eea8
revision 1 packet: 53beba00217274ec9357c3cf42fd11fa2501d306
```

First verify `SOURCE_MANIFEST.sha256`. Stop with `NO_GO` on a missing,
modified, or uninspectable required file.

## Review question

Does Revision 2 close the exact-state configuration provenance and sparse-fill
identity findings while preserving the acyclic two-level witness language?

Approval requires all of these statements:

1. B1A-valid content acquires active-configuration authority only by fresh
   binding to the same exact pre-state used by replay.
2. The binder checks recomputed root, pre-state-committed root, deployment, and
   activation sequence.
3. Original settlement fill ordinals survive zero-fee filtering and remain the
   only ordinal used in occurrence identity.
4. Admitted and freshly replayed tuples produce one exact controlled tuple.
5. The controlled batch owns that tuple, and a V2 consumer has no loose tuple
   or re-enumerating overload.
6. The controlled batch nests exact sources and does not duplicate derived
   roots, versions, or hashes as swappable constructor fields.
7. Early rejection creates no intermediate or downstream authority-like value.
8. The target remains design-only and unmounted.

## Proposed correction

The configuration pipeline is:

```text
untrusted content
  -> B1A admission and semantic validation
  -> validated_active_configuration_claim_v2

exact_pre_state_v2 + validated_active_configuration_claim_v2
  -> state_bound_active_configuration_v2
```

The binder freshly requires:

```text
validated root = recomputed body root
validated root = exact pre-state header configuration root
validated deployment = exact pre-state header deployment
validated activation sequence <= exact pre-state header sequence
```

The tuple pipeline is:

```text
admitted_local_claim_tuple_v2
  + recomputed_local_claim_tuple_v2
  -> exact_controlled_claim_tuple_v2
  -> state_bound_witness_batch_v2
  -> batch-owned exact tuple
  -> V2 sparse-ordinal normal form
```

There is no separately supplied consumed tuple.

## Mandatory falsification pass

### A. Valid but unauthorized configuration

Use an exact pre-state that commits `H_GOOD`. Supply a different B1A-valid
configuration with the same deployment, domain, protocol-fee share, algorithm,
and language, while changing destinations or weights so its root is `H_OTHER`.
Keep the authenticated command, settlement, local fee tuple, and occurrence
identities unchanged.

Confirm the exact-state binder rejects `H_OTHER` before replay or controlled
tuple construction. B1A validation alone must not satisfy this test.

Repeat with:

```text
wrong deployment
future activation sequence
bundle-carried historical state replacing store-current state
validated claim wired directly into replay
```

### B. Sparse settlement fill identity

Exercise these complete settlement fill patterns:

```text
zero fee, positive fee
positive fee, zero fee, positive fee
positive fee claims at settlement ordinals 1 and 3
```

Confirm the claim tuple retains original settlement ordinals, requires strict
increasing order and bounds against the complete fill tuple, and does not
require contiguity.

Mutate a claim ordinal from `3` to its positive-fee tuple index `1`. Recompute
every unrelated digest. Confirm rejection before occurrence identity exists.

### C. Cardinality and occurrence identity

For every complete settlement fill tuple, require:

```text
zero provisional fee -> zero claims for that settlement ordinal
positive provisional fee -> exactly one claim for that settlement ordinal
```

Try a missing positive claim, duplicate claim, zero-fee claim, out-of-range
ordinal, reordered claim, and occurrence ID based on claim tuple position.
Each must reject.

### D. One controlled tuple and downstream ownership

After admitted/replayed equality, try to supply a third consumed tuple. Also
try to drop, insert, copy, filter, reorder, group, or re-enumerate claims before
normalization.

Confirm the graph permits only:

```text
state_bound_witness_batch_v2.exact_controlled_claim_tuple
  -> V2 occurrence normal form
```

The existing V1 contiguous-position adapter must remain explicitly
nonconforming for this V2 interface.

### E. Minimal controlled batch

Add each of these constructor fields independently:

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

Confirm each mutation rejects. These facts must derive from nested exact
sources. Confirm the batch root remains absent from its own preimage.

### F. Complete settlement and command identity

Change one local claim field while preserving every other settlement field.
Confirm the complete settlement root changes. Confirm command-derived
occurrence identity remains downstream of the complete command root and uses
the original settlement fill ordinal.

Write and reject each cycle explicitly:

```text
settlement -> command root -> occurrence ID -> settlement
batch -> batch root -> batch
```

### G. Early rejection authority

Fail decoding, admission, B1A validation, exact-state binding, replay, tuple
equality, occurrence derivation, and batch derivation in turn.

Confirm failure leaves no:

```text
replay candidate
controlled claim tuple
occurrence ID tuple
witness batch
successor
patch
allocation
receipt
bundle
proof input
effect
outbox
```

### H. Scope and promotion

Search the exact target for an implemented or mounted:

```text
OwnedSettlementV2 carrier or codec
StateBoundFeeDistributionConfigurationV2
StateBoundProvisionalProtocolFeeWitnessBatchV2
V2 occurrence normalizer or allocator consumer
authenticated V2 command
committed V2 state
transition, receipt, bundle, proof, publication, or datastore path
runtime mount
```

Names in Markdown, JSON, policy constants, checkers, and mutation tests are not
runtime authority. Any production implementation of these excluded surfaces is
a scope violation.

## Required direct answers

1. Does the exact-state binder make valid-but-unauthorized configuration
   substitution impossible under the declared sources?
2. Do sparse positive-fee claims retain their original settlement ordinals?
3. Can any tuple index or consumer-side enumeration enter occurrence identity?
4. Does one batch-owned tuple replace the loose consumed-tuple surface?
5. Are the batch constructor fields minimal and source-bound?
6. Are the settlement, command, occurrence, and batch dependencies acyclic?
7. Is early rejection authority-empty across all listed artifacts?
8. Does the target remain design-only and unmounted?

## Verdict rule

Return exactly one:

```text
APPROVE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_2_UNMOUNTED
REVISE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_2
NO_GO
```

Approval permits only the next carrier/schema/codec/root/vector checkpoint.
It does not authorize state-bound configuration, controlled witness batches,
occurrence-ID authority, normalization, allocation, committed V2 state,
transitions, receipts, bundles, proof inputs, publication, datastore
integration, or runtime mounting.
