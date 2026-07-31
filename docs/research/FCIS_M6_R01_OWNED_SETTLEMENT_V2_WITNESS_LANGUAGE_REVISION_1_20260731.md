# FCIS M6-R01 OwnedSettlementV2 witness language Revision 1

**Date:** 2026-07-31

**Status:** `DRAFT_FOR_INDEPENDENT_REVIEW`; design-only and unmounted

**Base implementation:** `f891607a77671403042b34d6bc45d907aae69115`

## Result

This revision resolves a cyclic dependency in the proposed
`OwnedSettlementV2` witness language.

The architecture amendment currently requires:

```text
OwnedSettlementV2
  contains provisional_protocol_fee_witnesses

each provisional witness
  binds OwnedSettlementV2 root

protocol fee occurrence ID
  depends on command root

current FCIS command root
  depends on settlement bytes
```

Taken literally, the settlement root is needed to construct a value inside the
settlement whose bytes are needed to compute that root. The occurrence ID
creates the same cycle when the command root contains the settlement.

The selected correction separates exact claim data from controlled evidence:

```text
ProvisionalProtocolFeeOccurrenceClaimV2
  caller-visible exact data inside OwnedSettlementV2

StateBoundProvisionalProtocolFeeWitnessBatchV2
  controlled evidence outside OwnedSettlementV2
```

The inner claim carries no protocol authority. The outer batch is freshly
derived from all independent sources and binds the final settlement and command
roots.

## Minimal-witness discovery question

```text
Find the smallest exact witness language L such that:

1. one canonical OwnedSettlementV2 root commits every local fee occurrence;
2. every controlled occurrence binds the exact command, settlement, pre-state,
   active configuration, execution context, quote, and fill position;
3. no caller-selected root becomes an authority source;
4. the root dependency graph is acyclic;
5. rejection produces no successor, patch, receipt, bundle, or effect.
```

Five candidate languages were considered.

| Candidate | Result | Reason |
| --- | --- | --- |
| Final settlement root stored in each inner witness | Reject | Direct self-root cycle |
| Command-derived occurrence ID stored in each inner witness | Reject | Command root includes settlement bytes |
| Settlement-body root plus a second final settlement root | Reject for this checkpoint | Acyclic, but adds a second settlement identity and changes the frozen ABI |
| Root projection that omits or blanks inner witnesses | Reject | Breaks canonical identity and encoding injectivity |
| Exact inner claims plus a controlled outer batch | Select | Acyclic, one settlement root, complete point-of-use binding |

## Exact inner claim

The frozen outer field registry remains:

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

The field name remains frozen for ABI continuity. Its exact element type is
clarified as:

```text
ProvisionalProtocolFeeOccurrenceClaimV2
```

The claim has these fields, in order:

```text
fill_position
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

The claim excludes every downstream or independently sourced root:

```text
command_root
owned_settlement_root
pre_state_root
configuration_root
execution_context_hash
occurrence_id
source_witness_root
witness_batch_root
receipt_root
bundle_root
outbox_root
```

Derived roots are never cached inside their own canonical preimages.

Only positive provisional fee amounts produce an inner claim. Zero protocol
fees produce no claim. The mandatory tuple itself may be empty.

## Acyclic derivation

The normative order is:

```text
1. authenticate and canonically admit command bytes
2. admit the exact V2 settlement and exact intent tuple
3. admit the exact current pre-state
4. validate the active B1A configuration at point of use
5. authenticate the execution context
6. replay the complete accepted-language transition from those sources
7. derive the expected local occurrence-claim tuple
8. require:

   expected claim tuple
     = admitted settlement claim tuple
     = consumed claim tuple

9. compute the full OwnedSettlementV2 root over the exact canonical envelope,
   including the complete inner claim tuple
10. compute the command root over the exact canonical admitted command
11. derive occurrence IDs from command root and canonical fill ordinals
12. derive the controlled state-bound witness batch
13. allow later candidate, receipt, bundle, and publication phases to bind only
    the freshly derived batch
```

The settlement root remains:

```text
owned_settlement_root_v2 =
  sha256(
    domain_sep("owned_settlement", version=2)
    || canonical_owned_settlement_v2
  )
```

The occurrence ID remains:

```text
occurrence_id_v2 =
  sha256(
    domain_sep("protocol_fee_occurrence", version=2)
    || command_root_v2
    || canonical_fill_ordinal
  )
```

The occurrence ID is part of controlled evidence. It is absent from the inner
settlement claim.

## Controlled evidence boundary

The later controlled value is:

```text
StateBoundProvisionalProtocolFeeWitnessBatchV2(
  exact_owned_settlement,
  owned_settlement_root,
  command_root,
  exact_pre_state,
  pre_state_root,
  validated_active_configuration,
  configuration_root,
  configuration_version,
  algorithm_version,
  accepted_language_version,
  authenticated_execution_context,
  execution_context_hash,
  exact_replayed_claims,
  exact_occurrence_ids,
)
```

`witness_batch_root_v2` is derived after this value is constructed. It is not a
constructor field and never occurs in its own canonical preimage. The exact
batch-root preimage remains a later independent-review obligation.

Physical duplication of every batch-wide root into every leaf is unnecessary.
Each controlled leaf root derives from the batch context and one exact inner
claim. The batch owns the ordered leaf tuple. This gives every occurrence the
required binding while keeping one source of truth for batch-wide facts.

Direct construction, private tokens, frozen dataclasses, or canonical bytes do
not create authority. Every authority-bearing use must reconstruct this batch
from the store-current exact state, freshly reauthenticated command, validated
active configuration, and authenticated context.

## ATDD scenarios

### Scenario 1: self-root mutation rejects

```text
Given an inner occurrence claim
When owned_settlement_root is added to the claim
Then the contract checker rejects the downstream field
And the dependency graph cannot be promoted
```

### Scenario 2: command-root occurrence mutation rejects

```text
Given command_root includes the exact settlement bytes
When occurrence_id is added to the inner claim
Then command_root depends on occurrence_id through the settlement
And occurrence_id depends on command_root
And the contract checker rejects the cycle
```

### Scenario 3: settlement commits every occurrence

```text
Given two exact settlements that differ in one local fee occurrence field
When their canonical roots are recomputed
Then their OwnedSettlementV2 roots differ
```

### Scenario 4: caller-selected roots remain data

```text
Given a submitted settlement, command root, configuration root, and context hash
When the controlled batch is derived
Then every root is freshly recomputed or reauthenticated from its independent source
And submitted root fields are equality targets only
```

### Scenario 5: coordinated substitution rejects

```text
Given one authenticated command and one exact current pre-state
When a caller substitutes the settlement claim tuple and recomputes its settlement root
Then fresh replay derives the original expected tuple
And exact tuple equality rejects the substituted settlement
```

### Scenario 6: rejection is authority-empty

```text
Given any earlier decode, admission, validation, replay, equality, or binding failure
When the V2 relation rejects
Then it returns no successor, patch, allocation, receipt, bundle, proof input, or effect
```

## Implementation boundary

This document does not authorize implementation of:

```text
OwnedSettlementV2 admission or codec
StateBoundProvisionalProtocolFeeWitnessBatchV2
authenticated command construction
configuration authority
candidate, receipt, bundle, proof, publication, or datastore code
runtime mounting
```

The current V2 replay and SLNF modules remain unmounted research evidence.

Before implementing the carrier, an independent review must freeze:

```text
the exact V2 module and version literals
the exact command schema and command-root preimage
the exact inner-claim scalar schemas and bounds
the exact controlled batch and leaf-root preimages
the rejection order and stable codes
the V1/V2 consumer migration inventory
```

## Next safe checkpoint

After approval, implement only the exact inner claim, `OwnedSettlementV2`
admission, canonical bytes, root, and negative vectors. Keep the controlled
batch and every authority-bearing consumer out of that carrier checkpoint.

The following checkpoint can then derive the exact claim tuple from the
store-current pre-state, reauthenticated command, B1A-validated active
configuration, and authenticated execution context.
