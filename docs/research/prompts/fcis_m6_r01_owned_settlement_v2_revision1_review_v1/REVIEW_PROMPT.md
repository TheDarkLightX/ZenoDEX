# Independent review prompt: M6-R01 OwnedSettlementV2 Revision 1

Act as an adversarial functional-core authority reviewer. Work read-only. Do
not implement, amend, commit, push, open a pull request, or mount authority.

## Exact target

```text
repository: TheDarkLightX/ZenoDEX
target commit: dd4175ba5649e0c66d9c4af0594e747de8c3eea8
target tree: f2574e071ec3f19d0f03463ca3462b705a7b5650
target parent: f891607a77671403042b34d6bc45d907aae69115
architecture amendment:
  docs/research/prompts/fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/SRGD_V1_AMENDMENT.md
```

First verify `SOURCE_MANIFEST.sha256`. Stop with `NO_GO` on a missing,
modified, or uninspectable required file.

## Review question

Does Revision 1 define the smallest exact, acyclic witness language in which:

1. the complete canonical `OwnedSettlementV2` commits every local provisional
   protocol-fee occurrence claim;
2. no inner claim contains a downstream root or command-derived occurrence ID;
3. the controlled witness batch is freshly derived from the exact independent
   command, pre-state, validated active configuration, execution context,
   settlement, intent tuple, and replay result;
4. caller-supplied roots are equality targets only;
5. rejection before controlled derivation creates no successor, patch,
   allocation, receipt, bundle, proof input, outbox, or effect; and
6. the checkpoint remains design-only and unmounted?

## Proposed correction

The architecture amendment places provisional fee witnesses inside
`OwnedSettlementV2`, requires each witness to bind the settlement root, and
derives occurrence identity from a command root that includes settlement bytes.
A literal implementation is cyclic.

Revision 1 separates the phases:

```text
ProvisionalProtocolFeeOccurrenceClaimV2
  exact caller-visible data inside OwnedSettlementV2

full canonical OwnedSettlementV2
  -> owned_settlement_root_v2

full canonical admitted command
  -> command_root_v2
  -> occurrence_id_tuple_v2

independent exact sources + fresh replay + exact tuple equality
  -> StateBoundProvisionalProtocolFeeWitnessBatchV2
  -> witness_batch_root_v2
```

The batch root is downstream of the batch and is absent from its own canonical
preimage.

## Mandatory falsification pass

### A. Inner self-root

Add `owned_settlement_root`, `command_root`, `occurrence_id`,
`witness_batch_root`, `receipt_root`, or `bundle_root` to the inner claim.
Rebuild every unrelated hash.

Confirm the field registry or dependency graph rejects before any controlled
evidence exists.

### B. Root-projection omission

Construct two exact settlements that differ in one provisional-fee claim field.
Try a root projection that omits, blanks, separately hashes, or appends the
claim tuple outside the canonical settlement envelope.

Confirm the only accepted strategy commits the complete ordered claim tuple in
the one canonical settlement root.

### C. Command and occurrence cycle

Assume the command root commits settlement bytes. Put a command-derived
occurrence ID into the settlement claim.

Require the reviewer to write the resulting cycle explicitly:

```text
settlement bytes
  -> command root
  -> occurrence ID
  -> settlement bytes
```

Confirm Revision 1 derives occurrence IDs only after settlement and command
roots are known.

### D. Batch self-root

Put `witness_batch_root_v2` inside
`StateBoundProvisionalProtocolFeeWitnessBatchV2` and treat it as part of the
batch-root preimage.

Confirm both the prose relation and machine dependency graph reject:

```text
witness batch
  -> witness batch root
  -> witness batch
```

### E. Coordinated claim substitution

Use one authenticated command and one exact current pre-state. Substitute a
different internally consistent claim tuple and recompute the settlement and
command roots.

Confirm fresh accepted-language replay derives the expected tuple from:

```text
freshly reauthenticated command bytes
store-current exact pre-state
point-of-use B1A-validated active configuration
independently authenticated execution context
```

Require exact equality among expected, admitted, and consumed claim tuples.

### F. Loose roots and missing sources

Try supplying each value independently from the shell or submitted bundle:

```text
pre_state_root
configuration_root
execution_context_hash
owned_settlement_root
command_root
```

Delete each source-to-controlled-batch edge in turn. Confirm every mutation
rejects. An exact digest value is data; it does not recover provenance.

### G. Zero-fee cardinality

Exercise:

```text
zero provisional fee
positive provisional fee
empty settlement claim tuple
multiple claims for one positive-fee fill
```

Confirm zero has one canonical absence representation and every positive fee
has exactly one fill-bound claim.

### H. Rejection authority

Fail decoding, admission, B1A validation, replay, tuple equality, and root
binding in turn.

Confirm each earlier failure creates no:

```text
successor
patch
allocation
receipt
bundle
proof input
effect
outbox
```

### I. Scope and promotion

Search the exact target for an implemented:

```text
OwnedSettlementV2 carrier or codec
StateBoundProvisionalProtocolFeeWitnessBatchV2
authenticated V2 command
committed V2 state
transition, receipt, bundle, proof, publication, or datastore path
runtime mount
```

Any present authority-bearing implementation is a scope violation. Review-only
types and names in Markdown, JSON, checkers, and mutation tests are not a mount.

## Required direct answers

1. Is the full settlement-root dependency graph acyclic?
2. Does the settlement root commit the complete ordered local claim tuple?
3. Is every occurrence ID downstream of the complete command root?
4. Is the controlled batch reconstructed from independent exact sources?
5. Can coordinated claim and root substitution pass fresh replay equality?
6. Is the batch root absent from its own canonical preimage?
7. Are zero-fee cardinality and early-rejection authority closed?
8. Does the target remain design-only and unmounted?

## Verdict rule

Return exactly one:

```text
APPROVE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_1_UNMOUNTED
REVISE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_1
NO_GO
```

Approval permits only the next carrier checkpoint after its remaining literal,
scalar-schema, root-preimage, rejection-order, and migration-inventory details
are independently frozen. It does not authorize controlled evidence or runtime
mounting.
