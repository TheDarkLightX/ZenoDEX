# FCIS M6-R01 OwnedSettlementV2 witness language Revision 3

**Date:** 2026-07-31

**Status:** `DRAFT_FOR_INDEPENDENT_REVIEW`; design-only and unmounted

**Revision 2 target:** `16db3da7e3a6ee2716fac260f3de21b47bfd4827`

**Revision 2 packet:** `d6cd7e02e04b4721d993056bb95d68ab0dac1db9`

## Result

Revision 2 closed exact-state configuration binding and sparse settlement fill
identity. Independent review found two remaining authority gaps:

```text
whole submitted command or settlement
  contains submitted local fee claims
  -> alleged fresh replay could read those claims

controlled claims + separate occurrence-ID tuple
  -> independent permutation or truncation remained representable
```

Revision 3 introduces two smaller exact values:

```text
ExactSettlementReplayProjectionV2
  recursively claim-erased replay input
  no independent root or authority

ControlledProvisionalProtocolFeeOccurrenceV2
  one exact controlled claim
  one command-derived occurrence ID
```

The future controlled batch owns one ordered tuple of paired controlled
occurrences. A V2 occurrence normal form must consume that batch-owned paired
tuple and retain every ordered occurrence ID in lineage.

This revision implements no carrier, replay projection, state binder, controlled
occurrence, witness batch, normalizer, allocator, receipt, bundle, proof input,
publication path, datastore integration, or runtime mount.

## 1. Preflight record

### 1.1 Authority surface

Revision 3 owns a review contract for:

```text
claim-erased replay inputs
replay noninterference
claim-to-occurrence pointwise binding
downstream lineage ownership
configuration-binding versus currentness
composite rejection output closure
```

It owns no operational state or external effect.

### 1.2 Source-pinned inputs

The checker pins the exact prior design and load-bearing sources:

```text
Revision 2 target:
  16db3da7e3a6ee2716fac260f3de21b47bfd4827

Revision 2 packet:
  d6cd7e02e04b4721d993056bb95d68ab0dac1db9

Revision 2 document SHA-256:
  08dd04ad505913da7572a9437164f031f4935075ab5841bdc6bde8a63758aaef

Revision 2 matrix SHA-256:
  1de4c7af8b0b443151e60ede79ca8c94f74a8fee3530084465c160bb1278669a

approved B1B state-binding design SHA-256:
  cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5

current command-root source SHA-256:
  d6b10072761318b07813bb6b0898e7f5b6592b1cd22ef4ae7bf2d11073952000

current provisional replay source SHA-256:
  2b91fa0f4835bc53d98a2b17ef3f08a659b4f7b52917dc353e15398fed285f9e

current provisional replay values SHA-256:
  f1bab3b7b6a2c56c2e3ad175cc1ead8f94b559370c120ad3c5cbe448863b9176
```

These sources establish the reviewed dependency context. They do not promote
Revision 3 beyond design and deterministic-checker evidence.

## 2. Full settlement commitment and claim-erased replay

### 2.1 One canonical settlement identity

The complete `OwnedSettlementV2` field registry remains:

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

The full settlement root commits the complete canonical envelope, including
the exact ordered submitted claim tuple:

```text
owned_settlement_root_v2 =
  sha256(
    domain_sep("owned_settlement", version=2)
    || canonical_owned_settlement_v2
  )
```

The replay projection does not define a second settlement identity. It is a
non-authoritative deterministic view of an admitted settlement.

### 2.2 Exact replay projection

`ExactSettlementReplayProjectionV2` has exactly these fields:

```text
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

It excludes:

```text
provisional_protocol_fee_witnesses
```

The exclusion is recursive. Every projection component must be admitted into
an exact closed claim-independent type. A nested mapping, extension field,
alias, or wrapper cannot carry a provisional fee occurrence claim or any field
copied from one.

The projection has no independently accepted bytes, root, identifier, or
authority wrapper. It is reconstructed at point of use from the exact admitted
settlement.

### 2.3 Exact replay inputs

The recomputed local claim tuple has exactly five predecessors:

```text
exact_settlement_replay_projection_v2
admitted_intent_tuple_v2
exact_pre_state_v2
state_bound_active_configuration_v2
authenticated_execution_context_v2
```

These sources form the complete replay input language.

The following claim-bearing values are excluded as replay inputs:

```text
exact_authenticated_command_v2
admitted_owned_settlement_v2
admitted_local_claim_tuple_v2
```

The exact command remains available for command identity and later batch
lineage. The complete settlement remains available for the settlement root and
later batch lineage. Neither value may enter fee-claim recomputation.

### 2.4 Noninterference law

Let:

```text
P(S) = exact claim-erased replay projection of settlement S

R(P, I, X, C, E) = freshly recomputed local claim tuple

I = admitted intent tuple
X = exact pre-state
C = state-bound active configuration
E = authenticated execution context
```

For any two admitted settlements `S1` and `S2`:

```text
P(S1) = P(S2)
and I1 = I2
and X1 = X2
and C1 = C2
and E1 = E2

implies

R(P(S1), I1, X1, C1, E1)
  =
R(P(S2), I2, X2, C2, E2)
```

A mutation confined to `provisional_protocol_fee_witnesses` therefore:

```text
preserves the replay projection
preserves the independently recomputed tuple
changes the admitted submitted tuple
causes exact tuple equality to reject
```

This law is a required executable property for the later projection and replay
checkpoint. Revision 3 records and mutation-checks the design obligation.

### 2.5 Controlled claim equality

Only exact equality between the two independently constructed tuples produces:

```text
exact_controlled_claim_tuple_v2
```

The only predecessors are:

```text
admitted_local_claim_tuple_v2
recomputed_local_claim_tuple_v2
```

No third consumed tuple, copied tuple, filtered tuple, aggregate, or
caller-supplied expected tuple exists.

## 3. One paired controlled occurrence tuple

### 3.1 Paired value

The future controlled element is:

```text
ControlledProvisionalProtocolFeeOccurrenceV2(
  exact_claim,
  occurrence_id,
)
```

Its constructor is controlled by the pointwise derivation relation. A caller
cannot supply the occurrence ID as authority.

For each `i` in the exact controlled claim tuple:

```text
occurrence_id_i =
  sha256(
    domain_sep("protocol_fee_occurrence", version=2)
    || command_root_v2
    || canonical_settlement_fill_ordinal(claim_i)
  )

controlled_occurrence_i =
  (claim_i, occurrence_id_i)
```

The exact occurrence-ID byte projection remains a later codec checkpoint. The
dependency and pointwise relationship are frozen here.

### 3.2 Pairing laws

The construction requires:

```text
length(pairs) = length(controlled_claims)

pairs[i].exact_claim = controlled_claims[i]

pairs[i].occurrence_id =
  H(command_root_v2, controlled_claims[i].settlement_fill_ordinal)

pair order = controlled claim order

all occurrence IDs are unique

all occurrence IDs are derived inside the controlled constructor
```

The controlled claim order is already strictly increasing by original
settlement fill ordinal. It may be sparse.

Under the standard domain-separation and collision-resistance assumptions:

```text
same claims + different command roots
  -> different occurrence lineage
```

### 3.3 Swapped-ID falsifier

For claims at settlement ordinals `1` and `3`, the only valid tuple is:

```text
(
  (claim_1, H(command_root || 1)),
  (claim_3, H(command_root || 3)),
)
```

This mutation rejects:

```text
(
  (claim_1, H(command_root || 3)),
  (claim_3, H(command_root || 1)),
)
```

Each hash in the mutant is individually well formed and command-bound. The
pointwise owned pair makes the positional substitution unrepresentable as a
controlled value.

### 3.4 Minimal future batch

The future batch constructor contains exactly:

```text
StateBoundProvisionalProtocolFeeWitnessBatchV2(
  exact_authenticated_command,
  exact_pre_state,
  state_bound_active_configuration,
  authenticated_execution_context,
  exact_owned_settlement,
  exact_intent_tuple,
  exact_controlled_occurrence_tuple,
)
```

It does not store parallel or duplicated fields for:

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

Claims and occurrence IDs may be exposed only as read-only projections of the
one nested paired tuple.

## 4. Downstream V2 occurrence normal form

The exact downstream path is:

```text
state_bound_witness_batch_v2
  -> batch_owned_controlled_occurrence_tuple_v2
  -> v2_occurrence_normal_form_v2
```

The V2 normal form receives no loose claim tuple and no separate occurrence-ID
tuple. Its lineage projection must commit every ordered command-bound
occurrence ID.

The following paths are nonconforming:

```text
controlled claim tuple -> V2 normal form
submitted claim tuple -> V2 normal form
copied occurrence-ID tuple -> V2 normal form
positive-fee subset enumeration -> V2 normal form
normal form that commits amounts while dropping occurrence IDs
```

The current V1 SLNF adapter remains research evidence. Its contiguous
`enumerate(candidate.fee_witnesses)` behavior cannot consume this V2 language.

## 5. Configuration binding and datastore currentness

The exact-state configuration binder establishes:

```text
validated root = recomputed configuration-body root
validated root = exact pre-state header configuration root
validated deployment = exact pre-state header deployment
validated activation sequence <= exact pre-state header sequence
```

Its result means:

```text
this B1A-valid configuration is committed by this exact state candidate
```

The binder does not establish datastore currentness. A historical state can
produce valid state-bound candidate evidence.

The later publication shell must:

```text
atomically load the store-current exact state
revalidate and bind the active configuration to that state
rederive replay, equality, controlled occurrences, and the complete batch
compare the complete submitted candidate
publish or reject stale
```

No bundle-carried or caller-carried state may establish currentness.

## 6. Composite rejection output closure

Failure of the composite settlement-binding operation exports none of these
controlled or downstream values:

```text
state_bound_active_configuration
replay_candidate
controlled_claim_tuple
controlled_occurrence_tuple
occurrence_id
witness_batch
batch_owned_controlled_occurrence_tuple
v2_occurrence_normal_form
successor
patch
allocation
receipt
bundle
proof_input
effect
outbox
```

An independently valid input may remain available internally to its original
owner. It cannot be returned as successful evidence from the failed composite
operation.

## 7. Dependency graph

The frozen graph has:

```text
22 nodes
35 required edges
one complete topological order
no unknown or isolated node
```

The load-bearing path is:

```text
authenticated bytes
  -> exact command
  -> admitted settlement
      -> submitted claims
      -> full settlement root
      -> claim-erased replay projection

exact state + validated configuration
  -> state-bound active configuration

claim-erased projection
+ exact intents
+ exact state
+ state-bound configuration
+ authenticated context
  -> recomputed claims

submitted claims + recomputed claims
  -> exact controlled claims

exact controlled claims + command root
  -> exact paired controlled occurrences

exact command
+ exact settlement
+ exact intents
+ exact state
+ state-bound configuration
+ authenticated context
+ exact paired controlled occurrences
  -> state-bound witness batch
  -> batch root
  -> batch-owned paired occurrences
  -> V2 occurrence normal form
```

The graph has no path from any downstream root, pair, batch, or normal form
back into the settlement preimage.

## 8. Acceptance and mutation evidence

The machine-readable matrix defines 14 design-ready acceptance cases. The
mutation suite covers:

```text
submitted claims added to replay projection
recursive projection component leakage law removed
whole command, settlement, or submitted claims added to replay inputs
each required replay predecessor removed
each noninterference law removed or weakened
admitted/recomputed equality predecessor removed
parallel occurrence-ID tuple added
controlled occurrence extra field added
each pointwise pairing law removed
command-root or controlled-claim pairing source removed
every duplicated batch field added
claim-only normal-form consumer introduced
sparse ordinal and fee cardinality rules weakened
state binder overclaims currentness
each composite rejection output removed
inner command root added
full settlement claim commitment removed
batch-root cycle introduced
normative source identity drift
duplicate JSON member
implementation or mount authority enabled
```

The checker fails closed on unknown fields, unknown graph nodes, unknown edges,
duplicate edges, duplicate JSON members, source drift, incomplete cases, and an
invalid topological order.

## 9. Local validation

The exact local worktree passed:

```text
Revision 3 contract checker:
  ok=true
  acceptance_case_count=14
  implementation_authorized=false
  mount_authorized=false

Revision 3 mutation suite:
  87 passed

Revision 1-3, replay, normal-form, lineage, B1A, and B1B regressions:
  271 passed

Ruff:
  passed

strict mypy over the four Revision 3 Python modules:
  passed

Python compileall:
  passed

public claims registry:
  passed

security red-flag scan:
  no findings in the six Revision 3 files

diff whitespace check:
  passed
```

No hosted workflow result is claimed until an exact remote target exists and
GitHub Actions evaluates that target or its review-packet child.

## 10. Exact scope and nonclaims

Revision 3 establishes design and checker evidence for:

```text
one complete settlement commitment
one recursively claim-erased replay projection
one exact five-source replay relation
one admitted-versus-recomputed controlled claim tuple
one pointwise paired controlled occurrence tuple
one batch-owned V2 lineage path
one explicit binder/currentness division
one closed composite rejection-output registry
```

It does not establish:

```text
OwnedSettlementV2 source or admitted carriers
canonical Python or Rust V2 bytes
claim-erased projection implementation
executable noninterference
state-bound configuration implementation
controlled occurrence implementation
witness batch or batch root
V2 occurrence normal form
allocator consumption
candidate, transition, receipt, or bundle
proof input or verifier refinement
publication or datastore atomicity
migration or runtime mounting
Python and Rust parity
```

## 11. Smallest safe next checkpoint

After independent approval of Revision 3, the next unmounted checkpoint may
implement only:

```text
ProvisionalProtocolFeeOccurrenceClaimV2
OwnedSettlementV2 source and admitted values
ExactSettlementReplayProjectionV2
recursive claim-erasure validation
closed schemas and field registries
canonical Python and Rust settlement bytes
full settlement root
claim-only noninterference properties
positive, zero-fee, and sparse-ordinal vectors
```

It must continue to exclude:

```text
state-bound configuration implementation
controlled occurrence authority
controlled witness batch
occurrence normalizer and allocator
candidate and transition
receipt and bundle
proof input
publication
datastore integration
runtime mount
```

That boundary gives the next reviewer executable evidence for the claim-erased
carrier surface without introducing successor-producing authority.
