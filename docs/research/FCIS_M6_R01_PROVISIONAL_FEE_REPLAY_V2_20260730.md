# FCIS M6-R01 Provisional-Fee Replay V2

**Date:** 2026-07-30

**Status:** implemented and tested pure kernel; unmounted

**Base:** M6-R01 Segmented Lineage Normal Form and the PR #498 research stack

## Result

The repository now has a separately versioned quoted-swap replay kernel for:

```text
PROVISIONAL_FEES_NO_SAME_BATCH_FUNDING_V2
```

It recomputes each swap quote from the evolving exact spot state, applies the
sender debit and recipient output credit, and places each protocol-fee atom in
an immutable provisional witness. The protocol fee is absent from spendable
balances during the complete ordered fold.

The V1 evaluator remains unchanged. Its existing accepted language credits the
protocol-fee recipient during sequential replay, so that credit can fund a
later fill in the same batch. A retained differential scenario proves that the
same trace is accepted by V1 and rejected by this V2 kernel.

## Pure boundary

The public function is:

```text
replay_provisional_fee_swaps_v2(
  exact tuple of quoted-swap claims,
  exact spot pre-state,
  exact untrusted replay policy,
)
  -> replay candidate
   | typed rejection
```

The implementation is a functional core. It performs no IO, datastore writes,
receipt construction, publication, or external effect delivery.

The successful candidate owns exactly:

```text
post_state
ordered provisional fee witnesses
```

Each fee witness proves the local conservation relation:

```text
sender_input_debit
  = pool_reserve_credit + provisional_fee_amount
```

It also binds the fill position, intent, domain, exact committed-pool
fingerprint, assets, parties, swap kind, declared amount and limit, recomputed
output, fee parameters, reserve transition, and a domain-separated source root.

## Closed rejection order

The current pure boundary evaluates failures in this order:

1. exact tuple and bounded claim count;
2. exact claim types and point-of-use field validation;
3. canonical positions and unique intent identities;
4. exact pre-state and policy validation;
5. pool existence, active status, asset orientation, and supported fee curve;
6. fresh quote derivation, declared-fill equality, and slippage;
7. exact balance and reserve transition;
8. post-pool reserve equality;
9. controlled candidate and witness construction.

Every rejection returns no post-state or provisional witness tuple.

## SLNF connection

`provisional_fee_witness_claims_v2` point-of-use revalidates the complete replay
candidate and projects its fee witnesses into the existing
`FeeWitnessOccurrenceClaimV1` carrier. Positions are re-enumerated within the
fee-witness tuple because SLNF requires a contiguous local witness order. The
original settlement position remains committed inside each source-witness
root.

This projection is still untrusted SLNF input. Canonicalization can derive the
semantic and lineage roots, but those roots gain protocol relevance only after
they are bound to independently authenticated settlement and policy sources.

## Executable evidence

The focused tests retain these counterexamples and invariants:

```text
V1 accepts an earlier fee credit funding a later same-batch fill
V2 rejects that trace because the fee remains provisional
one swap conserves input across pool credit and provisional fee
the protocol-fee recipient receives no spendable replay credit
the replay-derived witness enters SLNF without a caller-selected amount
equal inputs produce equal candidates
noncanonical positions reject before replay
duplicate intent identity rejects before replay
declared fill substitution rejects against the fresh quote
post-replay witness mutation rejects during projection
committed-pool fingerprint mutation rejects during projection
Boolean-as-integer mutation rejects before state access
```

Verification on the implementation worktree:

```text
Ruff, repository mypy, and focused replay tests: passed
V1 replay, SLNF, lineage, and B1A configuration regressions: 66 passed
security red-flag scan over the three changed code/test files: 0 findings
design metrics: no flagged function or file smell in the two source modules
B1B-1 isolation checker: passed across 940 runtime files
```

## Authority impact and nonclaims

The quoted-swap claims, fee policy, replay candidate, and projected SLNF claims
remain untrusted or unmounted exact data. The private construction token is a
misuse barrier and is not the authority boundary. Later consumers must rerun
the deterministic relation from independently authenticated sources.

This checkpoint does not provide:

```text
an OwnedSettlementV2 command or decoder
authenticated command or sender authority
authenticated current-state provenance
authenticated fee-configuration binding
settlement-derived boundary and policy roots
allocator or entitlement-state transition
receipt, decision, bundle, proof input, or outbox
atomic publication, recovery, or no-bypass evidence
Python/Rust transition or byte parity
runtime mounting
```

## Next safe checkpoint

Define the exact V2 settlement source type and derive the quoted-swap tuple from
freshly admitted command bytes, authenticated intent ownership, exact current
state, and a B1A-validated active configuration. The adapter must extract the
policy values from that validated configuration and must not accept a separate
caller-selected policy root or replay result.

Then replay the complete V2 occurrence word, derive both SLNF roots, and bind
the command, pre-state, active configuration, witness lineage, allocation,
entitlement successor, receipt, bundle, and outbox through one rederived commit
lineage. Publication remains blocked until the datastore operation proves
atomic PRE-or-POST recovery and all alternate acceptance paths fail closed.
