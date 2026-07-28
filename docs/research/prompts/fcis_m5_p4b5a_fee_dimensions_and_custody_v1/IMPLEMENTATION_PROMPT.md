# Implement FCIS M5-P4B5A: fee dimensions and protocol custody

**Status:** frozen

**Prompt kind:** build

**Contract version:** `zenodex/fcis-m5-p4b5a-fee-dimensions-and-custody/v1`

**Required reviewed ancestor:** `6c4e7c6be89f76605e86c5532a4841d5e271611b`

**Authority posture:** unmounted evidence only

## Objective

Replace scalar fee authority with exact per-asset, per-custodian values derived
from the already validated swap replay.

The checkpoint closes:

```text
FEE-UNIT-001
FEE-CUSTODY-002
```

The target relation is:

```text
ValidatedProtocolFeeCreditsV2
  × FeeDistributionPolicyV2
  × FeeAccumulatorStateV2
  × CommittedBalanceTableV1

→ Reject(StableFeeRejectV2)
| Accept(
    FeeAccumulatorStateV2,
    CommittedBalanceTableV1,
    CanonicalBalancePatchV1,
    tuple[AssetFeeDistributionV2, ...],
  )
```

Every accepted distribution is applied to the returned balance candidate.
The receipt-facing distribution is a record of an already applied state
transition. It is not a second shell transfer instruction.

## Frozen semantic decisions

### P4B5A-D01: distinguish LP fees from protocol-owned fees

`fill.fee_paid` is the total swap fee retained by the AMM economics. It may
include value that remains in pool reserves for LPs. It is analytics only for
this checkpoint.

Only `protocol_fee_paid`, recomputed and accepted by the exact strong
settlement validator, may create a `ProtocolFeeCreditV2`.

```text
fee_paid
  -> never enters fee-distribution authority

protocol_fee_paid
  -> exact replay credit to protocol_fee_recipient_pubkey in asset_in
  -> may fund one same-asset distribution
```

Routed swaps currently produce aggregate LP fees and no exact protocol-fee
credit. They contribute zero to protocol distribution. CoW and liquidity
operations also contribute zero.

### P4B5A-D02: exact denomination and custody key

Every authoritative fee atom carries:

```text
source_custody_pubkey
asset
amount
```

The accumulator key is:

```text
(source_custody_pubkey, asset)
```

Keying dust by asset alone is insufficient because protocol custody may change
between authenticated policy epochs.

No conversion between assets is defined. Different keys are never added.

### P4B5A-D03: destination ownership

The fee-distribution policy must provide exact destination custody pubkeys for:

```text
buyback
treasury
rewards
```

The policy also provides three bounded basis-point shares whose sum is exactly
10,000. Each output distribution records the source custody, asset, all three
destination custodians, all three amounts, and residual dust.

The term `buyback` means same-asset custody earmarked for a later, separately
authorized buyback protocol. P4B5A does not execute an asset conversion.

### P4B5A-D04: state-applied distribution

For one key with fresh credit `f` and retained dust `d`:

```text
total = f + d

buyback  = floor(total × buyback_bps  / 10_000)
treasury = floor(total × treasury_bps / 10_000)
rewards  = floor(total × rewards_bps  / 10_000)
dust'    = total - buyback - treasury - rewards
```

The balance transition debits the source by:

```text
buyback + treasury + rewards
```

and credits each destination in the same asset. The residual `dust'` remains
in source custody and is retained in the accumulator under the same custody
key.

Aliases among source and destinations are legal. Deltas are aggregated by the
existing canonical balance transition. A complete alias may produce no balance
patch while still producing a valid distribution record.

### P4B5A-D05: canonical order and bounds

Credits may be produced in semantic fill order. The fee transition validates
every exact atom, groups them by custody key in bounded local scratch, and
emits distributions and dust entries in strict lexicographic order:

```text
(source_custody_pubkey, asset)
```

The maximum number of credits, accumulator entries, distributions, balance
deltas, and canonical bytes must be source-owned constants. Unknown or
exceeded bounds reject before authority is returned.

### P4B5A-D06: construction authority

Authority-bearing values are final, frozen, and slotted. Controlled
constructors own accepted transition results. Public callers may provide only
closed source values to the existing deterministic admission combinator.

Forbidden:

- `Any`, open `object`, raw mapping, or raw list in committed fields;
- generic `deep_freeze`, `copy`, `deepcopy`, JSON round-trip copying, mutable
  inheritance, or seal flags;
- `isinstance` admission or coercive `int(...)`, `str(...)`, truthiness, and
  defaulting at the authority boundary;
- caller-selected constructors, registries, encoders, roots, callbacks, or
  ordering functions;
- a second parser or schema interpreter;
- external effects, clocks, randomness, environment, network, or filesystem
  access in the fee core.

### P4B5A-D07: lineage derivation

Protocol credits must be generated at the exact swap replay site from:

```text
exact admitted intent.asset_in
exact recomputed quote.protocol_fee_paid
authenticated settlement context.protocol_fee_recipient_pubkey
```

Do not reconstruct credits later from `Settlement.balance_deltas`, total fee
fields, events, caller-supplied asset labels, or a second quote computation.

The exact strong-settlement candidate retains the resulting credit tuple.
Candidate construction revalidates the tuple and proves that every credit
matches a protocol-recipient balance atom from the same replay.

### P4B5A-D08: versioning and migration

Introduce distinct V2 schema IDs and record tags for:

```text
protocol fee credit
fee distribution policy
fee dust entry
fee accumulator
asset fee distribution
fee effects or receipt projection
```

Do not silently change a V1 accepted language.

Migration from the scalar V1 accumulator is defined only for:

```text
CommittedFeeAccumulatorStateV1(dust=0)
```

Nonzero scalar dust has no recoverable asset or custody owner and must reject
with a stable migration code.

All canonical encoders, roots, receipts, patches, and bundles that include the
new values must bind the V2 schema or algorithm version.

### P4B5A-D09: parity boundary

Python and Rust must share golden vectors for:

- each V2 value encoding;
- policy and accumulator edge values;
- mixed-asset credits;
- aliases;
- per-asset dust;
- accept and reject results;
- candidate/patch/effect/receipt roots.

No cross-language row may be marked passed without an exact-byte replay
artifact bound to both source heads.

### P4B5A-D10: mount isolation

P4B5A must leave these mounted paths byte-identical:

```text
src/core/dex.py
src/integration/dex_engine.py
src/core/route_settlement.py
src/state/legacy_state_snapshots.py
```

Legacy scalar fee logic remains an unchanged differential and migration
oracle. It is not authoritative evidence for the V2 semantics.

## Required failing evidence before repair

Add minimized tests that first demonstrate:

```text
100 units of asset A + 1 unit of asset C
  -> old scalar authority equals 101

fee_paid=100 and protocol_fee_paid=10
  -> old scalar distribution is funded from 100
  -> exact protocol custody is only 10
```

The preserved regression tests must assert the new positive laws rather than
calling the old buggy helper as their oracle.

## Required semantic evidence

At minimum:

1. Mixed assets never share one total or dust cell.
2. Protocol shares at `0`, `1`, `9_999`, and `10_000` bps.
3. LP-retained fee amount never appears in protocol distribution.
4. Partition invariance:

   ```text
   distribute(A ∪ B) = canonical_merge(distribute(A), distribute(B))
   ```

   for disjoint custody keys.
5. Exact per-key conservation.
6. Balance conservation before and after state-applied distribution.
7. Source/destination alias and all-destination alias cases.
8. Reject is a no-op with no candidate, patch, distribution, or accumulator.
9. Nonzero V1 dust migration rejects.
10. Structural mutation tests kill unit erasure, custody erasure, use of
    `fee_paid`, scalar summation, missing schema registration, and shell
    execution of an already applied distribution.

## Checkpoint order

Commit separately:

```text
P4B5A-A  frozen packet and minimized witnesses
P4B5A-B  exact V2 values, transition, admission, and codecs
P4B5A-C  exact replay lineage and step-candidate integration
P4B5A-D  effects, receipts, roots, migration, Rust parity, and evidence
```

Stop at the first failed invariant. Do not weaken the contract, tests,
structural checker, or prior evidence to obtain a pass.
