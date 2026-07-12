# ZRPF Perps Collateral Source Finality V2 Specification

Status: V1 aggregation scope guard implemented; V2 transfer profile designed,
no V2 guest or receipt evidence
Date: 2026-07-11

## Purpose

The V1 perps recursive leaf derives a locally checked perps transition. Its
deposit, withdrawal, and insurance-seed asset rows debit and credit the same
amount inside one child. Those rows are useful local audit metadata. They do
not identify an authenticated external source or destination.

A recursive aggregate that accepts those self-balancing rows can report global
asset conservation after observing only the perps child. The external wallet,
zUSD, custody, or bridge counterparty may be absent.

This specification closes that V1 interpretation and defines the minimum V2
profile required for global cross-lane collateral source finality.

## Actors and disaster state

- Alice deposits collateral from an authenticated source lane.
- Bob withdraws collateral to an authenticated destination lane.
- Mallory publishes a valid perps transition while omitting the external
  counterparty proof.
- A sequencer pairs an unrelated equal-amount transfer to make aggregate asset
  totals balance.
- A governance operator accidentally admits V1 local rows as global value
  evidence.

The disaster state is:

```text
perps transition valid
&& V1 self-balancing row accepted by aggregate conservation
&& external source or destination child absent
```

## Implemented V1 scope guard

The V1 aggregate applies this rule after exact child asset-row root binding and
before global asset conservation:

```text
identifies_perps_v1 =
    child.lane_kind == "perps_np"
    || child.proof_profile == "recursive_perps_np_leaf_v1"

identifies_perps_v1 && child.asset_delta_rows.nonempty
    -> reject Unsupported
```

Both identity projections are checked so changing only the lane kind or only
the profile cannot bypass the guard. An authenticated V1 perps RunEpoch child
with no external asset rows remains admissible.

The V1 leaf may still emit its historical local rows. Those rows cannot enter
the V1 aggregate value equation. Existing V1 leaf receipts therefore retain
only local transition and row-root meaning.

## V2 transfer object

V2 requires a versioned value-transfer object shared by the source and
destination guests:

```text
RecursiveValueTransferV2 {
    transfer_version,
    epoch_id,
    action_index,
    action_hash,
    direction,
    source_lane_id,
    destination_lane_id,
    asset_id,
    amount_atoms,
    sender_scope_hash,
    recipient_scope_hash,
    source_state_transition_hash,
    source_receipt_claim_hash,
    deadline_epoch,
}

transfer_id = H(
    "zenodex.zrpf.recursive_value_transfer.v2",
    canonical_fields
)
```

Required shape rules:

- `action_index` selects exactly one value-moving action;
- `action_hash` binds that action's canonical bytes;
- source and destination lanes are nonempty, bounded, and different;
- asset identity and atom unit are canonical and profile-pinned;
- amount is positive and uses checked integer conversion;
- scope and transition roots are nonzero;
- the deadline is not earlier than the transfer epoch;
- transfer IDs are sorted unique within each child and globally exact-once.

The host may propose this object. Each guest derives and checks every field
from its authenticated transition and governed scope before committing it.

## One-sided value rows

V2 maps perps actions to one-sided rows:

```text
InitMarket insurance seed:
    perps credit = amount
    perps inbox  = transfer

DepositCollateral:
    perps credit = amount
    perps inbox  = transfer

WithdrawCollateral:
    perps debit  = amount
    perps outbox = transfer
```

The authenticated external counterparty derives the opposite side:

```text
source of seed or deposit:
    source debit = amount
    source outbox = identical transfer

destination of withdrawal:
    destination credit = amount
    destination inbox = identical transfer
```

No single child self-balances an external transfer.

## Required composition laws

For every V2 child and asset, the guest or recursive composer checks:

```text
external_debit_atoms
    == sum(outbox.amount_atoms for asset)

external_credit_atoms
    == sum(inbox.amount_atoms for asset)
```

The aggregate then checks both laws:

```text
canonical_outbox_transfers == canonical_inbox_transfers

sum(debit_atoms) + sum(authorized_mint_atoms)
    == sum(credit_atoms) + sum(authorized_burn_atoms)
```

Asset-only equality is insufficient. Exact transfer equality binds action,
route, scopes, source transition, receipt claim, amount, and deadline. An
unrelated equal-amount transfer cannot satisfy the same transfer ID.

## Binding requirements

The perps V2 statement and authenticated journal must bind:

```text
perps V2 image ID and proof profile
chain and exact epoch
public policy, feature, dependency, and toolchain roots
operation hash and pre/post perps state roots
collateral transfer list root
inbox and outbox roots
one-sided asset-delta root
source-finality profile ID
maximum transfer count and serialized byte bounds
```

The aggregate must derive allowed verifier IDs from governed image/profile
pairs. A child journal cannot select its own expected verifier identity.

## Required negative evidence

Before V2 promotion, tests must reject:

- seed, deposit, or withdrawal with no counterparty child;
- self-balancing perps rows under the V2 profile;
- row amount different from transfer amount;
- asset or atom-unit substitution;
- action index or action hash substitution;
- source or destination lane substitution;
- scope, source transition, or receipt-claim substitution;
- outbox/inbox transfer mismatch;
- duplicate transfer ID within one child or across children;
- one transfer reused for two perps actions;
- withdrawal represented as an inbox or deposit represented as an outbox;
- valid totals balanced by an unrelated transfer;
- profile or image relabeling;
- count, byte, and checked-sum overflow.

## Explicit non-claims

The implemented V1 guard does not establish:

- a V2 transfer codec, guest, image ID, receipt, or public replay;
- authenticated external source or destination state;
- zUSD, Spot, custody, bridge, or chain-balance counterparty coverage;
- cross-lane transfer finality or durable exact-once admission;
- complete perps collateral, fee, funding, insurance, or liquidation coverage;
- a canonical parallel schedule or conflict-freedom proof;
- ledger, settlement, release, privacy, throughput, or production authority.

`RS-CBC-010` may advance only to `implemented_partial` for the V1 fail-closed
scope guard. Global perps source finality remains pending on the V2 proof path.

## Next executable step

Define the bounded `RecursiveValueTransferV2` codec and a pure derivation
reference for all three value-moving perps actions. Then add separate source
and perps V2 guests that derive identical transfer objects and one-sided rows.
Only after fresh receipts verify may a V2 aggregate admit those rows into its
global value equation.
