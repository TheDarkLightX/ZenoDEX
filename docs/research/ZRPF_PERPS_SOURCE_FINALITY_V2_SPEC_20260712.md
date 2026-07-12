# ZRPF Perps Collateral Source Finality V2 Specification

Date: 2026-07-12

Status: V1 aggregate scope guard implemented; V2 transfer object and proof path
pending

## Disaster state

The historical perps recursive leaf emits self-balancing rows for insurance
seed, collateral deposit, and collateral withdrawal. Those rows describe local
perps accounting. They do not authenticate the wallet, zUSD, custody, or bridge
state that supplied or received the collateral.

Accepting those rows into aggregate conservation permits this invalid state:

```text
perps transition is valid
and a local debit equals a local credit
and no external source or destination receipt exists
```

## Implemented V1 closure

After exact child asset-root verification and before aggregate conservation,
the V1 composer now applies:

```text
perps_v1 = lane_kind == "perps_np"
        or proof_profile == "recursive_perps_np_leaf_v1"

perps_v1 and asset_delta_rows.nonempty
    -> reject Unsupported
```

Both identifiers are checked independently so a one-field relabel cannot admit
the rows. A perps RunEpoch child with no external asset rows remains eligible
for its existing local transition claim.

## Required V2 transfer object

```text
RecursiveValueTransferV2 {
    version,
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
```

The transfer ID is a fixed-width domain-separated hash of every field. Source
and destination guests must derive the identical object from their own checked
transitions. Hosts may supply bounded bytes; they cannot select the resulting
identity.

## One-sided accounting

```text
insurance seed or deposit:
    external source debit + outbox
    perps credit + inbox

withdrawal:
    perps debit + outbox
    external destination credit + inbox
```

The aggregate requires exact outbox/inbox transfer equality and then checks:

```text
sum(debit) + sum(authorized_mint)
    = sum(credit) + sum(authorized_burn)
```

Asset totals alone are insufficient. Transfer equality also binds action,
route, scope, source transition, receipt claim, amount, and deadline.

## Required negative evidence

- value-moving perps action without a counterparty receipt;
- a V2 self-balancing perps row;
- amount, asset, action index, action hash, direction, lane, or scope mutation;
- source transition or receipt-claim substitution;
- unmatched outbox/inbox transfer;
- transfer reuse for two actions;
- duplicate transfer within or across subtrees;
- unrelated equal-amount transfer used to balance totals;
- image, profile, count, byte, or arithmetic-bound substitution.

## Explicit non-claims

The V1 guard supplies no V2 transfer codec, source guest, perps guest, image ID,
receipt, source finality, transfer finality, durable admission, complete perps
fee/funding/insurance/liquidation coverage, release authority, privacy,
throughput, or production authority.

The next executable step is a bounded `RecursiveValueTransferV2` codec plus
pure derivation references for seed, deposit, and withdrawal. Promotion then
requires separate source and perps guests and fresh cross-receipt evidence.
