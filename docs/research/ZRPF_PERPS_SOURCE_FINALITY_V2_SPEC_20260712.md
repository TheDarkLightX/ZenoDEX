# ZRPF Perps Collateral Source Finality V2 Specification

Date: 2026-07-12

Status: V1 aggregate scope guard, proof-neutral V2 transfer ABI, and pure perps
collateral row derivation reference implemented; authenticated source/perps proof
path pending

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

## Implemented proof-neutral V2 transfer object

```text
ValueTransferV2 {
    version,
    application_id,
    chain_or_domain_id,
    epoch_id,
    action_index,
    action_hash,
    kind,
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
and destination guests must eventually derive the identical object from their
own checked transitions.

The implemented `ValueTransferV2` and `ValueTransferSetV2` layer currently
establishes:

- exact bounded Postcard decoding;
- stable numeric transfer-kind tags;
- nonzero amount, distinct lanes, bounded action index, and valid deadline;
- one application, domain, and epoch per set;
- canonical ordering by transfer ID;
- unique transfer IDs and unique `(kind, action_index, action_hash)` bindings;
- canonical transfer, source-claim, and source-transition roots.

This layer is proof-neutral. A host can propose every input field. Receipt
authentication and source-transition derivation remain obligations of the
future source and destination guests and their sealed verifier.

## Implemented pure perps derivation reference

`zk/zrpf_protocol/perps_source_finality` now provides an independent `no_std`
reference adapter for insurance seed, collateral deposit, and collateral
withdrawal actions. It:

- decodes one exact bounded canonical `ValueTransferSetV2`;
- derives the action hash, asset identity, lane scopes, amount, direction,
  counterparty route, and deadline expected from each value-moving perps action;
- derives deposit and withdrawal actor scopes from their action pubkeys, while
  requiring an explicit proposed funder scope for an insurance seed because the
  historical `InitMarket` action does not identify that funder;
- requires exactly one transfer for every value-moving action and rejects extra
  transfers;
- derives one source debit row and one destination credit row for each transfer;
- rejects missing, duplicate, reordered-substitution, wrong-counterparty,
  amount, asset, scope, deadline, row-set, and conservation mutations;
- caps row decoding before authority-bearing typed output is returned;
- uses an exact canonical Postcard proposal codec.

The source-transition, receipt-claim, and insurance-seed funder commitments
remain explicitly host-proposed. This reference derives and checks structure
only. It does not authenticate those commitments and does not establish source
or external-chain finality.

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

The V1 guard and V2 protocol ABI supply no source guest, perps guest, image ID,
receipt, authenticated source derivation, source finality, transfer finality,
durable admission, complete perps fee/funding/insurance/liquidation coverage,
release authority, privacy, throughput, or production authority.

The next executable step is separate source and perps guests that independently
derive the identical `ValueTransferV2`, authenticate governed receipts and
image IDs, and produce fresh cross-receipt equality and mutation evidence.
