# ZRPF Ordinary Spot Settlement State V2 CBC Specification

Date: 2026-07-12

Status: proof-neutral sparse-Merkle state binding implemented and host-tested;
guest, receipt, durable admission, and settlement authority pending

## Disaster state

The compatibility `SpotSettlementProjectionV1` uses the authenticated raw Spot
lane roots as its batch and plan state roots. Those values identify the Spot
application transition. They do not prove that updating the corresponding
cell in a larger ZenoLedger state tree produces the ledger pre-state and
post-state roots.

An authority-bearing settlement path must therefore use V2:

```text
exact V5 value proposal
  -> canonical Spot action and cell write
  -> exact sparse-Merkle witness for that write
  -> derived ledger pre-root and post-root
  -> action batch and SettlementEffectPlanV2 using those ledger roots
```

## Construction boundary

`propose_spot_settlement_state_projection_v2` is a witness-builder helper. It
takes proposed ledger roots and derives the exact action ID, cell key, raw
pre/post value hashes, batch, and plan needed to construct a witness. It
validates no Merkle path and grants no authority.

`derive_spot_settlement_state_projection_v2` accepts one fixed-depth
`SparseMerkleCellTransitionWitnessV1`. It rederives the action and plan from the
witness roots, then requires the witness to match the complete sole
`LedgerCellWriteV2`:

```text
economic_action_id
cell_key
pre_value_hash
post_value_hash
```

The witness independently recomputes both tree roots from the same 256-sibling
path. The resulting private `SpotSettlementStateProjectionV2` contains the
recomputed plan and one `ValidatedSparseMerkleBatchTransitionV1` entry.

## Root roles

```text
raw_subtree_pre_state_root
raw_subtree_post_state_root
    exact Spot lane values stored in the ledger cell

sparse witness pre-root
sparse witness post-root
    complete ZenoLedger state-tree roots used by the action batch,
    settlement plan, and future settlement certificate
```

V2 prevents a caller from substituting a valid path for a different key,
different raw value, or different economic action. It also prevents using raw
lane roots as though they were full ledger roots.

## Initial bound

The ordinary Spot V2 profile currently emits exactly one aggregate economic
action and exactly one cell write. The underlying batch witness protocol
supports 1 through 64 canonically ordered writes, but this profile uses one.
Future multi-lane profiles must preserve unique keys, unique write identities,
strict key order, and continuous intermediate roots.

## Evidence

- exact accepted state projection binds sparse roots to batch and plan roots;
- raw Spot roots remain the exact cell pre/post values;
- valid sparse witnesses for a different cell key reject;
- valid sparse witnesses for a different raw value reject;
- economic-action substitution rejects;
- the underlying single-cell suite mutates every key bit, sibling, and value
  bit;
- the underlying batch suite checks ordering, duplicate identities, root-chain
  gaps, maximum size, and exact codec bounds;
- private construction of the V2 state projection is compile-fail checked.

## Promotion rule

The future ordinary Spot settlement guest must use the V2 state-bound
projection. A receipt over the V1 compatibility projection is insufficient for
ledger settlement authority.

## Explicit non-claims

V2 supplies no receipt verification, guest image, durable state storage,
transaction isolation, rollback protection, data availability, source
finality, authorization-grant existence, release authority, settlement
authority, privacy, throughput, or production authority.
