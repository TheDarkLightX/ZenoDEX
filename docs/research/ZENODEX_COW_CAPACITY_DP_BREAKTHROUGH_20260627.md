# ZenoDEX CoW Capacity-DP Breakthrough - 2026-06-27

## Executive Result

The CoW selector now replaces the greedy grouped-capacity fallback with exact DP for small coupled batches, preserving brute-force volume/surplus/tie semantics under repeated senders.

The selector proposes CoW netting pairs; settlement materialization still performs fail-closed aggregate balance checks before mutating balances.

Cases: `5`. Exact mismatches: `0`. Core selector mismatches: `0`. Greedy-lift cases: `5`. Max candidates: `9`.

## Cases

| case | candidates | DP=brute | core=DP | beats greedy | volume lift | surplus lift |
| --- | ---: | --- | --- | --- | ---: | ---: |
| `coupled_sender_volume_witness` | `9` | `True` | `True` | `True` | `210` | `130` |
| `surplus_witness` | `9` | `True` | `True` | `True` | `0` | `40` |
| `parity_seed_1` | `9` | `True` | `True` | `True` | `233` | `109` |
| `parity_seed_2` | `9` | `True` | `True` | `True` | `17` | `-2` |
| `parity_seed_3` | `9` | `True` | `True` | `True` | `57` | `120` |

## Algorithm

State:

```text
(side_01_prefix_index, used_side_10_mask, debits_by_asset0_sender, debits_by_asset1_sender)
```

The DP explores skip-or-pair decisions for each `asset0 -> asset1` candidate. A pair is admitted only when the reciprocal minimum-output inequalities hold and both sender debit vectors remain within the pre-netting balance snapshot. The selected suffix is compared with the same `(volume, surplus, pair-id tie)` key used by the brute-force oracle.

## Non-Claims

- This is a bounded exact DP for small grouped-capacity CoW batches, not a polynomial algorithm for arbitrary grouped-capacity matching.
- Uncoupled large batches still use Hungarian assignment; large coupled batches still retain the greedy/fail-closed fallback.
- The report measures selector quality against brute force on a deterministic bounded corpus, not production activation.

## Replay

```bash
python3 tools/zenodex_cow_capacity_dp_breakthrough_20260627.py
```
