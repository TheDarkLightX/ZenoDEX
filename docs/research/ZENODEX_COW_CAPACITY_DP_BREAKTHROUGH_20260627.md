# ZenoDEX CoW Capacity-DP Breakthrough - 2026-06-27

## Executive Result

The CoW selector now replaces the greedy grouped-capacity fallback with exact DP for small coupled batches, preserving brute-force volume/surplus/tie semantics under repeated senders.

The selector proposes CoW netting pairs; settlement materialization still performs fail-closed aggregate balance checks before mutating balances.

Cases: `5`. Exact mismatches: `0`. Core selector mismatches: `0`. Greedy-lift cases: `5`. Max candidates: `9`.

Adversarial cases: `20`. Exact mismatches: `0`. Core selector mismatches: `0`. Greedy-lift cases: `15`. Max candidates: `14`.

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

## Adversarial Replay

```bash
python3 tools/check_cow_capacity_dp_adversarial.py
```

Result:

```json
{
  "assignment_safe_case_count": 0,
  "case_count": 20,
  "core_mismatch_count": 0,
  "exact_mismatch_count": 0,
  "greedy_lift_case_count": 15,
  "max_candidate_count": 14,
  "max_surplus_lift": 192,
  "max_volume_lift": 261,
  "ok": true,
  "seed": 2026062805
}
```

Pattern coverage:

| pattern | cases | exact mismatches | core mismatches | greedy lifts |
| --- | ---: | ---: | ---: | ---: |
| `deterministic_fuzz` | `4` | `0` | `0` | `4` |
| `dual_coupled` | `4` | `0` | `0` | `4` |
| `shared_left` | `4` | `0` | `0` | `3` |
| `shared_right` | `4` | `0` | `0` | `0` |
| `sparse_cliff` | `4` | `0` | `0` | `4` |

Every adversarial case is intentionally outside the uncoupled Hungarian surface: `assignment_balance_safe` is false for all cases. The replay therefore exercises the bounded capacity-DP path rather than the assignment path.

## Non-Claims

- This is a bounded exact DP for small grouped-capacity CoW batches, not a polynomial algorithm for arbitrary grouped-capacity matching.
- Uncoupled large batches still use Hungarian assignment; large coupled batches still retain the greedy/fail-closed fallback.
- The report measures selector quality against brute force on a deterministic bounded corpus, not production activation.
- No settlement authority is derived from this research report.

## Replay

```bash
python3 tools/zenodex_cow_capacity_dp_breakthrough_20260627.py
python3 tools/check_cow_capacity_dp_adversarial.py
```
