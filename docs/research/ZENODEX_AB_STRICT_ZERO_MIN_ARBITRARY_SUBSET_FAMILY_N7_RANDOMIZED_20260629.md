# ZenoDEX AB Strict Zero-Min Arbitrary Subset-Family n=7 Randomized Stress - 2026-06-29

## Executive Result

A bounded n=7 randomized and positive-output-boundary falsification corpus found no counterexample to the strict zero-min arbitrary subset-family host certificate within the declared strict-executable scope.

Research-only falsification evidence; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Deterministic seed: `2026062907`
- Positive n=7 cases checked: `4`
- Valid positive cases: `4`
- Candidate budget: `12`
- Candidate rejections during positive search: `0`
- Reachable masks checked: `512`
- Full records checked: `54800`
- Singleton table obligations: `54800`
- Dominance checks: `161280`
- Scope probes: `4`
- Scope probe accepts: `0`
- Strict-executability rejection probes: `3`
- Strict-executability rejection accepts: `0`
- Deterministic replay ok: `True`

## Coverage

- `n` histogram: `{'7': 4}`
- Fee histogram: `{'1': 1, '100': 2, '9000': 1}`
- Regime/pattern histogram: `{'high_fee_deep_out/rand_stair': 1, 'near_domain_in/rand_burst': 1, 'near_zero_positive/rand_tie': 1, 'thin_positive_boundary/high_fee9000': 1}`
- Max records per mask: `5040`
- Max suffixes per mask: `5040`

## First Case

```json
{
  "bit_count": 7,
  "case_id": "n7_randomized_boundary_000_thin_fee9000_rout1100",
  "dominance_check_count": 40320,
  "fee_bps": 9000,
  "first_failure": null,
  "first_obligation": {
    "full_record_count": 1,
    "full_records_digest": "8d8059f1ce67e39ee0ac1f3824e56bc9e9b480af2ed50cbe5da5417fb96f01e1",
    "mask_id": 0,
    "singleton_family": [
      0
    ],
    "suffix": {
      "order_ids": [
        "0x00000000000000000000000000000000000000000000000000000000006cf5c0",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c1",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c2",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c3",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c4",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c5",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c6"
      ],
      "order_short": [
        "f5c0",
        "f5c1",
        "f5c2",
        "f5c3",
        "f5c4",
        "f5c5",
        "f5c6"
      ]
    },
    "winner": {
      "order_short": [],
      "processed_reserve_in": 10000,
      "reserve_out": 1100
    }
  },
  "full_mask_selected": {
    "order_short": [
      "f5c0",
      "f5c1",
      "f5c2",
      "f5c3",
      "f5c4",
      "f5c5",
      "f5c6"
    ],
    "processed_reserve_in": 10721,
    "reserve_out": 1093
  },
  "full_runtime_completion_count": 40320,
  "mask_count": 128,
  "max_records_per_mask": 5040,
  "max_suffix_per_mask": 5040,
  "obligation_digest": "8c0c7309a6b4a2a6ba032df85181cdbad447659a85dce7772be20085f392eaf2",
  "ok": true,
  "packet_hash": "1d8a445484be0df7782f5611667004bdbf9fc56b540685a84a5efad714de5ae6",
  "pattern": "thin_positive_boundary/high_fee9000",
  "reasons": [],
  "record_count": 13700,
  "selected_suffix_executable_count": 13700,
  "singleton_table_obligation_count": 13700
}
```

## Scope Probes

| case | accepted | reason |
| --- | ---: | --- |
| `n7_randomized_boundary_000_thin_fee9000_rout1100_nonzero_min_probe` | `False` | `nonzero_min_amount_out_out_of_scope` |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1_nonzero_min_probe` | `False` | `nonzero_min_amount_out_out_of_scope` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100_nonzero_min_probe` | `False` | `nonzero_min_amount_out_out_of_scope` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100_nonzero_min_probe` | `False` | `nonzero_min_amount_out_out_of_scope` |

## Strict-Executability Rejection Probes

| case | accepted | first reason |
| --- | ---: | --- |
| `n7_randomized_boundary_000_thin_fee9000_rout7` | `False` | `compressed_full_mask_not_executable` |
| `n7_randomized_boundary_000_thin_fee9000_rout20` | `False` | `compressed_full_mask_not_executable` |
| `n7_randomized_boundary_000_thin_fee9000_rout100` | `False` | `compressed_full_mask_not_executable` |

## Case Summary

| case | ok | n | pattern | singleton tables | dominance checks |
| --- | --- | ---: | --- | ---: | ---: |
| `n7_randomized_boundary_000_thin_fee9000_rout1100` | `True` | `7` | `thin_positive_boundary/high_fee9000` | `13700` | `40320` |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1` | `True` | `7` | `near_zero_positive/rand_tie` | `13700` | `40320` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100` | `True` | `7` | `high_fee_deep_out/rand_stair` | `13700` | `40320` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100` | `True` | `7` | `near_domain_in/rand_burst` | `13700` | `40320` |

## Non-Claims

- This n=7 randomized corpus is bounded and finite, not exhaustive over all n=7 states.
- This checker does not prove Lean-to-Python refinement.
- This checker does not cover nonzero min_amount_out certificates; those are rejected as out of scope.
- Strict-executability rejection probes are scope controls, not counterexamples to the in-scope claim.
- This checker does not add settlement, state-root, production, or governance authority.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_arbitrary_subset_family_n7_randomized.py
```
