# ZenoDEX AB Strict Zero-Min Arbitrary Subset-Family Extended Stress - 2026-06-29

## Executive Result

A broader deterministic falsification corpus found no counterexample to the strict zero-min arbitrary subset-family host certificate across reserve extremes, high fee schedules, tie-heavy inputs, and bursty inputs.

Research-only falsification evidence; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Deterministic seed: `2026062902`
- Cases checked: `90`
- Valid cases: `90`
- Reachable masks checked: `2232`
- Full records checked: `42642`
- Singleton table obligations: `42642`
- Dominance checks: `106380`
- Scope probes: `5`
- Scope probe accepts: `0`
- Deterministic replay ok: `True`

## Coverage

- `n` histogram: `{'2': 18, '3': 18, '4': 18, '5': 18, '6': 18}`
- Fee histogram: `{'0': 9, '1': 9, '100': 9, '2500': 9, '30': 9, '5': 9, '500': 9, '5000': 9, '75': 9, '9000': 9}`
- Regime/pattern histogram: `{'balanced_mid/alternating_large': 1, 'balanced_mid/ascending_stair': 1, 'balanced_mid/burst_prefix': 1, 'balanced_mid/burst_suffix': 1, 'balanced_mid/descending_stair': 1, 'balanced_mid/high_fee_safe': 1, 'balanced_mid/near_tie_stagger': 1, 'balanced_mid/powers': 1, 'balanced_mid/prime_steps': 1, 'balanced_mid/tie_heavy_flat': 1, 'deep_balanced/alternating_large': 1, 'deep_balanced/ascending_stair': 1, 'deep_balanced/burst_prefix': 1, 'deep_balanced/burst_suffix': 1, 'deep_balanced/descending_stair': 1, 'deep_balanced/high_fee_safe': 1, 'deep_balanced/near_tie_stagger': 1, 'deep_balanced/powers': 1, 'deep_balanced/prime_steps': 1, 'deep_balanced/tie_heavy_flat': 1, 'huge_out/alternating_large': 1, 'huge_out/ascending_stair': 1, 'huge_out/burst_prefix': 1, 'huge_out/burst_suffix': 1, 'huge_out/descending_stair': 1, 'huge_out/high_fee_safe': 1, 'huge_out/near_tie_stagger': 1, 'huge_out/powers': 1, 'huge_out/prime_steps': 1, 'huge_out/tie_heavy_flat': 1, 'low_in_high_out/alternating_large': 1, 'low_in_high_out/ascending_stair': 1, 'low_in_high_out/burst_prefix': 1, 'low_in_high_out/burst_suffix': 1, 'low_in_high_out/descending_stair': 1, 'low_in_high_out/high_fee_safe': 1, 'low_in_high_out/near_tie_stagger': 1, 'low_in_high_out/powers': 1, 'low_in_high_out/prime_steps': 1, 'low_in_high_out/tie_heavy_flat': 1, 'near_domain_reserve_in/alternating_large': 1, 'near_domain_reserve_in/ascending_stair': 1, 'near_domain_reserve_in/burst_prefix': 1, 'near_domain_reserve_in/burst_suffix': 1, 'near_domain_reserve_in/descending_stair': 1, 'near_domain_reserve_in/high_fee_safe': 1, 'near_domain_reserve_in/near_tie_stagger': 1, 'near_domain_reserve_in/powers': 1, 'near_domain_reserve_in/prime_steps': 1, 'near_domain_reserve_in/tie_heavy_flat': 1, 'skewed_in/alternating_large': 1, 'skewed_in/ascending_stair': 1, 'skewed_in/burst_prefix': 1, 'skewed_in/burst_suffix': 1, 'skewed_in/descending_stair': 1, 'skewed_in/high_fee_safe': 1, 'skewed_in/near_tie_stagger': 1, 'skewed_in/powers': 1, 'skewed_in/prime_steps': 1, 'skewed_in/tie_heavy_flat': 1, 'small_balanced/alternating_large': 1, 'small_balanced/ascending_stair': 1, 'small_balanced/burst_prefix': 1, 'small_balanced/burst_suffix': 1, 'small_balanced/descending_stair': 1, 'small_balanced/high_fee_safe': 1, 'small_balanced/near_tie_stagger': 1, 'small_balanced/powers': 1, 'small_balanced/prime_steps': 1, 'small_balanced/tie_heavy_flat': 1, 'thin_margin_high_out/alternating_large': 1, 'thin_margin_high_out/ascending_stair': 1, 'thin_margin_high_out/burst_prefix': 1, 'thin_margin_high_out/burst_suffix': 1, 'thin_margin_high_out/descending_stair': 1, 'thin_margin_high_out/high_fee_safe': 1, 'thin_margin_high_out/near_tie_stagger': 1, 'thin_margin_high_out/powers': 1, 'thin_margin_high_out/prime_steps': 1, 'thin_margin_high_out/tie_heavy_flat': 1, 'tight_out_positive/alternating_large': 1, 'tight_out_positive/ascending_stair': 1, 'tight_out_positive/burst_prefix': 1, 'tight_out_positive/burst_suffix': 1, 'tight_out_positive/descending_stair': 1, 'tight_out_positive/high_fee_safe': 1, 'tight_out_positive/near_tie_stagger': 1, 'tight_out_positive/powers': 1, 'tight_out_positive/prime_steps': 1, 'tight_out_positive/tie_heavy_flat': 1}`
- Max records per mask: `720`
- Max suffixes per mask: `720`

## First Case

```json
{
  "bit_count": 2,
  "case_id": "extended_000_balanced_mid_tie_heavy_flat_n2_fee0",
  "dominance_check_count": 6,
  "fee_bps": 0,
  "first_failure": null,
  "first_obligation": {
    "full_record_count": 1,
    "full_records_digest": "29dc346a591256ec963a9842df7fa288aa8077dc60efb1f82b1e47a8c0cbe610",
    "mask_id": 0,
    "singleton_family": [
      0
    ],
    "suffix": {
      "order_ids": [
        "0x00000000000000000000000000000000000000000000000000000000000dbba0",
        "0x00000000000000000000000000000000000000000000000000000000000dbba1"
      ],
      "order_short": [
        "bba0",
        "bba1"
      ]
    },
    "winner": {
      "order_short": [],
      "processed_reserve_in": 900,
      "reserve_out": 179200
    }
  },
  "full_mask_selected": {
    "order_short": [
      "bba0",
      "bba1"
    ],
    "processed_reserve_in": 964,
    "reserve_out": 167304
  },
  "full_runtime_completion_count": 6,
  "mask_count": 4,
  "max_records_per_mask": 2,
  "max_suffix_per_mask": 2,
  "obligation_digest": "52d72006d877d71df5a99b2caa3e5202141b33f773d82105924a1e0f49c8a15a",
  "ok": true,
  "packet_hash": "e4bab99b828392b5e6ec816af367122e3038c0862ec8fca6d59748793ac87d2b",
  "pattern": "balanced_mid/tie_heavy_flat",
  "reasons": [],
  "record_count": 5,
  "selected_suffix_executable_count": 5,
  "singleton_table_obligation_count": 5
}
```

## Scope Probes

| case | accepted | reason |
| --- | ---: | --- |
| `extended_000_balanced_mid_tie_heavy_flat_n2_fee0_nonzero_min_probe` | `False` | `nonzero_min_amount_out_out_of_scope` |
| `extended_001_low_in_high_out_near_tie_stagger_n3_fee1_nonzero_min_probe` | `False` | `nonzero_min_amount_out_out_of_scope` |
| `extended_002_near_domain_reserve_in_ascending_stair_n4_fee5_nonzero_min_probe` | `False` | `nonzero_min_amount_out_out_of_scope` |
| `extended_003_tight_out_positive_descending_stair_n5_fee30_nonzero_min_probe` | `False` | `nonzero_min_amount_out_out_of_scope` |
| `extended_004_huge_out_alternating_large_n6_fee75_nonzero_min_probe` | `False` | `nonzero_min_amount_out_out_of_scope` |

## Case Summary

| case | ok | n | pattern | singleton tables | dominance checks |
| --- | --- | ---: | --- | ---: | ---: |
| `extended_000_balanced_mid_tie_heavy_flat_n2_fee0` | `True` | `2` | `balanced_mid/tie_heavy_flat` | `5` | `6` |
| `extended_001_low_in_high_out_near_tie_stagger_n3_fee1` | `True` | `3` | `low_in_high_out/near_tie_stagger` | `16` | `24` |
| `extended_002_near_domain_reserve_in_ascending_stair_n4_fee5` | `True` | `4` | `near_domain_reserve_in/ascending_stair` | `65` | `120` |
| `extended_003_tight_out_positive_descending_stair_n5_fee30` | `True` | `5` | `tight_out_positive/descending_stair` | `326` | `720` |
| `extended_004_huge_out_alternating_large_n6_fee75` | `True` | `6` | `huge_out/alternating_large` | `1957` | `5040` |
| `extended_005_skewed_in_burst_prefix_n2_fee100` | `True` | `2` | `skewed_in/burst_prefix` | `5` | `6` |
| `extended_006_small_balanced_burst_suffix_n3_fee500` | `True` | `3` | `small_balanced/burst_suffix` | `16` | `24` |
| `extended_007_deep_balanced_powers_n4_fee2500` | `True` | `4` | `deep_balanced/powers` | `65` | `120` |
| `extended_008_thin_margin_high_out_prime_steps_n5_fee5000` | `True` | `5` | `thin_margin_high_out/prime_steps` | `326` | `720` |
| `extended_009_balanced_mid_high_fee_safe_n6_fee9000` | `True` | `6` | `balanced_mid/high_fee_safe` | `1957` | `5040` |
| `extended_010_low_in_high_out_tie_heavy_flat_n2_fee0` | `True` | `2` | `low_in_high_out/tie_heavy_flat` | `5` | `6` |
| `extended_011_near_domain_reserve_in_near_tie_stagger_n3_fee1` | `True` | `3` | `near_domain_reserve_in/near_tie_stagger` | `16` | `24` |
| `extended_012_tight_out_positive_ascending_stair_n4_fee5` | `True` | `4` | `tight_out_positive/ascending_stair` | `65` | `120` |
| `extended_013_huge_out_descending_stair_n5_fee30` | `True` | `5` | `huge_out/descending_stair` | `326` | `720` |
| `extended_014_skewed_in_alternating_large_n6_fee75` | `True` | `6` | `skewed_in/alternating_large` | `1957` | `5040` |
| `extended_015_small_balanced_burst_prefix_n2_fee100` | `True` | `2` | `small_balanced/burst_prefix` | `5` | `6` |
| `extended_016_deep_balanced_burst_suffix_n3_fee500` | `True` | `3` | `deep_balanced/burst_suffix` | `16` | `24` |
| `extended_017_thin_margin_high_out_powers_n4_fee2500` | `True` | `4` | `thin_margin_high_out/powers` | `65` | `120` |
| `extended_018_balanced_mid_prime_steps_n5_fee5000` | `True` | `5` | `balanced_mid/prime_steps` | `326` | `720` |
| `extended_019_low_in_high_out_high_fee_safe_n6_fee9000` | `True` | `6` | `low_in_high_out/high_fee_safe` | `1957` | `5040` |
| `extended_020_near_domain_reserve_in_tie_heavy_flat_n2_fee0` | `True` | `2` | `near_domain_reserve_in/tie_heavy_flat` | `5` | `6` |
| `extended_021_tight_out_positive_near_tie_stagger_n3_fee1` | `True` | `3` | `tight_out_positive/near_tie_stagger` | `16` | `24` |
| `extended_022_huge_out_ascending_stair_n4_fee5` | `True` | `4` | `huge_out/ascending_stair` | `65` | `120` |
| `extended_023_skewed_in_descending_stair_n5_fee30` | `True` | `5` | `skewed_in/descending_stair` | `326` | `720` |
| `extended_024_small_balanced_alternating_large_n6_fee75` | `True` | `6` | `small_balanced/alternating_large` | `1957` | `5040` |
| `extended_025_deep_balanced_burst_prefix_n2_fee100` | `True` | `2` | `deep_balanced/burst_prefix` | `5` | `6` |
| `extended_026_thin_margin_high_out_burst_suffix_n3_fee500` | `True` | `3` | `thin_margin_high_out/burst_suffix` | `16` | `24` |
| `extended_027_balanced_mid_powers_n4_fee2500` | `True` | `4` | `balanced_mid/powers` | `65` | `120` |
| `extended_028_low_in_high_out_prime_steps_n5_fee5000` | `True` | `5` | `low_in_high_out/prime_steps` | `326` | `720` |
| `extended_029_near_domain_reserve_in_high_fee_safe_n6_fee9000` | `True` | `6` | `near_domain_reserve_in/high_fee_safe` | `1957` | `5040` |
| `extended_030_tight_out_positive_tie_heavy_flat_n2_fee0` | `True` | `2` | `tight_out_positive/tie_heavy_flat` | `5` | `6` |
| `extended_031_huge_out_near_tie_stagger_n3_fee1` | `True` | `3` | `huge_out/near_tie_stagger` | `16` | `24` |
| `extended_032_skewed_in_ascending_stair_n4_fee5` | `True` | `4` | `skewed_in/ascending_stair` | `65` | `120` |
| `extended_033_small_balanced_descending_stair_n5_fee30` | `True` | `5` | `small_balanced/descending_stair` | `326` | `720` |
| `extended_034_deep_balanced_alternating_large_n6_fee75` | `True` | `6` | `deep_balanced/alternating_large` | `1957` | `5040` |
| `extended_035_thin_margin_high_out_burst_prefix_n2_fee100` | `True` | `2` | `thin_margin_high_out/burst_prefix` | `5` | `6` |
| `extended_036_balanced_mid_burst_suffix_n3_fee500` | `True` | `3` | `balanced_mid/burst_suffix` | `16` | `24` |
| `extended_037_low_in_high_out_powers_n4_fee2500` | `True` | `4` | `low_in_high_out/powers` | `65` | `120` |
| `extended_038_near_domain_reserve_in_prime_steps_n5_fee5000` | `True` | `5` | `near_domain_reserve_in/prime_steps` | `326` | `720` |
| `extended_039_tight_out_positive_high_fee_safe_n6_fee9000` | `True` | `6` | `tight_out_positive/high_fee_safe` | `1957` | `5040` |
| `extended_040_huge_out_tie_heavy_flat_n2_fee0` | `True` | `2` | `huge_out/tie_heavy_flat` | `5` | `6` |
| `extended_041_skewed_in_near_tie_stagger_n3_fee1` | `True` | `3` | `skewed_in/near_tie_stagger` | `16` | `24` |
| `extended_042_small_balanced_ascending_stair_n4_fee5` | `True` | `4` | `small_balanced/ascending_stair` | `65` | `120` |
| `extended_043_deep_balanced_descending_stair_n5_fee30` | `True` | `5` | `deep_balanced/descending_stair` | `326` | `720` |
| `extended_044_thin_margin_high_out_alternating_large_n6_fee75` | `True` | `6` | `thin_margin_high_out/alternating_large` | `1957` | `5040` |
| `extended_045_balanced_mid_burst_prefix_n2_fee100` | `True` | `2` | `balanced_mid/burst_prefix` | `5` | `6` |
| `extended_046_low_in_high_out_burst_suffix_n3_fee500` | `True` | `3` | `low_in_high_out/burst_suffix` | `16` | `24` |
| `extended_047_near_domain_reserve_in_powers_n4_fee2500` | `True` | `4` | `near_domain_reserve_in/powers` | `65` | `120` |
| `extended_048_tight_out_positive_prime_steps_n5_fee5000` | `True` | `5` | `tight_out_positive/prime_steps` | `326` | `720` |
| `extended_049_huge_out_high_fee_safe_n6_fee9000` | `True` | `6` | `huge_out/high_fee_safe` | `1957` | `5040` |
| `extended_050_skewed_in_tie_heavy_flat_n2_fee0` | `True` | `2` | `skewed_in/tie_heavy_flat` | `5` | `6` |
| `extended_051_small_balanced_near_tie_stagger_n3_fee1` | `True` | `3` | `small_balanced/near_tie_stagger` | `16` | `24` |
| `extended_052_deep_balanced_ascending_stair_n4_fee5` | `True` | `4` | `deep_balanced/ascending_stair` | `65` | `120` |
| `extended_053_thin_margin_high_out_descending_stair_n5_fee30` | `True` | `5` | `thin_margin_high_out/descending_stair` | `326` | `720` |
| `extended_054_balanced_mid_alternating_large_n6_fee75` | `True` | `6` | `balanced_mid/alternating_large` | `1957` | `5040` |
| `extended_055_low_in_high_out_burst_prefix_n2_fee100` | `True` | `2` | `low_in_high_out/burst_prefix` | `5` | `6` |
| `extended_056_near_domain_reserve_in_burst_suffix_n3_fee500` | `True` | `3` | `near_domain_reserve_in/burst_suffix` | `16` | `24` |
| `extended_057_tight_out_positive_powers_n4_fee2500` | `True` | `4` | `tight_out_positive/powers` | `65` | `120` |
| `extended_058_huge_out_prime_steps_n5_fee5000` | `True` | `5` | `huge_out/prime_steps` | `326` | `720` |
| `extended_059_skewed_in_high_fee_safe_n6_fee9000` | `True` | `6` | `skewed_in/high_fee_safe` | `1957` | `5040` |
| `extended_060_small_balanced_tie_heavy_flat_n2_fee0` | `True` | `2` | `small_balanced/tie_heavy_flat` | `5` | `6` |
| `extended_061_deep_balanced_near_tie_stagger_n3_fee1` | `True` | `3` | `deep_balanced/near_tie_stagger` | `16` | `24` |
| `extended_062_thin_margin_high_out_ascending_stair_n4_fee5` | `True` | `4` | `thin_margin_high_out/ascending_stair` | `65` | `120` |
| `extended_063_balanced_mid_descending_stair_n5_fee30` | `True` | `5` | `balanced_mid/descending_stair` | `326` | `720` |
| `extended_064_low_in_high_out_alternating_large_n6_fee75` | `True` | `6` | `low_in_high_out/alternating_large` | `1957` | `5040` |
| `extended_065_near_domain_reserve_in_burst_prefix_n2_fee100` | `True` | `2` | `near_domain_reserve_in/burst_prefix` | `5` | `6` |
| `extended_066_tight_out_positive_burst_suffix_n3_fee500` | `True` | `3` | `tight_out_positive/burst_suffix` | `16` | `24` |
| `extended_067_huge_out_powers_n4_fee2500` | `True` | `4` | `huge_out/powers` | `65` | `120` |
| `extended_068_skewed_in_prime_steps_n5_fee5000` | `True` | `5` | `skewed_in/prime_steps` | `326` | `720` |
| `extended_069_small_balanced_high_fee_safe_n6_fee9000` | `True` | `6` | `small_balanced/high_fee_safe` | `1957` | `5040` |
| `extended_070_deep_balanced_tie_heavy_flat_n2_fee0` | `True` | `2` | `deep_balanced/tie_heavy_flat` | `5` | `6` |
| `extended_071_thin_margin_high_out_near_tie_stagger_n3_fee1` | `True` | `3` | `thin_margin_high_out/near_tie_stagger` | `16` | `24` |
| `extended_072_balanced_mid_ascending_stair_n4_fee5` | `True` | `4` | `balanced_mid/ascending_stair` | `65` | `120` |
| `extended_073_low_in_high_out_descending_stair_n5_fee30` | `True` | `5` | `low_in_high_out/descending_stair` | `326` | `720` |
| `extended_074_near_domain_reserve_in_alternating_large_n6_fee75` | `True` | `6` | `near_domain_reserve_in/alternating_large` | `1957` | `5040` |
| `extended_075_tight_out_positive_burst_prefix_n2_fee100` | `True` | `2` | `tight_out_positive/burst_prefix` | `5` | `6` |
| `extended_076_huge_out_burst_suffix_n3_fee500` | `True` | `3` | `huge_out/burst_suffix` | `16` | `24` |
| `extended_077_skewed_in_powers_n4_fee2500` | `True` | `4` | `skewed_in/powers` | `65` | `120` |
| `extended_078_small_balanced_prime_steps_n5_fee5000` | `True` | `5` | `small_balanced/prime_steps` | `326` | `720` |
| `extended_079_deep_balanced_high_fee_safe_n6_fee9000` | `True` | `6` | `deep_balanced/high_fee_safe` | `1957` | `5040` |
| `extended_080_thin_margin_high_out_tie_heavy_flat_n2_fee0` | `True` | `2` | `thin_margin_high_out/tie_heavy_flat` | `5` | `6` |
| `extended_081_balanced_mid_near_tie_stagger_n3_fee1` | `True` | `3` | `balanced_mid/near_tie_stagger` | `16` | `24` |
| `extended_082_low_in_high_out_ascending_stair_n4_fee5` | `True` | `4` | `low_in_high_out/ascending_stair` | `65` | `120` |
| `extended_083_near_domain_reserve_in_descending_stair_n5_fee30` | `True` | `5` | `near_domain_reserve_in/descending_stair` | `326` | `720` |
| `extended_084_tight_out_positive_alternating_large_n6_fee75` | `True` | `6` | `tight_out_positive/alternating_large` | `1957` | `5040` |
| `extended_085_huge_out_burst_prefix_n2_fee100` | `True` | `2` | `huge_out/burst_prefix` | `5` | `6` |
| `extended_086_skewed_in_burst_suffix_n3_fee500` | `True` | `3` | `skewed_in/burst_suffix` | `16` | `24` |
| `extended_087_small_balanced_powers_n4_fee2500` | `True` | `4` | `small_balanced/powers` | `65` | `120` |
| `extended_088_deep_balanced_prime_steps_n5_fee5000` | `True` | `5` | `deep_balanced/prime_steps` | `326` | `720` |
| `extended_089_thin_margin_high_out_high_fee_safe_n6_fee9000` | `True` | `6` | `thin_margin_high_out/high_fee_safe` | `1957` | `5040` |

## Non-Claims

- This extended stress corpus is deterministic and finite, not exhaustive over all states.
- This checker does not prove Lean-to-Python refinement.
- This checker does not cover nonzero min_amount_out certificates; those are rejected as out of scope.
- This checker does not define canonical tie order.
- This checker does not add settlement, state-root, production, or governance authority.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_arbitrary_subset_family_extended_stress.py
```
