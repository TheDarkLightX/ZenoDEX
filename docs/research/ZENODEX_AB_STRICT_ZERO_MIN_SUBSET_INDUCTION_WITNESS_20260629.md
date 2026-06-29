# ZenoDEX AB Strict Zero-Min Subset Induction Witness - 2026-06-29

## Executive Result

A bounded host oracle checks the subset-mask induction obligations for strict zero-min one-record min-reserve-out compression across the deterministic stress corpus.

Research-only induction witness evidence; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Deterministic seed: `2026062901`
- Generated cases: `180`
- Strict cases checked: `180`
- Valid cases: `180`
- Reachable masks checked: `4464`
- Full records checked: `85284`
- Suffix checks: `212760`
- Runtime-executable completions: `212760`
- Negative controls: `6`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Induction Obligations Checked

```text
for each reachable subset mask:
  selected compressed record is present in the full-state record set
  all records share reserve_in = initial_reserve_in + subset_amount_sum
  selected reserve_out is the minimum reserve_out at that mask
  every runtime-executable full-record suffix completion executes from selected
  selected final reserve_out <= full-record final reserve_out
```

The last line is the host analogue of the Lean reserve-dominance direction:
lower final output reserve means weakly greater zero-min surplus.

## Coverage

- `n` histogram: `{'2': 36, '3': 36, '4': 36, '5': 36, '6': 36}`
- Fee histogram: `{'0': 26, '1': 26, '2': 26, '5': 26, '30': 26, '75': 25, '100': 25}`
- Pattern histogram: `{'alternating': 20, 'ascending': 20, 'descending': 20, 'fibonacci': 20, 'flat': 20, 'near_tie_pairs': 20, 'one_large_prefix': 20, 'one_large_suffix': 20, 'seeded_random': 20}`
- Max records per mask: `720`
- Max suffixes per record: `720`

## First Case

```json
{
  "bit_count": 2,
  "case_id": "stress_000_flat_n2_fee0",
  "executable_completion_count": 6,
  "fee_bps": 0,
  "first_failure": null,
  "full_mask_selected": {
    "order_short": [
      "93e0",
      "93e1"
    ],
    "processed_reserve_in": 528,
    "reserve_out": 32020
  },
  "mask_count": 4,
  "max_records_per_mask": 2,
  "max_suffix_per_record": 2,
  "ok": true,
  "pattern": "flat",
  "reasons": [],
  "record_count": 5,
  "suffix_check_count": 6
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `compressed_record_missing` | `False` | `compressed_record_missing` |
| `full_record_processed_reserve_in_mismatch` | `False` | `full_record_processed_reserve_in_mismatch` |
| `selected_reserve_out_not_min` | `False` | `selected_reserve_out_not_min` |
| `selected_record_not_in_full_state_records` | `False` | `selected_record_not_in_full_state_records` |
| `selected_suffix_executability_gap` | `False` | `selected_suffix_executability_gap` |
| `selected_final_reserve_dominance_failure` | `False` | `selected_final_reserve_dominance_failure` |

## Case Summary

| case | ok | n | masks | records | suffix checks |
| --- | --- | ---: | ---: | ---: | ---: |
| `stress_000_flat_n2_fee0` | `True` | `2` | `4` | `5` | `6` |
| `stress_001_ascending_n3_fee1` | `True` | `3` | `8` | `16` | `24` |
| `stress_002_descending_n4_fee2` | `True` | `4` | `16` | `65` | `120` |
| `stress_003_fibonacci_n5_fee5` | `True` | `5` | `32` | `326` | `720` |
| `stress_004_alternating_n6_fee30` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_005_one_large_prefix_n2_fee75` | `True` | `2` | `4` | `5` | `6` |
| `stress_006_one_large_suffix_n3_fee100` | `True` | `3` | `8` | `16` | `24` |
| `stress_007_near_tie_pairs_n4_fee0` | `True` | `4` | `16` | `65` | `120` |
| `stress_008_seeded_random_n5_fee1` | `True` | `5` | `32` | `326` | `720` |
| `stress_009_flat_n6_fee2` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_010_ascending_n2_fee5` | `True` | `2` | `4` | `5` | `6` |
| `stress_011_descending_n3_fee30` | `True` | `3` | `8` | `16` | `24` |
| `stress_012_fibonacci_n4_fee75` | `True` | `4` | `16` | `65` | `120` |
| `stress_013_alternating_n5_fee100` | `True` | `5` | `32` | `326` | `720` |
| `stress_014_one_large_prefix_n6_fee0` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_015_one_large_suffix_n2_fee1` | `True` | `2` | `4` | `5` | `6` |
| `stress_016_near_tie_pairs_n3_fee2` | `True` | `3` | `8` | `16` | `24` |
| `stress_017_seeded_random_n4_fee5` | `True` | `4` | `16` | `65` | `120` |
| `stress_018_flat_n5_fee30` | `True` | `5` | `32` | `326` | `720` |
| `stress_019_ascending_n6_fee75` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_020_descending_n2_fee100` | `True` | `2` | `4` | `5` | `6` |
| `stress_021_fibonacci_n3_fee0` | `True` | `3` | `8` | `16` | `24` |
| `stress_022_alternating_n4_fee1` | `True` | `4` | `16` | `65` | `120` |
| `stress_023_one_large_prefix_n5_fee2` | `True` | `5` | `32` | `326` | `720` |
| `stress_024_one_large_suffix_n6_fee5` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_025_near_tie_pairs_n2_fee30` | `True` | `2` | `4` | `5` | `6` |
| `stress_026_seeded_random_n3_fee75` | `True` | `3` | `8` | `16` | `24` |
| `stress_027_flat_n4_fee100` | `True` | `4` | `16` | `65` | `120` |
| `stress_028_ascending_n5_fee0` | `True` | `5` | `32` | `326` | `720` |
| `stress_029_descending_n6_fee1` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_030_fibonacci_n2_fee2` | `True` | `2` | `4` | `5` | `6` |
| `stress_031_alternating_n3_fee5` | `True` | `3` | `8` | `16` | `24` |
| `stress_032_one_large_prefix_n4_fee30` | `True` | `4` | `16` | `65` | `120` |
| `stress_033_one_large_suffix_n5_fee75` | `True` | `5` | `32` | `326` | `720` |
| `stress_034_near_tie_pairs_n6_fee100` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_035_seeded_random_n2_fee0` | `True` | `2` | `4` | `5` | `6` |
| `stress_036_flat_n3_fee1` | `True` | `3` | `8` | `16` | `24` |
| `stress_037_ascending_n4_fee2` | `True` | `4` | `16` | `65` | `120` |
| `stress_038_descending_n5_fee5` | `True` | `5` | `32` | `326` | `720` |
| `stress_039_fibonacci_n6_fee30` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_040_alternating_n2_fee75` | `True` | `2` | `4` | `5` | `6` |
| `stress_041_one_large_prefix_n3_fee100` | `True` | `3` | `8` | `16` | `24` |
| `stress_042_one_large_suffix_n4_fee0` | `True` | `4` | `16` | `65` | `120` |
| `stress_043_near_tie_pairs_n5_fee1` | `True` | `5` | `32` | `326` | `720` |
| `stress_044_seeded_random_n6_fee2` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_045_flat_n2_fee5` | `True` | `2` | `4` | `5` | `6` |
| `stress_046_ascending_n3_fee30` | `True` | `3` | `8` | `16` | `24` |
| `stress_047_descending_n4_fee75` | `True` | `4` | `16` | `65` | `120` |
| `stress_048_fibonacci_n5_fee100` | `True` | `5` | `32` | `326` | `720` |
| `stress_049_alternating_n6_fee0` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_050_one_large_prefix_n2_fee1` | `True` | `2` | `4` | `5` | `6` |
| `stress_051_one_large_suffix_n3_fee2` | `True` | `3` | `8` | `16` | `24` |
| `stress_052_near_tie_pairs_n4_fee5` | `True` | `4` | `16` | `65` | `120` |
| `stress_053_seeded_random_n5_fee30` | `True` | `5` | `32` | `326` | `720` |
| `stress_054_flat_n6_fee75` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_055_ascending_n2_fee100` | `True` | `2` | `4` | `5` | `6` |
| `stress_056_descending_n3_fee0` | `True` | `3` | `8` | `16` | `24` |
| `stress_057_fibonacci_n4_fee1` | `True` | `4` | `16` | `65` | `120` |
| `stress_058_alternating_n5_fee2` | `True` | `5` | `32` | `326` | `720` |
| `stress_059_one_large_prefix_n6_fee5` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_060_one_large_suffix_n2_fee30` | `True` | `2` | `4` | `5` | `6` |
| `stress_061_near_tie_pairs_n3_fee75` | `True` | `3` | `8` | `16` | `24` |
| `stress_062_seeded_random_n4_fee100` | `True` | `4` | `16` | `65` | `120` |
| `stress_063_flat_n5_fee0` | `True` | `5` | `32` | `326` | `720` |
| `stress_064_ascending_n6_fee1` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_065_descending_n2_fee2` | `True` | `2` | `4` | `5` | `6` |
| `stress_066_fibonacci_n3_fee5` | `True` | `3` | `8` | `16` | `24` |
| `stress_067_alternating_n4_fee30` | `True` | `4` | `16` | `65` | `120` |
| `stress_068_one_large_prefix_n5_fee75` | `True` | `5` | `32` | `326` | `720` |
| `stress_069_one_large_suffix_n6_fee100` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_070_near_tie_pairs_n2_fee0` | `True` | `2` | `4` | `5` | `6` |
| `stress_071_seeded_random_n3_fee1` | `True` | `3` | `8` | `16` | `24` |
| `stress_072_flat_n4_fee2` | `True` | `4` | `16` | `65` | `120` |
| `stress_073_ascending_n5_fee5` | `True` | `5` | `32` | `326` | `720` |
| `stress_074_descending_n6_fee30` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_075_fibonacci_n2_fee75` | `True` | `2` | `4` | `5` | `6` |
| `stress_076_alternating_n3_fee100` | `True` | `3` | `8` | `16` | `24` |
| `stress_077_one_large_prefix_n4_fee0` | `True` | `4` | `16` | `65` | `120` |
| `stress_078_one_large_suffix_n5_fee1` | `True` | `5` | `32` | `326` | `720` |
| `stress_079_near_tie_pairs_n6_fee2` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_080_seeded_random_n2_fee5` | `True` | `2` | `4` | `5` | `6` |
| `stress_081_flat_n3_fee30` | `True` | `3` | `8` | `16` | `24` |
| `stress_082_ascending_n4_fee75` | `True` | `4` | `16` | `65` | `120` |
| `stress_083_descending_n5_fee100` | `True` | `5` | `32` | `326` | `720` |
| `stress_084_fibonacci_n6_fee0` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_085_alternating_n2_fee1` | `True` | `2` | `4` | `5` | `6` |
| `stress_086_one_large_prefix_n3_fee2` | `True` | `3` | `8` | `16` | `24` |
| `stress_087_one_large_suffix_n4_fee5` | `True` | `4` | `16` | `65` | `120` |
| `stress_088_near_tie_pairs_n5_fee30` | `True` | `5` | `32` | `326` | `720` |
| `stress_089_seeded_random_n6_fee75` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_090_flat_n2_fee100` | `True` | `2` | `4` | `5` | `6` |
| `stress_091_ascending_n3_fee0` | `True` | `3` | `8` | `16` | `24` |
| `stress_092_descending_n4_fee1` | `True` | `4` | `16` | `65` | `120` |
| `stress_093_fibonacci_n5_fee2` | `True` | `5` | `32` | `326` | `720` |
| `stress_094_alternating_n6_fee5` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_095_one_large_prefix_n2_fee30` | `True` | `2` | `4` | `5` | `6` |
| `stress_096_one_large_suffix_n3_fee75` | `True` | `3` | `8` | `16` | `24` |
| `stress_097_near_tie_pairs_n4_fee100` | `True` | `4` | `16` | `65` | `120` |
| `stress_098_seeded_random_n5_fee0` | `True` | `5` | `32` | `326` | `720` |
| `stress_099_flat_n6_fee1` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_100_ascending_n2_fee2` | `True` | `2` | `4` | `5` | `6` |
| `stress_101_descending_n3_fee5` | `True` | `3` | `8` | `16` | `24` |
| `stress_102_fibonacci_n4_fee30` | `True` | `4` | `16` | `65` | `120` |
| `stress_103_alternating_n5_fee75` | `True` | `5` | `32` | `326` | `720` |
| `stress_104_one_large_prefix_n6_fee100` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_105_one_large_suffix_n2_fee0` | `True` | `2` | `4` | `5` | `6` |
| `stress_106_near_tie_pairs_n3_fee1` | `True` | `3` | `8` | `16` | `24` |
| `stress_107_seeded_random_n4_fee2` | `True` | `4` | `16` | `65` | `120` |
| `stress_108_flat_n5_fee5` | `True` | `5` | `32` | `326` | `720` |
| `stress_109_ascending_n6_fee30` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_110_descending_n2_fee75` | `True` | `2` | `4` | `5` | `6` |
| `stress_111_fibonacci_n3_fee100` | `True` | `3` | `8` | `16` | `24` |
| `stress_112_alternating_n4_fee0` | `True` | `4` | `16` | `65` | `120` |
| `stress_113_one_large_prefix_n5_fee1` | `True` | `5` | `32` | `326` | `720` |
| `stress_114_one_large_suffix_n6_fee2` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_115_near_tie_pairs_n2_fee5` | `True` | `2` | `4` | `5` | `6` |
| `stress_116_seeded_random_n3_fee30` | `True` | `3` | `8` | `16` | `24` |
| `stress_117_flat_n4_fee75` | `True` | `4` | `16` | `65` | `120` |
| `stress_118_ascending_n5_fee100` | `True` | `5` | `32` | `326` | `720` |
| `stress_119_descending_n6_fee0` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_120_fibonacci_n2_fee1` | `True` | `2` | `4` | `5` | `6` |
| `stress_121_alternating_n3_fee2` | `True` | `3` | `8` | `16` | `24` |
| `stress_122_one_large_prefix_n4_fee5` | `True` | `4` | `16` | `65` | `120` |
| `stress_123_one_large_suffix_n5_fee30` | `True` | `5` | `32` | `326` | `720` |
| `stress_124_near_tie_pairs_n6_fee75` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_125_seeded_random_n2_fee100` | `True` | `2` | `4` | `5` | `6` |
| `stress_126_flat_n3_fee0` | `True` | `3` | `8` | `16` | `24` |
| `stress_127_ascending_n4_fee1` | `True` | `4` | `16` | `65` | `120` |
| `stress_128_descending_n5_fee2` | `True` | `5` | `32` | `326` | `720` |
| `stress_129_fibonacci_n6_fee5` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_130_alternating_n2_fee30` | `True` | `2` | `4` | `5` | `6` |
| `stress_131_one_large_prefix_n3_fee75` | `True` | `3` | `8` | `16` | `24` |
| `stress_132_one_large_suffix_n4_fee100` | `True` | `4` | `16` | `65` | `120` |
| `stress_133_near_tie_pairs_n5_fee0` | `True` | `5` | `32` | `326` | `720` |
| `stress_134_seeded_random_n6_fee1` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_135_flat_n2_fee2` | `True` | `2` | `4` | `5` | `6` |
| `stress_136_ascending_n3_fee5` | `True` | `3` | `8` | `16` | `24` |
| `stress_137_descending_n4_fee30` | `True` | `4` | `16` | `65` | `120` |
| `stress_138_fibonacci_n5_fee75` | `True` | `5` | `32` | `326` | `720` |
| `stress_139_alternating_n6_fee100` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_140_one_large_prefix_n2_fee0` | `True` | `2` | `4` | `5` | `6` |
| `stress_141_one_large_suffix_n3_fee1` | `True` | `3` | `8` | `16` | `24` |
| `stress_142_near_tie_pairs_n4_fee2` | `True` | `4` | `16` | `65` | `120` |
| `stress_143_seeded_random_n5_fee5` | `True` | `5` | `32` | `326` | `720` |
| `stress_144_flat_n6_fee30` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_145_ascending_n2_fee75` | `True` | `2` | `4` | `5` | `6` |
| `stress_146_descending_n3_fee100` | `True` | `3` | `8` | `16` | `24` |
| `stress_147_fibonacci_n4_fee0` | `True` | `4` | `16` | `65` | `120` |
| `stress_148_alternating_n5_fee1` | `True` | `5` | `32` | `326` | `720` |
| `stress_149_one_large_prefix_n6_fee2` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_150_one_large_suffix_n2_fee5` | `True` | `2` | `4` | `5` | `6` |
| `stress_151_near_tie_pairs_n3_fee30` | `True` | `3` | `8` | `16` | `24` |
| `stress_152_seeded_random_n4_fee75` | `True` | `4` | `16` | `65` | `120` |
| `stress_153_flat_n5_fee100` | `True` | `5` | `32` | `326` | `720` |
| `stress_154_ascending_n6_fee0` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_155_descending_n2_fee1` | `True` | `2` | `4` | `5` | `6` |
| `stress_156_fibonacci_n3_fee2` | `True` | `3` | `8` | `16` | `24` |
| `stress_157_alternating_n4_fee5` | `True` | `4` | `16` | `65` | `120` |
| `stress_158_one_large_prefix_n5_fee30` | `True` | `5` | `32` | `326` | `720` |
| `stress_159_one_large_suffix_n6_fee75` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_160_near_tie_pairs_n2_fee100` | `True` | `2` | `4` | `5` | `6` |
| `stress_161_seeded_random_n3_fee0` | `True` | `3` | `8` | `16` | `24` |
| `stress_162_flat_n4_fee1` | `True` | `4` | `16` | `65` | `120` |
| `stress_163_ascending_n5_fee2` | `True` | `5` | `32` | `326` | `720` |
| `stress_164_descending_n6_fee5` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_165_fibonacci_n2_fee30` | `True` | `2` | `4` | `5` | `6` |
| `stress_166_alternating_n3_fee75` | `True` | `3` | `8` | `16` | `24` |
| `stress_167_one_large_prefix_n4_fee100` | `True` | `4` | `16` | `65` | `120` |
| `stress_168_one_large_suffix_n5_fee0` | `True` | `5` | `32` | `326` | `720` |
| `stress_169_near_tie_pairs_n6_fee1` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_170_seeded_random_n2_fee2` | `True` | `2` | `4` | `5` | `6` |
| `stress_171_flat_n3_fee5` | `True` | `3` | `8` | `16` | `24` |
| `stress_172_ascending_n4_fee30` | `True` | `4` | `16` | `65` | `120` |
| `stress_173_descending_n5_fee75` | `True` | `5` | `32` | `326` | `720` |
| `stress_174_fibonacci_n6_fee100` | `True` | `6` | `64` | `1957` | `5040` |
| `stress_175_alternating_n2_fee0` | `True` | `2` | `4` | `5` | `6` |
| `stress_176_one_large_prefix_n3_fee1` | `True` | `3` | `8` | `16` | `24` |
| `stress_177_one_large_suffix_n4_fee2` | `True` | `4` | `16` | `65` | `120` |
| `stress_178_near_tie_pairs_n5_fee5` | `True` | `5` | `32` | `326` | `720` |
| `stress_179_seeded_random_n6_fee30` | `True` | `6` | `64` | `1957` | `5040` |

## Non-Claims

- This bounded oracle is not a Lean proof of the full subset-mask induction theorem.
- This checker does not prove Lean-to-Python refinement.
- This checker does not define canonical tie order.
- Nonzero min_amount_out batches are outside this artifact.
- The stress corpus is deterministic and finite, not exhaustive over all pool states.
- No settlement authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_subset_induction_witness.py
```
