# ZenoDEX AB Strict Zero-Min Arbitrary Subset-Family Certificate - 2026-06-29

## Executive Result

A bounded host certificate checker instantiates the Lean StrictSubsetFamilyHostTable shape as singleton subset-family obligations over every reachable mask and completion suffix in the strict zero-min stress corpus.

Research-only certificate evidence; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Deterministic seed: `2026062901`
- Generated cases: `180`
- Strict cases checked: `180`
- Valid cases: `180`
- Reachable masks checked: `4464`
- Full records checked: `85284`
- Singleton table obligations: `85284`
- Selected suffix executable checks: `85284`
- Dominance checks: `212760`
- Runtime-executable full completions: `212760`
- Negative controls: `10`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Lean Shape Mirrored

```text
StrictSubsetFamilyHostTable:
  masks = [mask]
  winner = mask
  suffix = fixed completion suffix
  packetHashBound = true
  noAuthorityEffect = true
  winnerMembershipBound = true
```

For each singleton family, the checker validates local pruning, winner membership,
selected suffix executability, and selected-final reserve dominance against all
full-state records for the same mask and suffix.

## Coverage

- `n` histogram: `{'2': 36, '3': 36, '4': 36, '5': 36, '6': 36}`
- Fee histogram: `{'0': 26, '1': 26, '2': 26, '5': 26, '30': 26, '75': 25, '100': 25}`
- Pattern histogram: `{'alternating': 20, 'ascending': 20, 'descending': 20, 'fibonacci': 20, 'flat': 20, 'near_tie_pairs': 20, 'one_large_prefix': 20, 'one_large_suffix': 20, 'seeded_random': 20}`
- Max records per mask: `720`
- Max suffixes per mask: `720`

## First Packet

```json
{
  "amounts": [
    8,
    8
  ],
  "authority_boundary": "research_only_no_settlement_or_state_authority",
  "bit_count": 2,
  "case_id": "stress_000_flat_n2_fee0",
  "executed_input": 16,
  "first_obligation": {
    "full_record_count": 1,
    "full_records_digest": "26c651b194061bd3e792cf6ba44e238df4783fedaecd221193f8f8d8768da107",
    "mask_id": 0,
    "singleton_family": [
      0
    ],
    "suffix": {
      "order_ids": [
        "0x00000000000000000000000000000000000000000000000000000000000493e0",
        "0x00000000000000000000000000000000000000000000000000000000000493e1"
      ],
      "order_short": [
        "93e0",
        "93e1"
      ]
    },
    "winner": {
      "order_short": [],
      "processed_reserve_in": 512,
      "reserve_out": 33020
    }
  },
  "full_mask": 3,
  "initial_reserve_in": 512,
  "initial_reserve_out": 33020,
  "lean_contract": {
    "endpoint": "strictSubsetFamilyHostTable_validates",
    "family_shape": "singleton_per_reachable_mask_suffix",
    "structure": "StrictSubsetFamilyHostTable",
    "valid_predicate": "strictSubsetFamilyHostTableValid",
    "witness": "witness_strictSubsetFamilyHostTable_validates"
  },
  "mask_summaries": [
    {
      "full_record_count": 1,
      "full_records_digest": "26c651b194061bd3e792cf6ba44e238df4783fedaecd221193f8f8d8768da107",
      "mask_id": 0,
      "selected": {
        "order_short": [],
        "processed_reserve_in": 512,
        "reserve_out": 33020
      },
      "selected_digest": "e530ac7af66274eff37e8f98c933e0f5404f49262f22bb24710ec3022dda8dc2",
      "singleton_family_shape": true,
      "suffix_count": 2,
      "winner_member_of_family": true
    },
    {
      "full_record_count": 1,
      "full_records_digest": "e4851e6137ec00b7561c9dd281884aa89afd8ea82b3146b3d2cb30da2f9e04e5",
      "mask_id": 1,
      "selected": {
        "order_short": [
          "93e0"
        ],
        "processed_reserve_in": 520,
        "reserve_out": 32512
      },
      "selected_digest": "6cb1f8fda76725fe31215f7720b288b48d304aa6a9c80881816383687121d11b",
      "singleton_family_shape": true,
      "suffix_count": 1,
      "winner_member_of_family": true
    },
    {
      "full_record_count": 1,
      "full_records_digest": "6d9876660232fa5a67e55502346a920e9d28dd50e61862e4731862d9aa0a0070",
      "mask_id": 2,
      "selected": {
        "order_short": [
          "93e1"
        ],
        "processed_reserve_in": 520,
        "reserve_out": 32512
      },
      "selected_digest": "58cacd1c696b55c985449699277780e677ce00399ffc897a2243f3a67a042ef8",
      "singleton_family_shape": true,
      "suffix_count": 1,
      "winner_member_of_family": true
    },
    {
      "full_record_count": 2,
      "full_records_digest": "3dcc2bd9b70dabbf96adbf23e94e08f2e6a2e1293d29e23d9b4a8d3d655655b4",
      "mask_id": 3,
      "selected": {
        "order_short": [
          "93e0",
          "93e1"
        ],
        "processed_reserve_in": 528,
        "reserve_out": 32020
      },
      "selected_digest": "f9e07e969a2be50f02de0da7ea9f1556120356796e00d918b56818be5de37d16",
      "singleton_family_shape": true,
      "suffix_count": 1,
      "winner_member_of_family": true
    }
  ],
  "min_amount_out": [
    0,
    0
  ],
  "no_authority_effect": true,
  "obligation_summary": {
    "dominance_check_count": 6,
    "full_runtime_completion_count": 6,
    "mask_count": 4,
    "max_records_per_mask": 2,
    "max_suffix_per_mask": 2,
    "obligation_digest": "b1ade4270a8ad8e8d8aa01ef24ae4cd44c20e993f91f1b1f7d3632f0d2109f23",
    "record_count": 5,
    "selected_suffix_executable_count": 5,
    "singleton_table_obligation_count": 5
  },
  "packet_hash": "3c61753f1d5bdde3ed81d9df6a374f014384168ab1a4b4f0f5e65ca7e589e753",
  "packet_hash_bound": true,
  "pool": {
    "fee_bps": 0,
    "reserve_in": 512,
    "reserve_out": 33020
  },
  "schema": "zenodex.ab_strict_zero_min_arbitrary_subset_family_certificate_packet.v1",
  "scope": "stress_same_pool_same_direction_exact_in_zero_min_strict_executable",
  "stress": {
    "case_count": 180,
    "pattern": "flat",
    "seed": 2026062901
  },
  "winner_membership_bound": true
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `packet_hash_bound_missing` | `False` | `packet_hash_bound_missing` |
| `authority_effect_present` | `False` | `authority_effect_present` |
| `winner_membership_bound_missing` | `False` | `winner_membership_bound_missing` |
| `compressed_record_missing` | `False` | `compressed_record_missing` |
| `mask_pruning_full_record_processed_reserve_in_mismatch` | `False` | `mask_pruning_full_record_processed_reserve_in_mismatch` |
| `mask_pruning_selected_reserve_out_not_min` | `False` | `mask_pruning_selected_reserve_out_not_min` |
| `selected_record_not_in_full_state_records` | `False` | `selected_record_not_in_full_state_records` |
| `singleton_table_suffix_not_executable` | `False` | `singleton_table_suffix_not_executable` |
| `selected_final_reserve_dominance_failure` | `False` | `selected_final_reserve_dominance_failure` |

## Case Summary

| case | ok | n | masks | singleton tables | dominance checks |
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

- This bounded checker is not a Lean proof of the concrete Python emitter.
- This checker does not prove Lean-to-Python refinement.
- This checker does not prove exhaustive coverage over all pool states.
- This checker does not define canonical tie order.
- Nonzero min_amount_out batches are outside this artifact.
- The singleton-family packet shape is a host certificate shape, not a production ABI.
- No settlement, state-root, production, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_arbitrary_subset_family_certificate.py
```
