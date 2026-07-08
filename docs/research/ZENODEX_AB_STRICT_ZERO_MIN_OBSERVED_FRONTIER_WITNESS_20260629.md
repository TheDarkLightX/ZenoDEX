# ZenoDEX AB Strict Zero-Min Observed Frontier Witness - 2026-06-29

## Executive Result

A deterministic host checker validates the observed child-frontier obligations assumed by Lean's strictObservedFullMaskEmitterTableValid endpoint across the strict zero-min stress packet corpus.

Research-only observed-frontier evidence; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Deterministic seed: `2026062901`
- Generated cases: `180`
- Strict executable packets: `180`
- Valid observed-frontier packets: `180`
- Skipped cases: `0`
- Packet mutations checked: `2340`
- Mutation accepts: `0`
- Deterministic replay ok: `True`

## Lean Premise Shape Checked

```text
strictObservedFullMaskEmitterTableValid table
  -> packetHashBound and noAuthorityEffect rails
  -> winnerMembershipBound
  -> every observed child covers all bits below bitCount
  -> every observed child satisfies local maskPruningInvariant
  -> winner dominates observed selected family
  -> winner executes empty suffix
```

## Coverage

- `n` histogram: `{'2': 36, '3': 36, '4': 36, '5': 36, '6': 36}`
- Max bit count: `6`
- Max child frontier count: `720`
- Reject reason classes: `['base_witness_packet_invalid', 'child_all_records_digest_mismatch', 'child_local_pruning_processed_reserve_in_mismatch', 'child_local_pruning_reserve_out_not_min', 'child_local_pruning_selected_not_record', 'child_missing_full_mask_coverage', 'observed_economic_key_mismatch', 'observed_empty_suffix_not_executable', 'observed_winner_not_in_children', 'observed_winner_not_selected_family_dominator']`

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
  "children": [
    {
      "all_records": [
        {
          "order_ids": [
            "0x00000000000000000000000000000000000000000000000000000000000493e0",
            "0x00000000000000000000000000000000000000000000000000000000000493e1"
          ],
          "order_short": [
            "93e0",
            "93e1"
          ],
          "processed_reserve_in": 528,
          "reserve_out": 32020
        }
      ],
      "all_records_count": 1,
      "all_records_digest": "a4b70c4f35c9b1bea8739b145516ca3b02cf72d865e99178a38e0dc02b684144",
      "mask_id": 3,
      "selected": {
        "order_ids": [
          "0x00000000000000000000000000000000000000000000000000000000000493e0",
          "0x00000000000000000000000000000000000000000000000000000000000493e1"
        ],
        "order_short": [
          "93e0",
          "93e1"
        ],
        "processed_reserve_in": 528,
        "reserve_out": 32020
      }
    },
    {
      "all_records": [
        {
          "order_ids": [
            "0x00000000000000000000000000000000000000000000000000000000000493e1",
            "0x00000000000000000000000000000000000000000000000000000000000493e0"
          ],
          "order_short": [
            "93e1",
            "93e0"
          ],
          "processed_reserve_in": 528,
          "reserve_out": 32020
        }
      ],
      "all_records_count": 1,
      "all_records_digest": "5f1e8bfe7c021e0a9f05daf8f456037b8ce4c77848fe267189aa4ae4d24c79bc",
      "mask_id": 3,
      "selected": {
        "order_ids": [
          "0x00000000000000000000000000000000000000000000000000000000000493e1",
          "0x00000000000000000000000000000000000000000000000000000000000493e0"
        ],
        "order_short": [
          "93e1",
          "93e0"
        ],
        "processed_reserve_in": 528,
        "reserve_out": 32020
      }
    }
  ],
  "compressed_table": [
    {
      "mask_id": 0,
      "selected": {
        "order_ids": [],
        "order_short": [],
        "processed_reserve_in": 512,
        "reserve_out": 33020
      }
    },
    {
      "mask_id": 1,
      "selected": {
        "order_ids": [
          "0x00000000000000000000000000000000000000000000000000000000000493e0"
        ],
        "order_short": [
          "93e0"
        ],
        "processed_reserve_in": 520,
        "reserve_out": 32512
      }
    },
    {
      "mask_id": 2,
      "selected": {
        "order_ids": [
          "0x00000000000000000000000000000000000000000000000000000000000493e1"
        ],
        "order_short": [
          "93e1"
        ],
        "processed_reserve_in": 520,
        "reserve_out": 32512
      }
    },
    {
      "mask_id": 3,
      "selected": {
        "order_ids": [
          "0x00000000000000000000000000000000000000000000000000000000000493e0",
          "0x00000000000000000000000000000000000000000000000000000000000493e1"
        ],
        "order_short": [
          "93e0",
          "93e1"
        ],
        "processed_reserve_in": 528,
        "reserve_out": 32020
      }
    }
  ],
  "economic_keys": {
    "brute_force": [
      16,
      1000
    ],
    "compressed": [
      16,
      1000
    ],
    "full_subset_dp": [
      16,
      1000
    ]
  },
  "executed_input": 16,
  "full_mask": 3,
  "initial_reserve_in": 512,
  "initial_reserve_out": 33020,
  "lean_contract": {
    "endpoint": "strictCompressedFullMaskEconomicWitness_validates",
    "structure": "StrictCompressedFullMaskEconomicWitness",
    "valid_predicate": "strictCompressedFullMaskEconomicWitnessValid"
  },
  "masks": [
    {
      "all_records": [
        {
          "order_ids": [
            "0x00000000000000000000000000000000000000000000000000000000000493e0",
            "0x00000000000000000000000000000000000000000000000000000000000493e1"
          ],
          "order_short": [
            "93e0",
            "93e1"
          ],
          "processed_reserve_in": 528,
          "reserve_out": 32020
        }
      ],
      "all_records_count": 1,
      "all_records_digest": "a4b70c4f35c9b1bea8739b145516ca3b02cf72d865e99178a38e0dc02b684144",
      "mask_id": 3,
      "selected": {
        "order_ids": [
          "0x00000000000000000000000000000000000000000000000000000000000493e0",
          "0x00000000000000000000000000000000000000000000000000000000000493e1"
        ],
        "order_short": [
          "93e0",
          "93e1"
        ],
        "processed_reserve_in": 528,
        "reserve_out": 32020
      }
    }
  ],
  "min_amount_out": [
    0,
    0
  ],
  "no_authority_effect": true,
  "packet_hash": "d2f545c30e756689f505773883f17c468273e64ed1826b44004283a80af94292",
  "parent": {
    "all_records": [
      {
        "order_ids": [],
        "order_short": [],
        "processed_reserve_in": 512,
        "reserve_out": 33020
      }
    ],
    "all_records_count": 1,
    "all_records_digest": "e38571096e3d5d57a182e3a33859b0a50f10c71dc5ff8bb51464d2d62010ace9",
    "mask_id": 0,
    "selected": {
      "order_ids": [],
      "order_short": [],
      "processed_reserve_in": 512,
      "reserve_out": 33020
    }
  },
  "pool": {
    "fee_bps": 0,
    "reserve_in": 512,
    "reserve_out": 33020
  },
  "schema": "zenodex.ab_strict_zero_min_emitter_witness_packet.v1",
  "scope": "stress_same_pool_same_direction_exact_in_zero_min_strict_executable",
  "stress": {
    "case_count": 180,
    "pattern": "flat",
    "seed": 2026062901
  },
  "winner": {
    "all_records": [
      {
        "order_ids": [
          "0x00000000000000000000000000000000000000000000000000000000000493e0",
          "0x00000000000000000000000000000000000000000000000000000000000493e1"
        ],
        "order_short": [
          "93e0",
          "93e1"
        ],
        "processed_reserve_in": 528,
        "reserve_out": 32020
      }
    ],
    "all_records_count": 1,
    "all_records_digest": "a4b70c4f35c9b1bea8739b145516ca3b02cf72d865e99178a38e0dc02b684144",
    "mask_id": 3,
    "selected": {
      "order_ids": [
        "0x00000000000000000000000000000000000000000000000000000000000493e0",
        "0x00000000000000000000000000000000000000000000000000000000000493e1"
      ],
      "order_short": [
        "93e0",
        "93e1"
      ],
      "processed_reserve_in": 528,
      "reserve_out": 32020
    }
  }
}
```

## Case Summary

| case | ok | n | fee | children | key |
| --- | --- | ---: | ---: | ---: | --- |
| `stress_000_flat_n2_fee0` | `True` | `2` | `0` | `2` | `[16, 1000]` |
| `stress_001_ascending_n3_fee1` | `True` | `3` | `1` | `6` | `[39, 1824]` |
| `stress_002_descending_n4_fee2` | `True` | `4` | `2` | `24` | `[86, 6495]` |
| `stress_003_fibonacci_n5_fee5` | `True` | `5` | `5` | `120` | `[131, 21935]` |
| `stress_004_alternating_n6_fee30` | `True` | `6` | `30` | `720` | `[267, 3571]` |
| `stress_005_one_large_prefix_n2_fee75` | `True` | `2` | `75` | `2` | `[179, 14084]` |
| `stress_006_one_large_suffix_n3_fee100` | `True` | `3` | `100` | `6` | `[196, 5562]` |
| `stress_007_near_tie_pairs_n4_fee0` | `True` | `4` | `0` | `24` | `[98, 3388]` |
| `stress_008_seeded_random_n5_fee1` | `True` | `5` | `1` | `120` | `[527, 17666]` |
| `stress_009_flat_n6_fee2` | `True` | `6` | `2` | `720` | `[72, 658]` |
| `stress_010_ascending_n2_fee5` | `True` | `2` | `5` | `2` | `[21, 195]` |
| `stress_011_descending_n3_fee30` | `True` | `3` | `30` | `6` | `[57, 1642]` |
| `stress_012_fibonacci_n4_fee75` | `True` | `4` | `75` | `24` | `[76, 3566]` |
| `stress_013_alternating_n5_fee100` | `True` | `5` | `100` | `120` | `[186, 7218]` |
| `stress_014_one_large_prefix_n6_fee0` | `True` | `6` | `0` | `720` | `[219, 11425]` |
| `stress_015_one_large_suffix_n2_fee1` | `True` | `2` | `1` | `2` | `[185, 10288]` |
| `stress_016_near_tie_pairs_n3_fee2` | `True` | `3` | `2` | `6` | `[73, 3243]` |
| `stress_017_seeded_random_n4_fee5` | `True` | `4` | `5` | `24` | `[303, 7525]` |
| `stress_018_flat_n5_fee30` | `True` | `5` | `30` | `120` | `[55, 2212]` |
| `stress_019_ascending_n6_fee75` | `True` | `6` | `75` | `720` | `[123, 1980]` |
| `stress_020_descending_n2_fee100` | `True` | `2` | `100` | `2` | `[33, 1621]` |
| `stress_021_fibonacci_n3_fee0` | `True` | `3` | `0` | `6` | `[42, 2409]` |
| `stress_022_alternating_n4_fee1` | `True` | `4` | `1` | `24` | `[170, 4727]` |
| `stress_023_one_large_prefix_n5_fee2` | `True` | `5` | `2` | `120` | `[227, 10317]` |
| `stress_024_one_large_suffix_n6_fee5` | `True` | `6` | `5` | `720` | `[244, 13356]` |
| `stress_025_near_tie_pairs_n2_fee30` | `True` | `2` | `30` | `2` | `[48, 677]` |
| `stress_026_seeded_random_n3_fee75` | `True` | `3` | `75` | `6` | `[231, 3041]` |
| `stress_027_flat_n4_fee100` | `True` | `4` | `100` | `24` | `[40, 2211]` |
| `stress_028_ascending_n5_fee0` | `True` | `5` | `0` | `120` | `[90, 2150]` |
| `stress_029_descending_n6_fee1` | `True` | `6` | `1` | `720` | `[159, 8843]` |
| `stress_030_fibonacci_n2_fee2` | `True` | `2` | `2` | `2` | `[21, 1185]` |
| `stress_031_alternating_n3_fee5` | `True` | `3` | `5` | `6` | `[106, 4995]` |
| `stress_032_one_large_prefix_n4_fee30` | `True` | `4` | `30` | `24` | `[231, 7943]` |
| `stress_033_one_large_suffix_n5_fee75` | `True` | `5` | `75` | `120` | `[249, 12538]` |
| `stress_034_near_tie_pairs_n6_fee100` | `True` | `6` | `100` | `720` | `[150, 11416]` |
| `stress_035_seeded_random_n2_fee0` | `True` | `2` | `0` | `2` | `[176, 40681]` |
| `stress_036_flat_n3_fee1` | `True` | `3` | `1` | `6` | `[27, 1097]` |
| `stress_037_ascending_n4_fee2` | `True` | `4` | `2` | `24` | `[62, 2664]` |
| `stress_038_descending_n5_fee5` | `True` | `5` | `5` | `120` | `[120, 24986]` |
| `stress_039_fibonacci_n6_fee30` | `True` | `6` | `30` | `720` | `[220, 4911]` |
| `stress_040_alternating_n2_fee75` | `True` | `2` | `75` | `2` | `[92, 6869]` |
| `stress_041_one_large_prefix_n3_fee100` | `True` | `3` | `100` | `6` | `[194, 5716]` |
| `stress_042_one_large_suffix_n4_fee0` | `True` | `4` | `0` | `24` | `[192, 4850]` |
| `stress_043_near_tie_pairs_n5_fee1` | `True` | `5` | `1` | `120` | `[124, 1197]` |
| `stress_044_seeded_random_n6_fee2` | `True` | `6` | `2` | `720` | `[437, 11821]` |
| `stress_045_flat_n2_fee5` | `True` | `2` | `5` | `2` | `[16, 1973]` |
| `stress_046_ascending_n3_fee30` | `True` | `3` | `30` | `6` | `[39, 641]` |
| `stress_047_descending_n4_fee75` | `True` | `4` | `75` | `24` | `[86, 3515]` |
| `stress_048_fibonacci_n5_fee100` | `True` | `5` | `100` | `120` | `[131, 7474]` |
| `stress_049_alternating_n6_fee0` | `True` | `6` | `0` | `720` | `[270, 21482]` |
| `stress_050_one_large_prefix_n2_fee1` | `True` | `2` | `1` | `2` | `[183, 7089]` |
| `stress_051_one_large_suffix_n3_fee2` | `True` | `3` | `2` | `6` | `[196, 6277]` |
| `stress_052_near_tie_pairs_n4_fee5` | `True` | `4` | `5` | `24` | `[98, 5045]` |
| `stress_053_seeded_random_n5_fee30` | `True` | `5` | `30` | `120` | `[340, 19292]` |
| `stress_054_flat_n6_fee75` | `True` | `6` | `75` | `720` | `[72, 2002]` |
| `stress_055_ascending_n2_fee100` | `True` | `2` | `100` | `2` | `[21, 156]` |
| `stress_056_descending_n3_fee0` | `True` | `3` | `0` | `6` | `[57, 6581]` |
| `stress_057_fibonacci_n4_fee1` | `True` | `4` | `1` | `24` | `[76, 1457]` |
| `stress_058_alternating_n5_fee2` | `True` | `5` | `2` | `120` | `[188, 19326]` |
| `stress_059_one_large_prefix_n6_fee5` | `True` | `6` | `5` | `720` | `[242, 27332]` |
| `stress_060_one_large_suffix_n2_fee30` | `True` | `2` | `30` | `2` | `[196, 3104]` |
| `stress_061_near_tie_pairs_n3_fee75` | `True` | `3` | `75` | `6` | `[73, 4069]` |
| `stress_062_seeded_random_n4_fee100` | `True` | `4` | `100` | `24` | `[446, 63360]` |
| `stress_063_flat_n5_fee0` | `True` | `5` | `0` | `120` | `[55, 965]` |
| `stress_064_ascending_n6_fee1` | `True` | `6` | `1` | `720` | `[123, 3027]` |
| `stress_065_descending_n2_fee2` | `True` | `2` | `2` | `2` | `[33, 700]` |
| `stress_066_fibonacci_n3_fee5` | `True` | `3` | `5` | `6` | `[42, 968]` |
| `stress_067_alternating_n4_fee30` | `True` | `4` | `30` | `24` | `[172, 6747]` |
| `stress_068_one_large_prefix_n5_fee75` | `True` | `5` | `75` | `120` | `[247, 16580]` |
| `stress_069_one_large_suffix_n6_fee100` | `True` | `6` | `100` | `720` | `[267, 14894]` |
| `stress_070_near_tie_pairs_n2_fee0` | `True` | `2` | `0` | `2` | `[48, 1176]` |
| `stress_071_seeded_random_n3_fee1` | `True` | `3` | `1` | `6` | `[428, 17465]` |
| `stress_072_flat_n4_fee2` | `True` | `4` | `2` | `24` | `[40, 2606]` |
| `stress_073_ascending_n5_fee5` | `True` | `5` | `5` | `120` | `[90, 5002]` |
| `stress_074_descending_n6_fee30` | `True` | `6` | `30` | `720` | `[159, 8905]` |
| `stress_075_fibonacci_n2_fee75` | `True` | `2` | `75` | `2` | `[21, 357]` |
| `stress_076_alternating_n3_fee100` | `True` | `3` | `100` | `6` | `[107, 5082]` |
| `stress_077_one_large_prefix_n4_fee0` | `True` | `4` | `0` | `24` | `[190, 5880]` |
| `stress_078_one_large_suffix_n5_fee1` | `True` | `5` | `1` | `120` | `[204, 3389]` |
| `stress_079_near_tie_pairs_n6_fee2` | `True` | `6` | `2` | `720` | `[150, 8737]` |
| `stress_080_seeded_random_n2_fee5` | `True` | `2` | `5` | `2` | `[209, 14668]` |
| `stress_081_flat_n3_fee30` | `True` | `3` | `30` | `6` | `[27, 223]` |
| `stress_082_ascending_n4_fee75` | `True` | `4` | `75` | `24` | `[62, 4722]` |
| `stress_083_descending_n5_fee100` | `True` | `5` | `100` | `120` | `[120, 7615]` |
| `stress_084_fibonacci_n6_fee0` | `True` | `6` | `0` | `720` | `[220, 10124]` |
| `stress_085_alternating_n2_fee1` | `True` | `2` | `1` | `2` | `[93, 3743]` |
| `stress_086_one_large_prefix_n3_fee2` | `True` | `3` | `2` | `6` | `[194, 9196]` |
| `stress_087_one_large_suffix_n4_fee5` | `True` | `4` | `5` | `24` | `[209, 12460]` |
| `stress_088_near_tie_pairs_n5_fee30` | `True` | `5` | `30` | `120` | `[124, 6074]` |
| `stress_089_seeded_random_n6_fee75` | `True` | `6` | `75` | `720` | `[532, 57413]` |
| `stress_090_flat_n2_fee100` | `True` | `2` | `100` | `2` | `[16, 610]` |
| `stress_091_ascending_n3_fee0` | `True` | `3` | `0` | `6` | `[39, 2360]` |
| `stress_092_descending_n4_fee1` | `True` | `4` | `1` | `24` | `[86, 14788]` |
| `stress_093_fibonacci_n5_fee2` | `True` | `5` | `2` | `120` | `[131, 11453]` |
| `stress_094_alternating_n6_fee5` | `True` | `6` | `5` | `720` | `[273, 10667]` |
| `stress_095_one_large_prefix_n2_fee30` | `True` | `2` | `30` | `2` | `[194, 18459]` |
| `stress_096_one_large_suffix_n3_fee75` | `True` | `3` | `75` | `6` | `[210, 6578]` |
| `stress_097_near_tie_pairs_n4_fee100` | `True` | `4` | `100` | `24` | `[98, 8016]` |
| `stress_098_seeded_random_n5_fee0` | `True` | `5` | `0` | `120` | `[629, 8973]` |
| `stress_099_flat_n6_fee1` | `True` | `6` | `1` | `720` | `[72, 2396]` |
| `stress_100_ascending_n2_fee2` | `True` | `2` | `2` | `2` | `[21, 120]` |
| `stress_101_descending_n3_fee5` | `True` | `3` | `5` | `6` | `[57, 1968]` |
| `stress_102_fibonacci_n4_fee30` | `True` | `4` | `30` | `24` | `[76, 2916]` |
| `stress_103_alternating_n5_fee75` | `True` | `5` | `75` | `120` | `[190, 11037]` |
| `stress_104_one_large_prefix_n6_fee100` | `True` | `6` | `100` | `720` | `[265, 22535]` |
| `stress_105_one_large_suffix_n2_fee0` | `True` | `2` | `0` | `2` | `[200, 18047]` |
| `stress_106_near_tie_pairs_n3_fee1` | `True` | `3` | `1` | `6` | `[73, 7845]` |
| `stress_107_seeded_random_n4_fee2` | `True` | `4` | `2` | `24` | `[361, 69154]` |
| `stress_108_flat_n5_fee5` | `True` | `5` | `5` | `120` | `[55, 2115]` |
| `stress_109_ascending_n6_fee30` | `True` | `6` | `30` | `720` | `[123, 1912]` |
| `stress_110_descending_n2_fee75` | `True` | `2` | `75` | `2` | `[33, 2561]` |
| `stress_111_fibonacci_n3_fee100` | `True` | `3` | `100` | `6` | `[42, 2078]` |
| `stress_112_alternating_n4_fee0` | `True` | `4` | `0` | `24` | `[174, 8695]` |
| `stress_113_one_large_prefix_n5_fee1` | `True` | `5` | `1` | `120` | `[202, 7332]` |
| `stress_114_one_large_suffix_n6_fee2` | `True` | `6` | `2` | `720` | `[218, 14355]` |
| `stress_115_near_tie_pairs_n2_fee5` | `True` | `2` | `5` | `2` | `[48, 1637]` |
| `stress_116_seeded_random_n3_fee30` | `True` | `3` | `30` | `6` | `[235, 10255]` |
| `stress_117_flat_n4_fee75` | `True` | `4` | `75` | `24` | `[40, 1460]` |
| `stress_118_ascending_n5_fee100` | `True` | `5` | `100` | `120` | `[90, 3155]` |
| `stress_119_descending_n6_fee0` | `True` | `6` | `0` | `720` | `[159, 9879]` |
| `stress_120_fibonacci_n2_fee1` | `True` | `2` | `1` | `2` | `[21, 936]` |
| `stress_121_alternating_n3_fee2` | `True` | `3` | `2` | `6` | `[97, 3570]` |
| `stress_122_one_large_prefix_n4_fee5` | `True` | `4` | `5` | `24` | `[207, 5349]` |
| `stress_123_one_large_suffix_n5_fee30` | `True` | `5` | `30` | `120` | `[224, 14846]` |
| `stress_124_near_tie_pairs_n6_fee75` | `True` | `6` | `75` | `720` | `[150, 23693]` |
| `stress_125_seeded_random_n2_fee100` | `True` | `2` | `100` | `2` | `[156, 7705]` |
| `stress_126_flat_n3_fee0` | `True` | `3` | `0` | `6` | `[27, 1755]` |
| `stress_127_ascending_n4_fee1` | `True` | `4` | `1` | `24` | `[62, 2803]` |
| `stress_128_descending_n5_fee2` | `True` | `5` | `2` | `120` | `[120, 7980]` |
| `stress_129_fibonacci_n6_fee5` | `True` | `6` | `5` | `720` | `[220, 8441]` |
| `stress_130_alternating_n2_fee30` | `True` | `2` | `30` | `2` | `[94, 2989]` |
| `stress_131_one_large_prefix_n3_fee75` | `True` | `3` | `75` | `6` | `[208, 1758]` |
| `stress_132_one_large_suffix_n4_fee100` | `True` | `4` | `100` | `24` | `[226, 17875]` |
| `stress_133_near_tie_pairs_n5_fee0` | `True` | `5` | `0` | `120` | `[124, 6288]` |
| `stress_134_seeded_random_n6_fee1` | `True` | `6` | `1` | `720` | `[435, 20959]` |
| `stress_135_flat_n2_fee2` | `True` | `2` | `2` | `2` | `[16, 435]` |
| `stress_136_ascending_n3_fee5` | `True` | `3` | `5` | `6` | `[39, 5508]` |
| `stress_137_descending_n4_fee30` | `True` | `4` | `30` | `24` | `[86, 925]` |
| `stress_138_fibonacci_n5_fee75` | `True` | `5` | `75` | `120` | `[131, 7507]` |
| `stress_139_alternating_n6_fee100` | `True` | `6` | `100` | `720` | `[276, 18557]` |
| `stress_140_one_large_prefix_n2_fee0` | `True` | `2` | `0` | `2` | `[198, 4120]` |
| `stress_141_one_large_suffix_n3_fee1` | `True` | `3` | `1` | `6` | `[210, 12040]` |
| `stress_142_near_tie_pairs_n4_fee2` | `True` | `4` | `2` | `24` | `[98, 9036]` |
| `stress_143_seeded_random_n5_fee5` | `True` | `5` | `5` | `120` | `[395, 14107]` |
| `stress_144_flat_n6_fee30` | `True` | `6` | `30` | `720` | `[72, 15909]` |
| `stress_145_ascending_n2_fee75` | `True` | `2` | `75` | `2` | `[21, 545]` |
| `stress_146_descending_n3_fee100` | `True` | `3` | `100` | `6` | `[57, 2556]` |
| `stress_147_fibonacci_n4_fee0` | `True` | `4` | `0` | `24` | `[76, 4675]` |
| `stress_148_alternating_n5_fee1` | `True` | `5` | `1` | `120` | `[192, 2263]` |
| `stress_149_one_large_prefix_n6_fee2` | `True` | `6` | `2` | `720` | `[216, 8076]` |
| `stress_150_one_large_suffix_n2_fee5` | `True` | `2` | `5` | `2` | `[174, 11028]` |
| `stress_151_near_tie_pairs_n3_fee30` | `True` | `3` | `30` | `6` | `[73, 3210]` |
| `stress_152_seeded_random_n4_fee75` | `True` | `4` | `75` | `24` | `[369, 18841]` |
| `stress_153_flat_n5_fee100` | `True` | `5` | `100` | `120` | `[55, 2259]` |
| `stress_154_ascending_n6_fee0` | `True` | `6` | `0` | `720` | `[123, 3111]` |
| `stress_155_descending_n2_fee1` | `True` | `2` | `1` | `2` | `[33, 468]` |
| `stress_156_fibonacci_n3_fee2` | `True` | `3` | `2` | `6` | `[42, 2704]` |
| `stress_157_alternating_n4_fee5` | `True` | `4` | `5` | `24` | `[176, 2625]` |
| `stress_158_one_large_prefix_n5_fee30` | `True` | `5` | `30` | `120` | `[222, 19634]` |
| `stress_159_one_large_suffix_n6_fee75` | `True` | `6` | `75` | `720` | `[241, 26574]` |
| `stress_160_near_tie_pairs_n2_fee100` | `True` | `2` | `100` | `2` | `[48, 2819]` |
| `stress_161_seeded_random_n3_fee0` | `True` | `3` | `0` | `6` | `[216, 34867]` |
| `stress_162_flat_n4_fee1` | `True` | `4` | `1` | `24` | `[40, 3569]` |
| `stress_163_ascending_n5_fee2` | `True` | `5` | `2` | `120` | `[90, 7317]` |
| `stress_164_descending_n6_fee5` | `True` | `6` | `5` | `720` | `[159, 4277]` |
| `stress_165_fibonacci_n2_fee30` | `True` | `2` | `30` | `2` | `[21, 1480]` |
| `stress_166_alternating_n3_fee75` | `True` | `3` | `75` | `6` | `[98, 3199]` |
| `stress_167_one_large_prefix_n4_fee100` | `True` | `4` | `100` | `24` | `[224, 4819]` |
| `stress_168_one_large_suffix_n5_fee0` | `True` | `5` | `0` | `120` | `[216, 15988]` |
| `stress_169_near_tie_pairs_n6_fee1` | `True` | `6` | `1` | `720` | `[150, 4694]` |
| `stress_170_seeded_random_n2_fee2` | `True` | `2` | `2` | `2` | `[178, 19228]` |
| `stress_171_flat_n3_fee5` | `True` | `3` | `5` | `6` | `[27, 4370]` |
| `stress_172_ascending_n4_fee30` | `True` | `4` | `30` | `24` | `[62, 3100]` |
| `stress_173_descending_n5_fee75` | `True` | `5` | `75` | `120` | `[120, 4363]` |
| `stress_174_fibonacci_n6_fee100` | `True` | `6` | `100` | `720` | `[220, 10193]` |
| `stress_175_alternating_n2_fee0` | `True` | `2` | `0` | `2` | `[95, 15610]` |
| `stress_176_one_large_prefix_n3_fee1` | `True` | `3` | `1` | `6` | `[208, 20578]` |
| `stress_177_one_large_suffix_n4_fee2` | `True` | `4` | `2` | `24` | `[222, 20838]` |
| `stress_178_near_tie_pairs_n5_fee5` | `True` | `5` | `5` | `120` | `[124, 23190]` |
| `stress_179_seeded_random_n6_fee30` | `True` | `6` | `30` | `720` | `[698, 40062]` |

## Mutation Summary

| mutation | accepted count |
| --- | ---: |
| `authority_effect_present` | `0` |
| `bad_packet_hash` | `0` |
| `child_mask_missing_bit` | `0` |
| `child_processed_reserve_in_mismatch` | `0` |
| `child_selected_family_beats_winner` | `0` |
| `child_selected_not_local_min` | `0` |
| `child_selected_not_record` | `0` |
| `economic_key_mismatch` | `0` |
| `executed_input_mismatch` | `0` |
| `selected_no_longer_dominates` | `0` |
| `winner_empty_suffix` | `0` |
| `winner_missing_full_mask_bit` | `0` |
| `winner_removed_from_children` | `0` |

## Non-Claims

- This checker does not prove generation of the full child frontier.
- This checker does not prove recursive subset-mask induction.
- This checker does not prove Lean-to-Python refinement.
- This checker does not define canonical tie order.
- Nonzero min_amount_out batches are outside this artifact.
- Host bitset equivalence remains a separate proof obligation.
- No settlement authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_observed_frontier_witness.py
```
