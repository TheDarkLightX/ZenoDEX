# ZenoDEX AB Strict Zero-Min Emitter Witness - 2026-06-29

## Executive Result

A bounded host-side emitter witness packet schema maps strict zero-min compressed-DP outputs to the Lean full-mask economic witness contract and rejects packet mutations.

Research-only witness packets; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Witness packets checked: `8`
- Valid witness packets: `8`
- Packet mutations checked: `56`
- Mutation accepts: `0`
- Deterministic replay ok: `True`

## Lean Contract Mapping

```text
host packet parent/winner/children/bitCount/masks/initialReserveOut/executedInput
  -> StrictCompressedFullMaskEconomicWitness
strict host checks
  -> strictCompressedFullMaskEconomicWitnessValid candidate obligation
Lean endpoint
  -> full-mask coverage, economic-key dominance, empty-suffix executability
```

## First Packet

```json
{
  "amounts": [
    5,
    18
  ],
  "authority_boundary": "research_only_no_settlement_or_state_authority",
  "bit_count": 2,
  "case_id": "n2_variant0",
  "children": [
    {
      "all_records": [
        {
          "order_ids": [
            "0x0000000000000000000000000000000000000000000000000000000000002710",
            "0x0000000000000000000000000000000000000000000000000000000000002711"
          ],
          "order_short": [
            "2710",
            "2711"
          ],
          "processed_reserve_in": 723,
          "reserve_out": 872
        }
      ],
      "all_records_count": 1,
      "all_records_digest": "3ab4deb0f963cc40bdee7a0e2180f9bc49df92ef2aeadfe3a69a6cf5e530c922",
      "mask_id": 3,
      "selected": {
        "order_ids": [
          "0x0000000000000000000000000000000000000000000000000000000000002710",
          "0x0000000000000000000000000000000000000000000000000000000000002711"
        ],
        "order_short": [
          "2710",
          "2711"
        ],
        "processed_reserve_in": 723,
        "reserve_out": 872
      }
    },
    {
      "all_records": [
        {
          "order_ids": [
            "0x0000000000000000000000000000000000000000000000000000000000002711",
            "0x0000000000000000000000000000000000000000000000000000000000002710"
          ],
          "order_short": [
            "2711",
            "2710"
          ],
          "processed_reserve_in": 723,
          "reserve_out": 872
        }
      ],
      "all_records_count": 1,
      "all_records_digest": "a03e974d44bf8e1b75f5d7c055af8483ed8217b6f4c4671f03a327077f02d23c",
      "mask_id": 3,
      "selected": {
        "order_ids": [
          "0x0000000000000000000000000000000000000000000000000000000000002711",
          "0x0000000000000000000000000000000000000000000000000000000000002710"
        ],
        "order_short": [
          "2711",
          "2710"
        ],
        "processed_reserve_in": 723,
        "reserve_out": 872
      }
    }
  ],
  "compressed_table": [
    {
      "mask_id": 0,
      "selected": {
        "order_ids": [],
        "order_short": [],
        "processed_reserve_in": 700,
        "reserve_out": 900
      }
    },
    {
      "mask_id": 1,
      "selected": {
        "order_ids": [
          "0x0000000000000000000000000000000000000000000000000000000000002710"
        ],
        "order_short": [
          "2710"
        ],
        "processed_reserve_in": 705,
        "reserve_out": 894
      }
    },
    {
      "mask_id": 2,
      "selected": {
        "order_ids": [
          "0x0000000000000000000000000000000000000000000000000000000000002711"
        ],
        "order_short": [
          "2711"
        ],
        "processed_reserve_in": 718,
        "reserve_out": 878
      }
    },
    {
      "mask_id": 3,
      "selected": {
        "order_ids": [
          "0x0000000000000000000000000000000000000000000000000000000000002710",
          "0x0000000000000000000000000000000000000000000000000000000000002711"
        ],
        "order_short": [
          "2710",
          "2711"
        ],
        "processed_reserve_in": 723,
        "reserve_out": 872
      }
    }
  ],
  "economic_keys": {
    "brute_force": [
      23,
      28
    ],
    "compressed": [
      23,
      28
    ],
    "full_subset_dp": [
      23,
      28
    ]
  },
  "executed_input": 23,
  "full_mask": 3,
  "initial_reserve_in": 700,
  "initial_reserve_out": 900,
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
            "0x0000000000000000000000000000000000000000000000000000000000002710",
            "0x0000000000000000000000000000000000000000000000000000000000002711"
          ],
          "order_short": [
            "2710",
            "2711"
          ],
          "processed_reserve_in": 723,
          "reserve_out": 872
        }
      ],
      "all_records_count": 1,
      "all_records_digest": "3ab4deb0f963cc40bdee7a0e2180f9bc49df92ef2aeadfe3a69a6cf5e530c922",
      "mask_id": 3,
      "selected": {
        "order_ids": [
          "0x0000000000000000000000000000000000000000000000000000000000002710",
          "0x0000000000000000000000000000000000000000000000000000000000002711"
        ],
        "order_short": [
          "2710",
          "2711"
        ],
        "processed_reserve_in": 723,
        "reserve_out": 872
      }
    }
  ],
  "min_amount_out": [
    0,
    0
  ],
  "no_authority_effect": true,
  "packet_hash": "5405aeb35fbc0276c8819383df83f9f82253c5535a557cd3f11bfeb91ee5bad0",
  "parent": {
    "all_records": [
      {
        "order_ids": [],
        "order_short": [],
        "processed_reserve_in": 700,
        "reserve_out": 900
      }
    ],
    "all_records_count": 1,
    "all_records_digest": "44f96a566c0f635384b260bd46e4a36c14fdd32afad019b8e15d7afba69b4661",
    "mask_id": 0,
    "selected": {
      "order_ids": [],
      "order_short": [],
      "processed_reserve_in": 700,
      "reserve_out": 900
    }
  },
  "pool": {
    "fee_bps": 0,
    "reserve_in": 700,
    "reserve_out": 900
  },
  "schema": "zenodex.ab_strict_zero_min_emitter_witness_packet.v1",
  "scope": "same_pool_same_direction_exact_in_zero_min_strict_executable",
  "winner": {
    "all_records": [
      {
        "order_ids": [
          "0x0000000000000000000000000000000000000000000000000000000000002710",
          "0x0000000000000000000000000000000000000000000000000000000000002711"
        ],
        "order_short": [
          "2710",
          "2711"
        ],
        "processed_reserve_in": 723,
        "reserve_out": 872
      }
    ],
    "all_records_count": 1,
    "all_records_digest": "3ab4deb0f963cc40bdee7a0e2180f9bc49df92ef2aeadfe3a69a6cf5e530c922",
    "mask_id": 3,
    "selected": {
      "order_ids": [
        "0x0000000000000000000000000000000000000000000000000000000000002710",
        "0x0000000000000000000000000000000000000000000000000000000000002711"
      ],
      "order_short": [
        "2710",
        "2711"
      ],
      "processed_reserve_in": 723,
      "reserve_out": 872
    }
  }
}
```

## Case Summary

| case | ok | children | compressed table | key |
| --- | --- | ---: | ---: | --- |
| `n2_variant0` | `True` | `2` | `4` | `[23, 28]` |
| `n2_variant7` | `True` | `2` | `4` | `[66, 80]` |
| `n3_variant0` | `True` | `6` | `8` | `[54, 63]` |
| `n3_variant5` | `True` | `6` | `8` | `[104, 119]` |
| `n4_variant2` | `True` | `24` | `16` | `[154, 162]` |
| `n4_variant6` | `True` | `24` | `16` | `[101, 116]` |
| `n5_variant1` | `True` | `120` | `32` | `[135, 141]` |
| `n6_variant0` | `True` | `720` | `64` | `[170, 175]` |

## Mutation Summary

| mutation | accepted count |
| --- | ---: |
| `authority_effect_present` | `0` |
| `bad_packet_hash` | `0` |
| `economic_key_mismatch` | `0` |
| `executed_input_mismatch` | `0` |
| `selected_no_longer_dominates` | `0` |
| `winner_missing_full_mask_bit` | `0` |
| `winner_removed_from_children` | `0` |

## Non-Claims

- This is a bounded host witness/refuter, not a proof of full compressed-DP induction.
- The packet schema does not prove Lean-to-Python refinement.
- The packet schema does not define canonical tie order.
- Nonzero min_amount_out batches are outside this artifact.
- Host bitset equivalence remains a separate proof obligation.
- No settlement authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_emitter_witness.py
```
