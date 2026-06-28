# ZenoDEX AB Strict Zero-Min Exhaustive Small Refuter - 2026-06-28

## Executive Result

A deterministic exhaustive small-grid refuter found no strict-scope economic-key mismatch for one-record min-reserve-out compression, while preserving explicit overbroad zero-min boundary witnesses.

Research evidence only. This artifact does not select production AB orders or authorize settlement.

## Grid

```json
{
  "amount_values_by_n": {
    "2": [
      1,
      2,
      3,
      5,
      8
    ],
    "3": [
      1,
      2,
      3,
      5
    ],
    "4": [
      1,
      2,
      3
    ]
  },
  "fee_bps_values": [
    0,
    1,
    30
  ],
  "reserve_in_values": [
    3,
    5,
    8,
    13,
    21
  ],
  "reserve_out_values": [
    3,
    5,
    8,
    13,
    21,
    34
  ]
}
```

## Search Summary

- Cases: `15300`
- Strict-scope cases: `4298`
- Strict-scope economic mismatches: `0`
- Overbroad zero-min boundary witnesses: `24`

The strict surface requires the compressed full-mask order to execute all intents. Boundary witnesses are kept as non-claim evidence against the broader zero-min surface.

## First Overbroad Zero-Min Boundary

```json
{
  "amounts": [
    2,
    3,
    3
  ],
  "brute_key": [
    8,
    5
  ],
  "brute_order": [
    "caf6",
    "caf7",
    "caf8"
  ],
  "case_no": 1071,
  "compressed_key": [
    -1,
    -1
  ],
  "compressed_order": [],
  "fee_bps": 0,
  "full_key": [
    8,
    5
  ],
  "full_order": [
    "caf6",
    "caf7",
    "caf8"
  ],
  "n": 3,
  "overbroad_zero_min_boundary": true,
  "reserve_in": 3,
  "reserve_out": 8,
  "strict_economic_parity_ok": false,
  "strict_scope": false,
  "total_input": 8
}
```

## Non-Claims

- This is not a proof of the full strict executable zero-min compression theorem.
- The grid is finite and intentionally small.
- Canonical tie order remains outside the economic-key claim.
- Zero-min cases where compressed full-mask execution fails remain outside the strict supported surface.
- Nonzero min_amount_out batches remain outside this compression surface.
- No settlement authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_exhaustive_small.py
```
