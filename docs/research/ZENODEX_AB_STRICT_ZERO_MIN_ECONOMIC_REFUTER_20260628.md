# ZenoDEX AB Strict Zero-Min Economic Refuter - 2026-06-28

## Executive Result

A deterministic stress refuter found no economic-key mismatch inside the strict executable zero-min AB compression surface, while refuting simple amount-sorted greedy replacements.

This is research evidence only. It does not select production AB orders or authorize settlement.

## Search Summary

- Seed: `2026062802`
- Random cases: `600`
- Strict executable zero-min cases: `330`
- Non-strict skipped cases: `270`
- Brute-force cross-checks: `80`
- Economic-key mismatches: `0`
- Brute-force mismatches: `0`
- Ascending amount-greedy failures: `214`
- Descending amount-greedy failures: `161`

The strict surface requires a compressed executable full-mask order. Cases outside that surface are skipped rather than treated as support.

## First Ascending Greedy Failure

```json
{
  "amounts": [
    21,
    21,
    89,
    21,
    8,
    89,
    55,
    55
  ],
  "ascending_amount_greedy_ok": false,
  "ascending_amount_key": [
    359,
    456
  ],
  "ascending_amount_order": [
    "93f8",
    "93f4",
    "93f5",
    "93f7",
    "93fa",
    "93fb",
    "93f6",
    "93f9"
  ],
  "brute_checked": false,
  "brute_economic_key": null,
  "brute_order": null,
  "case_no": 1,
  "compressed_economic_key": [
    359,
    460
  ],
  "compressed_order": [
    "93f4",
    "93f6",
    "93fa",
    "93f5",
    "93f9",
    "93f7",
    "93fb",
    "93f8"
  ],
  "descending_amount_greedy_ok": false,
  "descending_amount_key": [
    359,
    457
  ],
  "descending_amount_order": [
    "93f6",
    "93f9",
    "93fa",
    "93fb",
    "93f4",
    "93f5",
    "93f7",
    "93f8"
  ],
  "economic_parity_ok": true,
  "full_economic_key": [
    359,
    460
  ],
  "full_order": [
    "93f4",
    "93f6",
    "93fa",
    "93f5",
    "93f9",
    "93f7",
    "93fb",
    "93f8"
  ],
  "n": 8,
  "pool": {
    "fee_bps": 75,
    "reserve0": 681,
    "reserve1": 1360
  },
  "strict_scope": true
}
```

## First Descending Greedy Failure

```json
{
  "amounts": [
    21,
    21,
    89,
    21,
    8,
    89,
    55,
    55
  ],
  "ascending_amount_greedy_ok": false,
  "ascending_amount_key": [
    359,
    456
  ],
  "ascending_amount_order": [
    "93f8",
    "93f4",
    "93f5",
    "93f7",
    "93fa",
    "93fb",
    "93f6",
    "93f9"
  ],
  "brute_checked": false,
  "brute_economic_key": null,
  "brute_order": null,
  "case_no": 1,
  "compressed_economic_key": [
    359,
    460
  ],
  "compressed_order": [
    "93f4",
    "93f6",
    "93fa",
    "93f5",
    "93f9",
    "93f7",
    "93fb",
    "93f8"
  ],
  "descending_amount_greedy_ok": false,
  "descending_amount_key": [
    359,
    457
  ],
  "descending_amount_order": [
    "93f6",
    "93f9",
    "93fa",
    "93fb",
    "93f4",
    "93f5",
    "93f7",
    "93f8"
  ],
  "economic_parity_ok": true,
  "full_economic_key": [
    359,
    460
  ],
  "full_order": [
    "93f4",
    "93f6",
    "93fa",
    "93f5",
    "93f9",
    "93f7",
    "93fb",
    "93f8"
  ],
  "n": 8,
  "pool": {
    "fee_bps": 75,
    "reserve0": 681,
    "reserve1": 1360
  },
  "strict_scope": true
}
```

## Non-Claims

- This is not a proof of the strict executable zero-min compression theorem.
- Canonical tie order remains outside the economic-key claim.
- Zero-min cases without a compressed executable full-mask order are outside this strict surface.
- Nonzero min_amount_out batches remain outside this compression surface.
- Amount-sorted greedy orders are refuted as replacements for the one-record DP.
- No settlement authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_economic_refuter.py
```
