# ZenoDEX AB Strict Zero-Min Reserve-State Quotient Certificate - 2026-06-29

## Executive Result

A reserve-state quotient certificate checker supports a smaller host witness shape for the n=7 strict zero-min corpus by grouping full order histories by processed reserve-in and reserve-out.

Research-only certificate-compression evidence; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Cases checked: `4`
- Valid cases: `4`
- Reachable masks checked: `512`
- Full records: `54800`
- Quotient states: `868`
- Record compression ratio: `63.133641`
- Lean observed-summary rows: `54800`
- Full dominance checks: `161280`
- Quotient dominance checks: `59987`
- Dominance-check compression ratio: `2.688583`
- Negative controls: `12`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Coverage

- `n` histogram: `{'7': 4}`
- Fee histogram: `{'1': 1, '100': 2, '9000': 1}`
- Regime/pattern histogram: `{'high_fee_deep_out/rand_stair': 1, 'near_domain_in/rand_burst': 1, 'near_zero_positive/rand_tie': 1, 'thin_positive_boundary/high_fee9000': 1}`
- Reason classes: `['authority_effect_present', 'compressed_record_missing', 'packet_first_obligation_mismatch', 'packet_hash_bound_missing', 'packet_hash_mismatch', 'packet_lean_contract_mismatch', 'packet_lean_observed_summary_mismatch', 'packet_mask_summaries_mismatch', 'packet_quotient_summary_mismatch', 'quotient_family_bound_missing', 'quotient_suffix_not_executable', 'reserve_state_only_bound_missing', 'selected_final_reserve_dominance_failure', 'selected_reserve_out_not_min', 'selected_state_not_in_quotient_family', 'selected_suffix_not_executable']`
- Max full records per mask: `5040`
- Max quotient states per mask: `5`
- Max suffixes per mask: `5040`
- Lean observed-summary digest: `74b4504376152ca62f08eb4fa0d2016eefc160487fd6ad5a88f0da6be8104bcf`

## Lean Projection Shape

```json
{
  "host_table": "ReserveStateQuotientHostTable",
  "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
  "projection_shape": "one_digest_row_per_reachable_mask_completion_suffix",
  "summary_endpoint": "reserveStateQuotientObservedSummary_validates",
  "summary_structure": "ReserveStateQuotientObservedSummary",
  "summary_valid_predicate": "reserveStateQuotientObservedSummaryValid"
}
```

Each digest row binds the observed summary fields used by
`reserveStateQuotientObservedSummary_validates`: quotient-state count, selected
reserve-in, selected reserve-out, completed gross input, initial output reserve,
selected-state digest, quotient-state digest, and one fixed completion suffix.

## First Case

```json
{
  "baseline_full_dominance_check_count": 40320,
  "bit_count": 7,
  "case_id": "n7_randomized_boundary_000_thin_fee9000_rout1100",
  "dominance_check_compression_saved": 26620,
  "fee_bps": 9000,
  "first_failure": null,
  "first_obligation": {
    "mask_id": 0,
    "quotient_digest": "74bfe2d98beff0789bbfc93d60ca66d200bedcd09aac3477d1548fe912a9ed49",
    "quotient_state_count": 1,
    "selected_state": {
      "processed_reserve_in": 10000,
      "reserve_out": 1100
    },
    "suffix_short": [
      "f5c0",
      "f5c1",
      "f5c2",
      "f5c3",
      "f5c4",
      "f5c5",
      "f5c6"
    ]
  },
  "full_mask_selected_state": {
    "processed_reserve_in": 10721,
    "reserve_out": 1093
  },
  "full_record_count": 13700,
  "lean_observed_summary": {
    "contract": {
      "host_table": "ReserveStateQuotientHostTable",
      "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
      "projection_shape": "one_digest_row_per_reachable_mask_completion_suffix",
      "summary_endpoint": "reserveStateQuotientObservedSummary_validates",
      "summary_structure": "ReserveStateQuotientObservedSummary",
      "summary_valid_predicate": "reserveStateQuotientObservedSummaryValid"
    },
    "digest": "471133f0bf28bcf0947c7fffc810cc4e3759f449a3f618877c2d8fdd2574bcbe",
    "first_row": {
      "lean_endpoint": "reserveStateQuotientObservedSummary_validates",
      "lean_structure": "ReserveStateQuotientObservedSummary",
      "mask_id": 0,
      "observed_executed_input": 721,
      "observed_initial_reserve_out": 1100,
      "observed_selected_reserve_in": 10000,
      "observed_selected_reserve_out": 1100,
      "observed_state_count": 1,
      "selected_state_digest": "bd9d9dfd318aac5e489dbd081b4535164c8759e8bb713dacf6a3273f30544fc3",
      "suffix_order_ids": [
        "0x00000000000000000000000000000000000000000000000000000000006cf5c0",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c1",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c2",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c3",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c4",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c5",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c6"
      ],
      "suffix_short": [
        "f5c0",
        "f5c1",
        "f5c2",
        "f5c3",
        "f5c4",
        "f5c5",
        "f5c6"
      ],
      "table_state_digest": "74bfe2d98beff0789bbfc93d60ca66d200bedcd09aac3477d1548fe912a9ed49"
    },
    "row_count": 13700
  },
  "mask_count": 128,
  "max_full_records_per_mask": 5040,
  "max_quotient_states_per_mask": 1,
  "max_suffix_per_mask": 5040,
  "ok": true,
  "packet_hash": "73ea1061a7002df6a9ac27ce650e2a67725e90c2b339f328fd46b9cdb92262b9",
  "pattern": "thin_positive_boundary/high_fee9000",
  "quotient_dominance_check_count": 13700,
  "quotient_obligation_digest": "214fe5ba1ba93e8487e05e60001be1e160e98933504843946ba10ea38db9f3a5",
  "quotient_runtime_completion_count": 13700,
  "quotient_state_count": 128,
  "quotient_table_obligation_count": 13700,
  "reasons": [],
  "record_compression_saved": 13572,
  "selected_suffix_executable_count": 13700
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `packet_hash_bound_missing` | `False` | `packet_hash_bound_missing` |
| `authority_effect_present` | `False` | `authority_effect_present` |
| `quotient_family_bound_missing` | `False` | `quotient_family_bound_missing` |
| `reserve_state_only_bound_missing` | `False` | `reserve_state_only_bound_missing` |
| `packet_lean_contract_mismatch` | `False` | `packet_lean_contract_mismatch` |
| `packet_lean_observed_summary_mismatch` | `False` | `packet_lean_observed_summary_mismatch` |
| `compressed_record_missing` | `False` | `compressed_record_missing` |
| `selected_state_not_in_quotient_family` | `False` | `selected_state_not_in_quotient_family` |
| `selected_reserve_out_not_min` | `False` | `selected_reserve_out_not_min` |
| `selected_suffix_not_executable` | `False` | `selected_suffix_not_executable` |
| `packet_quotient_summary_mismatch` | `False` | `packet_quotient_summary_mismatch` |

## Case Summary

| case | ok | full records | quotient states | record ratio | dominance ratio |
| --- | --- | ---: | ---: | ---: | ---: |
| `n7_randomized_boundary_000_thin_fee9000_rout1100` | `True` | `13700` | `128` | `107.03125` | `2.943066` |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1` | `True` | `13700` | `321` | `42.679128` | `2.397859` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100` | `True` | `13700` | `291` | `47.079038` | `2.556429` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100` | `True` | `13700` | `128` | `107.03125` | `2.943066` |

## Non-Claims

- This quotient checker is bounded to the committed n=7 randomized corpus.
- This checker does not prove Lean-to-Python refinement.
- This checker does not define canonical tie order or preserve order-id history.
- This checker does not cover nonzero min_amount_out certificates.
- This checker is not a Lean endpoint or production ABI.
- No settlement, state-root, production, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_reserve_state_quotient_certificate.py
```
