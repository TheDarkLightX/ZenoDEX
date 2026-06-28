# ZenoDEX Exact-In Staircase Hostile Certificate - 2026-06-28

## Executive Result

The two-pool CPMM exact-in staircase profile matched brute force on a deterministic hostile corpus and reduced profile-benchmark quote calls while keeping runtime default selection unchanged.

Advisory routing evidence only; this certificate does not change default routing, settle swaps, mutate pools, or authorize production promotion.

## Tau Certificate

- Spec: `src/tau_specs/recommended/exact_in_staircase_hostile_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau cases: `10`
- Invalid accepts: `0`

Certificate facts:
- `certificate_active` = `1`
- `bounded_corpus_ok` = `1`
- `brute_force_parity_ok` = `1`
- `leftmost_tie_break_ok` = `1`
- `quote_count_lift_ok` = `1`
- `known_gap_recovered` = `1`
- `baseline_gap_observed` = `1`
- `guarded_packet_replay_ok` = `1`
- `runtime_default_unchanged` = `1`
- `advisory_only` = `1`
- `no_authority_effect` = `1`

## Hostile Corpus

- Total cases: `136`
- Brute-force comparable cases: `134`
- Mismatches: `0`
- Leftmost tie mismatches: `0`
- Families: `14`

## Profile Benchmark

- Oracle quote calls: `101437`
- Staircase quote calls: `4112`
- Quote-count ratio vs oracle: `24.669`

| profile | oracle matches | total quotes | max quotes |
| --- | ---: | ---: | ---: |
| `adaptive_v6` | `6` | `80010` | `19322` |
| `dense24` | `5` | `54936` | `11606` |
| `staircase_exact` | `6` | `4112` | `3750` |

## Known Gap And Guarded Packet

- Baseline gap observed: `True`
- Staircase recovers gap: `True`
- Guard ok: `True`
- Packet verifier ok: `True`

## Tau Negative Cases

| case | ok | primary output |
| --- | --- | ---: |
| `certificate_pass` | `True` | `1` |
| `parity_reject` | `True` | `0` |
| `tie_break_reject` | `True` | `0` |
| `quote_lift_reject` | `True` | `0` |
| `gap_recovery_reject` | `True` | `0` |
| `baseline_gap_reject` | `True` | `0` |
| `guarded_packet_reject` | `True` | `0` |
| `default_change_reject` | `True` | `0` |
| `authority_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This does not change the live default split-routing profile.
- This is a two-pool CPMM exact-in integer-routing certificate, not a general CFMM network optimizer.
- The quote-count lift is measured on the declared bounded profile benchmark, not every possible pool configuration.
- Guarded packet replay proves certificate compatibility only for the replayed packet shape.

## Replay

```bash
python3 tools/zenodex_staircase_hostile_certificate_20260628.py
```
