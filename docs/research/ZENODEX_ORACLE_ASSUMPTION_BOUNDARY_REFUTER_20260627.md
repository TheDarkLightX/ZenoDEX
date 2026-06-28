# Zeno Oracle Assumption Boundary Refuter - 2026-06-27

## Executive Result

This artifact checks that the oracle Tau envelope rejects hidden assumptions and missing authority-boundary facts when host-computed flags are used.
Cases: `8`. Negative cases: `7`. Forged declared Tau admits: `7`. Computed-flag false admits: `0`. Overall: `ok=True`.

Result: Tau is a compact guard for declared proof-surface facts; the host must compute those facts from replayed interval, assumption, and authority evidence.

## Cases

| case | host ok | Tau with declared flags | Tau with computed flags | failed flags |
| --- | --- | --- | --- | --- |
| `valid_oracle_envelope_accepts` | `True` | `True` | `True` | none |
| `missing_boundary_walls_rejects` | `False` | `True` | `False` | `i7` |
| `hidden_mev_assumption_rejects` | `False` | `True` | `False` | `i8` |
| `hidden_probability_assumption_rejects` | `False` | `True` | `False` | `i9` |
| `oracle_update_authority_rejects` | `False` | `True` | `False` | `i10` |
| `missing_fail_closed_default_rejects` | `False` | `True` | `False` | `i11` |
| `point_verifier_parity_missing_rejects` | `False` | `True` | `False` | `i6` |
| `honest_challenge_interval_missing_rejects` | `False` | `True` | `False` | `i3` |

## Non-Claims

- This refuter checks the Tau proof-surface boundary; it does not estimate MEV, probability, or oracle truth.
- Forged all-true flags can still admit, so host computation of facts remains mandatory.
- The pointwise economic-security verifier remains authoritative.

## Replay

```bash
python3 tools/zenodex_oracle_assumption_boundary_refuter_20260627.py
```
