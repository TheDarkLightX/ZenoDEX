# ZenoDEX Perps Risk Antichain Breakthrough - 2026-06-28

## Executive Result

A bounded primitive perps risk lattice compresses dense scenario replay to a minimal rejection antichain while stale-Oracle and active-breaker states remain fail-closed.

Research certificate only. Tau has no settlement, liquidation, oracle-update, or state-root authority.

- Spec: `src/tau_specs/recommended/perp_risk_antichain_certificate_v1.tau`
- Direct risk spec: `src/tau_specs/recommended/perp_risk_envelope_proof_gate_v1.tau`
- Tau version: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Dense risk states: `4096`
- Minimal overall rejection antichain: `12`
- Compression: `4096:12`
- Certificate invalid accepts: `0`

## Minimal Overall Rejection Antichain

| boundary | reason |
| --- | --- |
| `['binding_missing']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['breaker_active_flag']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['funding_cap_bad']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['insurance_floor_bad']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['liq_penalty_cap_bad']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['margin_bad']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['mark_drift_bad']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['mark_oracle_gap_bad']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['open_interest_cap_bad']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['oracle_drift_bad']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['proof_missing']` | Any one of these primitive failures rejects the overall risk envelope. |
| `['stale_oracle_flag']` | Any one of these primitive failures rejects the overall risk envelope. |

Stale-Oracle and active-breaker flags are independent minimal rejection boundaries. Proof availability cannot override either guard.

## Tau Certificate Cases

| case | ok | primary |
| --- | --- | ---: |
| `antichain_certificate_pass` | `True` | `1` |
| `monotonicity_reject` | `True` | `0` |
| `minimal_antichain_reject` | `True` | `0` |
| `component_coverage_reject` | `True` | `0` |
| `containment_replay_reject` | `True` | `0` |
| `tau_parity_reject` | `True` | `0` |
| `stale_breaker_fail_closed_reject` | `True` | `0` |
| `authority_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This does not change perps runtime risk-gate semantics.
- The antichain is over the declared bounded primitive-risk lattice, not every possible perps market state.
- Tau does not compute numeric risk, enumerate states, liquidate positions, settle funding, or update oracles.
- Proof availability and binding remain host-supplied obligations.

## Replay

```bash
python3 tools/zenodex_perp_risk_antichain_breakthrough_20260628.py
```
