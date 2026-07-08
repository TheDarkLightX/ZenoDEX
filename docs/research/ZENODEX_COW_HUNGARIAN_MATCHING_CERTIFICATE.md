# ZenoDEX CoW Hungarian Matching Certificate - 2026-06-29

## Executive Result

A Tau host-projected certificate gates the uncoupled CoW Hungarian matching surface by requiring balance-scope separation, primal assignment parity, dual certificate consistency, brute-force parity, deterministic pair-id ties, resource limits, replay evidence, grouped-capacity non-claims, and no authority.

The certificate is research evidence only. It does not select production pairs, materialize settlement, mutate balances, mutate pools, or authorize state roots.

## Evidence Summary

- Certificate ok: `True`
- Case count: `25`
- Max candidate count: `12`
- Brute-force mismatches: `0`
- Dual certificate violations: `0`
- Certified assignment mismatches: `0`
- Pair-id tie mismatches: `0`
- Coupled boundary rejects assignment scope: `True`

## Tau Specification

- Spec: `src/tau_specs/recommended/cow_hungarian_matching_certificate_v1.tau`
- Latest Tau available: `True`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau trace replay ok: `True`

## Certificate Flags

| flag | value |
| --- | ---: |
| `balance_scope_ok` | `1` |
| `brute_force_parity_ok` | `1` |
| `deterministic_ties_ok` | `1` |
| `dual_certificate_ok` | `1` |
| `grouped_capacity_fallback_ok` | `1` |
| `no_arbitrary_grouped_capacity_claim` | `1` |
| `no_settlement_authority` | `1` |
| `primal_assignment_ok` | `1` |
| `replay_evidence_ok` | `1` |
| `resource_budget_ok` | `1` |
| `uncoupled_capacity_scope_ok` | `1` |

## Tau Mode Checks

| case | ok | rationale |
| --- | --- | --- |
| `hungarian_certificate_pass` | `True` | All host-projected assignment, boundary, replay, and authority facts admit the certificate. |
| `inactive_safe` | `True` | Inactive certificate does not admit while no-authority remains true. |
| `scope_reject` | `True` | Missing i2 fails the certificate closed. |
| `primal_reject` | `True` | Missing i3 fails the certificate closed. |
| `dual_reject` | `True` | Missing i4 fails the certificate closed. |
| `bruteforce_reject` | `True` | Missing i5 fails the certificate closed. |
| `grouped_fallback_reject` | `True` | Missing i6 fails the certificate closed. |
| `tie_reject` | `True` | Missing i7 fails the certificate closed. |
| `balance_reject` | `True` | Missing i8 fails the certificate closed. |
| `budget_reject` | `True` | Missing i9 fails the certificate closed. |
| `grouped_claim_reject` | `True` | Missing i10 fails the certificate closed. |
| `authority_reject` | `True` | Missing i11 fails the certificate closed. |
| `replay_reject` | `True` | Missing i12 fails the certificate closed. |

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `scope_reject` | `False` | Missing i2 fails the certificate closed. |
| `primal_reject` | `False` | Missing i3 fails the certificate closed. |
| `dual_reject` | `False` | Missing i4 fails the certificate closed. |
| `bruteforce_reject` | `False` | Missing i5 fails the certificate closed. |
| `grouped_fallback_reject` | `False` | Missing i6 fails the certificate closed. |
| `tie_reject` | `False` | Missing i7 fails the certificate closed. |
| `balance_reject` | `False` | Missing i8 fails the certificate closed. |
| `budget_reject` | `False` | Missing i9 fails the certificate closed. |
| `grouped_claim_reject` | `False` | Missing i10 fails the certificate closed. |
| `authority_reject` | `False` | Missing i11 fails the certificate closed. |
| `replay_reject` | `False` | Missing i12 fails the certificate closed. |

## Case Samples

```json
[
  {
    "assignment_balance_safe": true,
    "candidate_count": 4,
    "case_id": "uncoupled_size_2_variant_0",
    "certified_assignment_matches_production": true,
    "dual_certificate_ok": true,
    "pair_count": 2,
    "production_matches_bruteforce": true,
    "same_pair_id_tie": true,
    "surplus": 258,
    "volume": 350
  },
  {
    "assignment_balance_safe": true,
    "candidate_count": 4,
    "case_id": "uncoupled_size_2_variant_1",
    "certified_assignment_matches_production": true,
    "dual_certificate_ok": true,
    "pair_count": 2,
    "production_matches_bruteforce": true,
    "same_pair_id_tie": true,
    "surplus": 258,
    "volume": 410
  },
  {
    "assignment_balance_safe": true,
    "candidate_count": 4,
    "case_id": "uncoupled_size_2_variant_2",
    "certified_assignment_matches_production": true,
    "dual_certificate_ok": true,
    "pair_count": 2,
    "production_matches_bruteforce": true,
    "same_pair_id_tie": true,
    "surplus": 258,
    "volume": 470
  }
]
```

## Non-Claims

- This is an uncoupled CoW Hungarian matching research certificate, not production activation.
- This is not a certificate for grouped-capacity matching; coupled senders require the capacity-DP or fallback boundary.
- The host computes the primal assignment and dual certificate; Tau combines projected facts only.
- No settlement authority, state-root authority, routing authority, pool mutation, or balance mutation is derived.

## Replay

```bash
python3 tools/check_cow_hungarian_matching_certificate.py
```
