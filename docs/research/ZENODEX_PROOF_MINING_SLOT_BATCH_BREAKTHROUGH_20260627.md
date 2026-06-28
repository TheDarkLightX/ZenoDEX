# ZenoDEX Proof-Mining Slot Batch Breakthrough - 2026-06-27

## Executive Result

A bounded exact oracle minimizes proof-mining slot displacement over the 8-slot registry and emits a certificate that Tau can admit through host-projected proof facts.

The Tau spec admits a certificate envelope only. It cannot pay rewards, mutate claimed slots, or authorize settlement.

- Spec: `src/tau_specs/recommended/proof_mining_slot_batch_certificate_v1.tau`
- Tau replay ok: `True`
- Tau version: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Certificate cases: `5`
- Lift cases over sequential linear probing: `4`

## Algorithm

Existing single-proposal assignment hashes to a preferred slot and linear-probes for the first free slot.

Batch objective: `minimize(max_cyclic_displacement, total_cyclic_displacement, sorted_displacements_desc, slots_by_input_order)`.
At most P(8, k) assignments for k new proposals; the largest replay case uses k=6 and evaluates 20160 assignments.

This is a research oracle/certificate surface. Runtime activation needs a versioned batch command because it can assign earlier proposals to non-linear-probe slots.

## Certificate Cases

| case | preferred slots | candidates | sequential key | exact key | lift |
| --- | --- | ---: | --- | --- | --- |
| `no_collision_parity` | `[0, 1, 2, 3]` | `1680` | `[0, 0, [0, 0, 0, 0], [0, 1, 2, 3]]` | `[0, 0, [0, 0, 0, 0], [0, 1, 2, 3]]` | `False` |
| `interleaved_collision_lift` | `[0, 1, 0]` | `336` | `[2, 2, [2, 0, 0], [0, 1, 2]]` | `[1, 2, [1, 1, 0], [0, 2, 1]]` | `True` |
| `wraparound_tail_lift` | `[0, 7, 7, 7]` | `1680` | `[3, 5, [3, 2, 0, 0], [0, 7, 1, 2]]` | `[2, 5, [2, 2, 1, 0], [2, 0, 1, 7]]` | `True` |
| `occupied_preferred_slot_lift` | `[1, 0]` | `42` | `[2, 2, [2, 0], [1, 2]]` | `[1, 2, [1, 1], [2, 1]]` | `True` |
| `six_proposal_pressure` | `[0, 1, 0, 7, 7, 0]` | `20160` | `[4, 10, [4, 4, 2, 0, 0, 0], [0, 1, 2, 7, 3, 4]]` | `[3, 10, [3, 3, 2, 1, 1, 0], [1, 4, 2, 0, 7, 3]]` | `True` |

## Tau Specification Frontier

| spec | benefit | status |
| --- | --- | --- |
| `src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau` | Gates work item 1 AB subset-DP certificates and work item 2 CoW exact-matching certificates. | existing supported rail; replay with tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py |
| `src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau` | Compresses optimizer proof surfaces into domain-hash-bound quotient certificates. | existing supported rail; replay with tools/zenodex_tau_optimizer_quotient_breakthrough_20260627.py |
| `src/tau_specs/recommended/proof_mining_slot_batch_certificate_v1.tau` | New bounded exact certificate lane for proof-mining slot assignment collisions. | implemented in this report |

## Work Items 1 And 2

1. Held-Karp-style subset DP remains the high-value algorithm target for same-direction AB batches; the existing Tau envelope gates the certificate facts while host code computes the DP.
2. Hungarian matching remains the clean exact reduction for uncoupled CoW batches; the existing Tau envelope gates the assignment certificate facts while host code computes matching.

## Mutation Checks

| mutation | rejected | error |
| --- | --- | --- |
| `bad_domain_hash` | `True` | `domain hash mismatch` |
| `duplicate_assigned_slot` | `True` | `duplicate assigned slot` |
| `bad_objective_key` | `True` | `objective key mismatch` |

## Non-Claims

- The new slot-batch oracle is not wired into runtime proof payout flow.
- The certificate is bounded to the current 8-slot registry.
- Tau does not compute hashes, enumerate assignments, or decide payouts.
- Work items 1 and 2 keep their existing host/kernel exactness boundaries.

## Replay

```bash
python3 tools/zenodex_proof_mining_slot_batch_breakthrough_20260627.py
```
