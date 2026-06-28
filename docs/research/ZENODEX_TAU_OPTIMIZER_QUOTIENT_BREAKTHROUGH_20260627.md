# ZenoDEX Tau Optimizer Quotient Breakthrough - 2026-06-27

## Executive Result

A Tau host-projected quotient certificate turns bounded route-label domains into small domain-hash-bound proof packets and provides the same admission shape for AB ordering and CoW matching proof surfaces.

Tau admits optimizer certificates only; deterministic host/kernel verifiers remain authoritative for settlement, routing, and matching.

## Breakthrough Specification

- Spec: `src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau trace replay ok: `True`
- Tau elapsed: `55.179364s`

The spec accepts exactly one optimizer mode per step: route dominance, AB ordering, or CoW matching. It requires a domain commitment, quotient witness, canonical winner proof, replay, projection cover, arithmetic scope, resource budget, fallback, no-authority, and non-vacuity.

## Route Quotient Evidence

Route cases: `3`. Max labels: `215`. Min compression ratio: `41.55x`. Max compression ratio: `177.47x`.

| case | labels | full bytes | cert bytes | ratio | selected |
| --- | ---: | ---: | ---: | ---: | --- |
| `baseline_route_amount42` | `45` | `16247` | `391` | `41.55x` | `twohop:p_ac>p_cb` |
| `wide_split_route_amount36` | `215` | `71697` | `404` | `177.47x` | `direct:p_ab_direct_3` |
| `twohop_route_amount48` | `53` | `19398` | `418` | `46.41x` | `twohop:p_ac_thin>p_cb_fee` |

The verifier recomputes the route-label domain, checks the domain hash, proves that the selected label is the canonical minimum under the objective key, and confirms that every omitted label is covered by the single selected representative.

## Tau Mode Checks

| case | ok | rationale |
| --- | --- | --- |
| `route_quotient_pass` | `True` | A fully verified route quotient certificate admits only the route output. |
| `ab_work_item_1_pass` | `True` | The same quotient surface admits an AB full-state subset-DP certificate. |
| `cow_work_item_2_pass` | `True` | The same quotient surface admits an uncoupled CoW assignment certificate. |
| `domain_commitment_reject` | `True` | A stale or mismatched domain hash fails closed. |
| `quotient_witness_reject` | `True` | A missing representative/dominator witness cannot admit. |
| `two_modes_reject` | `True` | Two optimizer modes fail one-hot decoding. |
| `authority_reject` | `True` | A certificate with authority-bearing effects is rejected. |
| `inactive_safe` | `True` | Inactive requests do not admit, while the no-authority rail remains safe. |

## Work Items 1 And 2

### 1. AB Ordering

The same quotient envelope can gate a domain-hash-bound full-state subset-DP certificate without putting DP state expansion in Tau.

### 2. CoW Matching

The same quotient envelope can gate an uncoupled Hungarian assignment certificate and reject stale, authority-bearing, or grouped-capacity proof surfaces.

## Tau Language Design Frontier

Use Tau for small Boolean proof-surface composition and mode diagnostics; keep hashes, large arithmetic, route enumeration, DP, and matching in deterministic host/kernel code.

This spec uses `14` inputs, `8` outputs, `10` host-projected proof facts, and `0` direct bitvector operations.

## Mutation Checks

| mutation | accepted | failed flags |
| --- | --- | --- |
| `bad_domain_hash` | `False` | `domain_commitment_ok` |
| `bad_selected_route` | `False` | `quotient_witness_ok`, `canonical_winner_ok` |
| `bad_label_count` | `False` | `quotient_witness_ok`, `projection_cover_ok` |

## Non-Claims

- The route measurement covers the bounded direct/two-hop/parallel-split label generator used by the refuter, not every possible path family.
- The quotient certificate commits to a recomputable domain; it is not useful without host replay of that domain.
- Tau does not compute the domain hash or the optimizer winner.
- The AB and CoW modes are proof-surface gates for existing host algorithms, not new settlement authority.

## Replay

```bash
python3 tools/zenodex_tau_optimizer_quotient_breakthrough_20260627.py
```
