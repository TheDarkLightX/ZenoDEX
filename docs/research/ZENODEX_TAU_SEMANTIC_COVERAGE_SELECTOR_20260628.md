# ZenoDEX Tau Semantic Coverage Selector - 2026-06-28

## Executive Result

A replayable Tau certificate and report generator that converts runtime-active Tau semantic gaps into a deterministic promotion frontier.

The selector is advisory. Runtime kernels, host verifiers, and settlement code remain authoritative.

## Current Tau Coverage Frontier

- Runtime-active Tau specs: `112`
- Semantic contracts: `3`
- Formal contracts: `3`
- Review-packet-only specs: `0`
- Missing semantic contracts: `109`
- Refinement queue entries: `109`

## New Tau Specifications

| spec | work item | benefit |
| --- | --- | --- |
| `ab_ordering_held_karp_dp_certificate_v1` | `1_ab_ordering` | Certifies that an AB-ordering upgrade used full CPMM state, bounded brute-force parity, deterministic ties, state-cap fallback, and no settlement authority. |
| `cow_hungarian_matching_certificate_v1` | `2_cow_matching` | Certifies that an uncoupled CoW matching upgrade supplied primal/dual assignment evidence, bounded parity, grouped-capacity fallback, deterministic ties, and no settlement authority. |
| `tau_semantic_coverage_selector_certificate_v1` | `semantic_coverage_frontier` | Certifies that the active Tau inventory and refinement queue were replayed and that AB/CoW promotion targets remain selected. |

## Selected Promotion Targets

| spec | bucket | score | next action |
| --- | --- | ---: | --- |
| `settlement_canonical_order_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_module_flag_bundle_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_no_sandwich_aligned_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_price_rails_aligned_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_price_stability_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_v1_proof_gate` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_v2_buyback_proof_gate` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_v3_buyback_floor_proof_gate` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_v4_buyback_floor_rebate_lock` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_v4_buyback_floor_rebate_lock_proof_gate` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `settlement_v5_aligned_compact_bundle` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `swap_bv32_safe_range_guard_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `swap_exact_in_fee_proof_gate_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `swap_exact_in_proof_gate_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `swap_exact_in_protocol_fee_apply_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `swap_exact_in_v1` | `consensus_core` | `203` | write semantic contract; add formal contract or bounded proof note |
| `add_liquidity_apply_v1` | `spot_math_core` | `195` | write semantic contract; add formal contract or bounded proof note |
| `autotrader_budget_guard_v1` | `policy_gate` | `160` | write semantic contract; add formal contract or bounded proof note |
| `parameter_registry_v2` | `governance_tokenomics` | `150` | write semantic contract; add formal contract or bounded proof note |

## Work Items 1 And 2

### 1_ab_ordering

- Spec: `ab_ordering_held_karp_dp_certificate_v1`
- Target: Replace bounded brute-force AB ordering with a full-state Held-Karp subset-DP evidence path where the state cap permits it.
- Benefit: Moves the exact-solving frontier from factorial enumeration toward O(n^2 * 2^n) host search under explicit state-cap and parity gates.

### 2_cow_matching

- Spec: `cow_hungarian_matching_certificate_v1`
- Target: Use assignment-style primal/dual evidence for uncoupled CoW matching and fail closed for grouped capacity.
- Benefit: Gives CoW matching a polynomial exact certificate surface under the uncoupled-capacity scope.

## Tau Replay Evidence

- Tau surfaces: `3`
- Replay cases: `44`
- Required-fact mutations: `38`
- Invalid accepts: `0`
- False rejects: `0`

## Selector Facts

- `active_inventory_built`: `1`
- `advisory_selection_only`: `1`
- `budget_profile_ok`: `1`
- `coverage_gaps_present`: `1`
- `critical_bucket_coverage_ok`: `1`
- `deterministic_priority_order_ok`: `1`
- `mutation_atlas_dependency_bound`: `1`
- `no_runtime_authority_effect`: `1`
- `proposed_spec_artifacts_present`: `1`
- `selector_active`: `1`
- `semantic_contract_next_actions_bound`: `1`
- `semantic_refinement_queue_built`: `1`
- `tau_replay_invalid_accepts_zero`: `1`
- `work_item_1_ab_selected`: `1`
- `work_item_2_cow_selected`: `1`

## Non-Claims

- This artifact does not prove the proposed host algorithms correct.
- This artifact does not authorize settlement, oracle updates, governance actions, or state roots.
- The selector ranks the current bounded repo inventory and proposed work-item specs; it does not rank an unbounded Tau language space.
- The AB certificate does not validate compressed one-record Held-Karp state.
- The CoW certificate does not claim arbitrary grouped-capacity matching is polynomial.

## Replay

```bash
python3 tools/zenodex_tau_semantic_coverage_selector_20260628.py
```
